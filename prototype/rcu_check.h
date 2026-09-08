// rcu_check.h -- the statement IR and the dataflow driver.
//
// This is the boundary between a compiler frontend and the checker.  The
// frontend's whole job is to translate a function body into the Stmt IR below;
// everything after that is here and is dependency-free, so the checker can be
// developed, tested and debugged without a compiler in the loop, and lifted
// into one without changing.
//
// The IR is deliberately small.  It contains exactly the actions the type
// system has rules for, and nothing about C: no expressions, no types, no
// declarations.  Recognising which C constructs produce which action is the
// frontend's problem, and the table in apiAction() below is that contract.

#ifndef RCU_CHECK_H
#define RCU_CHECK_H

#include "rcu_rules.h"

#include <deque>
#include <set>

namespace rcu {

// ---------------------------------------------------------------------------
// Statements
// ---------------------------------------------------------------------------

struct Stmt {
  enum Kind {
    Root,         // y = <the root>
    ReadS,        // z = x
    ReadH,        // z = x.f
    Alloc,        // x = new
    WriteFH,      // p.f = z, p fresh
    UnlinkH,      // x.f1 = r, unlinking z where x.f1==z and z.f2==r
    Replace,      // p.f = n, replacing o
    Insert,       // p.f = n, splicing n above o
    Sync,         // SyncStart; SyncStop
    Free,         // free(x)
    RefineField,  // assume x.f == y
    Nop
  } kind = Nop;

  int x = -1, y = -1, z = -1, r = -1, n = -1, o = -1;
  FieldSet f = 0, f2 = 0, f4 = 0;
  int line = 0;  // for diagnostics
};

// ---------------------------------------------------------------------------
// What a frontend must recognise
// ---------------------------------------------------------------------------
//
// The contract with the frontend, and the reason no new annotation language is
// needed: every action below is already a distinguishable construct in RCU
// source.  Kernel spellings are given; a user-level codebase substitutes its
// own, and only this table changes.
//
//   rcu_dereference(x->f)        ReadH
//   rcu_assign_pointer(p->f, n)  one of WriteFH / UnlinkH / Replace / Insert,
//                                decided by the types of p and n in the
//                                environment at that point -- which the checker
//                                knows and the frontend does not, so the
//                                frontend emits the assignment and the driver
//                                selects the rule
//   synchronize_rcu()            Sync
//   kfree(x) / call_rcu(x, ...)  Free
//   rcu_read_lock/unlock         critical section boundaries
//   __rcu on a struct field      marks the field RCU-typed
//
// Only the root needs marking, because nothing in the source distinguishes it.
inline const char *apiAction(Stmt::Kind k) {
  switch (k) {
    case Stmt::ReadH:   return "rcu_dereference";
    case Stmt::Sync:    return "synchronize_rcu";
    case Stmt::Free:    return "kfree";
    case Stmt::Alloc:   return "allocation";
    default:            return "assignment";
  }
}

// ---------------------------------------------------------------------------
// Applying one statement
// ---------------------------------------------------------------------------

struct Config {
  FieldSet rcuFields = 0;
  int numFields = 0;
};

// A field write is one of four rules, and which one depends on the types of the
// operands rather than on the syntax -- rcu_assign_pointer(p->f, n) is a write
// to a fresh node, a replacement, an insertion or an unlink according to what p
// and n are at that point.  The frontend cannot tell; the driver can, so it
// tries each applicable rule and accepts if one applies.  Each rule is sound on
// its own, so accepting when any applies is sound.
//
// The operands the rules need beyond the statement -- the node being replaced,
// the field the fresh node already links through -- are read out of the
// environment rather than guessed.
inline Result applyWrite(const TypeEnv &g, const Stmt &s, const Config &cfg) {
  const Type *tx = detail::lookup(g, s.x);
  const Type *tz = detail::lookup(g, s.z);
  if (!tx) return Result::no(detail::name(s.x) + " is not in scope");
  if (!tz) return Result::no(detail::name(s.z) + " is not in scope");

  // writing a field of a fresh node
  if (tx->kind == Type::Fresh) return tWriteFH(g, s.x, s.f, s.z);

  // what the field currently holds, which the other three rules need
  int victim = -1;
  auto it = tx->fields.find(s.f);
  if (it != tx->fields.end() && it->second.kind == FieldVal::Var)
    victim = it->second.var;
  if (victim < 0)
    return Result::no("the field being written is not in " + detail::name(s.x) +
                      "'s field map, so what it currently holds is unknown; "
                      "read it before writing it");

  if (tz->kind == Type::Fresh) {
    // replacement, or insertion if the fresh node already links to the victim
    for (const auto &fe : tz->fields)
      if (fe.second.kind == FieldVal::Var && fe.second.var == victim) {
        Result r = tInsert(g, s.x, s.f, victim, s.z, fe.first, cfg.numFields);
        if (r.ok) return r;
      }
    return tReplace(g, s.x, s.f, victim, s.z, cfg.rcuFields, cfg.numFields);
  }

  // unlinking: the written value must be a grandchild through some field
  const Type *tv = detail::lookup(g, victim);
  if (tv)
    for (const auto &fe : tv->fields)
      if (fe.second.kind == FieldVal::Var && fe.second.var == s.z)
        return tUnlinkH(g, s.x, s.f, victim, fe.first, s.z, cfg.numFields);
  return Result::no("writing " + detail::name(s.z) + " over " +
                    detail::name(victim) + " is not one of the four heap "
                    "mutations: it is neither fresh nor a child of " +
                    detail::name(victim));
}

inline Result applyStmt(const TypeEnv &g, const Stmt &s, const Config &cfg) {
  switch (s.kind) {
    case Stmt::Root:        return tRoot(g, s.x, s.y);
    case Stmt::ReadH:       return tReadH(g, s.x, s.f, s.z);
    case Stmt::Alloc:       return tAlloc(g, s.x);
    case Stmt::WriteFH:     return applyWrite(g, s, cfg);
    case Stmt::UnlinkH:     return tUnlinkH(g, s.x, s.f, s.z, s.f2, s.r, cfg.numFields);
    case Stmt::Replace:     return tReplace(g, s.x, s.f, s.o, s.n, cfg.rcuFields, cfg.numFields);
    case Stmt::Insert:      return tInsert(g, s.x, s.f, s.o, s.n, s.f4, cfg.numFields);
    case Stmt::Sync:        return tSync(g);
    case Stmt::Free:        return tFree(g, s.x);
    case Stmt::RefineField: return tRefineField(g, s.x, s.f, s.y);
    case Stmt::ReadS: {
      const Type *tx = detail::lookup(g, s.x);
      if (!tx || tx->kind != Type::Itr)
        return Result::no(detail::name(s.x) + " is not an iterator");
      TypeEnv h = g;
      h[s.z] = tItr(tx->path);
      return Result::yes(std::move(h));
    }
    case Stmt::Nop:         return Result::yes(g);
  }
  return Result::yes(g);
}

// ---------------------------------------------------------------------------
// Control flow
// ---------------------------------------------------------------------------

struct Block {
  std::vector<Stmt> stmts;
  std::vector<int> succs;      // ordinary edges, merged with joinEnv
  std::vector<int> backSuccs;  // loop back edges, closed with closeBackEdge
};
using Cfg = std::vector<Block>;

struct Diagnosis {
  int block = -1, index = -1, line = 0;
  std::string why;
};

struct CheckResult {
  bool ok = true;
  std::vector<Diagnosis> errors;
  std::vector<TypeEnv> entry;  // environment on entry to each block
};

// Projecting a type environment onto the path domain and back.  Env is "one
// path per RCU-typed local, positionally", so the order has to be stable; the
// sorted variable ids give that.
inline std::pair<Env, std::vector<int>> projectPaths(const TypeEnv &g) {
  Env e;
  std::vector<int> order;
  for (const auto &kv : g)
    if (kv.second.kind == Type::Itr) { e.push_back(kv.second.path); order.push_back(kv.first); }
  return {e, order};
}

inline void injectPaths(TypeEnv &g, const Env &e, const std::vector<int> &order) {
  for (size_t i = 0; i < order.size() && i < e.size(); ++i) {
    auto it = g.find(order[i]);
    if (it != g.end() && it->second.kind == Type::Itr) it->second.path = e[i];
  }
}

// A back edge whose exit environment is not the entry environment needs the
// loop machinery rather than a join: reindex if the exit is the entry with the
// counter advanced, widen otherwise.  Returns the environment to re-enter the
// loop with, or nothing if the loop does not converge -- which is a diagnosis,
// not a crash.
//
// This is separate from check() below, which handles straight-line code and
// branch/merge.  Wiring it in needs the back edges identified, which is
// dominator information the frontend has and this IR deliberately does not
// carry.
inline std::optional<TypeEnv> closeBackEdge(const TypeEnv &entry,
                                            const TypeEnv &exit,
                                            int freshVar) {
  // Only iterators live at *both* ends take part.  A variable declared inside
  // the body is live at the back edge and not at the head, and demanding the
  // two agree would fail every loop that declares one -- which is most of them.
  std::vector<int> order;
  Env pe, px;
  for (const auto &kv : entry) {
    if (kv.second.kind != Type::Itr) continue;
    auto it = exit.find(kv.first);
    if (it == exit.end() || it->second.kind != Type::Itr) continue;
    order.push_back(kv.first);
    pe.push_back(kv.second.path);
    px.push_back(it->second.path);
  }
  if (order.empty()) return entry;
  if (reindex(pe, px)) return entry;          // closes as it stands
  std::optional<Env> w = widen(pe, px, freshVar);
  if (!w) return std::nullopt;
  TypeEnv out = entry;
  injectPaths(out, *w, order);
  return out;
}

// Back edges are separated from ordinary ones because they need different
// treatment: an ordinary merge joins two environments, while a loop must be
// closed by reindexing or widening, which is what turns a traversal's growing
// path into a loop-invariant one.  Joining a back edge instead would either
// fail (the paths differ) or lose the relationship between cursors that the
// field maps depend on.
//
// Which edges are back edges is dominator information, which the frontend
// computes and passes in rather than this layer rediscovering.
inline CheckResult check(const Cfg &cfg, const TypeEnv &initial,
                         const Config &conf, int entryBlock = 0,
                         int maxRounds = 64) {
  CheckResult res;
  res.entry.assign(cfg.size(), TypeEnv{});
  std::vector<bool> seen(cfg.size(), false);
  std::deque<int> work;

  if (!cfg.empty() && entryBlock >= 0 && entryBlock < int(cfg.size())) {
    res.entry[entryBlock] = initial;
    seen[entryBlock] = true;
    work.push_back(entryBlock);
  }

  int freshVar = 1000;  // path variables introduced by widening
  int rounds = 0;
  while (!work.empty() && rounds++ < maxRounds * int(cfg.size())) {
    int b = work.front(); work.pop_front();
    TypeEnv g = res.entry[b];

    bool failed = false;
    for (size_t i = 0; i < cfg[b].stmts.size(); ++i) {
      Result r = applyStmt(g, cfg[b].stmts[i], conf);
      if (!r.ok) {
        res.ok = false;
        res.errors.push_back(Diagnosis{b, int(i), cfg[b].stmts[i].line, r.why});
        failed = true;
        break;
      }
      g = std::move(r.env);
    }
    if (failed) continue;

    for (int s : cfg[b].succs) {
      TypeEnv incoming = g;
      if (!seen[s]) {
        res.entry[s] = incoming; seen[s] = true; work.push_back(s);
        continue;
      }
      int bad = -1; bool kindClash = false;
      std::optional<TypeEnv> m = joinEnvWhy(res.entry[s], incoming, &bad, &kindClash);
      if (!m) {
        res.ok = false;
        res.errors.push_back(Diagnosis{
            s, -1, cfg[b].stmts.empty() ? 0 : cfg[b].stmts.back().line,
            kindClash
                ? (detail::name(bad) + " reaches this point with different "
                   "kinds on different paths, so there is no type it has here")
                : (detail::name(bad) + " reaches this point by paths that do "
                   "not join: the path abstraction cannot describe both")});
        continue;
      }
      if (!(*m == res.entry[s])) { res.entry[s] = *m; work.push_back(s); }
    }

    for (int s : cfg[b].backSuccs) {
      if (!seen[s]) continue;  // the head is always visited first
      std::optional<TypeEnv> closed = closeBackEdge(res.entry[s], g, freshVar++);
      if (!closed) {
        res.ok = false;
        res.errors.push_back(Diagnosis{
            b, -1, cfg[b].stmts.empty() ? 0 : cfg[b].stmts.back().line,
            "the loop does not converge: the paths at the back edge are "
            "neither a reindexing nor a widening of the paths at the head, so "
            "no loop-invariant environment was found"});
        continue;
      }
      if (!(*closed == res.entry[s])) {
        // Widening weakens the loop head.  Everything downstream was computed
        // from the stronger environment of the first pass, and joining the two
        // fails -- not because the program is wrong but because the earlier
        // result is stale.  Discard it and recompute from the weakened head.
        res.entry[s] = *closed;
        for (size_t i = 0; i < seen.size(); ++i)
          if (int(i) != s && int(i) != entryBlock) seen[i] = false;
        work.clear();
        work.push_back(s);
        break;
      }
    }
  }
  return res;
}

}  // namespace rcu

#endif  // RCU_CHECK_H
