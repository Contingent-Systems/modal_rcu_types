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

inline Result applyStmt(const TypeEnv &g, const Stmt &s, const Config &cfg) {
  switch (s.kind) {
    case Stmt::Root:        return tRoot(g, s.x, s.y);
    case Stmt::ReadH:       return tReadH(g, s.x, s.f, s.z);
    case Stmt::Alloc:       return tAlloc(g, s.x);
    case Stmt::WriteFH:     return tWriteFH(g, s.x, s.f, s.z);
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
  std::vector<int> succs;
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
  std::pair<Env, std::vector<int>> pe = projectPaths(entry);
  std::pair<Env, std::vector<int>> px = projectPaths(exit);
  if (pe.second != px.second) return std::nullopt;  // different variables live
  if (reindex(pe.first, px.first)) return entry;     // closes as it stands
  std::optional<Env> w = widen(pe.first, px.first, freshVar);
  if (!w) return std::nullopt;
  TypeEnv out = entry;
  injectPaths(out, *w, pe.second);
  return out;
}

// Forward dataflow.  Blocks are visited from a worklist; a block is re-visited
// when an incoming environment changes.  Merges use joinEnv, which rejects
// rather than inventing a join for incompatible kinds.
inline CheckResult check(const Cfg &cfg, const TypeEnv &initial,
                         const Config &conf, int maxRounds = 64) {
  CheckResult res;
  res.entry.assign(cfg.size(), TypeEnv{});
  std::vector<bool> seen(cfg.size(), false);
  std::deque<int> work;

  if (!cfg.empty()) { res.entry[0] = initial; seen[0] = true; work.push_back(0); }

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
      std::optional<TypeEnv> m = joinEnv(res.entry[s], incoming);
      if (!m) {
        res.ok = false;
        res.errors.push_back(Diagnosis{
            s, -1, 0,
            "the environments reaching this point cannot be merged: a "
            "reference has different kinds on different paths"});
        continue;
      }
      if (!(*m == res.entry[s])) { res.entry[s] = *m; work.push_back(s); }
    }
  }
  return res;
}

}  // namespace rcu

#endif  // RCU_CHECK_H
