// rcu_rules.h -- the type rules as transfer functions.
//
// Each rule takes a type environment and the operands of a statement, and
// returns either the post-environment or a diagnosis.  Together with join at
// merges and analyzeLoop at back edges, this is the forward dataflow that
// checks a critical section.
//
// Diagnostics are strings rather than codes because the checker infers its
// environments: when a rule does not apply, the programmer has no annotation to
// look at, so the message has to say which premise failed and on what.  That is
// the cost of inferring rather than annotating, and it has to be paid here.
//
// The framing premises are the interesting part.  Each mutation must leave
// every other reference in the environment valid, which is where MayAlias is
// used -- always under a negation, so over-approximating rejects safe programs
// but never accepts unsafe ones.

#ifndef RCU_RULES_H
#define RCU_RULES_H

#include "rcu_types.h"

#include <functional>
#include <sstream>

namespace rcu {

struct Result {
  bool ok = false;
  TypeEnv env;
  std::string why;

  static Result yes(TypeEnv g) { Result r; r.ok = true; r.env = std::move(g); return r; }
  static Result no(std::string w) { Result r; r.ok = false; r.why = std::move(w); return r; }
};

namespace detail {

inline const Type *lookup(const TypeEnv &g, int x) {
  auto it = g.find(x);
  return it == g.end() ? nullptr : &it->second;
}

// Diagnostics name variables and fields as the source does.  The checker works
// in dense ids; a frontend installs a resolver so that a message reads "cur"
// rather than "v1".  This matters more here than usual: the environments are
// inferred, so there is no annotation for the reader to compare against and the
// message is the only thing they have.
inline std::function<std::string(int)> &varNamer() {
  static std::function<std::string(int)> f =
      [](int v) { return "v" + std::to_string(v); };
  return f;
}
inline std::function<std::string(int)> &fieldNamer() {
  static std::function<std::string(int)> f =
      [](int v) { return std::to_string(v); };
  return f;
}

inline std::string name(int v) { return varNamer()(v); }

// A field-set key, for diagnostics: "1" for a single field, "0|1" for a
// disjunctive one.
inline std::string fieldsToString(FieldSet k) {
  std::string out;
  for (int f = 0; f < 32; ++f)
    if (k & bit(f)) { if (!out.empty()) out += "|"; out += fieldNamer()(f); }
  return out.empty() ? "-" : out;
}

// Extending a path by a field-map key: a singleton key is one step along that
// field, a disjunctive key one step along any of them.
inline Path extend(const Path &p, FieldSet k) {
  Path q = p; q.push_back(mkStep(k)); return q;
}

}  // namespace detail

// ---------------------------------------------------------------------------
// Reading
// ---------------------------------------------------------------------------

// T-Root: y = r, with r the root.  The reader and the writer both get an
// iterator at the empty path.
inline Result tRoot(TypeEnv g, int r, int y) {
  const Type *tr = detail::lookup(g, r);
  if (!tr || tr->kind != Type::Root)
    return Result::no(detail::name(r) + " is not the root");
  g[y] = tItr(Path{});
  return Result::yes(std::move(g));
}

// T-ReadH: z = x.f.  The read is recorded in x's field map -- that is what
// makes the relationship between x and z available to later rules -- and z gets
// x's path extended by f.
inline Result tReadH(TypeEnv g, int x, FieldSet f, int z) {
  const Type *tx = detail::lookup(g, x);
  if (!tx || tx->kind != Type::Itr)
    return Result::no(detail::name(x) + " is not an iterator, so " +
                      detail::name(x) + "." + detail::fieldsToString(f) +
                      " cannot be read into an iterator");
  Path px = tx->path;
  FieldMap nx = tx->fields;
  nx[f] = fvVar(z);
  g[x] = tItr(px, nx);
  g[z] = tItr(detail::extend(px, f));
  return Result::yes(std::move(g));
}

// ---------------------------------------------------------------------------
// Building a fresh node
// ---------------------------------------------------------------------------

inline Result tAlloc(TypeEnv g, int x) {
  g[x] = tFresh();
  return Result::yes(std::move(g));
}

// T-WriteFH: p.f = z, writing a field of a fresh node.  The rule requires the
// field to be untracked so far, which is what keeps the fresh node's map
// growing monotonically -- and is what makes the denotation's "every RCU field
// outside dom(N) is null" an invariant rather than an assumption.
inline Result tWriteFH(TypeEnv g, int p, FieldSet f, int z) {
  const Type *tp = detail::lookup(g, p);
  if (!tp || tp->kind != Type::Fresh)
    return Result::no(detail::name(p) + " is not a fresh node");
  if (tp->fields.count(f))
    return Result::no("field " + detail::fieldsToString(f) + " of " + detail::name(p) +
                      " has already been written");
  const Type *tz = detail::lookup(g, z);
  if (!tz || tz->kind != Type::Itr)
    return Result::no(detail::name(z) + " is not an iterator, so it cannot be "
                      "stored into a fresh node");
  FieldMap np = tp->fields;
  np[f] = fvVar(z);
  g[p] = tFresh(np);
  return Result::yes(std::move(g));
}

// ---------------------------------------------------------------------------
// Field refinement
// ---------------------------------------------------------------------------

// In the branch where x.f == y is known to hold, the entry that recorded y
// under a disjunctive key is refined to f alone, and y's path is refined with
// it.
//
// This is the rule the paper describes as "one field-refining rule per control
// flow construct".  It is needed because a loop leaves the field through which
// a child was reached known only disjunctively -- after the BST's outer loop,
// parent : rcuItr (l|r)^k {l|r -> current} -- while the mutation rules need a
// concrete field.  The BST delete tests `parent.Left == current` for exactly
// this reason, and without the rule the replacement that follows cannot be
// typed at all.
inline Result tRefineField(TypeEnv g, int x, FieldSet f, int y) {
  const Type *tx = detail::lookup(g, x);
  if (!tx || tx->kind != Type::Itr)
    return Result::no(detail::name(x) + " is not an iterator");
  const Type *ty = detail::lookup(g, y);
  if (!ty || ty->kind != Type::Itr)
    return Result::no(detail::name(y) + " is not an iterator");

  for (auto it = tx->fields.begin(); it != tx->fields.end(); ++it) {
    if ((it->first & f) != f) continue;
    if (!(it->second == fvVar(y))) continue;
    FieldMap n = tx->fields;
    n.erase(it->first);
    n[f] = fvVar(y);
    Path px = tx->path;
    g[x] = tItr(px, n);
    // y is now known to sit at x's path extended by f, not by the disjunction
    g[y] = tItr(detail::extend(px, f), ty->fields);
    return Result::yes(std::move(g));
  }
  return Result::no("no field map entry of " + detail::name(x) +
                    " records " + detail::name(y) + " under a key containing " +
                    detail::fieldsToString(f));
}

// In the branch where x.f == NULL holds, the field map records it as null.
//
// T-UnlinkH needs this and cannot get it any other way: its premise is that
// every field of the unlinked node other than the one being spliced is null,
// and a field map entry only ever records a *variable* until something proves
// otherwise.  The proof is the test the code already performs -- the BST
// delete's `if (current.Right == null)` exists for exactly this.
inline Result tRefineNull(TypeEnv g, int x, FieldSet f) {
  const Type *tx = detail::lookup(g, x);
  if (!tx || (tx->kind != Type::Itr && tx->kind != Type::Fresh))
    return Result::no(detail::name(x) + " is not a reference with fields");
  FieldMap n = tx->fields;
  n[f] = fvNull();
  g[x] = (tx->kind == Type::Itr) ? tItr(tx->path, n) : tFresh(n);
  return Result::yes(std::move(g));
}

// ---------------------------------------------------------------------------
// The framing premises
// ---------------------------------------------------------------------------

namespace detail {

// No other iterator may alias the paths under mutation, and none may hold a
// field-map entry naming a node whose type is about to change.
inline std::string frameItr(const TypeEnv &g, const std::vector<int> &actors,
                            const std::vector<Path> &under,
                            const std::vector<int> &victims, int numFields) {
  for (const auto &kv : g) {
    if (kv.second.kind != Type::Itr) continue;
    // The rules quantify over x:rcuItr rho N([f |-> y]) -- an iterator with a
    // field map *entry*.  One with an empty map is not constrained, and should
    // not be: what the premise protects is a map going stale when the mutation
    // changes the field it records, and an empty map records nothing.
    // Checking every iterator instead rejects a live root reference whenever a
    // traversal might have taken zero steps, which is the paper's own example.
    if (kv.second.fields.empty()) continue;
    bool isActor = false;
    for (int a : actors) if (a == kv.first) isActor = true;
    if (isActor) continue;
    if (mayAlias(kv.second.path, under, numFields))
      return name(kv.first) + " may alias a path under mutation";
    for (const auto &fe : kv.second.fields)
      if (fe.second.kind == FieldVal::Var)
        for (int v : victims)
          if (fe.second.var == v)
            return name(kv.first) + " has a field map entry naming " + name(v);
  }
  return "";
}

}  // namespace detail

// ---------------------------------------------------------------------------
// The three mutations
// ---------------------------------------------------------------------------

// T-UnlinkH: x.f1 = r, where x.f1 == z and z.f2 == r.  Removes z.
inline Result tUnlinkH(TypeEnv g, int x, FieldSet f1, int z, FieldSet f2, int r,
                       int numFields) {
  const Type *tx = detail::lookup(g, x);
  const Type *tz = detail::lookup(g, z);
  const Type *tr = detail::lookup(g, r);
  if (!tx || tx->kind != Type::Itr) return Result::no(detail::name(x) + " is not an iterator");
  if (!tz || tz->kind != Type::Itr) return Result::no(detail::name(z) + " is not an iterator");
  if (!tr || tr->kind != Type::Itr) return Result::no(detail::name(r) + " is not an iterator");

  auto nf1 = tx->fields.find(f1);
  if (nf1 == tx->fields.end() || nf1->second != fvVar(z))
    return Result::no("the rule needs " + detail::name(x) + "." +
                      detail::fieldsToString(f1) + " == " + detail::name(z) +
                      ", which is not in its field map");
  auto nf2 = tz->fields.find(f2);
  if (nf2 == tz->fields.end() || nf2->second != fvVar(r))
    return Result::no("the rule needs " + detail::name(z) + "." +
                      detail::fieldsToString(f2) + " == " + detail::name(r) +
                      ", which is not in its field map");
  // all other fields of z null: unlinking must remove one node, not a subtree
  for (const auto &fe : tz->fields)
    if (fe.first != f2 && fe.second.kind != FieldVal::Null)
      return Result::no("unlinking " + detail::name(z) + " would detach more "
                        "than one node: its field " + detail::fieldsToString(fe.first) +
                        " is not null");
  // the premise added to close the FPI defect
  if (!noFreshPointsAt(g, z))
    return Result::no("a fresh reference has a field pointing at " +
                      detail::name(z) + ", which is about to be unlinked");

  std::string bad = detail::frameItr(g, {x, z, r},
                                     {tx->path, tz->path, tr->path}, {z, r},
                                     numFields);
  if (!bad.empty()) return Result::no(bad);

  FieldMap nx = tx->fields; nx[f1] = fvVar(r);
  g[x] = tItr(tx->path, nx);
  g[r] = tItr(tz->path, tr->fields);   // r takes z's place
  g[z] = tUnlinked();
  return Result::yes(std::move(g));
}

// T-Replace: p.f = n, replacing o by the fresh node n.
inline Result tReplace(TypeEnv g, int p, FieldSet f, int o, int n,
                       FieldSet rcuFields, int numFields) {
  const Type *tp = detail::lookup(g, p);
  const Type *to = detail::lookup(g, o);
  const Type *tn = detail::lookup(g, n);
  if (!tp || tp->kind != Type::Itr)   return Result::no(detail::name(p) + " is not an iterator");
  if (!to || to->kind != Type::Itr)   return Result::no(detail::name(o) + " is not an iterator");
  if (!tn || tn->kind != Type::Fresh) return Result::no(detail::name(n) + " is not a fresh node");

  auto nf = tp->fields.find(f);
  if (nf == tp->fields.end() || nf->second != fvVar(o))
    return Result::no("the rule needs " + detail::name(p) + "." +
                      detail::fieldsToString(f) + " == " + detail::name(o));
  if (to->path != detail::extend(tp->path, f))
    return Result::no(detail::name(o) + "'s path is not " + detail::name(p) +
                      "'s extended by " + detail::fieldsToString(f));
  if (!(to->fields == tn->fields))
    return Result::no("the fresh node's field map differs from the one it "
                      "replaces, so it would not mirror it");
  // repair: the maps must pin every RCU field, or an untracked one may differ
  if (!coversRCUFields(to->fields, rcuFields, numFields))
    return Result::no("the field map of " + detail::name(o) + " does not cover "
                      "every RCU field, so the replacement need not mirror it; "
                      "read the remaining fields before replacing");
  // repair: no fresh reference may point at the node being unlinked
  if (!noFreshPointsAt(g, o))
    return Result::no("a fresh reference has a field pointing at " +
                      detail::name(o) + ", which is about to be unlinked");

  std::string bad = detail::frameItr(g, {p, o, n}, {tp->path, to->path}, {o},
                                     numFields);
  if (!bad.empty()) return Result::no(bad);

  FieldMap np = tp->fields; np[f] = fvVar(n);
  g[p] = tItr(tp->path, np);
  g[n] = tItr(to->path, tn->fields);
  g[o] = tUnlinked();
  return Result::yes(std::move(g));
}

// T-Insert: p.f = n, splicing the fresh node n above o.  Unlinks nothing.
inline Result tInsert(TypeEnv g, int p, FieldSet f, int o, int n, FieldSet f4,
                      int numFields) {
  const Type *tp = detail::lookup(g, p);
  const Type *to = detail::lookup(g, o);
  const Type *tn = detail::lookup(g, n);
  if (!tp || tp->kind != Type::Itr)   return Result::no(detail::name(p) + " is not an iterator");
  if (!to || to->kind != Type::Itr)   return Result::no(detail::name(o) + " is not an iterator");
  if (!tn || tn->kind != Type::Fresh) return Result::no(detail::name(n) + " is not a fresh node");

  auto nf = tp->fields.find(f);
  if (nf == tp->fields.end() || nf->second != fvVar(o))
    return Result::no("the rule needs " + detail::name(p) + "." +
                      detail::fieldsToString(f) + " == " + detail::name(o));
  auto n4 = tn->fields.find(f4);
  if (n4 == tn->fields.end() || n4->second != fvVar(o))
    return Result::no("the fresh node's field " + detail::fieldsToString(f4) +
                      " must already point at " + detail::name(o));
  if (!onlyFieldIs(tn->fields, f4))
    return Result::no("the fresh node has a second link, so inserting it would "
                      "give it two children");

  std::string bad = detail::frameItr(g, {p, o, n}, {tp->path}, {}, numFields);
  if (!bad.empty()) return Result::no(bad);

  FieldMap np = tp->fields; np[f] = fvVar(n);
  g[p] = tItr(tp->path, np);
  g[n] = tItr(to->path, tn->fields);
  g[o] = tItr(detail::extend(to->path, f4), to->fields);
  return Result::yes(std::move(g));
}

// ---------------------------------------------------------------------------
// Reclamation
// ---------------------------------------------------------------------------

// T-Sync: the grace period.  Everything unlinked becomes freeable.
inline Result tSync(TypeEnv g) {
  for (auto &kv : g)
    if (kv.second.kind == Type::Unlinked) kv.second = tFreeable();
  return Result::yes(std::move(g));
}

// T-Free.  Only a freeable reference may be freed, which is what the grace
// period is for.
inline Result tFree(TypeEnv g, int x) {
  const Type *tx = detail::lookup(g, x);
  if (!tx) return Result::no(detail::name(x) + " is not in scope");
  if (tx->kind == Type::Unlinked)
    return Result::no(detail::name(x) + " is unlinked but not yet freeable: a "
                      "grace period must elapse first");
  if (tx->kind != Type::Freeable)
    return Result::no(detail::name(x) + " is not freeable");
  g[x] = tUndef();
  return Result::yes(std::move(g));
}

}  // namespace rcu

#endif  // RCU_RULES_H
