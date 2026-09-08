// rcu_types.h -- the RCU type system's type and environment domain.
//
// Layer above path_domain.h: types, field maps, type environments, and the
// operations a forward dataflow needs over them.  Dependency-free C++17, same
// as the layer below, and written to be lifted into a frontend.
//
// Nothing here is a surface syntax.  The type system is flow-sensitive -- in
// the binary search tree delete, `current` gains two field-map entries two
// lines after it is bound -- so a variable has no single type to declare, and
// annotations at declaration sites cannot express what is true.  These
// environments are *inferred*; the specification lines in the paper's proofs
// are exactly what this computes.
//
// The inputs the inference needs are already present in RCU source: which
// struct fields are RCU-typed, where critical sections begin and end, and which
// calls are the RCU actions.  Only the root needs marking.
//
// Operations:
//   joinType/joinEnv   control-flow merge
//   wellFormed         the environment is in the class MayAlias decides exactly
//   coversRCUFields    T-Replace's side condition
//   onlyFieldIs        T-Insert's null condition on the fresh node
//   noFreshPointsAt    the premise added to T-Replace and T-UnlinkH

#ifndef RCU_TYPES_H
#define RCU_TYPES_H

#include "path_domain.h"

#include <map>
#include <optional>
#include <string>
#include <vector>

namespace rcu {

// ---------------------------------------------------------------------------
// Field maps
// ---------------------------------------------------------------------------
//
// A field map records, for the fields read or written so far, what they hold:
// a local variable, or null.  Fields outside its domain are untracked -- which
// is the gap the revised rcuFresh denotation closes, and which is why the
// codomain needs an explicit null rather than just a variable.

struct FieldVal {
  enum Kind { Var, Null } kind;
  int var = -1;  // Var only

  bool operator==(const FieldVal &o) const {
    return kind == o.kind && (kind == Null || var == o.var);
  }
  bool operator!=(const FieldVal &o) const { return !(*this == o); }
};

inline FieldVal fvVar(int v) { return FieldVal{FieldVal::Var, v}; }
inline FieldVal fvNull()     { return FieldVal{FieldVal::Null, -1}; }

// Keys are field *sets*, not single fields.  After a merge the field through
// which a child was reached is known only disjunctively -- the paper writes
// par : rcuItr eps {Left|Right -> cur} -- so a single-field key cannot express
// what a traversal produces.  A singleton key is the ordinary case.
using FieldMap = std::map<FieldSet, FieldVal>;  // fields -> value; absent = untracked

// ---------------------------------------------------------------------------
// Types
// ---------------------------------------------------------------------------

struct Type {
  enum Kind { Itr, Fresh, Unlinked, Freeable, Undef, Root } kind;
  Path path;        // Itr only
  FieldMap fields;  // Itr and Fresh only

  bool operator==(const Type &o) const {
    if (kind != o.kind) return false;
    if (kind == Itr && path != o.path) return false;
    if (kind == Itr || kind == Fresh) return fields == o.fields;
    return true;
  }
};

inline Type tItr(Path p, FieldMap n = {}) { return Type{Type::Itr, std::move(p), std::move(n)}; }
inline Type tFresh(FieldMap n = {})       { return Type{Type::Fresh, {}, std::move(n)}; }
inline Type tUnlinked()                   { return Type{Type::Unlinked, {}, {}}; }
inline Type tFreeable()                   { return Type{Type::Freeable, {}, {}}; }
inline Type tUndef()                      { return Type{Type::Undef, {}, {}}; }
inline Type tRoot()                       { return Type{Type::Root, {}, {}}; }

using TypeEnv = std::map<int, Type>;  // variable -> type

// ---------------------------------------------------------------------------
// Control-flow merge
// ---------------------------------------------------------------------------
//
// Field maps are intersected: an entry survives only if both branches agree on
// it.  That is the sound direction -- a smaller domain is a weaker assertion --
// and it is why a rule needing dom(N) to cover every RCU field may not apply
// after a merge, which is correct rather than unfortunate.

inline FieldMap joinFields(const FieldMap &a, const FieldMap &b) {
  FieldMap out;
  for (const auto &kv : a) {
    auto it = b.find(kv.first);
    if (it != b.end() && it->second == kv.second) out.insert(kv);
  }
  return out;
}

// Types join only within a kind.  A variable that is an iterator on one branch
// and unlinked on the other has no common type, and the merge is rejected --
// the type system has no join for that, and inventing one would be unsound.
inline std::optional<Type> joinType(const Type &a, const Type &b) {
  if (a.kind != b.kind) return std::nullopt;
  switch (a.kind) {
    case Type::Itr: {
      std::optional<Path> p = join(a.path, b.path);
      if (!p) return std::nullopt;
      return tItr(*p, joinFields(a.fields, b.fields));
    }
    case Type::Fresh:
      return tFresh(joinFields(a.fields, b.fields));
    default:
      return a;
  }
}

// A variable bound on only one branch is dropped: it has no type on the other,
// so nothing can be asserted about it after the merge.
inline std::optional<TypeEnv> joinEnv(const TypeEnv &a, const TypeEnv &b) {
  TypeEnv out;
  for (const auto &kv : a) {
    auto it = b.find(kv.first);
    if (it == b.end()) continue;
    std::optional<Type> t = joinType(kv.second, it->second);
    if (!t) return std::nullopt;
    out.emplace(kv.first, *t);
  }
  return out;
}

// The same, reporting which variable failed and why.  A merge can fail two
// ways, and they mean different things to a programmer: a reference with
// different *kinds* on the two paths is a real inconsistency, while two paths
// that will not join is the path abstraction giving up.  Reporting both as one
// message hides which happened.
// A merge fails only on a kind clash.  Two paths that will not join are not an
// error: the reference simply has no describable path afterwards, so it is
// dropped, exactly as a variable bound on only one branch is dropped.  Any
// later use then fails on its own, at the use, which is where a programmer can
// act on it.
//
// Failing the merge instead reports every dead local carried past a branch,
// which is a false positive and the kind that makes a checker unusable.  The
// alternative -- consulting liveness -- needs the frontend's own CFG and
// analysis context to agree, and buys nothing this does not.
inline std::optional<TypeEnv> joinEnvWhy(const TypeEnv &a, const TypeEnv &b,
                                         int *badVar, bool *kindClash) {
  TypeEnv out;
  for (const auto &kv : a) {
    auto it = b.find(kv.first);
    if (it == b.end()) continue;
    if (kv.second.kind != it->second.kind) {
      // Different kinds matter only when one of them carries an obligation.
      // A reference freed on one path and still an iterator on the other is
      // ordinary code -- neither owes anything afterwards, so it is dropped.
      // But fresh, unlinked or freeable on one path and not the other is a
      // leak on that path, and has to be reported.
      auto owes = [](Type::Kind k) {
        return k == Type::Fresh || k == Type::Unlinked || k == Type::Freeable;
      };
      if (!owes(kv.second.kind) && !owes(it->second.kind)) continue;
      if (badVar) *badVar = kv.first;
      if (kindClash) *kindClash = true;
      return std::nullopt;
    }
    std::optional<Type> t = joinType(kv.second, it->second);
    if (!t) continue;  // no common path: the reference does not survive
    out.emplace(kv.first, *t);
  }
  return out;
}

// ---------------------------------------------------------------------------
// Well-formedness
// ---------------------------------------------------------------------------

// The paths an environment mentions, in a deterministic order.
inline Env pathsOf(const TypeEnv &g) {
  Env e;
  for (const auto &kv : g)
    if (kv.second.kind == Type::Itr) e.push_back(kv.second.path);
  return e;
}

// The class on which MayAlias is decided exactly rather than merely soundly.
// A checker should reject outside it, and lose nothing real by doing so: the
// cursors of a loop are reindexed by the same back edge, so a traversal
// produces anchored environments.
inline bool wellFormed(const TypeEnv &g) { return inAnchoredCNF(pathsOf(g)); }

// ---------------------------------------------------------------------------
// The rules' side conditions
// ---------------------------------------------------------------------------

// T-Replace: dom(N) covers every RCU field.
//
// Without this the fresh node and the node it replaces agree only where both
// are tracked, and an untracked field may differ -- which moves a subtree
// rather than preserving it.  It is what makes the mirroring the soundness
// proof needs follow from the two denotations.
inline bool coversRCUFields(const FieldMap &n, FieldSet rcuFields, int numFields) {
  FieldSet covered = 0;
  for (const auto &kv : n) covered |= kv.first;
  for (int f = 0; f < numFields; ++f)
    if ((rcuFields & bit(f)) && !(covered & bit(f))) return false;
  return true;
}

// T-Insert: every tracked field of the fresh node other than f4 is null.
// The untracked ones are handled by the rcuFresh denotation, not here.
inline bool onlyFieldIs(const FieldMap &n, FieldSet f4) {
  for (const auto &kv : n)
    if (kv.first != f4 && kv.second.kind != FieldVal::Null) return false;
  return true;
}

// The premise added to T-Replace and T-UnlinkH: no rcuFresh reference in the
// environment has a field pointing at the node being unlinked.
//
// Without it a well-typed program reaches a state where a fresh node points at
// an unlinked one, and linking that fresh node in later splices a node already
// scheduled for reclamation back into the structure.  The aliasing premises the
// rules already had quantify only over rcuItr references, and the environment
// denotation is an intersection rather than a separating conjunction, so
// nothing else excludes it.
inline bool noFreshPointsAt(const TypeEnv &g, int victim) {
  for (const auto &kv : g) {
    if (kv.second.kind != Type::Fresh) continue;
    for (const auto &fe : kv.second.fields)
      if (fe.second.kind == FieldVal::Var && fe.second.var == victim) return false;
  }
  return true;
}

// ToRCUWrite's exit condition: no unlinked or freeable reference escapes the
// critical section, and no fresh one either.
inline bool noPendingReclamation(const TypeEnv &g) {
  for (const auto &kv : g)
    if (kv.second.kind == Type::Unlinked || kv.second.kind == Type::Freeable ||
        kv.second.kind == Type::Fresh)
      return false;
  return true;
}

}  // namespace rcu

#endif  // RCU_TYPES_H
