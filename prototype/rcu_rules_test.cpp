// rcu_rules_test.cpp -- the type rules as transfer functions.
//
//   c++ -std=c++17 -O2 -Wall -o rcu_rules_test prototype/rcu_rules_test.cpp
//   ./rcu_rules_test
//
// The main test replays the two-child case of the binary search tree delete --
// the hardest case in the paper, and the one the appendix annotates by hand --
// through the rules, and checks that the environment the checker computes is
// the one the proof writes.
//
// The rest check that the premises reject what they are there to reject,
// including the two added by this work.

#include "rcu_rules.h"

#include <iostream>

using namespace rcu;

static int checks = 0, failures = 0;

static void expect(bool cond, const std::string &what) {
  ++checks;
  if (!cond) { ++failures; std::cout << "  FAIL  " << what << "\n"; }
  else       { std::cout << "  ok    " << what << "\n"; }
}

static void expectOk(const Result &r, const std::string &what) {
  ++checks;
  if (!r.ok) { ++failures; std::cout << "  FAIL  " << what << "\n        rejected: " << r.why << "\n"; }
  else       { std::cout << "  ok    " << what << "\n"; }
}

static void expectNo(const Result &r, const std::string &what) {
  ++checks;
  if (r.ok) { ++failures; std::cout << "  FAIL  " << what << " (accepted)\n"; }
  else      { std::cout << "  ok    " << what << "\n        " << r.why << "\n"; }
}

enum { LeftF = 0, RightF = 1 };
static const FieldSet Left = bit(LeftF), Right = bit(RightF);
static const FieldSet BOTH = Left | Right;
static const int NF = 2;
enum { parent = 0, current = 1, currentL = 2, lmParent = 3, currentF = 4 };

// ===========================================================================
// The BST delete, two-child case
// ===========================================================================
//
//   parent  : rcuItr (l|r)^k         {l|r -> current}
//   current : rcuItr (l|r)^k.(l|r)   {}
// then
//   lmParent = current.Right;  currentL = current.Left;
//   currentF = new;  currentF.Right = lmParent;  currentF.Left = currentL;
//   parent.Left = currentF;                       // T-Replace
//   sync; free(current)

static void bstDelete() {
  std::cout << "== BST delete, two-child case ==\n";

  TypeEnv g;
  // After the outer loop the field through which current was reached is known
  // only disjunctively, exactly as the paper writes it.
  g[parent]  = tItr(Path{V(0, BOTH)}, FieldMap{{BOTH, fvVar(current)}});
  g[current] = tItr(Path{V(0, BOTH), D(BOTH)});
  expect(wellFormed(g), "the entry environment is anchored");

  // Read both children of current.
  Result r = tReadH(std::move(g), current, Right, lmParent);
  expectOk(r, "lmParent = current.Right");
  r = tReadH(std::move(r.env), current, Left, currentL);
  expectOk(r, "currentL = current.Left");

  // Build the replacement.
  r = tAlloc(std::move(r.env), currentF);
  expectOk(r, "currentF = new");
  r = tWriteFH(std::move(r.env), currentF, Right, lmParent);
  expectOk(r, "currentF.Right = lmParent");
  r = tWriteFH(std::move(r.env), currentF, Left, currentL);
  expectOk(r, "currentF.Left = currentL");

  // The field maps now match, and cover every RCU field, so T-Replace applies.
  expect(r.env[currentF].fields == r.env[current].fields,
         "the fresh node's field map matches the node it replaces");
  expect(coversRCUFields(r.env[current].fields, BOTH, NF),
         "... and covers every RCU field, so the replacement mirrors it");

  // The code tests `parent.Left == current` before writing; that test is what
  // refines the disjunctive field map entry to a concrete field.
  Result rf = tRefineField(r.env, parent, Left, current);
  expectOk(rf, "if (parent.Left == current)   refines {l|r -> current}");

  Result rep = tReplace(rf.env, parent, Left, current, currentF, BOTH, NF);
  expectOk(rep, "parent.Left = currentF   (T-Replace)");
  if (rep.ok) {
    expect(rep.env[current].kind == Type::Unlinked,
           "... current becomes unlinked");
    // The refinement made current's path concrete, so the replacement inherits
    // the concrete one -- (l|r)^k.Left, not (l|r)^k.(l|r).
    expect(rep.env[currentF].kind == Type::Itr &&
           rep.env[currentF].path == (Path{V(0, BOTH), F(LeftF)}),
           "... and currentF takes its path");
  }

  // Reclamation.
  Result tooSoon = tFree(rep.env, current);
  expectNo(tooSoon, "free(current) before the grace period is rejected");

  Result sy = tSync(rep.env);
  expectOk(sy, "SyncStart; SyncStop");
  expect(sy.env[current].kind == Type::Freeable,
         "... current becomes freeable");
  Result fr = tFree(sy.env, current);
  expectOk(fr, "free(current)");
  expect(noPendingReclamation(fr.env),
         "the critical section may now be left");
}

// ===========================================================================
// The premises reject what they are for
// ===========================================================================

static void premises() {
  std::cout << "== premises ==\n";

  // T-Replace without every RCU field read.  This is the side condition added
  // by this work; without it the replacement need not mirror what it replaces.
  {
    TypeEnv g;
    g[parent]  = tItr(Path{V(0, BOTH)}, FieldMap{{Left, fvVar(current)}});
    g[current] = tItr(Path{V(0, BOTH), F(LeftF)}, FieldMap{{Left, fvVar(currentL)}});
    g[currentL] = tItr(Path{V(0, BOTH), F(LeftF), F(LeftF)});
    g[currentF] = tFresh(FieldMap{{Left, fvVar(currentL)}});
    expectNo(tReplace(g, parent, Left, current, currentF, BOTH, NF),
             "replacing without having read Right is rejected");
  }

  // The premise added to close the FPI defect.
  {
    TypeEnv g;
    g[parent]  = tItr(Path{V(0, BOTH)}, FieldMap{{Left, fvVar(current)}});
    g[current] = tItr(Path{V(0, BOTH), F(LeftF)},
                      FieldMap{{Left, fvNull()}, {Right, fvNull()}});
    g[currentF] = tFresh(FieldMap{{Left, fvNull()}, {Right, fvNull()}});
    // a *second* fresh node that points at the victim
    g[9] = tFresh(FieldMap{{Left, fvVar(current)}});
    expectNo(tReplace(g, parent, Left, current, currentF, BOTH, NF),
             "replacing a node a fresh reference points at is rejected");
  }

  // T-UnlinkH must remove one node, not a subtree.
  {
    TypeEnv g;
    g[parent]  = tItr(Path{V(0, BOTH)}, FieldMap{{Left, fvVar(current)}});
    g[current] = tItr(Path{V(0, BOTH), F(LeftF)},
                      FieldMap{{Left, fvVar(currentL)}, {Right, fvVar(lmParent)}});
    g[currentL] = tItr(Path{V(0, BOTH), F(LeftF), F(LeftF)});
    g[lmParent] = tItr(Path{V(0, BOTH), F(LeftF), F(RightF)});
    expectNo(tUnlinkH(g, parent, Left, current, Left, currentL, NF),
             "unlinking a node with two children is rejected");
  }

  // T-Insert must not give the inserted node a second child.
  {
    TypeEnv g;
    g[parent]  = tItr(Path{V(0, BOTH)}, FieldMap{{Left, fvVar(current)}});
    g[current] = tItr(Path{V(0, BOTH), F(LeftF)});
    g[currentF] = tFresh(FieldMap{{Left, fvVar(current)}, {Right, fvVar(parent)}});
    expectNo(tInsert(g, parent, Left, current, currentF, Left, NF),
             "inserting a fresh node with two links is rejected");
  }

  // Framing: an iterator that may alias the path under mutation.
  {
    TypeEnv g;
    g[parent]  = tItr(Path{V(0, BOTH)}, FieldMap{{Left, fvVar(current)}});
    g[current] = tItr(Path{V(0, BOTH), F(LeftF)},
                      FieldMap{{Left, fvNull()}, {Right, fvNull()}});
    g[currentF] = tFresh(FieldMap{{Left, fvNull()}, {Right, fvNull()}});
    g[9] = tItr(Path{V(0, BOTH), F(LeftF)});   // an alias of current
    expectNo(tReplace(g, parent, Left, current, currentF, BOTH, NF),
             "an aliasing iterator elsewhere in the environment is rejected");
  }
}

int main() {
  bstDelete();
  premises();
  std::cout << "\n" << (checks - failures) << "/" << checks << " checks passed\n";
  return failures ? 1 : 0;
}
