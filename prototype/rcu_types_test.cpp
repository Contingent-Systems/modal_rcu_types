// rcu_types_test.cpp -- tests for the type and environment domain.
//
//   c++ -std=c++17 -O2 -Wall -o rcu_types_test prototype/rcu_types_test.cpp
//   ./rcu_types_test
//
// The environments used are the ones the paper's proofs annotate by hand, so
// what is checked here is that the domain computes what those proofs write.

#include "rcu_types.h"

#include <iostream>

using namespace rcu;

static int checks = 0, failures = 0;

static void expect(bool cond, const std::string &what) {
  ++checks;
  if (!cond) { ++failures; std::cout << "  FAIL  " << what << "\n"; }
  else       { std::cout << "  ok    " << what << "\n"; }
}

// Field names, as in the binary search tree: 0 = Left, 1 = Right.
enum { Left = 0, Right = 1 };
static const FieldSet BOTH = bit(Left) | bit(Right);
static const FieldSet RCU_FIELDS = BOTH;
static const int NF = 2;

// Variables.
enum { parent = 0, current = 1, currentL = 2, lmParent = 3, currentF = 4, root = 5 };

// ===========================================================================
// The environment the BST delete reaches after its outer loop
// ===========================================================================

static TypeEnv bstAfterOuterLoop() {
  TypeEnv g;
  // parent : rcuItr (Left|Right)^k {Left|Right -> current}
  g[parent] = tItr(Path{V(0, BOTH)}, FieldMap{{Left, fvVar(current)}});
  // current : rcuItr (Left|Right)^k.(Left|Right) {}
  g[current] = tItr(Path{V(0, BOTH), D(BOTH)});
  return g;
}

static void unitTests() {
  std::cout << "== unit tests ==\n";

  TypeEnv g = bstAfterOuterLoop();
  expect(wellFormed(g),
         "the BST environment after the outer loop is anchored");

  // Both cursors carry the loop word at the same position, which is what makes
  // the environment anchored -- they were reindexed by the same back edge.
  {
    TypeEnv bad;
    bad[parent]  = tItr(Path{V(0, BOTH), F(Left)});
    bad[current] = tItr(Path{F(Right), V(0, BOTH)});
    expect(!wellFormed(bad),
           "an environment with one variable at two depths is rejected");
  }

  // After reading current's two children, its field map is full.
  {
    TypeEnv g2 = g;
    g2[current].fields[Left]  = fvVar(currentL);
    g2[current].fields[Right] = fvVar(lmParent);
    expect(coversRCUFields(g2[current].fields, RCU_FIELDS, NF),
           "reading both children covers every RCU field (T-Replace's premise)");
    expect(!coversRCUFields(g[current].fields, RCU_FIELDS, NF),
           "... and before those reads it does not");
  }

  // T-Insert's condition on the fresh node.
  {
    FieldMap n{{Right, fvVar(current)}, {Left, fvNull()}};
    expect(onlyFieldIs(n, Right),
           "a fresh node with one link and the rest null satisfies T-Insert");
    FieldMap bad{{Right, fvVar(current)}, {Left, fvVar(currentL)}};
    expect(!onlyFieldIs(bad, Right),
           "... and one with two links does not");
  }

  // The premise added to T-Replace and T-UnlinkH.
  {
    TypeEnv g2 = g;
    // The BST builds currentF pointing at current's *children*, never at
    // current itself, so the premise holds and the example still type checks.
    g2[currentF] = tFresh(FieldMap{{Left, fvVar(currentL)},
                                   {Right, fvVar(lmParent)}});
    expect(noFreshPointsAt(g2, current),
           "the BST's fresh node does not point at the node being replaced");
    // A fresh node pointing at the victim is what the repair excludes.
    TypeEnv g3 = g;
    g3[currentF] = tFresh(FieldMap{{Left, fvVar(current)}});
    expect(!noFreshPointsAt(g3, current),
           "a fresh node pointing at it is rejected (the added premise)");
  }

  // ToRCUWrite's exit condition.
  {
    TypeEnv g2 = g;
    expect(noPendingReclamation(g2),
           "an environment of iterators may leave the critical section");
    g2[current] = tUnlinked();
    expect(!noPendingReclamation(g2),
           "... one with an unlinked reference may not");
  }
}

// ===========================================================================
// Control-flow merge
// ===========================================================================

static void joinTests() {
  std::cout << "== join ==\n";

  // The BST's conditional: parent.Left == current on one branch, .Right on the
  // other.  The merge must keep the shared prefix and widen the last step.
  TypeEnv a, b;
  a[current] = tItr(Path{V(0, BOTH), F(Left)});
  b[current] = tItr(Path{V(0, BOTH), F(Right)});
  std::optional<TypeEnv> m = joinEnv(a, b);
  expect(m.has_value(), "the two branches of the BST conditional merge");
  if (m) {
    Path expected{V(0, BOTH), D(BOTH)};
    expect((*m)[current].path == expected,
           "... to (Left|Right)^k.(Left|Right), as the paper writes it");
    expect(wellFormed(*m), "... and the merged environment is anchored");
  }

  // A field map entry survives a merge only if both branches agree.
  {
    TypeEnv x, y;
    x[parent] = tItr(Path{V(0, BOTH)}, FieldMap{{Left, fvVar(current)}});
    y[parent] = tItr(Path{V(0, BOTH)}, FieldMap{{Left, fvVar(currentL)}});
    std::optional<TypeEnv> j = joinEnv(x, y);
    expect(j.has_value() && (*j)[parent].fields.empty(),
           "a field map entry the branches disagree on is dropped");
  }

  // Kinds do not join.  A reference unlinked on one branch and an iterator on
  // the other has no common type, and inventing one would be unsound.
  {
    TypeEnv x, y;
    x[current] = tItr(Path{V(0, BOTH)});
    y[current] = tUnlinked();
    expect(!joinEnv(x, y).has_value(),
           "an iterator and an unlinked reference do not merge");
  }

  // A variable bound on only one branch is dropped.
  {
    TypeEnv x, y;
    x[current] = tItr(Path{V(0, BOTH)});
    x[currentL] = tItr(Path{V(0, BOTH), F(Left)});
    y[current] = tItr(Path{V(0, BOTH)});
    std::optional<TypeEnv> j = joinEnv(x, y);
    expect(j.has_value() && j->count(currentL) == 0,
           "a variable bound on one branch only does not survive the merge");
  }
}

int main() {
  unitTests();
  joinTests();
  std::cout << "\n" << (checks - failures) << "/" << checks << " checks passed\n";
  return failures ? 1 : 0;
}
