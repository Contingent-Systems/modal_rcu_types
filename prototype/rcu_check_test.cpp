// rcu_check_test.cpp -- the statement IR and dataflow driver.
//
//   c++ -std=c++17 -O2 -Wall -o rcu_check_test prototype/rcu_check_test.cpp
//
// Runs whole procedures through the driver rather than rules one at a time,
// which is what a frontend will do.

#include "rcu_check.h"

#include <iostream>

using namespace rcu;

static int checks = 0, failures = 0;
static void expect(bool c, const std::string &w) {
  ++checks;
  std::cout << (c ? "  ok    " : "  FAIL  ") << w << "\n";
  if (!c) ++failures;
}

enum { LeftF = 0, RightF = 1 };
static const FieldSet Left = bit(LeftF), Right = bit(RightF);
static const FieldSet BOTH = Left | Right;
enum { parent = 0, current = 1, currentL = 2, lmParent = 3, currentF = 4 };

static Stmt readH(int x, FieldSet f, int z, int line) {
  Stmt s; s.kind = Stmt::ReadH; s.x = x; s.f = f; s.z = z; s.line = line; return s;
}
static Stmt alloc(int x, int line)  { Stmt s; s.kind = Stmt::Alloc; s.x = x; s.line = line; return s; }
static Stmt writeFH(int p, FieldSet f, int z, int line) {
  Stmt s; s.kind = Stmt::WriteFH; s.x = p; s.f = f; s.z = z; s.line = line; return s;
}
static Stmt refine(int x, FieldSet f, int y, int line) {
  Stmt s; s.kind = Stmt::RefineField; s.x = x; s.f = f; s.y = y; s.line = line; return s;
}
static Stmt replace_(int p, FieldSet f, int o, int n, int line) {
  Stmt s; s.kind = Stmt::Replace; s.x = p; s.f = f; s.o = o; s.n = n; s.line = line; return s;
}
static Stmt sync_(int line) { Stmt s; s.kind = Stmt::Sync; s.line = line; return s; }
static Stmt free_(int x, int line) { Stmt s; s.kind = Stmt::Free; s.x = x; s.line = line; return s; }

static TypeEnv afterOuterLoop() {
  TypeEnv g;
  g[parent]  = tItr(Path{V(0, BOTH)}, FieldMap{{BOTH, fvVar(current)}});
  g[current] = tItr(Path{V(0, BOTH), D(BOTH)});
  return g;
}

int main() {
  Config conf; conf.rcuFields = BOTH; conf.numFields = 2;

  // -- the whole two-child delete, as one basic block -----------------------
  std::cout << "== BST delete through the driver ==\n";
  {
    Cfg cfg(1);
    cfg[0].stmts = {
      readH(current, Right, lmParent, 46),
      readH(current, Left,  currentL, 47),
      alloc(currentF, 148),
      writeFH(currentF, Right, lmParent, 148),
      writeFH(currentF, Left,  currentL, 150),
      refine(parent, Left, current, 158),
      replace_(parent, Left, current, currentF, 163),
      sync_(170),
      free_(current, 171),
    };
    CheckResult r = check(cfg, afterOuterLoop(), conf);
    expect(r.ok, "the two-child delete type checks end to end");
    for (const Diagnosis &d : r.errors)
      std::cout << "        line " << d.line << ": " << d.why << "\n";
  }

  // -- freeing before the grace period, diagnosed at the right line ---------
  std::cout << "== a real mistake, diagnosed ==\n";
  {
    Cfg cfg(1);
    cfg[0].stmts = {
      readH(current, Right, lmParent, 46),
      readH(current, Left,  currentL, 47),
      alloc(currentF, 148),
      writeFH(currentF, Right, lmParent, 148),
      writeFH(currentF, Left,  currentL, 150),
      refine(parent, Left, current, 158),
      replace_(parent, Left, current, currentF, 163),
      free_(current, 170),          // no synchronize_rcu
    };
    CheckResult r = check(cfg, afterOuterLoop(), conf);
    expect(!r.ok, "freeing without a grace period is rejected");
    expect(r.errors.size() == 1 && r.errors[0].line == 170,
           "... and reported at the free, not somewhere else");
    if (!r.errors.empty()) std::cout << "        line " << r.errors[0].line
                                     << ": " << r.errors[0].why << "\n";
  }

  // -- a conditional, merged --------------------------------------------------
  std::cout << "== branch and merge ==\n";
  {
    // if (...) currentL = current.Left; else currentL = current.Right;
    Cfg cfg(4);
    cfg[0].succs = {1, 2};
    cfg[1].stmts = { readH(current, Left,  currentL, 10) }; cfg[1].succs = {3};
    cfg[2].stmts = { readH(current, Right, currentL, 12) }; cfg[2].succs = {3};
    CheckResult r = check(cfg, afterOuterLoop(), conf);
    expect(r.ok, "both branches merge");
    if (r.ok) {
      const Type &t = r.entry[3].at(currentL);
      expect(t.path == (Path{V(0, BOTH), D(BOTH), D(BOTH)}),
             "... and the merged path abstracts the field taken");
    }
  }

  // -- a merge that must be rejected ----------------------------------------
  std::cout << "== an unmergeable merge ==\n";
  {
    Cfg cfg(4);
    cfg[0].succs = {1, 2};
    cfg[1].stmts = { refine(parent, Left, current, 20),
                     replace_(parent, Left, current, currentF, 21) };
    cfg[1].succs = {3};
    cfg[2].succs = {3};
    TypeEnv g = afterOuterLoop();
    g[currentF] = tFresh(FieldMap{{Left, fvNull()}, {Right, fvNull()}});
    g[current]  = tItr(Path{V(0, BOTH), D(BOTH)},
                       FieldMap{{Left, fvNull()}, {Right, fvNull()}});
    CheckResult r = check(cfg, g, conf);
    expect(!r.ok, "current unlinked on one branch and live on the other is rejected");
    for (const Diagnosis &d : r.errors)
      std::cout << "        " << d.why << "\n";
  }

  std::cout << "\n" << (checks - failures) << "/" << checks << " checks passed\n";
  return failures ? 1 : 0;
}
