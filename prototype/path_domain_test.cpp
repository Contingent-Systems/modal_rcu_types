// path_domain_test.cpp -- unit and property tests for the RCU path domain.
//
//   c++ -std=c++17 -O2 -Wall -o path_domain_test prototype/path_domain_test.cpp
//   ./path_domain_test
//
// Unit tests use only paths that appear in the paper.  Property tests check the
// abstract operations against the concrete semantics by brute-force
// enumeration of valuations.

#include "path_domain.h"

#include <iostream>
#include <random>
#include <iomanip>

using namespace rcu;

static int checks = 0, failures = 0;

static void expect(bool cond, const std::string &what) {
  ++checks;
  if (!cond) { ++failures; std::cout << "  FAIL  " << what << "\n"; }
  else       { std::cout << "  ok    " << what << "\n"; }
}

// ===========================================================================
// Unit tests -- paths from Figure 1, Section 5, and Appendix B
// ===========================================================================

static void unitTests() {
  std::cout << "== unit tests ==\n";

  // ---- Bag: one field ----------------------------------------------------
  const int Next = 0, nfBag = 1;
  std::vector<std::string> bagNames{"Next"};
  const FieldSet N = fields({Next});

  Path par{V(0, N)};              // par : rcuItr (Next)^k      {Next -> cur}
  Path cur{V(0, N), F(Next)};     // cur : rcuItr (Next)^k.Next {}

  expect(inFragment(par) && inFragment(cur), "bag paths are in the fragment");
  expect(!mayAlias(par, cur, nfBag),
         "par and cur cannot alias (differ by a mandatory Next)");
  expect(mayAlias(par, par, nfBag), "a path aliases itself");
  expect(mayAlias(Path{V(0, N)}, Path{V(1, N)}, nfBag),
         "distinct path variables may alias (both may be empty)");
  expect(mayAlias(cur, Path{V(0, N), F(Next)}, nfBag),
         "a genuine descendant is reported as aliasing");

  // ---- BST: two fields ---------------------------------------------------
  const int L = 0, R = 1, nfBst = 2;
  std::vector<std::string> bstNames{"Left", "Right"};
  const FieldSet LR = fields({L, R}), Lonly = fields({L});

  Path pr{V(0, LR)};
  Path cr{V(0, LR), D(LR)};
  expect(!mayAlias(pr, cr, nfBst), "BST outer: pr and cr cannot alias");

  Path lmParent{V(0, LR), D(LR), F(R), F(L), V(1, Lonly)};
  Path leftmost{V(0, LR), D(LR), F(R), F(L), V(1, Lonly), F(L)};
  expect(inFragment(lmParent) && inFragment(leftmost),
         "BST two-cursor paths are in the fragment");
  expect(!mayAlias(lmParent, leftmost, nfBst),
         "BST inner: lmParent and leftmost cannot alias");
  expect(!mayAlias(cr, lmParent, nfBst), "outer cursor cannot alias inner cursor");
  expect(!mayAlias(cr, leftmost, nfBst), "outer cursor cannot alias inner leftmost");

  // ---- Join (Figure 5) ---------------------------------------------------
  auto j = join(Path{F(L), F(L)}, Path{F(R), F(R)});
  expect(j && *j == (Path{D(LR), D(LR)}),
         "join Left.Left with Right.Right = (Left|Right).(Left|Right)");
  auto j2 = join(Path{F(L)}, Path{F(R)});
  expect(j2 && *j2 == (Path{D(LR)}), "join Left with Right = (Left|Right)");
  expect(!join(Path{V(0, LR)}, Path{F(L)}),
         "join refuses to merge a variable with a concrete step");

  expect(!inFragment(Path{V(0, LR), F(L), V(0, LR)}),
         "a variable occurring twice is outside the fragment");

  // ---- Widening: the bag loop -------------------------------------------
  // Entering remove()'s loop:  par : eps {Next->cur},  cur : Next {}
  // Body:                      par = cur; cur = par.Next;
  std::cout << "-- widening: bag loop --\n";
  Env bagEntry{Path{}, Path{F(Next)}};
  auto bagBody = [&](const Env &e) -> Env {
    Path np = e[1];                 // par = cur
    Path nc = np; nc.push_back(F(Next));  // cur = par.Next
    return Env{np, nc};
  };
  auto bagLoop = analyzeLoop(bagEntry, bagBody, /*firstFreshVar=*/0);
  expect(bagLoop.converged, "bag loop converges");
  if (bagLoop.converged) {
    std::cout << "     par = " << show(bagLoop.invariant[0], bagNames)
              << ",  cur = " << show(bagLoop.invariant[1], bagNames)
              << "   (" << bagLoop.widenings << " widening)\n";
    expect(bagLoop.invariant[0] == par && bagLoop.invariant[1] == cur,
           "  ... to exactly Figure 1's (Next)^k and (Next)^k.Next");
    expect(bagLoop.widenings == 1, "  ... after a single widening");
  }

  // ---- Widening: the BST outer loop -------------------------------------
  std::cout << "-- widening: BST outer loop --\n";
  Env bstEntry{Path{}, Path{D(LR)}};
  auto bstBody = [&](const Env &e) -> Env {
    Path np = e[1];
    Path nc = np; nc.push_back(D(LR));
    return Env{np, nc};
  };
  auto bstLoop = analyzeLoop(bstEntry, bstBody, 0);
  expect(bstLoop.converged, "BST outer loop converges");
  if (bstLoop.converged) {
    std::cout << "     pr = " << show(bstLoop.invariant[0], bstNames)
              << ",  cr = " << show(bstLoop.invariant[1], bstNames) << "\n";
    expect(bstLoop.invariant[0] == pr && bstLoop.invariant[1] == cr,
           "  ... to (l|r)^k and (l|r)^k.(l|r)");
  }

  // ---- Widening: the BST inner loop, with the outer cursors frozen -------
  // Entering the successor search:
  //   pr, cr frozen;  lmParent : (l|r)^k.(l|r).Right,  leftmost : ....Left
  std::cout << "-- widening: BST inner loop (outer cursors frozen) --\n";
  Env inEntry{pr, cr,
              Path{V(0, LR), D(LR), F(R)},
              Path{V(0, LR), D(LR), F(R), F(L)}};
  auto inBody = [&](const Env &e) -> Env {
    Path nlp = e[3];                    // lmParent = leftmost
    Path nlm = nlp; nlm.push_back(F(L));  // leftmost = lmParent.Left
    return Env{e[0], e[1], nlp, nlm};
  };
  auto inLoop = analyzeLoop(inEntry, inBody, /*firstFreshVar=*/1);
  expect(inLoop.converged, "BST inner loop converges");
  if (inLoop.converged) {
    std::cout << "     lmParent = " << show(inLoop.invariant[2], bstNames) << "\n"
              << "     leftmost = " << show(inLoop.invariant[3], bstNames) << "\n";
    expect(inLoop.invariant[0] == pr && inLoop.invariant[1] == cr,
           "  ... leaving the frozen outer cursors untouched");
    expect(inLoop.invariant[2] == (Path{V(0, LR), D(LR), F(R), V(1, Lonly)}),
           "  ... generalising lmParent to (l|r)^k.(l|r).Right.(Left)^m");
    expect(!mayAlias(inLoop.invariant[1], inLoop.invariant[2], nfBst),
           "  ... and the inferred invariant still separates the two cursors");
  }

  // The relational point: widening path-by-path would give cur = Next.(Next)^k,
  // which denotes the right language but says cur is par with a step PREPENDED.
  expect(bagLoop.converged && bagLoop.invariant[1] != (Path{F(Next), V(0, N)}),
         "widening does not produce the language-equal but relationally wrong form");

  // ---- Widening must refuse what it cannot represent ---------------------
  Env unevenA{Path{}, Path{F(Next)}};
  Env unevenB{Path{F(Next)}, Path{F(Next), F(Next), F(Next)}};  // grew 1 and 2
  expect(!widen(unevenA, unevenB, 9), "widening refuses unevenly advancing cursors");
}

// ===========================================================================
// Property tests
// ===========================================================================

namespace prop {

#ifndef RCU_TEST_SEED
#define RCU_TEST_SEED 20240101u
#endif
static std::mt19937 rng(RCU_TEST_SEED);

static int uni(int lo, int hi) {
  return std::uniform_int_distribution<int>(lo, hi)(rng);
}

static FieldSet randAlphabet(int numFields) {
  FieldSet m = 0;
  while (m == 0)
    for (int f = 0; f < numFields; ++f)
      if (uni(0, 1)) m |= bit(f);
  return m;
}

// A variable's alphabet is a property of the variable, not of an occurrence, so
// it must be fixed once per trial and shared by every path.  Generating it
// per-occurrence makes the same pi mean different things in two paths, which is
// not a well-formed environment.
using VarEnv = std::map<int, FieldSet>;

static VarEnv randVarEnv(int numFields, int varPool) {
  VarEnv v;
  for (int i = 0; i < varPool; ++i) v[i] = randAlphabet(numFields);
  return v;
}

// Random path in Cursor Normal Form.
static Path randPath(int numFields, int maxLen, const VarEnv &venv) {
  Path p;
  std::set<int> used;
  int len = uni(0, maxLen);
  int varPool = int(venv.size());
  for (int i = 0; i < len; ++i) {
    int k = uni(0, 2);
    if (k == 2 && int(used.size()) < varPool) {
      int v = uni(0, varPool - 1);
      if (used.count(v)) { p.push_back(mkStep(randAlphabet(numFields))); continue; }
      used.insert(v);
      p.push_back(V(v, venv.at(v)));
    } else {
      p.push_back(mkStep(randAlphabet(numFields)));
    }
  }
  return p;
}

// Ground truth for MayAlias, by enumerating valuations up to a length bound.
// Incomplete (a true alias could need a longer word), so only ever used to
// establish the direction "truly aliases => mayAlias says yes".
static bool bruteAlias(const Path &p, const Path &q, int numFields, int bound) {
  std::map<int, FieldSet> vars;
  varsOf(p, vars);
  varsOf(q, vars);
  bool found = false;
  forEachValuation(vars, numFields, bound, [&](const std::map<int, Word> &theta) {
    if (found) return;
    std::set<Word> a = lang(p, theta, numFields);
    std::set<Word> b = lang(q, theta, numFields);
    for (const Word &w : a)
      if (b.count(w)) { found = true; return; }
  });
  return found;
}

static bool subsetOf(const std::set<Word> &a, const std::set<Word> &b) {
  for (const Word &w : a)
    if (!b.count(w)) return false;
  return true;
}

// P1  truly aliases  =>  mayAlias says yes            (soundness of the negation)
static void p1_aliasSoundness() {
  const int nf = 2, trials = 40000, bound = 3;
  std::vector<std::string> names{"a", "b"};
  int imprecise = 0, aliasing = 0, bad = 0;
  for (int t = 0; t < trials; ++t) {
    VarEnv venv = randVarEnv(nf, 2);
    Path p = randPath(nf, 4, venv), q = randPath(nf, 4, venv);
    bool brute = bruteAlias(p, q, nf, bound);
    bool abs = mayAlias(p, q, nf);
    if (brute) {
      ++aliasing;
      if (!abs) {
        if (++bad <= 3)
          std::cout << "        counterexample: " << show(p, names)
                    << "   vs   " << show(q, names) << "\n";
      }
    } else if (abs) ++imprecise;
  }
  expect(bad == 0, "P1  mayAlias never misses a real alias (" +
                       std::to_string(trials) + " pairs, " +
                       std::to_string(aliasing) + " truly aliasing)");
  std::cout << "        precision: " << imprecise << "/" << trials
            << " conservative yes-answers ("
            << std::fixed << std::setprecision(1)
            << (100.0 * imprecise / trials) << "%)\n";
}

// P2  join is an upper bound of both operands
static void p2_joinUpperBound() {
  const int nf = 2, trials = 20000, bound = 2;
  int bad = 0, joined = 0;
  for (int t = 0; t < trials; ++t) {
    VarEnv venv = randVarEnv(nf, 2);
    Path p = randPath(nf, 3, venv), q = randPath(nf, 3, venv);
    auto r = join(p, q);
    if (!r) continue;
    ++joined;
    std::map<int, FieldSet> vars;
    varsOf(p, vars); varsOf(q, vars); varsOf(*r, vars);
    forEachValuation(vars, nf, bound, [&](const std::map<int, Word> &th) {
      if (!subsetOf(lang(p, th, nf), lang(*r, th, nf)) ||
          !subsetOf(lang(q, th, nf), lang(*r, th, nf)))
        ++bad;
    });
  }
  expect(bad == 0, "P2  join over-approximates both operands (" +
                       std::to_string(joined) + " successful joins)");
}

// P3  widening is an upper bound: fresh := eps recovers entry, and some value
//     of fresh covers exit.
static void p3_widenUpperBound() {
  const int nf = 2, trials = 6000, bound = 2, FRESH = 7;
  int bad_entry = 0, bad_exit = 0, widened = 0;

  for (int t = 0; t < trials; ++t) {
    int n = uni(1, 3);
    VarEnv venv = randVarEnv(nf, 2);
    Env entry;
    size_t minLen = SIZE_MAX;
    for (int i = 0; i < n; ++i) {
      entry.push_back(randPath(nf, 3, venv));
      minLen = std::min(minLen, entry.back().size());
    }
    // Splice a common chunk into a nonempty subset of the paths.
    size_t i0 = size_t(uni(0, int(minLen)));
    int d = uni(1, 2);
    Path w;
    for (int k = 0; k < d; ++k) w.push_back(mkStep(randAlphabet(nf)));

    std::vector<bool> move(n, false);
    move[uni(0, n - 1)] = true;
    for (int i = 0; i < n; ++i) if (uni(0, 1)) move[i] = true;

    Env exit;
    for (int i = 0; i < n; ++i) {
      if (!move[i]) { exit.push_back(entry[i]); continue; }
      Path p(entry[i].begin(), entry[i].begin() + i0);
      p.insert(p.end(), w.begin(), w.end());
      p.insert(p.end(), entry[i].begin() + i0, entry[i].end());
      exit.push_back(p);
    }

    auto W = widen(entry, exit, FRESH);
    if (!W) continue;   // refusing is always allowed; only the answer must be sound
    ++widened;

    std::map<int, FieldSet> vars;
    for (const Path &p : entry) varsOf(p, vars);
    for (const Path &p : exit) varsOf(p, vars);
    FieldSet freshAlpha = 0;
    for (const Path &p : *W) for (const Seg &s : p)
      if (s.kind == Seg::Var && s.var == FRESH) freshAlpha |= s.fields;

    forEachValuation(vars, nf, bound, [&](const std::map<int, Word> &th) {
      // fresh := eps must recover entry exactly
      std::map<int, Word> t0 = th; t0[FRESH] = Word();
      for (int i = 0; i < n; ++i)
        if (lang((*W)[i], t0, nf) != lang(entry[i], th, nf)) ++bad_entry;

      // some value of fresh must cover exit
      std::vector<Word> us = wordsUpTo(freshAlpha, nf, 2);
      for (int i = 0; i < n; ++i) {
        std::set<Word> cover;
        for (const Word &u : us) {
          std::map<int, Word> tu = th; tu[FRESH] = u;
          for (const Word &x : lang((*W)[i], tu, nf)) cover.insert(x);
        }
        if (!subsetOf(lang(exit[i], th, nf), cover)) ++bad_exit;
      }
    });
  }
  expect(bad_entry == 0, "P3a widening with fresh := eps recovers the entry environment (" +
                             std::to_string(widened) + " widenings)");
  expect(bad_exit == 0, "P3b widening covers the exit environment");
}

// P4  reindexing recovers any suffix-extension substitution
static void p4_reindexRoundTrip() {
  const int nf = 2, trials = 20000;
  int bad = 0, tried = 0;
  for (int t = 0; t < trials; ++t) {
    int n = uni(1, 3);
    VarEnv venv = randVarEnv(nf, 2);
    Env entry;
    std::set<int> vars;
    for (int i = 0; i < n; ++i) {
      entry.push_back(randPath(nf, 3, venv));
      for (const Seg &s : entry.back()) if (s.kind == Seg::Var) vars.insert(s.var);
    }
    if (vars.empty()) continue;

    int pick = *std::next(vars.begin(), uni(0, int(vars.size()) - 1));
    Path w{V(pick, venv.at(pick))};
    int d = uni(1, 2);
    for (int k = 0; k < d; ++k) w.push_back(mkStep(randAlphabet(nf)));
    std::map<int, Path> sigma{{pick, w}};

    Env exit;
    for (const Path &p : entry) exit.push_back(substitute(p, sigma));
    ++tried;

    auto got = reindex(entry, exit);
    if (!got) { ++bad; continue; }
    for (size_t i = 0; i < entry.size(); ++i)
      if (substitute(entry[i], *got) != exit[i]) { ++bad; break; }
  }
  expect(bad == 0, "P4  reindex recovers suffix-extension substitutions (" +
                       std::to_string(tried) + " cases)");
}

}  // namespace prop

int main() {
  unitTests();
  std::cout << "\n== property tests ==\n";
  prop::p1_aliasSoundness();
  prop::p2_joinUpperBound();
  prop::p3_widenUpperBound();
  prop::p4_reindexRoundTrip();

  std::cout << "\n" << (checks - failures) << "/" << checks << " checks passed\n";
  return failures == 0 ? 0 : 1;
}
