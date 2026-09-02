// path_domain.h -- the RCU type system's path domain, decidable fragment.
//
// Reference implementation of chapters/PathFragment.tex.  Dependency-free
// C++17, written to be lifted into a Clang Sema check.
//
// Operations:
//   inFragment   Cursor Normal Form membership
//   mayAlias     the framing side conditions of T-UnlinkH / T-Replace / T-Insert
//   join         control-flow merge (T-PSub1 / T-PSub2)
//   reindex      loop back edge (T-ReIndex), as first-order matching
//   widen        introduces (f)^k when reindexing cannot close the edge
//   analyzeLoop  the fixpoint driver: reindex, else widen, else give up

#ifndef RCU_PATH_DOMAIN_H
#define RCU_PATH_DOMAIN_H

#include <cstdint>
#include <cstddef>
#include <vector>
#include <string>
#include <set>
#include <map>
#include <queue>
#include <optional>
#include <functional>
#include <algorithm>

namespace rcu {

// ---------------------------------------------------------------------------
// Representation
// ---------------------------------------------------------------------------
//
//   Field f        one step along f                        ("Next", "Left")
//   Disj  D        one step along some f in D              ("Left|Right")
//   Var   pi : D   the word bound to pi, lying in D*       ("(Left|Right)^k")
//
// The departure from the paper: (f1|..|fn)^k is written there as a *length*
// index, but every use requires two occurrences to denote the same *word* --
// otherwise the field map relating a parent to its child does not hold.  We
// make the sharing explicit with a path variable.  See PathFragment.tex 6.1.

using FieldSet = uint32_t;

struct Seg {
  enum Kind { Field, Disj, Var } kind;
  FieldSet fields = 0;  // Field: one bit.  Disj: >=1 bits.  Var: alphabet of pi.
  int var = -1;         // Var only.

  bool operator==(const Seg &o) const {
    return kind == o.kind && fields == o.fields && var == o.var;
  }
  bool operator!=(const Seg &o) const { return !(*this == o); }
};

using Path = std::vector<Seg>;
using Env = std::vector<Path>;  // one path per RCU-typed local, positionally

inline FieldSet bit(int f) { return FieldSet(1) << f; }
inline Seg F(int f) { return Seg{Seg::Field, bit(f), -1}; }
inline Seg D(FieldSet m) { return Seg{Seg::Disj, m, -1}; }
inline Seg V(int id, FieldSet alpha) { return Seg{Seg::Var, alpha, id}; }

inline FieldSet fields(std::initializer_list<int> fs) {
  FieldSet m = 0;
  for (int f : fs) m |= bit(f);
  return m;
}

inline int popcount(FieldSet m) {
  int n = 0;
  while (m) { m &= m - 1; ++n; }
  return n;
}

// Normalise a singleton disjunction back to a concrete step.
inline Seg mkStep(FieldSet m) {
  return popcount(m) == 1 ? Seg{Seg::Field, m, -1} : D(m);
}

// ---------------------------------------------------------------------------
// Fragment membership (Cursor Normal Form)
// ---------------------------------------------------------------------------
//
// No path variable may occur twice in one path; repeated occurrences would
// require solving genuine word equations.  We reject rather than approximate,
// so coverage stays a syntactic property the programmer can see.

inline bool inFragment(const Path &p) {
  std::set<int> seen;
  for (const Seg &s : p)
    if (s.kind == Seg::Var && !seen.insert(s.var).second) return false;
  return true;
}

inline bool inFragment(const Env &e) {
  for (const Path &p : e)
    if (!inFragment(p)) return false;
  return true;
}

// ---------------------------------------------------------------------------
// MayAlias
// ---------------------------------------------------------------------------

namespace detail {

// A path relaxed to an NFA over the field alphabet.  State i sits before
// segment i; state n accepts.
struct Nfa {
  int n = 0;
  std::vector<bool> eps;       // may skip segment i without consuming
  std::vector<FieldSet> loop;  // i -> i
  std::vector<FieldSet> step;  // i -> i+1
};

inline Nfa build(const Path &p) {
  Nfa a;
  a.n = int(p.size());
  a.eps.assign(a.n, false);
  a.loop.assign(a.n, 0);
  a.step.assign(a.n, 0);
  for (int i = 0; i < a.n; ++i) {
    if (p[i].kind == Seg::Var) {
      a.eps[i] = true;          // pi may be empty
      a.loop[i] = p[i].fields;  // or consume any number of its letters
    } else {
      a.step[i] = p[i].fields;  // exactly one step
    }
  }
  return a;
}

inline void epsClose(const Nfa &a, int i, std::vector<int> &out) {
  while (true) {
    out.push_back(i);
    if (i < a.n && a.eps[i]) ++i; else break;
  }
}

inline bool intersects(const Nfa &a, const Nfa &b, int numFields) {
  std::set<std::pair<int, int>> seen;
  std::queue<std::pair<int, int>> work;

  std::vector<int> ca, cb;
  epsClose(a, 0, ca);
  epsClose(b, 0, cb);
  for (int i : ca)
    for (int j : cb)
      if (seen.insert({i, j}).second) work.push({i, j});

  while (!work.empty()) {
    auto [i, j] = work.front();
    work.pop();
    if (i == a.n && j == b.n) return true;

    for (int f = 0; f < numFields; ++f) {
      FieldSet m = bit(f);
      std::vector<int> na, nb;
      if (i < a.n && (a.loop[i] & m)) na.push_back(i);
      if (i < a.n && (a.step[i] & m)) na.push_back(i + 1);
      if (j < b.n && (b.loop[j] & m)) nb.push_back(j);
      if (j < b.n && (b.step[j] & m)) nb.push_back(j + 1);

      for (int x : na)
        for (int y : nb) {
          std::vector<int> cx, cy;
          epsClose(a, x, cx);
          epsClose(b, y, cy);
          for (int xi : cx)
            for (int yj : cy)
              if (seen.insert({xi, yj}).second) work.push({xi, yj});
        }
    }
  }
  return false;
}

}  // namespace detail

// Stage 1 consumes the maximal identical prefix -- exact, since equal whole
// words force the prefixes to resolve identically.  Stage 2 relaxes each
// variable to D* and tests NFA intersection, which can only over-approximate
// aliasing.  Every use site is under a negation, so over-approximating here
// rejects safe programs but never accepts unsafe ones.
inline bool mayAlias(const Path &p, const Path &q, int numFields) {
  size_t k = 0;
  while (k < p.size() && k < q.size() && p[k] == q[k]) ++k;

  Path pr(p.begin() + k, p.end());
  Path qr(q.begin() + k, q.end());
  return detail::intersects(detail::build(pr), detail::build(qr), numFields);
}

inline bool mayAlias(const Path &p, const std::vector<Path> &qs, int numFields) {
  for (const Path &q : qs)
    if (mayAlias(p, q, numFields)) return true;
  return false;
}

// ---------------------------------------------------------------------------
// Join (T-PSub1 / T-PSub2)
// ---------------------------------------------------------------------------

inline std::optional<Path> join(const Path &p, const Path &q) {
  if (p.size() != q.size()) return std::nullopt;
  Path r;
  r.reserve(p.size());
  for (size_t i = 0; i < p.size(); ++i) {
    if (p[i].kind == Seg::Var || q[i].kind == Seg::Var) {
      if (p[i] != q[i]) return std::nullopt;  // cannot merge a variable with a step
      r.push_back(p[i]);
    } else {
      r.push_back(mkStep(p[i].fields | q[i].fields));
    }
  }
  return r;
}

// ---------------------------------------------------------------------------
// Reindexing (T-ReIndex)
// ---------------------------------------------------------------------------
//
// Find one substitution sigma, applied uniformly to the whole environment,
// with sigma(entry) == exit.  Uniformity is exactly the paper's side condition
// that "either all are reindexed, or none".  sigma is restricted to suffix
// extension, sigma(pi) = pi . w.

inline Path substitute(const Path &p, const std::map<int, Path> &sigma) {
  Path r;
  for (const Seg &s : p) {
    if (s.kind == Seg::Var) {
      auto it = sigma.find(s.var);
      if (it != sigma.end()) {
        r.insert(r.end(), it->second.begin(), it->second.end());
        continue;
      }
    }
    r.push_back(s);
  }
  return r;
}

inline std::optional<std::pair<int, Path>> proposeReindex(const Path &entry,
                                                          const Path &exit) {
  if (exit.size() <= entry.size()) return std::nullopt;
  size_t grew = exit.size() - entry.size();

  for (size_t i = 0; i < entry.size(); ++i) {
    if (entry[i].kind != Seg::Var) continue;
    // entry = A . pi . B ; require exit = A . pi . w . B with |w| = grew.
    bool ok = true;
    for (size_t j = 0; j <= i && ok; ++j) ok = (entry[j] == exit[j]);
    for (size_t j = i + 1; j < entry.size() && ok; ++j)
      ok = (entry[j] == exit[j + grew]);
    if (!ok) continue;

    Path w{entry[i]};
    w.insert(w.end(), exit.begin() + i + 1, exit.begin() + i + 1 + grew);
    return std::make_pair(entry[i].var, w);
  }
  return std::nullopt;
}

inline std::optional<std::map<int, Path>> reindex(const Env &entry, const Env &exit) {
  if (entry.size() != exit.size()) return std::nullopt;

  std::map<int, Path> sigma;
  for (size_t i = 0; i < entry.size(); ++i) {
    if (entry[i] == exit[i]) continue;
    auto cand = proposeReindex(entry[i], exit[i]);
    if (!cand) return std::nullopt;
    auto it = sigma.find(cand->first);
    if (it != sigma.end()) {
      if (it->second != cand->second) return std::nullopt;  // not uniform
    } else {
      sigma.insert(*cand);
    }
  }
  if (sigma.empty()) return std::map<int, Path>{};  // already invariant

  for (size_t i = 0; i < entry.size(); ++i)
    if (substitute(entry[i], sigma) != exit[i]) return std::nullopt;
  return sigma;
}

// ---------------------------------------------------------------------------
// Widening
// ---------------------------------------------------------------------------
//
// Reindexing closes a back edge only once a variable exists to extend.  On the
// first arrival there is none -- the bag enters its loop with par : eps and
// cur : Next -- so the variable has to be *introduced*.  That is this operation:
// it is how one infers (Next)^k rather than being handed it.
//
// The essential constraint is that widening cannot be done path by path.  If
// each path generalises at its own longest-common-prefix, the bag yields
// par : (Next)^k and cur : Next.(Next)^k, which happens to denote the right
// language but asserts that cur is par with a step *prepended*.  The relational
// structure -- cur is par's child -- is destroyed, and with it every field map.
// So a single fresh variable is inserted at one common position across the
// whole environment:
//
//    find the smallest i, and a single inserted chunk w, such that
//    exit[x] = entry[x][0..i) . w . entry[x][i..)   for every moving x
//
// then replace w by a fresh variable over the union of w's alphabets.  Paths
// the loop leaves alone (d = 0) pass through untouched.
//
// Soundness: taking the fresh variable to be eps recovers entry exactly, and
// taking it to be a word of w covers exit, so the result is an upper bound of
// both.  Because all moving paths share one w, a single valuation serves the
// whole environment.

inline std::optional<Env> widen(const Env &entry, const Env &exit, int freshVar) {
  if (entry.size() != exit.size()) return std::nullopt;

  int d = -1;
  std::vector<bool> moving(entry.size(), false);
  for (size_t x = 0; x < entry.size(); ++x) {
    if (entry[x] == exit[x]) continue;                 // frozen
    if (exit[x].size() <= entry[x].size()) return std::nullopt;
    int dx = int(exit[x].size() - entry[x].size());
    if (d == -1) d = dx;
    else if (d != dx) return std::nullopt;             // cursors advanced unevenly
    moving[x] = true;
  }
  if (d <= 0) return std::nullopt;                      // nothing to widen

  size_t minLen = SIZE_MAX;
  for (size_t x = 0; x < entry.size(); ++x)
    if (moving[x]) minLen = std::min(minLen, entry[x].size());

  for (size_t i = 0; i <= minLen; ++i) {
    std::optional<Path> w;
    bool ok = true;
    for (size_t x = 0; x < entry.size() && ok; ++x) {
      if (!moving[x]) continue;
      for (size_t j = 0; j < i && ok; ++j) ok = (entry[x][j] == exit[x][j]);
      for (size_t j = i; j < entry[x].size() && ok; ++j)
        ok = (entry[x][j] == exit[x][j + d]);
      if (!ok) break;
      Path wx(exit[x].begin() + i, exit[x].begin() + i + d);
      if (!w) w = wx;
      else if (*w != wx) ok = false;                    // no single common chunk
    }
    if (!ok || !w) continue;

    FieldSet alpha = 0;
    for (const Seg &s : *w) alpha |= s.fields;
    Seg fresh = V(freshVar, alpha);

    Env out;
    for (size_t x = 0; x < entry.size(); ++x) {
      if (!moving[x]) { out.push_back(entry[x]); continue; }
      Path p(entry[x].begin(), entry[x].begin() + i);
      p.push_back(fresh);
      p.insert(p.end(), entry[x].begin() + i, entry[x].end());
      out.push_back(p);
    }
    return out;
  }
  return std::nullopt;
}

// ---------------------------------------------------------------------------
// Loop fixpoint
// ---------------------------------------------------------------------------
//
// Try the body; if the edge closes (equal, or equal after reindexing) we have
// the invariant.  Otherwise widen and retry.  maxRounds bounds the iteration:
// each widening introduces one variable, and the count of live cursors is
// bounded by loop-nesting depth, so a small cap suffices in practice.  Failure
// to converge is reported rather than silently approximated.

struct LoopResult {
  bool converged = false;
  Env invariant;
  std::map<int, Path> sigma;
  int widenings = 0;
};

inline LoopResult analyzeLoop(const Env &entry,
                              const std::function<Env(const Env &)> &body,
                              int firstFreshVar,
                              int maxRounds = 4) {
  LoopResult r;
  Env cur = entry;
  for (int round = 0; round < maxRounds; ++round) {
    Env next = body(cur);
    if (auto s = reindex(cur, next)) {
      r.converged = true;
      r.invariant = cur;
      r.sigma = *s;
      return r;
    }
    auto w = widen(cur, next, firstFreshVar + r.widenings);
    if (!w) return r;  // outside the fragment
    ++r.widenings;
    cur = *w;
  }
  return r;
}

// ---------------------------------------------------------------------------
// Concrete semantics -- used only by the property tests
// ---------------------------------------------------------------------------

using Word = std::string;  // letter f is encoded as char('a' + f)

// The set of concrete words a path denotes under a valuation of its variables.
inline std::set<Word> lang(const Path &p, const std::map<int, Word> &theta, int numFields) {
  std::set<Word> cur{Word()};
  for (const Seg &s : p) {
    std::set<Word> next;
    if (s.kind == Seg::Var) {
      auto it = theta.find(s.var);
      Word w = (it == theta.end()) ? Word() : it->second;
      for (const Word &c : cur) next.insert(c + w);
    } else {
      for (int f = 0; f < numFields; ++f)
        if (s.fields & bit(f))
          for (const Word &c : cur) next.insert(c + char('a' + f));
    }
    cur.swap(next);
  }
  return cur;
}

inline void varsOf(const Path &p, std::map<int, FieldSet> &out) {
  for (const Seg &s : p)
    if (s.kind == Seg::Var) out[s.var] |= s.fields;
}

inline std::vector<Word> wordsUpTo(FieldSet alpha, int numFields, int maxLen) {
  std::vector<Word> all{Word()};
  std::vector<Word> level{Word()};
  for (int L = 1; L <= maxLen; ++L) {
    std::vector<Word> next;
    for (const Word &w : level)
      for (int f = 0; f < numFields; ++f)
        if (alpha & bit(f)) next.push_back(w + char('a' + f));
    for (const Word &w : next) all.push_back(w);
    level.swap(next);
  }
  return all;
}

// Enumerate every valuation of the given variables with |theta(pi)| <= maxLen.
inline void forEachValuation(const std::map<int, FieldSet> &vars, int numFields, int maxLen,
                             const std::function<void(const std::map<int, Word> &)> &f) {
  std::vector<int> ids;
  std::vector<std::vector<Word>> choices;
  for (const auto &kv : vars) {
    ids.push_back(kv.first);
    choices.push_back(wordsUpTo(kv.second, numFields, maxLen));
  }
  std::vector<size_t> idx(ids.size(), 0);
  while (true) {
    std::map<int, Word> theta;
    for (size_t i = 0; i < ids.size(); ++i) theta[ids[i]] = choices[i][idx[i]];
    f(theta);
    size_t i = 0;
    for (; i < ids.size(); ++i) {
      if (++idx[i] < choices[i].size()) break;
      idx[i] = 0;
    }
    if (i == ids.size()) break;
  }
}

// ---------------------------------------------------------------------------
// Printing
// ---------------------------------------------------------------------------

inline std::string show(const Path &p, const std::vector<std::string> &names) {
  if (p.empty()) return "eps";
  std::string out;
  for (size_t i = 0; i < p.size(); ++i) {
    if (i) out += ".";
    bool multi = popcount(p[i].fields) > 1;
    bool paren = multi || p[i].kind == Seg::Var;
    if (paren) out += "(";
    bool first = true;
    for (size_t f = 0; f < names.size(); ++f)
      if (p[i].fields & bit(int(f))) {
        if (!first) out += "|";
        out += names[f];
        first = false;
      }
    if (paren) out += ")";
    if (p[i].kind == Seg::Var) out += "^" + std::to_string(p[i].var);
  }
  return out;
}

}  // namespace rcu

#endif  // RCU_PATH_DOMAIN_H
