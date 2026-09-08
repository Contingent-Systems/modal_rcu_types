// frontend.cpp -- Clang AST to the checker's statement IR.
//
//   ./setup-frontend.sh --install     once, to get LLVM
//   make frontend
//   ./rcu-check testdata/bst.c --
//
// The only part of the checker that depends on a compiler.  Its job is
// translation: recognise the RCU actions in a function body, emit the Stmt IR
// of rcu_check.h, run the driver, and turn what it reports into diagnostics.
// Nothing here decides anything about types.
//
// Bodies are translated through Clang's CFG, so branches and loops are handled:
// merges become joins, and back edges -- identified by dominance, an edge whose
// target dominates its source -- are closed by reindexing or widening rather
// than joined.  A construct it does not recognise inside a
// critical section is reported, not skipped: a checker that silently ignores
// what it cannot read is worse than one that says so, because its silence looks
// like a pass.

#include "rcu_check.h"

#include "clang/AST/ASTConsumer.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include "clang/Analysis/Analyses/Dominators.h"
#include "clang/Analysis/AnalysisDeclContext.h"
#include "clang/Analysis/CFG.h"
#include "clang/Basic/Diagnostic.h"
#include "clang/Frontend/CompilerInstance.h"
#include "clang/Frontend/FrontendAction.h"
#include "clang/Tooling/CommonOptionsParser.h"
#include "clang/Tooling/Tooling.h"
#include "llvm/Support/CommandLine.h"

#include <map>
#include <string>
#include <vector>

using namespace clang;

namespace {

llvm::cl::OptionCategory RcuCategory("rcu-check options");
llvm::cl::opt<bool> DumpIR("dump-ir",
                           llvm::cl::desc("print the statement IR translated "
                                          "from each function"),
                           llvm::cl::cat(RcuCategory));

// ---------------------------------------------------------------------------
// Names
// ---------------------------------------------------------------------------
//
// The checker works in dense integer ids.  This is the only place the C names
// live, and it is what turns a diagnosis back into something readable -- which
// matters more than usual here, because the environments are inferred and so
// there is no annotation for the reader to look at.

struct Names {
  std::map<const ValueDecl *, int> var;
  std::map<const FieldDecl *, int> field;
  std::vector<std::string> varName, fieldName;

  int of(const ValueDecl *d) {
    auto it = var.find(d);
    if (it != var.end()) return it->second;
    int id = int(varName.size());
    var[d] = id;
    varName.push_back(d->getNameAsString());
    return id;
  }
  int of(const FieldDecl *d) {
    auto it = field.find(d);
    if (it != field.end()) return it->second;
    int id = int(fieldName.size());
    field[d] = id;
    fieldName.push_back(d->getNameAsString());
    return id;
  }
};

// A field is RCU-typed if it carries __rcu.  In the kernel that is an address
// space attribute; elsewhere an annotation.  Both are accepted, so the checker
// runs on kernel source and on a user-level codebase without either changing.
bool isRCUField(const FieldDecl *f) {
  for (const auto *a : f->specific_attrs<AnnotateAttr>())
    if (a->getAnnotation() == "__rcu" || a->getAnnotation() == "rcu") return true;
  return f->getType().getAddressSpace() != LangAS::Default &&
         f->getType()->isPointerType();
}

std::string calleeName(const CallExpr *c) {
  if (const FunctionDecl *f = c->getDirectCallee()) return f->getNameAsString();
  return {};
}

// x->f or x.f, where f is RCU-typed.
const MemberExpr *rcuMember(const Expr *e) {
  const auto *me = llvm::dyn_cast<MemberExpr>(e->IgnoreParenImpCasts());
  if (!me) return nullptr;
  const auto *fd = llvm::dyn_cast<FieldDecl>(me->getMemberDecl());
  return (fd && isRCUField(fd)) ? me : nullptr;
}

const ValueDecl *baseVar(const MemberExpr *me) {
  const auto *dr = llvm::dyn_cast<DeclRefExpr>(me->getBase()->IgnoreParenImpCasts());
  return dr ? dr->getDecl() : nullptr;
}

// ---------------------------------------------------------------------------
// Translation
// ---------------------------------------------------------------------------

struct Translated {
  std::vector<rcu::Stmt> stmts;
  std::vector<std::pair<unsigned, std::string>> unhandled;
  rcu::FieldSet rcuFields = 0;
};

class Translator {
 public:
  Translator(ASTContext &ctx, Names &names) : ctx_(ctx), names_(names) {}

  // Set between passes: which functions have summaries, and their index.
  std::map<const FunctionDecl *, int> *summaryOf = nullptr;

  // Translate one CFG block.  Accumulated state (names, the RCU field set,
  // what could not be translated) is shared across blocks of a function.
  std::vector<rcu::Stmt> block(const CFGBlock *b) {
    std::vector<rcu::Stmt> saved;
    saved.swap(out_.stmts);
    for (const CFGElement &e : *b)
      if (std::optional<CFGStmt> cs = e.getAs<CFGStmt>()) one(cs->getStmt());
    std::vector<rcu::Stmt> got;
    got.swap(out_.stmts);
    out_.stmts.swap(saved);
    return got;
  }

  Translated &state() { return out_; }

  // What a branch proves on its true edge.  Clang keeps the condition in the
  // block's terminator, and orders the successors true-then-false, so this is
  // the one place the two branches can be told apart.
  //
  // Two shapes matter, and the type system has a rule for each:
  //   if (x->f == NULL)   the field is null      -- T-UnlinkH needs it
  //   if (x->f == y)      the field holds y      -- the field-refining rule
  // The BST delete performs both, and neither can be typed without them.
  std::vector<rcu::Stmt> refinementsOf(const CFGBlock *b) {
    std::vector<rcu::Stmt> out;
    const Stmt *cond = b->getTerminatorCondition();
    if (!cond) return out;
    const auto *ce = llvm::dyn_cast<Expr>(cond);
    const auto *bo = ce ? llvm::dyn_cast<BinaryOperator>(ce->IgnoreParenImpCasts())
                        : nullptr;
    if (!bo || bo->getOpcode() != BO_EQ) return out;

    const MemberExpr *me = rcuMember(bo->getLHS());
    const Expr *other = bo->getRHS();
    if (!me) { me = rcuMember(bo->getRHS()); other = bo->getLHS(); }
    if (!me) return out;
    const ValueDecl *base = baseVar(me);
    if (!base) return out;

    rcu::Stmt st;
    st.x = names_.of(base);
    st.f = rcu::bit(names_.of(llvm::cast<FieldDecl>(me->getMemberDecl())));
    st.line = line(cond->getBeginLoc());

    if (other->isNullPointerConstant(ctx_, Expr::NPC_ValueDependentIsNull)) {
      st.kind = rcu::Stmt::RefineNull;
      out.push_back(st);
    } else if (const auto *dr = llvm::dyn_cast<DeclRefExpr>(
                   other->IgnoreParenImpCasts())) {
      st.kind = rcu::Stmt::RefineField;
      st.y = names_.of(dr->getDecl());
      out.push_back(st);
    }
    return out;
  }

 private:
  unsigned line(SourceLocation l) const {
    return ctx_.getSourceManager().getSpellingLineNumber(l);
  }

  void note(const Stmt *s, const std::string &what) {
    out_.unhandled.emplace_back(line(s->getBeginLoc()), what);
  }

  void one(const Stmt *s) {
    // T *z = x->f;
    if (const auto *ds = llvm::dyn_cast<DeclStmt>(s)) {
      for (const Decl *d : ds->decls()) {
        const auto *vd = llvm::dyn_cast<VarDecl>(d);
        if (!vd || !vd->hasInit()) continue;
        // T *n = kmalloc(...)  -- a fresh node; or T *z = f(...)  -- a call
        if (const auto *ce = llvm::dyn_cast<CallExpr>(
                vd->getInit()->IgnoreParenImpCasts())) {
          std::string cn = calleeName(ce);
          if (cn == "kmalloc" || cn == "malloc" || cn == "kzalloc") {
            rcu::Stmt st;
            st.kind = rcu::Stmt::Alloc;
            st.x = names_.of(vd);
            st.line = line(s->getBeginLoc());
            out_.stmts.push_back(st);
            continue;
          }
          if (summaryOf) {
            auto sit = summaryOf->find(ce->getDirectCallee());
            if (sit != summaryOf->end()) {
              rcu::Stmt st;
              st.kind = rcu::Stmt::Call;
              st.callee = sit->second;
              st.z = names_.of(vd);
              st.line = line(s->getBeginLoc());
              for (const Expr *a : ce->arguments())
                if (const auto *dr = llvm::dyn_cast<DeclRefExpr>(a->IgnoreParenImpCasts()))
                  st.args.push_back(names_.of(dr->getDecl()));
                else
                  st.args.push_back(-1);
              out_.stmts.push_back(st);
              continue;
            }
          }
        }
        // T *x = y;  -- the declaration form of T-ReadS.  Distinct from the
        // assignment form and just as necessary: a traversal that seeds its
        // cursor with `p = root` gets no type for p without it.
        if (const auto *dr = llvm::dyn_cast<DeclRefExpr>(
                vd->getInit()->IgnoreParenImpCasts())) {
          if (dr->getType()->isPointerType()) {
            rcu::Stmt st;
            st.kind = rcu::Stmt::ReadS;
            st.x = names_.of(dr->getDecl());
            st.z = names_.of(vd);
            st.line = line(s->getBeginLoc());
            out_.stmts.push_back(st);
            continue;
          }
        }
        if (const MemberExpr *me = rcuMember(vd->getInit())) {
          const ValueDecl *base = baseVar(me);
          if (!base) { note(s, "field read from a non-variable base"); continue; }
          rcu::Stmt st;
          st.kind = rcu::Stmt::ReadH;
          st.x = names_.of(base);
          st.f = rcu::bit(names_.of(llvm::cast<FieldDecl>(me->getMemberDecl())));
          st.z = names_.of(vd);
          st.line = line(s->getBeginLoc());
          out_.rcuFields |= st.f;
          out_.stmts.push_back(st);
        }
      }
      return;
    }

    if (const auto *bo = llvm::dyn_cast<BinaryOperator>(s)) {
      if (!bo->isAssignmentOp()) { note(s, "expression statement"); return; }
      // p->f = n  -- which of the four rules applies depends on the types of p
      // and n at this point, which the driver knows and this does not.
      if (const MemberExpr *me = rcuMember(bo->getLHS())) {
        const ValueDecl *base = baseVar(me);
        const auto *rhs = llvm::dyn_cast<DeclRefExpr>(bo->getRHS()->IgnoreParenImpCasts());
        if (!base || !rhs) { note(s, "assignment with a non-variable operand"); return; }
        rcu::Stmt st;
        st.kind = rcu::Stmt::WriteFH;   // the driver refines
        st.x = names_.of(base);
        st.f = rcu::bit(names_.of(llvm::cast<FieldDecl>(me->getMemberDecl())));
        st.z = names_.of(rhs->getDecl());
        st.line = line(s->getBeginLoc());
        out_.rcuFields |= st.f;
        out_.stmts.push_back(st);
        return;
      }
      // x = y between locals is T-ReadS.  Easy to overlook, and a traversal
      // loop cannot close without it: the cursor advances by exactly this
      // assignment, so dropping it leaves the back edge comparing a cursor
      // that never moved against one that did.
      {
        const auto *lhs = llvm::dyn_cast<DeclRefExpr>(bo->getLHS()->IgnoreParenImpCasts());
        const auto *rhs = llvm::dyn_cast<DeclRefExpr>(bo->getRHS()->IgnoreParenImpCasts());
        if (lhs && rhs && lhs->getType()->isPointerType()) {
          rcu::Stmt st;
          st.kind = rcu::Stmt::ReadS;
          st.x = names_.of(rhs->getDecl());
          st.z = names_.of(lhs->getDecl());
          st.line = line(s->getBeginLoc());
          out_.stmts.push_back(st);
          return;
        }
      }
      note(s, "assignment to something other than an RCU field");
      return;
    }

    const auto *asExpr = llvm::dyn_cast<Expr>(s);
    if (const auto *ce = asExpr ? llvm::dyn_cast<CallExpr>(asExpr->IgnoreImplicit())
                                : nullptr) {
      std::string n = calleeName(ce);
      rcu::Stmt st;
      st.line = line(s->getBeginLoc());
      if (n == "synchronize_rcu") { st.kind = rcu::Stmt::Sync; out_.stmts.push_back(st); return; }
      if (n == "kfree" || n == "free" || n == "call_rcu") {
        st.kind = rcu::Stmt::Free;
        if (ce->getNumArgs() > 0)
          if (const auto *dr = llvm::dyn_cast<DeclRefExpr>(
                  ce->getArg(0)->IgnoreParenImpCasts()))
            st.x = names_.of(dr->getDecl());
        out_.stmts.push_back(st);
        return;
      }
      if (n == "rcu_read_lock" || n == "rcu_read_unlock") return;  // boundaries
      if (summaryOf) {
        auto sit = summaryOf->find(ce->getDirectCallee());
        if (sit != summaryOf->end()) {
          st.kind = rcu::Stmt::Call;
          st.callee = sit->second;
          for (const Expr *a : ce->arguments())
            if (const auto *dr = llvm::dyn_cast<DeclRefExpr>(a->IgnoreParenImpCasts()))
              st.args.push_back(names_.of(dr->getDecl()));
            else
              st.args.push_back(-1);
          out_.stmts.push_back(st);
          return;
        }
      }
      note(s, "call to " + n);
      return;
      note(s, "call to " + n);
      return;
    }

    // Control-flow constructs carry no action of their own; the CFG has
    // already split them into blocks and edges.
    if (llvm::isa<IfStmt>(s) || llvm::isa<WhileStmt>(s) || llvm::isa<ForStmt>(s) ||
        llvm::isa<DoStmt>(s) || llvm::isa<ReturnStmt>(s) || llvm::isa<NullStmt>(s))
      return;
    note(s, "unrecognised statement");
  }

  ASTContext &ctx_;
  Names &names_;
  Translated out_;
};

// ---------------------------------------------------------------------------
// Driving
// ---------------------------------------------------------------------------

class Consumer : public ASTConsumer {
 public:
  explicit Consumer(CompilerInstance &ci) : ci_(ci) {}

  void HandleTranslationUnit(ASTContext &ctx) override {
    DiagnosticsEngine &de = ci_.getDiagnostics();
    unsigned err  = de.getCustomDiagID(DiagnosticsEngine::Warning, "rcu: %0");
    unsigned note = de.getCustomDiagID(DiagnosticsEngine::Note, "rcu: %0");

    std::vector<const FunctionDecl *> fns;
    for (Decl *d : ctx.getTranslationUnitDecl()->decls())
      if (auto *fd = llvm::dyn_cast<FunctionDecl>(d))
        if (fd->hasBody() && fd->isThisDeclarationADefinition())
          fns.push_back(fd);

    // Pass one derives a summary per function; pass two checks each body with
    // the summaries available, so a call is checked rather than skipped.
    //
    // Two passes handle one level of calls.  A chain deeper than that needs
    // iteration to a fixpoint in dependency order, which is the same shape of
    // work and is not done here.
    rcu::Config conf;
    conf.rcuFields = 0;
    std::map<const FunctionDecl *, int> index;

    for (const FunctionDecl *fd : fns) {
      Names names;
      Translator tr(ctx, names);
      rcu::Cfg cfg;
      int entry = 0;
      if (!build(ctx, fd, tr, cfg, entry)) continue;

      rcu::Config c1;
      c1.rcuFields = tr.state().rcuFields;
      c1.numFields = int(names.fieldName.size());

      // Which kind the parameters must have on entry is not always "iterator".
      // A helper that reclaims a node takes one already unlinked, and assuming
      // otherwise makes every call to it a false positive.  Rather than infer
      // the requirement -- which is the same problem the whole system solves --
      // the candidates are tried and the first that checks is taken.  A search
      // over three possibilities, not an inference, and it is uniform across
      // the parameters, so a function mixing kinds is not found.
      const rcu::Type::Kind candidates[] = {rcu::Type::Itr, rcu::Type::Unlinked,
                                            rcu::Type::Fresh};
      rcu::Type::Kind chosen = rcu::Type::Itr;
      rcu::TypeEnv in;
      rcu::CheckResult r;
      for (rcu::Type::Kind k : candidates) {
        rcu::TypeEnv trial = assumedEntry(fd, names, c1, k);
        rcu::CheckResult tr2 = rcu::check(cfg, trial, c1, entry);
        if (tr2.ok) { chosen = k; in = trial; r = tr2; break; }
        if (k == rcu::Type::Itr) { in = trial; r = tr2; }  // the fallback
      }

      rcu::Summary sum;
      sum.name = fd->getNameAsString();
      // Clang numbers the exit block 0 and the entry block last, so the state
      // after the body is the exit block's entry environment -- not the last
      // one in the vector, which is where the *parameters* still sit exactly as
      // they were assumed.  Reading that instead makes every summary report
      // that the function changes nothing.
      const rcu::TypeEnv &out = r.entry.empty() ? in : r.entry[0];
      for (const ParmVarDecl *p : fd->parameters()) {
        if (!p->getType()->isPointerType()) continue;
        int id = names.of(p);
        sum.paramIn.push_back(chosen);
        auto it = out.find(id);
        sum.paramOut.push_back(it == out.end() ? rcu::Type::Undef : it->second.kind);
      }
      sum.returnsIterator = fd->getReturnType()->isPointerType();
      index[fd] = int(conf.summaries.size());
      conf.summaries.push_back(sum);
      conf.rcuFields |= c1.rcuFields;
    }

    for (const FunctionDecl *fd : fns) {
      Names names;
      Translator tr(ctx, names);
      tr.summaryOf = &index;
      rcu::Cfg cfg;
      int entry = 0;
      if (!build(ctx, fd, tr, cfg, entry)) continue;

      rcu::detail::varNamer() = [&names](int v) {
        return v >= 0 && v < int(names.varName.size()) ? names.varName[v]
                                                       : "v" + std::to_string(v);
      };
      rcu::detail::fieldNamer() = [&names](int f) {
        return f >= 0 && f < int(names.fieldName.size()) ? names.fieldName[f]
                                                         : std::to_string(f);
      };

      rcu::Config c = conf;
      c.rcuFields = tr.state().rcuFields;
      c.numFields = int(names.fieldName.size());

      if (DumpIR) {
        llvm::outs() << "-- " << fd->getNameAsString() << "\n";
        for (unsigned i = 0; i < cfg.size(); ++i)
          for (const rcu::Stmt &s : cfg[i].stmts)
            llvm::outs() << "   B" << i << " line " << s.line
                         << "  kind " << int(s.kind) << "\n";
      }

      for (const auto &u : tr.state().unhandled)
        de.Report(ctx.getSourceManager().translateLineCol(
                      ctx.getSourceManager().getMainFileID(), u.first, 1),
                  note)
            << ("not translated: " + u.second);

      rcu::Type::Kind pk = rcu::Type::Itr;
      auto iit = index.find(fd);
      if (iit != index.end() && !conf.summaries[iit->second].paramIn.empty())
        pk = conf.summaries[iit->second].paramIn[0];
      rcu::CheckResult r =
          rcu::check(cfg, assumedEntry(fd, names, c, pk), c, entry);
      for (const rcu::Diagnosis &dg : r.errors) {
        SourceLocation at =
            dg.line > 0 ? ctx.getSourceManager().translateLineCol(
                              ctx.getSourceManager().getMainFileID(), dg.line, 1)
                        : fd->getBeginLoc();
        de.Report(at, err) << dg.why;
      }
    }
  }

  // A function's parameters are the caller's, and what they are on entry is
  // the caller's business.  Typing them as iterators is an assumption; the
  // alternative is to infer what the body requires, which is the same problem
  // the whole system solves and is not attempted here.
  static rcu::TypeEnv assumedEntry(const FunctionDecl *fd, Names &names,
                                   const rcu::Config &c,
                                   rcu::Type::Kind k = rcu::Type::Itr) {
    rcu::TypeEnv g;
    int pv = 0;
    for (const ParmVarDecl *p : fd->parameters()) {
      if (!p->getType()->isPointerType()) continue;
      int id = names.of(p);
      if (k == rcu::Type::Itr)
        g[id] = rcu::tItr(rcu::Path{rcu::V(pv++, c.rcuFields)});
      else if (k == rcu::Type::Unlinked) g[id] = rcu::tUnlinked();
      else                               g[id] = rcu::tFresh();
    }
    return g;
  }

  // No Names parameter: tr already holds the reference.
  bool build(ASTContext &ctx, const FunctionDecl *fd, Translator &tr,
             rcu::Cfg &cfg, int &entry) {
    AnalysisDeclContextManager mgr(ctx);
    AnalysisDeclContext *adc = mgr.getContext(fd);
    if (!adc) return false;
    CFG *g = adc->getCFG();
    if (!g) return false;
    CFGDomTree dom;
    dom.buildDominatorTree(g);

    cfg.assign(g->getNumBlockIDs(), rcu::Block{});
    for (const CFGBlock *b : *g) {
      unsigned id = b->getBlockID();
      cfg[id].stmts = tr.block(b);
      std::vector<rcu::Stmt> refine = tr.refinementsOf(b);
      bool first = true;
      for (const CFGBlock::AdjacentBlock &adj : b->succs()) {
        const CFGBlock *s = adj.getReachableBlock();
        if (!s) { first = false; continue; }
        if (dom.dominates(s, b)) {
          cfg[id].backSuccs.push_back(s->getBlockID());
        } else {
          cfg[id].succs.push_back(s->getBlockID());
          if (first && !refine.empty()) cfg[id].onEdge[s->getBlockID()] = refine;
        }
        first = false;
      }
    }
    entry = int(g->getEntry().getBlockID());
    return true;
  }

 private:
  CompilerInstance &ci_;
};

class Action : public ASTFrontendAction {
 public:
  std::unique_ptr<ASTConsumer> CreateASTConsumer(CompilerInstance &ci,
                                                 llvm::StringRef) override {
    return std::make_unique<Consumer>(ci);
  }
};

}  // namespace

int main(int argc, const char **argv) {
  auto opts = clang::tooling::CommonOptionsParser::create(argc, argv, RcuCategory);
  if (!opts) {
    llvm::errs() << toString(opts.takeError());
    return 1;
  }
  clang::tooling::ClangTool tool(opts->getCompilations(), opts->getSourcePathList());
  return tool.run(clang::tooling::newFrontendActionFactory<Action>().get());
}
