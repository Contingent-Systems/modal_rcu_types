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
// Scope, stated plainly: this translates *straight-line* bodies.  Branches and
// loops need the CFG with dominators, which is the next piece -- see
// setup-frontend.sh --status.  A construct it does not recognise inside a
// critical section is reported, not skipped: a checker that silently ignores
// what it cannot read is worse than one that says so, because its silence looks
// like a pass.

#include "rcu_check.h"

#include "clang/AST/ASTConsumer.h"
#include "clang/AST/RecursiveASTVisitor.h"
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

  Translated run(const FunctionDecl *fd) {
    out_ = Translated{};
    if (const auto *body = llvm::dyn_cast_or_null<CompoundStmt>(fd->getBody()))
      for (const Stmt *s : body->body()) one(s);
    return out_;
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
      note(s, "call to " + n);
      return;
    }

    if (llvm::isa<IfStmt>(s) || llvm::isa<WhileStmt>(s) || llvm::isa<ForStmt>(s)) {
      note(s, "control flow: needs the CFG, which is not wired up yet");
      return;
    }
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

    for (Decl *d : ctx.getTranslationUnitDecl()->decls()) {
      auto *fd = llvm::dyn_cast<FunctionDecl>(d);
      if (!fd || !fd->hasBody() || !fd->isThisDeclarationADefinition()) continue;

      Names names;
      Translator tr(ctx, names);
      Translated t = tr.run(fd);
      if (t.stmts.empty() && t.unhandled.empty()) continue;

      if (DumpIR) {
        llvm::outs() << "-- " << fd->getNameAsString() << "\n";
        for (const rcu::Stmt &s : t.stmts)
          llvm::outs() << "   line " << s.line << "  kind " << int(s.kind) << "\n";
      }

      for (const auto &u : t.unhandled)
        de.Report(ctx.getSourceManager().translateLineCol(
                      ctx.getSourceManager().getMainFileID(), u.first, 1),
                  note)
            << ("not translated: " + u.second);

      rcu::Config conf;
      conf.rcuFields = t.rcuFields;
      conf.numFields = int(names.fieldName.size());

      rcu::Cfg cfg(1);
      cfg[0].stmts = t.stmts;
      rcu::CheckResult r = rcu::check(cfg, rcu::TypeEnv{}, conf);
      for (const rcu::Diagnosis &dg : r.errors)
        de.Report(ctx.getSourceManager().translateLineCol(
                      ctx.getSourceManager().getMainFileID(), dg.line, 1),
                  err)
            << dg.why;
    }
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
