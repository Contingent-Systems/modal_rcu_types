#!/bin/sh
#
# setup-frontend.sh -- toolchain setup for the Clang frontend.
#
#   ./setup-frontend.sh              report what is present and what is missing
#   ./setup-frontend.sh --status     the same, verbosely, with next steps
#   ./setup-frontend.sh --install    install the missing pieces (macOS/Homebrew)
#   ./setup-frontend.sh --llvm-config    print the path to llvm-config, or nothing
#
# Nothing is installed unless --install is passed.  The checker itself needs
# none of this: `make check` builds and runs the whole test suite with the
# system compiler.  LLVM is needed only for the frontend that translates C into
# the statement IR.

set -eu

# ---------------------------------------------------------------------------
# Finding llvm-config
# ---------------------------------------------------------------------------
#
# Apple's toolchain ships clang but not llvm-config or the development headers,
# so a bare `clang++` on the PATH proves nothing.  These are the usual places a
# real installation lands.

find_llvm_config() {
  for c in \
    "${LLVM_CONFIG:-}" \
    "$(command -v llvm-config 2>/dev/null || true)" \
    /opt/homebrew/opt/llvm/bin/llvm-config \
    /usr/local/opt/llvm/bin/llvm-config \
    /opt/homebrew/opt/llvm@18/bin/llvm-config \
    /usr/local/opt/llvm@18/bin/llvm-config \
    /usr/lib/llvm-18/bin/llvm-config \
    /usr/bin/llvm-config
  do
    [ -n "${c:-}" ] || continue
    [ -x "$c" ] || continue
    echo "$c"
    return 0
  done
  return 1
}

# Clang's own development headers, which llvm-config does not report on.
have_clang_dev() {
  lc="$1"
  inc="$($lc --includedir 2>/dev/null || true)"
  [ -n "$inc" ] && [ -f "$inc/clang/AST/ASTConsumer.h" ]
}

case "${1:-}" in
--llvm-config)
  find_llvm_config || true
  exit 0
  ;;
esac

# ---------------------------------------------------------------------------
# Report
# ---------------------------------------------------------------------------

echo "RCU checker -- frontend toolchain"
echo

if cxx="$(command -v c++ 2>/dev/null)"; then
  echo "  C++ compiler   $cxx"
else
  echo "  C++ compiler   MISSING -- the checker itself will not build"
fi

if lc="$(find_llvm_config)"; then
  echo "  llvm-config    $lc  ($($lc --version))"
  if have_clang_dev "$lc"; then
    echo "  clang headers  $($lc --includedir)/clang"
    ready=yes
  else
    echo "  clang headers  MISSING -- llvm is present but the Clang development"
    echo "                 headers are not; on Homebrew these come with the same"
    echo "                 formula, so the install is probably partial"
    ready=no
  fi
else
  echo "  llvm-config    MISSING"
  echo "  clang headers  MISSING"
  ready=no
fi

echo

if [ "${1:-}" = "--install" ]; then
  if [ "$ready" = yes ]; then
    echo "Nothing to install."
    exit 0
  fi
  if ! command -v brew >/dev/null 2>&1; then
    echo "Homebrew not found.  Install LLVM by whatever means your platform"
    echo "prefers, then re-run this script; it only needs llvm-config on the"
    echo "PATH or in one of the usual prefixes."
    exit 1
  fi
  echo "Installing LLVM via Homebrew.  This is a large download and will take"
  echo "several minutes."
  echo
  brew install llvm
  echo
  if lc="$(find_llvm_config)"; then
    echo "Installed: $lc ($($lc --version))"
  else
    echo "Installed, but llvm-config is still not on the PATH.  Homebrew keeps"
    echo "LLVM keg-only; add its bin directory to your PATH, or pass"
    echo "LLVM_CONFIG=... to make."
  fi
  exit 0
fi

# ---------------------------------------------------------------------------
# Status and next steps
# ---------------------------------------------------------------------------

if [ "$ready" = yes ]; then
  echo "Ready to build a frontend."
else
  echo "Not ready to build a frontend.  Run:"
  echo
  echo "    ./setup-frontend.sh --install"
  echo
  echo "The checker does not need it.  'make check' builds and runs every"
  echo "suite with the system compiler."
fi

if [ "${1:-}" = "--status" ]; then
  echo
  echo "What the frontend has to do, and what is already done:"
  echo
  echo "  done   the path domain          path_domain.h     40 checks"
  echo "  done   types and environments   rcu_types.h       16 checks"
  echo "  done   the rules                rcu_rules.h       22 checks"
  echo "  done   statement IR and driver  rcu_check.h        6 checks"
  echo
  echo "  done   Clang AST -> Stmt IR     frontend.cpp, via Clang's CFG"
  echo "  done   CFG with dominators      back edges found by dominance and"
  echo "                                  closed by reindexing or widening"
  echo "  done   read __rcu on fields     both the attribute and the address"
  echo "                                  space spelling"
  echo "  done   diagnostic emission      named after the source, not internal ids"
  echo
  echo "  todo   function summaries       so a function can be checked without"
  echo "                                  --assume-entry, which is an assumption"
  echo "                                  and says so"
  echo "  todo   null refinement          if (p->f == NULL) records a null field"
  echo "                                  map entry, which T-UnlinkH needs"
  echo
  echo "No new annotation language is needed: rcu_dereference, rcu_assign_pointer,"
  echo "synchronize_rcu, kfree and __rcu already distinguish every action the"
  echo "type system has a rule for.  Only the root must be marked."
fi
