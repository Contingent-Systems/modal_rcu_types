# The RCU checker prototype.
#
#   make            build the test suites
#   make check      build and run them
#   make frontend   build the Clang frontend (needs LLVM; see setup-frontend.sh)
#   make clean
#
# Everything except `frontend` is dependency-free C++17 and builds with the
# system compiler.  That is deliberate: the checker is developed and tested
# without a compiler in the loop, and the frontend is a translation into the
# statement IR of rcu_check.h rather than a rewrite.

CXX      ?= c++
CXXFLAGS ?= -std=c++17 -O2 -Wall -Wextra

HEADERS := path_domain.h rcu_types.h rcu_rules.h rcu_check.h

# Layered lowest first, so a failure names the layer that broke.
TESTS := path_domain_test rcu_types_test rcu_rules_test rcu_check_test

all: $(TESTS)

$(TESTS): %: %.cpp $(HEADERS)
	$(CXX) $(CXXFLAGS) -o $@ $<

# frontend.cpp is not one of the suites, but it includes the same headers, so a
# change to one can break it while every suite still passes.  Compile it here
# too when LLVM is present, and say when it is skipped rather than passing
# quietly -- an unchecked file is how a build lies about what works.
check: $(TESTS)
	@fail=0; \
	for t in $(TESTS); do \
	  echo "== $$t"; \
	  ./$$t || fail=1; \
	  echo; \
	done; \
	echo "== frontend.cpp"; \
	if [ -z "$(LLVM_CONFIG)" ]; then \
	  echo "  skipped: no llvm-config (see ./setup-frontend.sh)"; \
	elif $(CXX) $(CXXFLAGS) -fsyntax-only -fno-rtti -I. \
	     $$($(LLVM_CONFIG) --cxxflags | sed -E 's/(^| )-I/\1-isystem /g') \
	     frontend.cpp; then \
	  echo "  compiles against the current headers"; \
	else \
	  fail=1; \
	fi; \
	echo; \
	if [ $$fail -ne 0 ]; then echo "FAILED"; exit 1; fi; \
	echo "all suites passed"

# The frontend is built only when LLVM is present.  setup-frontend.sh reports
# what is missing and can install it.  Simply expanded, and guarded on origin so
# an override from the environment or command line still wins: with `?=` this is
# a deferred $(shell ...), which re-runs the script at every one of the five
# references below.
ifeq ($(origin LLVM_CONFIG),undefined)
LLVM_CONFIG := $(shell ./setup-frontend.sh --llvm-config 2>/dev/null)
endif

frontend: rcu-check

rcu-check: frontend.cpp $(HEADERS)
	@if [ -z "$(LLVM_CONFIG)" ]; then \
	  echo "no llvm-config found; run ./setup-frontend.sh for what is needed"; \
	  exit 1; \
	fi
	$(CXX) $(CXXFLAGS) -fno-rtti -I. \
	  $$($(LLVM_CONFIG) --cxxflags | sed -E 's/(^| )-I/\1-isystem /g') \
	  -o $@ frontend.cpp \
	  $$($(LLVM_CONFIG) --ldflags) \
	  -lclang-cpp $$($(LLVM_CONFIG) --libs) $$($(LLVM_CONFIG) --system-libs)

clean:
	rm -f $(TESTS) rcu-check

.PHONY: all check frontend clean
