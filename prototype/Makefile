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

check: $(TESTS)
	@fail=0; \
	for t in $(TESTS); do \
	  echo "== $$t"; \
	  ./$$t || fail=1; \
	  echo; \
	done; \
	if [ $$fail -ne 0 ]; then echo "FAILED"; exit 1; fi; \
	echo "all suites passed"

# The frontend is built only when LLVM is present.  setup-frontend.sh reports
# what is missing and can install it.
LLVM_CONFIG ?= $(shell ./setup-frontend.sh --llvm-config 2>/dev/null)

frontend:
	@if [ -z "$(LLVM_CONFIG)" ]; then \
	  echo "no llvm-config found; run ./setup-frontend.sh for what is needed"; \
	  exit 1; \
	fi; \
	echo "llvm-config: $(LLVM_CONFIG)"; \
	echo "frontend sources are not written yet -- see setup-frontend.sh --status"

clean:
	rm -f $(TESTS)

.PHONY: all check frontend clean
