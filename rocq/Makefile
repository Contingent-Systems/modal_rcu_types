# The Iris development.
#
#   make          build
#   make clean
#
# Requires Rocq 9.0 (tested with 9.0+rc1).  Nothing here depends on Iris or
# stdpp yet -- WellFormed's invariants are pure propositions and HeapPaths is
# plain reachability theory.  Later milestones (ghost state, type denotations,
# atomic-action soundness) will add both, which are present in the `bluerock`
# opam switch.
#
# Milestones:
#   WellFormed.v  the seventeen global invariants, corrected; satisfiability;
#                 machine-checked proofs that five of the published ones are
#                 defective.
#   HeapPaths.v   reachability under a single field update, on the raw-heap
#                 encoding.  Infrastructure for the three heap-mutation rules.

ROCQ      ?= rocq
ROCQFLAGS := -R . RCU

VFILES  := WellFormed.v HeapPaths.v
VOFILES := $(VFILES:.v=.vo)

all: $(VOFILES)

HeapPaths.vo: WellFormed.vo

%.vo: %.v
	$(ROCQ) compile $(ROCQFLAGS) $<

clean:
	rm -f *.vo *.vok *.vos *.glob .*.aux

.PHONY: all clean
