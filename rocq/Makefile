# The Iris development.
#
#   make          build
#   make clean
#
# Requires Rocq 9.0 or later (tested with 9.0+rc1 and 9.2).  The first two
# milestones are Iris-free -- WellFormed's invariants are pure propositions and
# HeapPaths is plain reachability theory -- so they build against Stdlib alone.
# IrisGhost needs Iris and stdpp, which are present in the `bluerock` opam
# switch under lib/coq/user-contrib and are found without extra -R flags.
#
# Milestones:
#   WellFormed.v  the seventeen global invariants, corrected; satisfiability;
#                 machine-checked proofs that five of the published ones are
#                 defective, and that T-Replace/T-UnlinkH needed a further
#                 premise.
#   HeapPaths.v   reachability under a single field update, on the raw-heap
#                 encoding, plus heap-domain closure.  Infrastructure for the
#                 three heap-mutation rules.
#   IrisGhost.v   the observation map and free list as Iris ghost state, and
#                 the invariant tying them to the pure layer.
#   Denotations.v the type denotations, and the proofs that they supply the
#                 hypotheses HeapPaths takes for T-Replace and T-Insert.
#   Actions.v     joins the ghost updates to the pure state: to_LState
#                 commutes with a field write and with an observation update.

ROCQ      ?= rocq
ROCQFLAGS := -R . RCU

VFILES  := WellFormed.v HeapPaths.v IrisGhost.v Denotations.v Actions.v
VOFILES := $(VFILES:.v=.vo)

all: $(VOFILES)

HeapPaths.vo: WellFormed.vo
IrisGhost.vo: WellFormed.vo
Denotations.vo: WellFormed.vo HeapPaths.vo
Actions.vo: WellFormed.vo HeapPaths.vo IrisGhost.vo Denotations.vo

%.vo: %.v
	$(ROCQ) compile $(ROCQFLAGS) $<

clean:
	rm -f *.vo *.vok *.vos *.glob .*.aux

.PHONY: all clean
