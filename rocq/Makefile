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
#                 machine-checked proofs that seven of the published ones are
#                 defective, and that T-Replace/T-UnlinkH needed a further
#                 premise.
#   HeapPaths.v   reachability under a single field update, on the raw-heap
#                 encoding, plus heap-domain closure and what each rule makes
#                 unreachable.  Infrastructure for the three heap-mutation
#                 rules.
#   IrisGhost.v   the observation map and free list as Iris ghost state, and
#                 the invariant tying them to the pure layer.
#   Denotations.v the type denotations, and the proofs that they supply the
#                 hypotheses HeapPaths takes for T-Replace and T-Insert.
#   Actions.v     joins the ghost updates to the pure state: to_LState
#                 commutes with a field write and with an observation update;
#                 then the per-invariant obligations for each atomic action,
#                 and WellFormed preservation for Free, SyncStop and ReadEnd
#                 as whole actions.

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

# A successful build proves less here than it looks.  `Admitted.` compiles and
# writes a .vo like any other proof, and `Print Assumptions` reports an axiom on
# stdout without failing anything.  So the development's actual claim -- 84
# results, every one closed under the global context, no axioms -- is precisely
# the thing that building it does not check.  This target checks it.
#
# It also checks that VFILES and _CoqProject still agree with the .v files on
# disk, since both lists are maintained by hand and a file missing from VFILES
# is a file that silently is not built.
CHECKLOG := check.log

check:
	@bad=$$(grep -nE 'Admitted\.|(^|[^A-Za-z_])admit\.|^Axiom |^Parameter |^Hypothesis ' $(VFILES) || true); \
	 if [ -n "$$bad" ]; then \
	   echo "$$bad"; echo "FAILED: the development contains none of these by design"; exit 1; \
	 fi
	@for v in $(wildcard *.v); do \
	   case " $(VFILES) " in *" $$v "*) ;; \
	     *) echo "FAILED: $$v is not in VFILES, so it is never built"; exit 1;; esac; \
	   grep -q "^$$v$$" _CoqProject || { echo "FAILED: $$v is not in _CoqProject"; exit 1; }; \
	 done
	@rm -f $(VOFILES)
	@$(MAKE) --no-print-directory all > $(CHECKLOG) 2>&1 || { cat $(CHECKLOG); exit 1; }
	@cmds=$$(grep -hc '^Print Assumptions ' $(VFILES) | paste -sd+ - | bc); \
	 closed=$$(grep -c 'Closed under the global context' $(CHECKLOG) || true); \
	 axioms=$$(grep -c '^Axioms:' $(CHECKLOG) || true); \
	 echo "Print Assumptions commands   $$cmds"; \
	 echo "closed under global context  $$closed"; \
	 echo "reporting axioms             $$axioms"; \
	 if [ "$$axioms" -ne 0 ] || [ "$$cmds" -ne "$$closed" ]; then \
	   echo; echo "FAILED"; exit 1; \
	 fi; \
	 echo; echo "all $$closed assumption checks closed, no axioms"

# Rebuild everything if the flags or the file list change, rather than leaving
# .vo files built under the old ones.
$(VOFILES): Makefile _CoqProject

clean:
	rm -f *.vo *.vok *.vos *.glob .*.aux $(CHECKLOG)
	rm -rf .coq-native

.PHONY: all check clean
