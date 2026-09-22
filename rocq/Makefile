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
#   WellFormed.v  the nineteen global invariants, corrected; satisfiability;
#                 machine-checked proofs that seven of the published ones are
#                 defective, that T-Replace/T-UnlinkH needed a further
#                 premise, that nothing in the nineteen says where free-list
#                 entries may live, and that neither the root observation nor a
#                 fresh one is tied to the thread that should hold it.
#   HeapPaths.v   reachability under a single field update, on the raw-heap
#                 encoding, plus heap-domain closure and what each rule makes
#                 unreachable.  Infrastructure for the three heap-mutation
#                 rules.  Allocation takes the node's field list, which is the
#                 repair Triples.v forced: without it the heap is infinite.
#   IrisGhost.v   the observation map and free list as Iris ghost state, and
#                 the invariant tying them to the pure layer.
#   Denotations.v the type denotations, and the proofs that they supply the
#                 hypotheses HeapPaths takes for T-Replace and T-Insert.
#   Compose.v     the separation algebra on logical states: a counterexample to
#                 the claim that WellFormed is closed under the published
#                 operation -- the framing property the Views framework
#                 requires -- and a repaired operation under which it is,
#                 with a check that the repair is not vacuous.
#   Triples.v     the heap moved into the Iris invariant, and every atomic
#                 action restated against it -- the experiment that says
#                 whether the action lemmas survive the architecture that
#                 framing needs.  Free first, then T-UnlinkH, which is the
#                 case that exercises the per-thread observation ghost state;
#                 then the bulk updates -- a map-wide write is an iterated
#                 single-key one, legal because the thread owns every fragment
#                 it touches -- and the five actions that need them.  Then the
#                 physical state: a proof that the original allocation makes
#                 the heap infinite and so admits no points-to assertion, the
#                 finite heap the field list gives, its camera, the path
#                 assertion, the type environment as a resource, the
#                 allocator -- a finite state has a computable fresh location,
#                 so allocation needs no operational semantics -- and eight
#                 closed triples covering the whole write side, in which every
#                 premise is carried by a resource the thread holds or derived
#                 from the invariant it opens -- and then the type environment
#                 as a resource: own the thread's maps once and read each
#                 variable's type as a condition on them, which needs no
#                 fractional permissions on the write side -- and then every
#                 heap mutation and the allocation stated with a type
#                 environment on both sides, the untouched variables framed
#                 and the touched ones supplied.
#   Epochs.v               the epoch-based reading of the reclamation bookkeeping:
#                          what registering with a counter buys, and why the
#                          counter is incremented
#   LinkedList.v           the linked-list delete, the paper's other example
#   BST.v                  the write side of the paper's binary search tree delete, run
#                 through those rules as a chain over a concrete tree.  The
#                 point is not the example: it is that chaining is what finds
#                 interface defects, and it found one in the allocation rule.
#   Actions.v     joins the ghost updates to the pure state: to_LState
#                 commutes with a field write and with an observation update;
#                 then the per-invariant obligations for each atomic action,
#                 and WellFormed preservation for every atomic action of
#                 the system, as fifteen theorems.

ROCQ      ?= rocq
ROCQFLAGS := -R . RCU

VFILES  := WellFormed.v HeapPaths.v IrisGhost.v Denotations.v Actions.v \
           Compose.v Epochs.v Refine.v Reclaim.v Weak.v Triples.v BST.v LinkedList.v
VOFILES := $(VFILES:.v=.vo)

all: $(VOFILES)

HeapPaths.vo: WellFormed.vo
IrisGhost.vo: WellFormed.vo
Denotations.vo: WellFormed.vo HeapPaths.vo
Actions.vo: WellFormed.vo HeapPaths.vo IrisGhost.vo Denotations.vo
Compose.vo: WellFormed.vo
Triples.vo: WellFormed.vo HeapPaths.vo IrisGhost.vo Denotations.vo Actions.vo \
            Epochs.vo
Epochs.vo: WellFormed.vo HeapPaths.vo IrisGhost.vo Denotations.vo Actions.vo
Refine.vo: WellFormed.vo HeapPaths.vo IrisGhost.vo Denotations.vo Actions.vo \
           Epochs.vo
Reclaim.vo: WellFormed.vo HeapPaths.vo Denotations.vo
Weak.vo: WellFormed.vo HeapPaths.vo IrisGhost.vo Denotations.vo \
         Actions.vo Epochs.vo
LinkedList.vo: WellFormed.vo HeapPaths.vo IrisGhost.vo Denotations.vo \
                Actions.vo Triples.vo
BST.vo: WellFormed.vo HeapPaths.vo IrisGhost.vo Denotations.vo Actions.vo \
        Triples.vo

%.vo: %.v
	$(ROCQ) compile $(ROCQFLAGS) $<

# A successful build proves less here than it looks.  `Admitted.` compiles and
# writes a .vo like any other proof, and `Print Assumptions` reports an axiom on
# stdout without failing anything.  So the development's actual claim -- 307
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
	@indented=$$(grep -nE '^[[:space:]]+Print Assumptions ' $(VFILES) || true); \
	 if [ -n "$$indented" ]; then \
	   echo "$$indented"; \
	   echo "FAILED: Print Assumptions inside a section prints nothing, so these check nothing"; \
	   exit 1; \
	 fi
	@bad=$$(grep -nE 'Admitted\.' $(VFILES) || true); \
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
