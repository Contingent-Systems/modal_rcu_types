# Plan

Written 2026-09-21, against commit `2e8601e`.  State at that point: 257
assumption checks, axiom-free, clean from scratch; paper 140 pages; prototype 93
checks.  Nothing below blocks sending the response.

Effort figures are for one person working on this and nothing else.  "Risk"
means risk of leaving the tree broken or of discovering the plan is wrong
partway, not risk of the result being false.

---

## Part I — if a reviewer pushes

### R1. Axiom soundness for the rules that do not have it

**The real debt.**  Every action preserves `WellFormed` (fifteen theorems, plus
`reachable_WellFormed` over runs).  Axiom soundness asks for more: the
post-state must satisfy the denotation of the *post-type environment*.  Two
halves per rule — a pure one and a resource-level one — and the current position
is uneven rather than simply incomplete:

| | have | missing |
|---|---|---|
| preservation (`_preserves_WellFormed`) | 15 | — |
| pure environment (`_post_env`) | 9 | read_begin, read_end, sync_start, sync_stop, write_begin, write_end |
| typed rule (`_typed`, environment both sides) | 6 | bind, free, reader_acquire, and the six above |

So the work splits three ways, cheapest first.

**R1a — bind, free, reader_acquire (3 rules).  Done.**  `free_typed`,
`bind_typed` and `read_typed` all have an environment on both sides.

Two framing lemmas were missing and are new.  `EnvOK_free` is reclamation's: it
is the only action that makes the thread *give cells up*, so it is the only
place the cell map comes apart (`cells_split`, `cells_list`), and the fold that
reads a path has to survive deletion rather than overwriting
(`hstarC_stable_free`, the mirror of `hstarC_stable_cell` and the harder
direction, since a missing cell makes the fold fail rather than return
something else).  `AvoidsNode` is the environment condition it needs.
`EnvOK_obs_grow` is the binding rules': `EnvOK_obs` frames a write at a node the
environment does *not* read, and a bind writes at the node it does — but every
condition a type puts on an entry is a membership, so growth is free.
`EnvOK_scope` carries the rebound variable out of scope.

`free_atomic` was generalised from a singleton observation to any entry holding
\frbl{}, which is what the environment actually supplies.

`read_typed` is **not** a Hoare triple, for the reason recorded at R4: the edge
is a hypothesis because a reader cannot learn a cell's contents while the
points-to assertion is exclusive.  Everything else — the bounding obligation,
the observation grant, the environment on both sides — is discharged.  The
reader's environment condition is `REnvOK`, the hypothesis `reader_env` already
took, now named and carried across the read by `REnvOK_read`.

**R1b — read_begin, read_end (2 rules).  Done.**  `read_begin_typed`,
`read_end_typed` and, because the point of the pair is that they compose,
`read_section_typed`.

Both environments are fixed rather than derived — ToRCURead scopes the reader's
variables to the block, so the section starts with nothing and ends with
nothing — so what is worth proving is not that an environment survives but that
the two rules *fit*.  Entering, the reader gets a registration whose domain is
the domain of its (empty) observation map, which is exactly the shape
`read_typed` consumes; leaving, it hands back exactly the entries that domain
names, which is exactly what `read_end_atomic` takes.  `read_section_typed` is
the two composed, and it makes re-entry a matter of resources rather than of
argument: the postcondition of a section *is* its own precondition, which is
`reentry_safe` in `Epochs.v` one level down.

**R1c — sync_start, sync_stop (2 rules).  Done.**  `sync_start_typed` and
`sync_stop_typed`, with two framing lemmas.  The free list is read by exactly
one type, so a free list that keeps the entries it had carries any environment
the old one did (`EnvOK_fl`) — that is the whole of SyncStart's effect.
SyncStop goes the other way: the free list is untouched and the environment
changes, because every variable typed `unlinked` becomes `freeable`
(`syncenv`, `EnvOK_syncstop`) while every other type asks for an observation
`sync_obs` fixes.  The certificate the retyped variables need is the grace
period's own, so it is a hypothesis of the framing lemma rather than something
the environment carried.

**R1d — write_begin, write_end (2 rules).  Done.**  `write_begin_typed` and
`write_end_typed`.  The environment halves turned out to be the two smallest in
the file, and one of them is small *because of R4*: entering, the writer's only
type is `rcuRoot`, and `RootOK` is now a stack binding and nothing else — under
the old encoding it would have needed the entry at the root to hold `Oroot`,
which is precisely the entry WriteBegin's bulk update overwrites.  Leaving, the
post-environment is empty for the same reason ReadEnd's is, and that is now a
statement about resources because WriteEnd deletes rather than blanks.

**The enumeration premise is unavoidable, and is stated as such.**  All four of
SyncStart, SyncStop, WriteBegin and WriteEnd are bulk updates, and a bulk update
needs its set enumerated: "every detached node is stamped", "every entry of the
writer's is recoloured", "every reachable node is observed", "every entry is
given up".  No resource a thread holds discharges those, so these four are the
four without Hoare triples.  Where it could be stated as a fact about the
*thread's own* map rather than the shared one — SyncStop and WriteEnd — it is
(`forall o sg, Og !! (o, lw) = Some sg -> Ob !! o = Some sg`, the writer holds
its whole column), which is the honest form and what a writer that has tracked
its observations since WriteBegin actually has.

**Total, as spent** one session rather than 2.5 weeks, because R4 had already
done the two things that would have made R1a and R1d expensive: the root
observation stopped needing an entry, and ReadEnd/WriteEnd started deleting.

### R2. The step relation, written out

Pure transcription.  `Inductive lstep` with fifteen constructors, each carrying
exactly the hypotheses of the corresponding `_preserves_WellFormed` theorem;
`lstep_preserves_WellFormed` is then one case analysis with fifteen `exact`s.
Instantiate the existing `executions` section (`reachable_WellFormed`, `safety`)
at it, replacing `free_step` as the witness.

Then progress, which is cheap because the pieces exist: the six guards are
defined (`guard_ReadBegin` … `guard_WriteEnd`), two are discharged
(`read_begin_guard`, `read_end_guard`), one is trivial
(`write_end_unconditional`), and the remaining three are proved *not* to be
invariants (`writer_guards_are_not_invariants`).  What is left is stating
enabledness per constructor.

*Effort* 1 day for the relation, 1 more for progress.  *Risk* none.
*Acceptance* `safety` stated at the full relation.

### R3. Fairness

**No work, and that is the answer.**  `wait_shrinks`, `wait_terminates` and
`wait_then_free` reduce the grace period's termination to fairness and no
further, and fairness is a property of the client — no invariant of the shared
state could supply it.  The paper says this in "What is left, and it is four
things."

If a reviewer wants it made syntactically visible, the optional move is to add
fairness as an explicit hypothesis of a liveness statement over `reachable`
(half a day).  It proves nothing new; it only puts the assumption in a theorem
statement instead of a paragraph.  Do it only if asked.

### R4. The root observation — **done**

*Option (a), derive `Oroot` from the structure*, is what the development now
does.  `to_LState_t`'s `obsv` branches on the observation: at `Oroot` it is
`o = rt m`, and at every tagged observation it is the entry lookup it was
before, which is why the change cost the proofs about tagged observations
nothing.  `ObsWF` is thread-tagged only.

What landed, against the six tasks as written:

1. Done, in the branching form rather than the disjunctive one.
2. Done.  `root_has_no_owner` in `Actions.v` is the old counterexample state,
   now rejected by the encoding: one of the twenty defects turned into a
   non-issue rather than a repair, and it is the only one that went that way.
3. Done.  RTO is definitional; `Denotations.v`'s root conjunct is `reflexivity`.
4. Done, and it turned out to be required rather than optional.  `tobs_del`,
   `tobs_del_list` and `del_list` were added; ReadEnd and WriteEnd delete their
   keys.  Blanking them is not enough: a blank key belongs to no running
   thread, and then the reader's read cannot tell an absent entry from a blank
   one.
5. Done, and it needed one more conjunct than the plan expected.  The domain
   clause is now about *entries* (`Og !! (o,t) = Some sg -> o ∈ D`), and a new
   conjunct says no key is left behind empty.  Together they make ReadBegin's
   empty domain provable, which is what the strengthening needed.
6. Partly.  `read_update` is the reader's read as a step on the invariant's
   contents, and everything observational in it is discharged: the bounding
   obligation from FLR, IFL and SameSnap (`read_bound`, with `HSS_SameSnap`
   supplying SameSnap from the epoch layer), and the entry it must create from
   the registration cell.  It is **not** a closed Hoare triple, and the reason
   is not the one R4 was about: a reader must learn what a field holds, and
   `pt` is exclusive.  That is the fractional or snapshot heap, and it is R1's
   business, not this item's.

*Acceptance, as met* RTO by computation; the "ten closed triples" claim stands
(ReadBegin and ReadEnd, not the read); `read_update` closed at the update
level.  *Not met* `read_atomic` as a triple — blocked on a fractional heap.

---

## Part II — after, in this order

### A1. The single refinement obligation

**The one that changes what the paper can claim.**  Today: the type system is
sound against *one* abstract model, and that the model is a valid RCU
implementation is argued against Alglave et al.'s requirements — two as theorems
now, one as the guards, one excluded.  To claim client safety on a *real*
implementation you need that implementation to refine the model.  Proved once,
parameterised, that is one theorem; proved per implementation it is one per
implementation, forever.

Tasks:

1. Formalise the four requirements as a record `Conforms (I : Impl)`, reusing
   the statements already proved on our side —
   `no_section_spans_a_grace_period`, `readers_cannot_see_unpublished`, the six
   `guard_*` definitions.
2. State the simulation: every run of a conforming `I` is matched by a run of
   `lstep` (R2's relation), under a relation from `I`'s states to `LState`.
3. Prove the reclamation clause, which is the only hard one: `I`'s free must
   land where our `Free` lands, and requirement 1 is what makes it.
4. Sanity-check by instantiating at the epoch model.  **`Epochs.v` already is an
   implementation shape**, and `Sim` with `sim_read_begin` / `sim_read_end` /
   `sim_sync_start` / `sim_sync_stop` is exactly the four step obligations
   written out once.  Use it as the template and as the first instance.

*Effort* 3–4 weeks.  *Risk* high — this is research, and the shape of the
simulation may need rethinking once (2) is attempted.  *Mitigation* do (4)
first, as a rehearsal: if the epoch model does not slot in, the interface in (1)
is wrong and you have lost days rather than weeks.

**Status: the rehearsal is done and the interface survived it.**  `rocq/Refine.v`
has the `Impl` record, the relation `ISim` (which is `Epochs.v`'s `Sim` with the
epoch state made abstract), and the obligation `Refines` as five clauses — one
per protocol action, plus one saying the implementation's grace-period guard
decides the model's.  `EpochImpl` is the first instance and `epochs_refine`
assembles it from the five theorems `Epochs.v` already had, for a different
purpose.  It slotted in unchanged, which is the signal the mitigation was
looking for.

Two things were added beyond the four tasks.  `refines_run` lifts the obligation
from one step to a run (`rtc` of the paired step), which is what a claim about a
client actually needs.  And `eager_is_not_a_refinement` shows the fifth clause
is load-bearing rather than decorative: the epoch model with its guard replaced
by "always" satisfies all four *step* clauses — they are literally the same
theorems — and fails only the guard, because the model's SyncStop does not
itself check anything; the checking is in when it is allowed to run.  So the
obligation is not four equations with a condition attached for tidiness: the
condition is the safety property.

**Task 3 and the bridge are done too, so A1 is complete as scoped.**

*Task 3, the reclamation clause.*  Two clauses, and only one has content.
`ref_free` is bookkeeping — freeing removes the free-list entry, which is what
the published `Free` does.  `ref_free_quiesced` is Alglave's first requirement
stated where it bites: an implementation may free a node only when the node's
entry is empty.  Nothing constrains *how* the implementation decides that — the
epoch model compares counters, something else may count quiescent states — only
*when* the answer may be yes.  `refines_free_is_freeable` reads it back: when a
conforming implementation decides it may reclaim, the model agrees the node is
`freeable`, which is exactly the conjunct the `freeable` denotation asks for.

A fifth clause came out of the bridge and belongs with it: `ref_snapshot`, that
the grace period waits for exactly the threads now reading.  `ref_guard` says
when the wait may *end*; this says what it was waiting *for*, and the two
together are the whole of requirement 1 at this interface.

*The bridge.*  `Conf`, `xstep`, and three theorems.  `xstep` carries exactly the
hypotheses of the corresponding `lstep` constructor plus the implementation's
guard — nothing assumed twice, nothing smuggled — and the two halves come from
different places: the implementation supplies the protocol half, the typing
derivation supplies the observation half.  `xstep_ok` is the implementation
half, `xstep_lstep` the type-system half, `xrun_WellFormed` the two over a run,
and `xrun_safe` the payoff: a run of a conforming implementation reaches only
states in which a `freeable` node has no live reference.  `epoch_run_safe` is
that at `EpochImpl`, so the chain is visible end to end.

**What A1 does not cover, stated rather than implied.**  `xstep` has the five
protocol actions and not the ten heap ones, because the heap actions do not
involve the implementation at all — they are the writer's, they touch the heap
and the observation map and never the free list or the reader set, and `lstep`
already has them.  Interleaving the two relations is taking their union; we have
not checked that composition, so we do not state it.

### A2. Hazard pointers

**The cheapest way to find out how RCU-specific this is.**  `Oiter t` —
"thread *t* has announced it may access *o*" — is a hazard pointer.  The
hypothesis is that the observation structure and the invariants about
announcements-versus-reclamation carry over, and only the *reclamation guard*
changes: from "a grace period has elapsed" to "no thread's announced set
contains this node".

There is a strong prior that this works, and it is worth stating because it
makes the experiment cheap to evaluate: `freeable_is_unobserved` and
`no_live_reference_to_a_freeable_node` — the whole memory-safety argument — use
**IFL and RWOW and nothing else**, and neither mentions a grace period.

Tasks:

1. Partition the twenty invariants into those that mention the grace period
   (the free list, the bounding set, the epochs) and those that do not.  The
   second group is the claim.
2. Define an HP reclamation guard and an HP `freeable` denotation.
3. Re-prove `freeable_is_unobserved` and `no_live_reference_to_a_freeable_node`
   against it.  If they go through unchanged, the safety argument is
   reclamation-agnostic and the paper's scope grows a great deal.
4. If they do not, the failure names exactly what is RCU-specific — which is a
   result, not a setback, and should be written up as one.

*Effort* 1–2 weeks to a decisive answer either way.  *Risk* low, because both
outcomes are publishable content.

**Answered, and it is the good outcome.**  `rocq/Reclaim.v`.

*Task 1, the partition, done mechanically rather than by reading.*  Change the
free list to *anything* and see which invariants survive: twenty-one of the
twenty-six conjuncts do, and the proof of `free_list_is_local` is twenty-one
`exact`s — they are not *preserved*, they are *unchanged*, because the free list
does not occur in them.  The five that do not survive are exactly IFL, FLR,
RINFL, FLD and SameSnap, and `free_list_is_not_local` gives one witness state
that breaks all five at once.

*Tasks 2 and 3.*  The discipline is a record with two components — `d_ann`
("thread `t` is recorded as a potential accessor of `o`") and `d_free` ("`o` may
be reclaimed") — and two conditions: `Announced`, that an observation is
recorded, and `Retires`, that the guard means nothing is recorded.
`reclaim_unobserved` and `reclaim_no_live_reference` are the two safety theorems
against that interface, and they are *the same proofs* with every mention of a
free list gone.

`RCU` is one instance: `Announced` at it is IFL (`rcu_Announced`, an iff), and
`Retires` needs nothing, the free list being a function.  `rcu_no_live_reference`
recovers the original theorem, which is the check that the abstraction did not
weaken anything.  `HP` is the other: announcement is set membership, so `Retires`
holds by construction, and `Publishes` — what a thread observes it has published
— is IFL's exact analogue with the indices swapped: IFL puts the *thread* in the
node's entry, `Publishes` puts the *node* in the thread's set.

*Task 4 does not arise*, but two cautions are recorded in the file rather than
left implicit.  This is the *safety* argument, not the whole system: the five
free-list invariants do real work elsewhere (FLR and SameSnap discharge the
reader's read, FLD is SyncStart's, RINFL ties entries to the bounding set), and a
hazard-pointer system would need analogues or would do without the rules that use
them.  And what carries over is the argument, not the implementation: hazard
pointers must publish before dereferencing and re-validate after, which is a
memory-ordering obligation this development does not model.  `Publishes` is
stated as an invariant of the logical state and is therefore exactly the thing
A3 would have to earn.

### A3. Weak memory

Tassarotti et al. verify under release-acquire; we are sequentially consistent.
The piece their proof turns on is per-thread counters, and those are now in the
model (`Epochs.v`), which is the reason to think this is approachable at all.

Tasks: identify which invariants are stable under a weak reading — observations
are already per-thread, which is the right shape; identify the synchronisation
points, which are SyncStart's snapshot and ReadEnd's registration clear, and
which are the release/acquire pairs; restate `Sim` against a weak-memory
operational model.

*Effort* a paper.  **Not before this one is out.**

---

## Sequencing

*As planned:* ship first, then R2, then R4 on a branch, then R1a–R1d as a block,
then A1 rehearsing at the epoch model first; A2 in parallel if there are two
people, since it shares no files.

*As it went:* R2, R4, R1a–R1d, A1, A2 — all of Part I and the first two of Part
II, in that order.  Two things about the order are worth recording.

R4 first was right, and for a reason the plan only half anticipated.  It was
sequenced early because it closed the reader's read; what it also did was make
R1a and R1d cheap.  `RootOK` stopped needing an observation, which is why
WriteBegin's environment half is one lookup; and ReadEnd/WriteEnd started
deleting rather than blanking, which is why WriteEnd's empty post-environment is
a statement about resources rather than a convention.  R1 was budgeted at 2.5
weeks and did not take it, and that is where the difference went.

A1's mitigation earned its keep.  The interface was read off `Epochs.v`'s
existing proof rather than designed, and the five theorems that file already had
slotted in unchanged — which is what said the record was the right shape before
any time was spent on the bridge.

**A3 is the only item left, and it is deliberately not started.**

## Do not

- Do not start R1d (write_begin/write_end) before the rest of R1.
- Do not attempt option (b) of R4.
- Do not start A3 before the paper is out.
- Do not add `Print Assumptions` inside a `Section`; `make check` now rejects it,
  and the reason is in the appendix.
