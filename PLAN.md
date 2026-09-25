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

**The composition is done too.**  `xstep`'s `X_heap` admits any `lstep`
on the condition that it leaves `rds` and `bnd` alone, and
`heap_actions_are_quiet` discharges that for all ten heap actions by
reflexivity — the machine-state transformers are written to carry both through
unchanged.  So `xstep` is the union of the two relations, a run may interleave
the writer's mutations with the protocol freely, and `xrun_safe` is about whole
programs rather than the protocol in isolation.

**What A1 still does not claim.**  That these are the only steps, or that a
scheduler exists producing any particular interleaving.  The relation says what
may happen, not what does; progress and fairness are untouched by it.

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

*Effort* a paper.

**Task 1 is done, and it changed the guess in task 2.**  `rocq/Weak.v`.  Under
release-acquire a thread's view is a *sub-heap* of what has been written, so the
question an invariant faces is exactly "does it still hold when the heap
shrinks?"  Asked mechanically: sixteen of the twenty-six conjuncts do not
mention the heap at all and survive any change to it, proof `exact` each; nine
mention it only to rule something out and survive shrinking; and exactly one
does not.

That one is **HD**, heap-domain closure — and read as an obligation, what it
asks is that a thread which can see an edge can see the node at the end of it.
That is publish-subscribe: Alglave's second requirement, and the release-acquire
pair Tassarotti names first.  `publication_is_the_obligation` is the witness,
and it is the publication race written down: the writer initialises then links,
the reader acquires the link without the initialisation.

So the guess in task 2 was incomplete.  The synchronisation points are not only
the protocol's two; the type system needs a third, at the **link**, which is
where a writer publishes.  Our SC model gets that for free and a weak one does
not.

Also worth having before the rest starts: the memory-safety argument is
untouched by any of this.  It uses IFL and RWOW, both heap-free, and
`readers_cannot_see_unpublished` uses FNR and FRW — one heap-free, one that
survives shrinking.  None of the three has anything to say about views.

**Task 2 is done, and it is one theorem.**  `WState` is a base state plus a view
per thread; `w_ok` says each view is a sub-heap of the base; `Published` says
every thread that can reach a node can see it.  Then
`views_are_well_formed`: nineteen of `WellFormed`'s twenty conjuncts transfer
from the union to every view with *no hypothesis at all*, and the twentieth is
`Published`.  So a weak account does not re-prove the invariants per thread — it
establishes one property at the link.  Nothing the reader does needs
synchronisation, and neither does reclamation, since the memory-safety argument
never looks at a heap.

**Task 3 is done, and it turned up the useful asymmetry.**  The heap is not the
only shared state: the registrations are too, and `Sim` relates them to the
reader set.  For the heap, a thread seeing *less* is safe — twenty-five of
twenty-six conjuncts survive shrinking.  For the registrations it is exactly
reversed: `stale_registrations_are_unsafe` gives a writer whose view of `ereg`
is a sub-map of the truth, which concludes a grace period has ended when it has
not, takes the certificate, and frees a node whose snapshot still contains the
reader.  Seeing less is the hazard.

So the two kinds of shared state need synchronisation for opposite reasons, and
that is why they need it in different places: the heap at the write that
publishes, the registrations at the read that decides the wait is over.  `Sim`'s
first clause is an *iff*, and a sub-map view gives one direction and loses the
one the wait depends on — so the weak-memory refinement obligation is not a
weakened form of the SC one, it is the same obligation with the reads that
establish it required to be acquires.

That lands the three synchronisation points exactly where Tassarotti et al. put
them, which is the check on the whole section: the link is their
Release-Acquire-1, the registration write and the scan that reads it are their
-2 and -3.  We arrive at the same three from the invariants rather than from the
algorithm.

**The model is now written too.**  `rastep` is release-acquire in its view
form: a history per cell, a view as a timestamp per cell, and three steps — a
write that may or may not release (`rcu_assign_pointer` is the one that does, a
field initialisation the one that does not) and a read that acquires
(`rcu_dereference`).  Nothing about views is assumed any more: `ra_ok` and
`RAClosed` hold at the initial configuration and are preserved by every step
(`rastep_ok`, `rastep_closed`).

One modelling point was worth getting right rather than nearly right: the
released view belongs to the **message**, not to the location.  Attaching it to
the location is the obvious simplification and it is wrong — publishing a
location twice would retroactively change what an earlier reader is obliged to
have acquired, and `rastep_closed` would not hold.

What comes out: `ra_publication`, that a reader is at least as far along as the
publisher of anything it can see; `ra_reader_sees`, the same as the guarantee a
reader wants, with the two programmer's obligations named
(initialise-before-publish, and don't rewrite afterwards — both of which the
`rcuFresh` discipline enforces); and `release_is_necessary`, the same run twice
differing in one bit, where the relaxed version is a perfectly good run of the
semantics in which the reader sees the link and the node's field as it was
before initialisation.

And the bridge: `weak_run_is_sound`.  A run of the semantics under the
discipline reaches a configuration in which **every thread's own view satisfies
every invariant**, given that the SC state whose heap is what has been written
does.  Nineteen conjuncts come free from task 1's partition; the twentieth is
publication, and `publication_holds` gets it from the semantics.

**What is still not proved**, stated in the file rather than left as "future
work":

- ~~`weak_run_is_sound` is restricted to write-once cells.~~ **Lifted.**  See
  below.
- ~~The semantics is over the heap only.~~ **Done.**  See below.
- It is release-acquire and not weaker.  Every read acquires and every view
  only grows, so there is nothing out of thin air to rule out, and none of it
  would survive a relaxed model unchanged.  This one stands.

### The three items, worked

**(4) The registrations, done — and the guess was wrong in a useful way.**
A registration is a cell, so the three steps already carry it.  What the
section settles is which half does the work, and it is not the half the plan
guessed.  A *stale generation* read by a reader is safe: it registers at an
earlier generation, so it looks older than it is and a grace period that need
not have waited for it waits anyway (`stale_generation_is_conservative`).  A
*stale registration* read by the writer is the hazard, and
`stale_scan_misses_the_reader` is that run.  But reads only move forward
(`reads_only_move_forward` — coherence is built into the read step), so a
scan that keeps reading advances monotonically, and all it needs is to reach
the last message.  **That is the same fairness assumption the SC development
already reduces the wait's termination to.**  So weak memory adds no new
obligation to the grace period: the assumption that makes SyncStop terminate
makes it sound.

**(3) Reclamation, done — and it is the one place the memory model is not the
answer.**  A view holds only what was written; a thread that has caught up past
the unlink cannot see the old link; so reclamation is safe exactly when every
thread has caught up past every unlink of the node
(`reclamation_safe_when_caught_up`).  And the witness at the end,
`the_grace_period_is_what_makes_this_safe`, is a reader holding a reference to
a node nothing reachable points at any more — with *both* writes releasing,
the strongest thing the model has.  No amount of synchronisation helps; only
not reclaiming does.  That is the division of labour the whole development is
about, in one run.

**(2) The write-once restriction — lifted, not worked around.**  We set out to
show the restriction was necessary by building a reader whose view was never
the heap.  Every attempt failed at the same step: the acquire pulled the reader
forward *everywhere*, not just at the cell it read.  The theorem is why.  Under
RCU's actual discipline — one writer, every write releasing, readers that only
read — a releasing write publishes the writer's whole knowledge, and with a
single writer those publications are totally ordered, so
`reader_views_are_past_writer_views`: **every reader's view is one of the
writer's past views.**  A reader is therefore always looking at a heap the
writer really had, and `weak_run_is_sound_under_the_discipline` needs nothing
about which cells are written twice.  It assumes only that the states the
writer passed through are well formed, which is what the SC development proves.

The restriction was an artefact of proving the wrong thing.  Two writers and
the publications stop being a chain; a relaxed write and the reader acquires
nothing — and both are outside what ToRCUWrite permits, which is to say the
type system is what enforces this theorem's hypothesis.

The claim is narrower than "RCU is verified under weak memory" and more useful:
the single invariant a weak memory model endangers is publication, publication
is what the releasing write buys, and the buying is written down.

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

**A3's release-acquire account is done.  The gaps it leaves are Part III.**

---

## Part III — the gaps, listed

Seven items.  W1–W3 are the memory model being made faithful to Linux and are
the subject of this pass.  W4 is the replacement for what W1 destroys.  W5 is
the prerequisite everything else has been borrowing against.  W6 is the
external claim.  W7 cannot be fixed and must be said.

### W1. `rcu_dereference` as it actually is

**The model is stronger than Linux and that is a defect, not a simplification.**
`RA_read` unconditionally unions in the message's release view: every read
acquires, and there is no relaxed load in the model at all.  Linux is not that.
`rcu_assign_pointer` *is* a release store — that half matches — but
`rcu_dereference` is `READ_ONCE` plus a compiler barrier, and the ordering
comes from the **address dependency** between loading the pointer and loading
through it.  An acquire orders the load against everything the publisher knew;
a dependency orders it only against accesses that use the value.

Tasks: a second step relation with three steps — the same releasing write, a
relaxed read (`READ_ONCE`), and a dependency-ordered read (`rcu_dereference`)
which acquires *only at the target's own cells*.  Keep the release-acquire
relation beside it: having both is what lets the difference be stated.

*Risk* low.  *Acceptance* the publication guarantee still holds.

**Done.**  `kstep` with `K_write`, `K_rlx` and `K_dep`; `at_node` is acquire
restricted to the target's own cells.  `kstep_ok` holds.  The relaxed read is
of a non-pointer, which is the discipline rather than a limitation: reading a
pointer without `rcu_dereference` is the bug `rcu_dereference` exists to
prevent.  The release-acquire relation is kept beside it.

### W2. What the weaker read costs, exhibited

`reader_views_are_past_writer_views` is available only because reads acquire.
Under dependency ordering it should be false, and the counterexample we could
not build under release-acquire should build immediately.

Tasks: run it.  If the view is now a genuine mixture that was never the heap,
that is the decisive statement of what acquire was buying, and it says the
whole-state bridge has to be replaced rather than repaired.

*Risk* low — both outcomes are informative.  *Acceptance* a run whose reader's
view violates an invariant the heap satisfies throughout.

**Done, and it builds immediately.**
`dependency_ordering_loses_the_whole_view`: the writer points the root's second
field at 5, then at 6, then the first field at 5, so unique-paths holds at
every moment.  A reader that dereferences the second field while it still
reads 5, then dereferences the first, is carried forward only at node 5's
cells — not at the root's — so it keeps the stale field.  Its view has both
fields at 5, which no state ever had, and in it 5 has two paths.  That is the
exact statement of what acquire was buying.

### W3. The publication guarantee under dependency ordering

The one invariant a weak model endangers is **HD**, and HD says exactly that a
thread which can see an edge can see the node at the end of it — which is
exactly what an address dependency orders, and nothing more.  So the
expectation is that dependency ordering buys precisely what is needed and not
a byte more.

Tasks: the dependency-ordered analogue of `RAClosed`, restricted to the
target's cells; preservation; and `Published` for every thread's view.

*Acceptance* HD holds of every view under the weaker read.

**Done, and the acceptance criterion was wrong.**  HD does *not* hold of every
view under dependency ordering, and it should not: a thread may come to hold a
link it never dereferenced — carried forward at one cell as a side effect of
dereferencing another — and nothing orders the target of a pointer that was
never followed.  So the guarantee is not a property of a configuration at all.
It is a property of the *step*, and `k_dereference_sees` is it: after an
`rcu_dereference` of `n`, the reader sees whatever the publisher of that
pointer had already written into `n`.

That is the right shape rather than a concession.  Heap-domain closure says a
thread that can see an edge can see the node at the end of it — and a thread
that has not followed the edge has no business seeing the node.  The
per-dereference statement is the obligation with nothing left over, and it is
the per-traversal form identified under W4 arriving early.

### W4. Per-message state tagging, to replace the whole-state bridge

W2 removes the bridge's hypothesis.  The replacement is the one identified
earlier and avoided: record with each message the logical state it was written
in, prove every recorded state well formed along a run, and conclude that every
edge a reader holds was an edge of a well-formed state.  Properties the reader
needs that are *stable forward in time* then transfer; the one that is not is
"not yet reclaimed", which is the grace period's job and is already proved.

*Effort* the largest item after W5.  *Risk* medium.

**Done.**  `SConf` carries the weak state, the logical state now, and the state
each message was written in; `sstep` writes both halves at once, with the link
between them as a premise — the message's value is what the logical write put
there.  `SInv` has three clauses and `sstep_inv` preserves them.
`every_edge_was_real`: every edge a thread can see was an edge of a well-formed
state, the one the writer was in when it wrote that very message.

That is weaker than "the view is well formed" and is the right weakening: what
a thread does with an edge is follow it, and following it is a per-edge act.
Properties of the target stable forward in time — not being `fresh`, since a
node stops being fresh when published and does not go back — therefore still
hold when the reader gets there.  The one property that is *not* stable forward
is not having been reclaimed, and nothing about memory ordering could give it:
the value really was written and the thread really read it.  That is the grace
period's job.

### W5. A program semantics

**The prerequisite everything has been borrowing against.**  There is no
command language, no thread pool, no configurations, and no typing judgement
over programs anywhere in the development: `lstep : LState -> LState -> Prop`
relates states.  So "well-typed program" is not an object that can be
quantified over, and every theorem is of the form "any state reached by these
steps satisfies…".  This is also why W1 has to model a dependency as a combined
step rather than as a relation on program order — there is no program order.

Tasks: commands, a thread pool, configurations, a typing judgement; lift
`lstep` to configurations; restate progress per thread.

*Effort* weeks.  *Risk* medium-high, and it touches everything.

**Done.**  `rocq/Programs.v`.  A command language whose primitives are the
fifteen actions, with the two block forms *derived* rather than primitive —
which is what the desugaring in the paper says they are.  A thread pool,
configurations, a thread-local step relation and its lift to an interleaving.
`programs_are_memory_safe`: at no point in any interleaving of any program,
from any well-formed start, does a thread other than the writer hold a live
reference to a node the writer is about to reclaim.  That is the statement the
earlier files could not make.

Typing is structural, with the action case a parameter and the hypothesis tying
it to the action's effect being exactly axiom soundness — which `Triples.v`
proves for all fifteen, so it is taken here and discharged there.
`subject_reduction` holds.

Two abstractions, stated in the file rather than hidden.  Conditions are
abstracted (`CIf` steps to either branch): there is no expression language, and
for safety taking either branch quantifies over *more* runs than a real
condition would.  And the action's effect is a parameter required only to be an
`lstep`, which is what lets the file be about programs without re-encoding
fifteen actions' side conditions.

**And pool-level typing, which the first pass left open.**  One thread's step
changes shared state and something has to say the *other* threads' environments
survive it.  `Frames s s' t` is that condition, and it is read off the
denotations rather than guessed: eight components — `t`'s stack slots, the
observations tagged `t`, the root observation, `t`'s scope, the free list, the
heap, the lock, the root — and `Frames_D_env` is the proof that the list is
complete, one case per type.  It is deliberately not minimal per type, because a
frame condition has to cover an environment, which may hold any of the six.

Two things it says by what it constrains.  The heap, the lock and the root are
constrained *as wholes*, which makes the writer's actions non-framing — correct,
since an unlink really can invalidate another writer's path, and that is what
the lock is for.  And the free list is constrained as a whole rather than at
`t`'s own nodes, because `undef` and `freeable` quantify over entries the thread
does not name.

`pool_step` indexes the step by the thread performing it, which the earlier
sections did not need and this one does: soundness is about the stepping
thread's environment and framing is about everybody else's, and saying so needs
the two distinguishable.  `pool_ok_preserved` and `pool_run_ok`: from a typed
pool, every reachable configuration is a typed pool with every thread still
heading for the same final environment.

**The framing hypothesis is discharged, action by action, and the answer is not
uniform.**  `Frames_machine`: a step that changes only the reader or bounding
set frames *every* thread, because neither set is mentioned by any denotation —
`frames_read_begin`, `frames_sync_start_ms`, `frames_sync_stop_ms`.
`frames_read`: a reader's Read extends its own column of the observation map,
so it frames every other thread, and `ObsWF` is exactly what separates the
columns.  `frames_bind`: Bind writes one stack slot.  `frames_read_end`: its
free list only *shrinks* entries, which is why the free-list clauses of `Frames`
are two weak conditions rather than an equality; the one hypothesis it needs is
that the other threads' scopes are unchanged, which the abstract step does not
say — an under-specification of the action, visible as a hypothesis rather than
as prose.

`heap_changes_do_not_frame`: the writer's ten do not frame, with a witness.
That is correct rather than a weakness, and `heap_types_need_the_lock` /
`heap_types_are_exclusive` are why: every type whose denotation constrains the
heap requires the lock, so no two threads hold one, and a writer's mutation has
no *other* thread's path type to invalidate.  The protocol's answer to framing
is the lock, and the frame condition is where that becomes visible.

**Progress, which the task list above asked for and the first pass skipped.**
`head_act` names the action a command is about to perform; the control
constructs have none.  `tstep_progress`: a non-skip command steps unless the
action it is about to perform cannot — which is the right statement, because an
action whose guard is false genuinely blocks and should.  `pool_progress` lifts
it, and `finished_pools_are_stuck` closes the other side, so a stuck
configuration is finished or blocked on a guard and never a third thing.

**And the parameter instantiated.**  `RealStep` is the action relation itself,
so `real_programs_are_memory_safe` is a statement about the fifteen actions
rather than about an abstraction of them.

### W6. The LKMM correspondence

Two different projects hide under "verify against the LKMM".  **(a)** Take its
RCU axioms as given and show the type system sound with respect to them — the
core guarantee is that a read-side section does not span a grace period, which
is literally Alglave's first requirement and is already
`no_section_spans_a_grace_period`.  The natural home is `Refine.v`: instantiate
`Impl` and discharge the clauses.  The obstacle is that `Refines` is
operational and the LKMM is axiomatic over executions, so an
operational-to-axiomatic bridge is needed.  **(b)** Implement RCU from counters
and verify it under the LKMM — the Tassarotti-shaped project, much larger, and
note they chose release-acquire rather than the LKMM precisely to keep it
tractable.

Do (a), after W5.

**Done, sense (a).**  The LKMM does not derive RCU from anything — it
*axiomatises* it, and the axiom is that a read-side critical section does not
span a grace period.  `lkmm_gives_reclamation`: that axiom gives the
reclamation clause outright.  `lkmm_conformance_is_refinement`: the five-clause
obligation's two clauses *with content* are the axiom's two halves, and the
rest is bookkeeping any implementation of the four actions must get right
whatever model it is verified against.  `epochs_satisfy_the_axiom` checks the
statement is not vacuous.

So someone who has verified their RCU against the kernel memory model has
thereby done our work; we are not asking for something extra.

The split is stated as an iff, `refines_split`, so it says both things: the
obligation contains the axiom and nothing about reclamation beyond it, and
conformance discharges the obligation.

**And the bridge, which the first pass named rather than did.**  The LKMM is a
predicate on whole *executions* and `Impl` is a state machine, so reading an
execution as a run is a real translation.  `ev` is the five RCU events an
execution contains at this interface — section entries and exits,
grace-period starts and stops, reclamations — `ev_enabled` is what each
requires of the state it happens in, and `Enabled` is where conformance enters:
an execution that reclaims a node with a section still standing is one whose
`EFree` is not enabled, and `ns_free` is the axiom that rules those out.
`execution_replays`: an execution all of whose events are enabled replays as a
run of `pstep`.  `lkmm_execution_is_a_run`: therefore any execution of a
conforming implementation keeps the published model in step — which is the claim
the first pass was short of, "any conforming execution is one of ours" rather
than "an implementation whose guard means what the axiom says satisfies the
interface".  `executions_free_only_quiesced_nodes` says it at every reclamation
in the execution rather than only at its end.

Two things are explicit rather than assumed away.  Reading an execution as a
*sequence* assumes a total order, which is not free in a weak memory model; what
makes it available is that all five events touch the protocol's own state, so
the model's coherence on that state orders them.  And `Enabled` is a conjunction
of guards, which can be unsatisfiable, so `around_enabled` exhibits a whole
round — a reader enters and leaves, a writer detaches a node, waits, reclaims
it — at the counter implementation, end to end.

**And the same translation at the client's level, which is where the safety
theorem lives.**  The protocol-level bridge reads an execution as a run of
`pstep`, which is the right object for an axiom about grace periods and is not
yet the statement a client wants: a client's execution contains its own loads
and stores.  So `xev` is one of the five protocol events or one heap mutation,
carrying what the corresponding `xstep` constructor leaves existential — which
is not a weakening, since an execution *is* a record of what happened, so an
event that names its own outcome is the faithful reading and enabledness is then
exactly the constructor's premises.  `xexecution_replays`,
`conforming_executions_are_memory_safe`: any execution of any client against an
implementation conforming to the axiom, all of whose events are enabled, reaches
only states in which no thread but the writer holds a live reference to a node
the writer may reclaim.  Conformance enters in one place — the reclamation
event's guard — and nothing else about the implementation is used.
`client_executions_free_only_quiesced_nodes` is the reclamation half at every
reclamation; `epoch_executions_are_memory_safe` is the chain from the axiom to
the client in one statement; and `xround_enabled` exhibits a whole client round,
the writer's unlinked observation recoloured by SyncStop, so that the
reclamation guard is reached rather than assumed.

### W7. The dependency the compiler may not preserve

**Cannot be fixed here and must be stated.**  Source-level address dependencies
are not guaranteed by C: a compiler may break them by value speculation or by
arithmetic that cancels.  The LKMM models the kernel's assumptions about its
toolchain, not standard C semantics.  A proof against it is a proof against a
model in which the compiler is *trusted*, not proven, to respect dependencies.
Say so in the paper rather than absorb it.

**Order** W1, W2, W3 together; then W4; then W5; then W6.  W7 throughout, as
prose.

## Do not

- Do not start R1d (write_begin/write_end) before the rest of R1.
- Do not attempt option (b) of R4.
- Do not start A3 before the paper is out.
- Do not add `Print Assumptions` inside a `Section`; `make check` now rejects it,
  and the reason is in the appendix.

## Part IV — the two items the response named as open

Both are in `rocq/Closed.v`, after `Triples.v`.

### C1. The reader's read — **done, and the diagnosis was wrong**

The recorded obstacle was that a reader must learn what a field holds and the
points-to assertion is exclusive, so the repair was a fractional heap.  Wrong
obstacle.  The authoritative heap is *in* the invariant, so a reader that opens
it reads the edge there, and a reader's `rcuItr` mentions no cell — so nothing
is carried out past the closing and a fraction buys nothing.

What was actually in the way is the **bind**.  The rule moves the reader's
stack, so the machine's stack must move with it, and the general binding lemma
asks the bound node to be neither detached nor awaiting reclamation — which is
exactly what a reader cannot promise, since holding a reference to a node a
writer has already unlinked is the whole of RCU.

`reader_bind_preserves_WellFormed` is the replacement, and it is *smaller* than
the general bind, which is the part worth recording.  With the observation
already granted by the read, the bind changes only the stack and the scope, and
exactly four of the twenty conjuncts mention those — RWOW, AWRT, FR, WFresh.
The other sixteen are identities.  So a reader's bind cannot break an invariant
about detachment or reclamation, and the general bind's two premises are not
weakened here but *absent*: they were never the bind's business, they belong to
the writer's bind, whose post-type asks for a path and a field map.

`read_atomic`: the rule against the invariant — edge read, machine moved,
invariant re-established, with the postcondition a disjunction (the field held a
reference, or it did not and nothing moved).  `read_typed_closed`: the same with
the reader's environment on both sides, the iterator at `x` coming *out* of the
environment rather than in as a hypothesis.

### C2. The enumeration premises — **done, by finiteness**

"No resource a thread holds discharges those" conflated two things.  Whether the
thread *owns* the pieces is a resource question and stays one — that is what
ownership is.  Whether the set is *enumerable* is mathematics, and the answer is
yes in all four cases for the same reason: each set is a set of keys of a finite
map the invariant already carries.

Two lists are immediate.  `detached_list` is the nodes carrying a detaching
observation, read off the observation map (`detached_list_NoDup` / `_epoch` /
`_covers` / `_sound` are SyncStart's four premises).  `column` is the writer's
column of it, so SyncStop's and WriteEnd's two clauses hold by `column_lookup`
definitionally.

The third is not.  WriteBegin's set is the *reachable* nodes, and reachability
is a closure rather than a lookup.  `reach_upto` iterates "add the successors";
`reach_upto_sound` and `reach_upto_complete` are the two directions;
`chain_stabilises` is the pigeonhole that says iterating as many times as there
are locations the heap mentions is enough, stated on its own because it has
nothing to do with heaps.  `wb_list` is then the writer's entry at every
reachable node and the rule's six enumeration clauses are readings of it.

`sync_start_enumerated`, `sync_stop_enumerated`, `write_begin_enumerated` and
`write_end_enumerated` are the four rules at their own lists, asking for the
conditions the action carries, for the resources, and for nothing else.

### What is left

Fairness — that a reader inside a critical section eventually leaves it.  It is
a property of the client and no invariant of the shared state could supply it.
