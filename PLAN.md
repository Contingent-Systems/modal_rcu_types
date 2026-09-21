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

**R1c — sync_start, sync_stop (2 rules).**  These need the environment to
survive a bulk observation change.  `TyOK_freeable` already gives SyncStop's
touched case (unlinked becomes freeable) and `wm_lb_entry_empty` gives the
certificate it needs.  SyncStart's difficulty is that its post-environment is
unchanged but its free list is not, so what has to be shown is that no
variable's type reads the free list except `freeable`, which none does yet at
that point.  *Effort* 3 days each.  *Risk* medium — the bulk update is where the
"these are all" premises live.

**R1d — write_begin, write_end (2 rules).**  The hardest, and they should be
done last.  `write_begin_preserves_WellFormed` requires the writer to take an
iterator observation on *every reachable node*, which is a bulk ghost update
needing the reachable set enumerated — the same premise `sync_start_update`
carries.  `write_end` is the mirror: retire them all, and its `Hclean` premise
(nothing left detached) is what ToRCUWrite enforces.  *Effort* 1 week for the
pair.  *Risk* medium-high; this is where an enumeration premise may prove
unavoidable, in which case say so rather than dress it up.

**Total** ~2.5 weeks.  **Order** R1a, R1b, R1c, R1d.  Do not start R1d first
because it is the interesting one; it is the one most likely to consume a week
and leave nothing.

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

Ship first.  Then R2 (two days, no risk, removes the most obvious reviewer
question).  Then R4 on a branch, because it also closes the reader's read and
turns a defect into a non-issue.  Then R1a–R1d as a block, because partial axiom
soundness is harder to describe than either none or all.  Then A1, rehearsing
with A2's step (4) first.  A2 can run in parallel with R1 if there are two
people; it shares no files.

## Do not

- Do not start R1d (write_begin/write_end) before the rest of R1.
- Do not attempt option (b) of R4.
- Do not start A3 before the paper is out.
- Do not add `Print Assumptions` inside a `Section`; `make check` now rejects it,
  and the reason is in the appendix.
