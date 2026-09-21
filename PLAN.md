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

**R1a — bind, free, reader_acquire (3 rules).**  The pure half exists
(`bind_post_env`, `free_post_env`, `reader_post_env`); only the typed rule is
missing, and the pattern is `alloc_typed`'s: open the invariant, apply the
atomic triple, frame the untouched environment with `EnvOK_cell` / `EnvOK_obs` /
`EnvOK_stack`, supply the touched variable with `TyOK_demoted` /
`TyOK_freeable` / `TyOK_promoted`.  `bind_atomic` and `free_atomic` already
exist as closed triples; `reader_acquire` has `reader_env` for the reader side.
*Effort* 2 days each.  *Risk* low — this is the established pattern.
*Acceptance* `bind_typed`, `free_typed`, `read_typed`, each with `EnvOK` on both
sides.

**R1b — read_begin, read_end (2 rules).**  Both have closed triples already
(`read_begin_atomic`, `read_end_atomic`) and neither touches the heap, so the
environment survives without any framing lemma about cells.  `reader_env` is the
bridge.  Note that `read_end`'s post-environment is *empty* — ToRCURead scopes
the reader's variables to the block — which is what `Hundf_t` already encodes.
*Effort* 2 days each.  *Risk* low.  *Blocked by* R4 if you want the read rule
itself (see below); the two block-boundary rules are not blocked.

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

### R4. The root observation

**A model decision, and only one of the two options survives contact.**

*Option (b), assign `Oroot` to the lock holder* — does not work.  `WriteEnd`
releases the lock while `retire_self` keeps the root observation, so between
critical sections it would sit in a thread that is not the writer.  Established;
do not spend time on it.

*Option (a), derive `Oroot` from the structure* — works, and is more faithful to
what the paper already says it is ("a property of the structure, not of an
observer").  Tasks:

1. Change `to_LState_t`'s `obsv` to
   `(∃ t s, Og !! (o,t) = Some s ∧ ob ∈ s) ∨ (ob = Oroot ∧ o = rt m)`.
2. Strengthen `ObsWF` to *thread-tagged only* — entries no longer carry `Oroot`.
3. `RTO` becomes definitional (`reflexivity`), so one of the twenty defects
   turns into a non-issue rather than a repair.  Say so.
4. `read_end_update` deletes its keys instead of retiring them, since there is
   no longer a root observation to preserve.
5. Strengthen the invariant's domain clause from *t-tagged entries* to *all
   entries* — now sound, because a reader's entries are all its own.
6. `read_atomic` closes: the reader can grant an observation at a node it has
   not observed, because the entry's absence is now derivable from its cell.

*Effort* 1–2 days.  *Risk* medium — `Oroot` appears 52 times and `obsv` is
everywhere.  **Do it on a branch**, and expect most affected proofs to get
shorter rather than longer.  *Acceptance* `RTO` by `reflexivity`; `read_atomic`
a closed triple; the "ten closed triples" claim becomes eleven.

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
