(** * Refinement: what it takes for an implementation to stand in for the model

    Milestone 5.  Everything before this file is about one abstract model: the
    type system is sound against it, and that the model is a faithful RCU is
    argued against Alglave et al.'s four requirements --- two of them as
    theorems, one as the six guards, one excluded as an optimisation.

    That is not yet a claim about any implementation.  A client compiled
    against a real RCU is safe only if that RCU *refines* the model, and
    refinement proved once, over an interface, is one theorem; refinement
    argued per implementation is one argument per implementation, forever.
    This file is the interface and the first instance.

    The shape is taken from [Epochs.v] rather than invented.  That file already
    contains a second model of the same protocol --- per-thread counters in
    place of a reader set, which the paper's related work asserts to be
    equivalent --- together with a relation [Sim] and one theorem per protocol
    action across it.  So the honest way to design the interface is to read it
    off that proof and check that the proof slots back in: if it does not, the
    interface is wrong, and finding that out costs a day rather than a month.
    It does slot in, and [epochs_refine] below is that instance, assembled from
    the five theorems [Epochs.v] already had.

    What the interface deliberately does *not* abstract is the published
    model's own steps.  [read_begin_ms], [read_end_ms], [sync_start_ms] and
    [sync_stop_ms] are fixed; an implementation is free in how it represents
    who is reading and what the free list is, and is obliged to move in step
    with those.  That is what makes the obligation checkable: it is four
    equations and a guard, not a bisimulation up to anything.

    Checked with Rocq 9.2, axiom-free. *)

From stdpp Require Import gmap sets.
From RCU Require Import WellFormed HeapPaths IrisGhost Denotations Actions
                        Epochs.

(** ** The interface

    An implementation is a state space with the four protocol actions on it,
    a well-formedness predicate it maintains, a guard for the grace period, and
    three observations: who is reading, who is bounding, and what the free list
    says.  The last three are what the published model *is*, and they are what
    the relation below compares. *)

Record Impl := {
  IState :> Type;
  (* the four protocol actions.  ReadBegin is guarded because a thread may not
     enter a section it is already in; the other three are total *)
  i_can_begin  : IState -> TID -> Prop;
  i_read_begin : IState -> TID -> IState;
  i_read_end   : IState -> TID -> IState;
  i_sync_start : IState -> gset Loc -> IState;
  i_sync_stop  : IState -> IState;
  (* the guard the grace period waits on *)
  i_quiet      : IState -> Prop;
  (* the threads a grace period beginning now will wait for *)
  i_snapshot   : IState -> gset TID;
  (* what the implementation is prepared to say about itself *)
  i_wf         : IState -> Prop;
  i_rds        : IState -> TID -> Prop;
  i_bnd        : IState -> TID -> Prop;
  i_F          : IState -> gmap Loc (gset TID);
}.

Arguments i_can_begin {_} _ _.
Arguments i_read_begin {_} _ _.
Arguments i_read_end {_} _ _.
Arguments i_sync_start {_} _ _.
Arguments i_sync_stop {_} _.
Arguments i_quiet {_} _.
Arguments i_snapshot {_} _.
Arguments i_wf {_} _.
Arguments i_rds {_} _ _.
Arguments i_bnd {_} _ _.
Arguments i_F {_} _.

(** The relation.  It is [Sim] from [Epochs.v] with the epoch state replaced by
    an arbitrary implementation state, which is the whole of the
    generalisation: the published model's three components are recoverable from
    the implementation's, and nothing is said about the rest of its state. *)
Definition ISim {I : Impl} (i : I) (m : MState) (F : gmap Loc (gset TID))
  : Prop :=
  (forall t, rds m t <-> i_rds i t)
  /\ (forall t, bnd m t <-> i_bnd i t)
  /\ F = i_F i.

(** The free list a SyncStart writes, in the published model's terms: every
    detached node gets an entry holding the threads the grace period waits for.
    This is [ss_F] from [Epochs.v], and it is stated over the implementation's
    snapshot rather than over the epoch model's. *)
Definition i_ss_F {I : Impl} (i : I) (F : gmap Loc (gset TID))
    (ds : gset Loc) : gmap Loc (gset TID) :=
  ss_F F ds (i_snapshot i).

(** ** The obligation

    Five clauses: one per protocol action, and one saying the implementation's
    guard decides the model's.  The fifth is the interesting one, and it is
    where an implementation can go wrong without any single step going wrong:
    it may wait for the wrong set. *)
Record Refines (I : Impl) : Prop := {
  (* the well-formedness the implementation maintains is its own business, but
     it has to be maintained *)
  ref_wf_begin : forall (i : I) t,
    i_wf i -> i_can_begin i t -> i_wf (i_read_begin i t);
  ref_wf_end : forall (i : I) t, i_wf i -> i_wf (i_read_end i t);
  ref_wf_start : forall (i : I) ds, i_wf i -> i_wf (i_sync_start i ds);
  ref_wf_stop : forall (i : I), i_wf i -> i_wf (i_sync_stop i);

  (* and the four steps move in step with the published model's *)
  ref_read_begin : forall (i : I) m F t,
    i_wf i -> i_can_begin i t -> ISim i m F ->
    ISim (i_read_begin i t) (read_begin_ms m t) F;
  ref_read_end : forall (i : I) m F t,
    i_wf i -> ISim i m F ->
    ISim (i_read_end i t) (read_end_ms m t) (read_end_F F t);
  ref_sync_start : forall (i : I) m F ds,
    i_wf i -> ISim i m F ->
    ISim (i_sync_start i ds) (sync_start_ms m) (i_ss_F i F ds);
  ref_sync_stop : forall (i : I) m F,
    i_wf i -> i_quiet i -> ISim i m F ->
    ISim (i_sync_stop i) (sync_stop_ms m) F;

  (* the guard decides the model's: the implementation waits for exactly the
     threads the model would *)
  ref_guard : forall (i : I) m F,
    i_wf i -> ISim i m F -> (i_quiet i <-> forall t, ~ bnd m t);
}.

(** ** The epoch model as the first instance

    [Epochs.v] proved the five theorems this record asks for, one at a time and
    for a different purpose -- to settle the paper's own assertion that the
    counter model and the reader-set model are equivalent.  Assembling them
    here is the rehearsal the interface needed: it is what shows the record is
    the right shape rather than a shape. *)

Definition EpochImpl : Impl :=
  {| IState      := EState;
     i_can_begin := fun s t => ereg s !! t = None;
     i_read_begin := e_begin;
     i_read_end   := e_end;
     i_sync_start := e_sync_start;
     i_sync_stop  := fun s => s;
     i_quiet      := fun s => forall t e, ereg s !! t = Some e -> egen s <= e;
     i_snapshot   := fun s => dom (ereg s);
     i_wf         := EWF;
     i_rds        := e_rds;
     i_bnd        := e_bnd;
     i_F          := e_F |}.

Lemma epoch_ISim (s : EpochImpl) m F : ISim s m F <-> Sim m F s.
Proof. reflexivity. Qed.

Theorem epochs_refine : Refines EpochImpl.
Proof.
  constructor.
  - intros s t HWF Hnone. exact (EWF_begin s t HWF).
  - intros s t HWF. exact (EWF_end s t HWF).
  - intros s ds HWF. exact (EWF_sync_start s ds HWF).
  - intros s HWF. exact HWF.
  - intros s m F t HWF Hnone HS. exact (sim_read_begin m F s t HWF Hnone HS).
  - intros s m F t HWF HS. exact (sim_read_end m F s t HS).
  - intros s m F ds HWF HS. exact (sim_sync_start m F s ds HWF HS).
  - intros s m F HWF Hq HS. exact (sim_sync_stop m F s (proj2 (sim_sync_stop_guard m F s HS) Hq) HS).
  - intros s m F HWF HS. exact (iff_sym (sim_sync_stop_guard m F s HS)).
Qed.

Print Assumptions epochs_refine.

(** ** Runs

    One step is not the claim.  The claim is that a client running against the
    implementation sees a state the published model could have been in, and
    that is the reflexive-transitive closure of the paired step. *)

Inductive pstep {I : Impl} :
    (I * MState * gmap Loc (gset TID)) ->
    (I * MState * gmap Loc (gset TID)) -> Prop :=
| P_begin (i : I) m F t :
    i_can_begin i t ->
    pstep (i, m, F) (i_read_begin i t, read_begin_ms m t, F)
| P_end (i : I) m F t :
    pstep (i, m, F) (i_read_end i t, read_end_ms m t, read_end_F F t)
| P_start (i : I) m F ds :
    pstep (i, m, F) (i_sync_start i ds, sync_start_ms m, i_ss_F i F ds)
| P_stop (i : I) m F :
    i_quiet i ->
    pstep (i, m, F) (i_sync_stop i, sync_stop_ms m, F).

Definition IOK {I : Impl} (c : I * MState * gmap Loc (gset TID)) : Prop :=
  i_wf c.1.1 /\ ISim c.1.1 c.1.2 c.2.

Theorem refines_step (I : Impl) (HR : Refines I) c c' :
  pstep c c' -> IOK c -> IOK (I := I) c'.
Proof.
  intros Hst [Hwf HS]. destruct Hst; simpl in Hwf, HS |- *.
  - split; [exact (ref_wf_begin I HR i t Hwf H)
           | exact (ref_read_begin I HR i m F t Hwf H HS)].
  - split; [exact (ref_wf_end I HR i t Hwf)
           | exact (ref_read_end I HR i m F t Hwf HS)].
  - split; [exact (ref_wf_start I HR i ds Hwf)
           | exact (ref_sync_start I HR i m F ds Hwf HS)].
  - split; [exact (ref_wf_stop I HR i Hwf)
           | exact (ref_sync_stop I HR i m F Hwf H HS)].
Qed.

Theorem refines_run (I : Impl) (HR : Refines I) c c' :
  rtc pstep c c' -> IOK c -> IOK (I := I) c'.
Proof.
  induction 1 as [| a b c Hab Hbc IH]; intros Hok; [exact Hok |].
  exact (IH (refines_step I HR a b Hab Hok)).
Qed.

Print Assumptions refines_step.
Print Assumptions refines_run.

(** ** The clause that is load-bearing, and why it is not decorative

    Four of the five clauses are about single steps agreeing, and an
    implementation that got one of them wrong would be wrong in an obvious way.
    The fifth is not like that.  [ref_guard] says the implementation's grace
    period waits for exactly the threads the model would, and an implementation
    can satisfy the other four while waiting for none of them: every individual
    step still agrees with the model's, because the model's \textsc{SyncStop}
    does not itself check anything -- the checking is in when it is allowed to
    run.

    The witness is the epoch model with its guard replaced by ``always''.  It
    satisfies all four step clauses, because they are literally the same
    theorems; it fails [ref_guard], and reclamation under it can free a node a
    reader still holds.  So the obligation is not four equations with a
    condition attached for tidiness: the condition is the safety property. *)

Definition EagerImpl : Impl :=
  {| IState      := EState;
     i_can_begin := fun s t => ereg s !! t = None;
     i_read_begin := e_begin;
     i_read_end   := e_end;
     i_sync_start := e_sync_start;
     i_sync_stop  := fun s => s;
     i_quiet      := fun _ => True;
     i_snapshot   := fun s => dom (ereg s);
     i_wf         := EWF;
     i_rds        := e_rds;
     i_bnd        := e_bnd;
     i_F          := e_F |}.

(** The four step clauses hold of it, unchanged. *)
Lemma eager_steps_agree :
  (forall (i : EagerImpl) m F t,
     i_wf i -> i_can_begin i t -> ISim i m F ->
     ISim (i_read_begin i t) (read_begin_ms m t) F)
  /\ (forall (i : EagerImpl) m F t,
     i_wf i -> ISim i m F ->
     ISim (i_read_end i t) (read_end_ms m t) (read_end_F F t))
  /\ (forall (i : EagerImpl) m F ds,
     i_wf i -> ISim i m F ->
     ISim (i_sync_start i ds) (sync_start_ms m) (i_ss_F i F ds)).
Proof.
  repeat apply conj.
  - intros s m F t HWF Hnone HS. exact (sim_read_begin m F s t HWF Hnone HS).
  - intros s m F t HWF HS. exact (sim_read_end m F s t HS).
  - intros s m F ds HWF HS. exact (sim_sync_start m F s ds HWF HS).
Qed.

(** And the guard clause does not.  The state is one reader registered at the
    epoch its grace period is waiting on -- the reader is inside a section the
    grace period must wait for, the model says so, and the eager
    implementation says it may proceed. *)
Definition eager_s : EState :=
  {| egen := 1; ereg := {[ 7%nat := 0 ]}; estamp := ∅ |}.

Definition eager_m : MState :=
  {| stk := fun _ _ => None; hp := fun _ _ => None; lk := None; rt := 0;
     rds := fun t => t = 7%nat; bnd := fun t => t = 7%nat |}.

Lemma eager_wf : EWF eager_s.
Proof.
  split.
  - intros o e Ho. simpl in Ho. by rewrite lookup_empty in Ho.
  - intros t e Ht. simpl in Ht.
    destruct (decide (t = 7%nat)) as [-> | Hne].
    + rewrite lookup_singleton_eq in Ht. injection Ht as <-. apply Nat.le_0_l.
    + rewrite lookup_singleton_ne in Ht;
        [discriminate | exact (fun Hc => Hne (eq_sym Hc))].
Qed.

Lemma eager_sim : ISim (I := EagerImpl) eager_s eager_m (e_F eager_s).
Proof.
  repeat apply conj; [| | reflexivity].
  - intros t. simpl. unfold e_rds. simpl. split.
    + intros ->. rewrite lookup_singleton_eq. by exists 0.
    + intros [e He]. destruct (decide (t = 7%nat)) as [-> | Hne];
        [reflexivity |].
      rewrite lookup_singleton_ne in He;
        [discriminate | exact (fun Hc => Hne (eq_sym Hc))].
  - intros t. simpl. unfold e_bnd. simpl. split.
    + intros ->. exists 0. rewrite lookup_singleton_eq. split; [reflexivity |].
      apply Nat.lt_0_1.
    + intros [e [He Hlt]]. destruct (decide (t = 7%nat)) as [-> | Hne];
        [reflexivity |].
      rewrite lookup_singleton_ne in He;
        [discriminate | exact (fun Hc => Hne (eq_sym Hc))].
Qed.

Theorem eager_is_not_a_refinement : ~ Refines EagerImpl.
Proof.
  intros HR.
  destruct (proj1 (ref_guard EagerImpl HR eager_s eager_m (e_F eager_s)
                     eager_wf eager_sim) I 7%nat) as [].
  reflexivity.
Qed.

Print Assumptions eager_steps_agree.
Print Assumptions eager_is_not_a_refinement.
