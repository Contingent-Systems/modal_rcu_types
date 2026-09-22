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
  (* reclamation, and the guard it runs under.  This is the action the whole
     protocol exists to make safe, so it is the one clause below with content
     rather than bookkeeping *)
  i_can_free   : IState -> Loc -> Prop;
  i_free       : IState -> Loc -> IState;
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
Arguments i_can_free {_} _ _.
Arguments i_free {_} _ _.
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
  ref_wf_free : forall (i : I) o, i_wf i -> i_can_free i o -> i_wf (i_free i o);

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

  (* Reclamation.  Two clauses, and only the second has content.  The first is
     bookkeeping: freeing a node removes its free-list entry, which is what the
     published Free does.  The second is Alglave et al.'s first requirement,
     stated where it bites -- an implementation may free a node only once its
     grace period has completed, and "completed" is the published model's own
     condition, that the node's entry is empty.  Nothing about how the
     implementation decides that is constrained; what is constrained is that
     when it decides it may free, the model agrees. *)
  ref_free : forall (i : I) m F o,
    i_wf i -> i_can_free i o -> ISim i m F ->
    ISim (i_free i o) (free_ms m o) (delete o F);
  ref_free_quiesced : forall (i : I) o,
    i_wf i -> i_can_free i o -> i_F i !! o = Some ∅;

  (* and the grace period waits for the right set.  [ref_guard] says when the
     wait may end; this says what it was waiting for, and the two together are
     the whole of Alglave et al.'s first requirement at this interface *)
  ref_snapshot : forall (i : I) m F,
    i_wf i -> ISim i m F -> (forall t, t ∈ i_snapshot i <-> rds m t);
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
     i_can_free   := fun s o => exists e, estamp s !! o = Some e
                                       /\ e_quiescent s e;
     i_free       := e_free;
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
  - intros s o HWF _. destruct HWF as [Hst Hrg]. split; [| exact Hrg].
    intros q e Hq. simpl in Hq. apply lookup_delete_Some in Hq as [_ Hq].
    exact (Hst q e Hq).
  - intros s m F t HWF Hnone HS. exact (sim_read_begin m F s t HWF Hnone HS).
  - intros s m F t HWF HS. exact (sim_read_end m F s t HS).
  - intros s m F ds HWF HS. exact (sim_sync_start m F s ds HWF HS).
  - intros s m F HWF Hq HS.
    exact (sim_sync_stop m F s (proj2 (sim_sync_stop_guard m F s HS) Hq) HS).
  - intros s m F HWF HS. exact (iff_sym (sim_sync_stop_guard m F s HS)).
  - intros s m F o HWF Hfree (Hr & Hb & Hf). repeat apply conj.
    + intros t. simpl. exact (Hr t).
    + intros t. simpl. exact (Hb t).
    + rewrite Hf. simpl. exact (eq_sym (e_F_free s o)).
  - intros s o HWF [e [Hst Hq]]. exact (e_free_premise s o e Hst Hq).
  - intros s m F HWF (Hr & _ & _) t. simpl. rewrite elem_of_dom.
    exact (iff_sym (Hr t)).
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
    pstep (i, m, F) (i_sync_stop i, sync_stop_ms m, F)
| P_free (i : I) m F o :
    i_can_free i o ->
    pstep (i, m, F) (i_free i o, free_ms m o, delete o F).

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
  - split; [exact (ref_wf_free I HR i o Hwf H)
           | exact (ref_free I HR i m F o Hwf H HS)].
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
     i_can_free   := fun s o => exists e, estamp s !! o = Some e
                                       /\ e_quiescent s e;
     i_free       := e_free;
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

(** ** The reclamation clause, read back

    What [ref_free_quiesced] buys is one sentence, and it is the sentence the
    whole protocol exists for: when a conforming implementation decides it may
    reclaim a node, the published model agrees that the node is \frbl{} --- its
    free-list entry exists and is empty, which is exactly the conjunct the
    \frbl{} denotation asks for and which \texttt{Denotations.v} turns into
    ``nobody holds a live reference''.

    The implementation is free in how it decides.  The epoch model decides it
    by comparing counters; something else may decide it by counting
    quiescent states, or by a callback.  What it is not free in is *when* the
    answer may be yes. *)
Theorem refines_free_is_freeable (I : Impl) (HR : Refines I)
    (i : I) m Og U T F o :
  i_wf i -> ISim i m F -> i_can_free i o ->
  exists Tr, flist (to_LState_t m Og U T F) o = Some Tr /\ forall t, ~ Tr t.
Proof.
  intros Hwf (_ & _ & Hf) Hfree.
  exists (fun t => t ∈ (∅ : gset TID)). split.
  - simpl. rewrite Hf. rewrite (ref_free_quiesced I HR i o Hwf Hfree).
    reflexivity.
  - intros t. by apply not_elem_of_empty.
Qed.

Print Assumptions refines_free_is_freeable.

(** * The bridge

    [pstep] is about the protocol's bookkeeping: who is reading, who is
    bounding, what the free list says.  The type system is about the
    observation map, and [lstep] in [Actions.v] is the two together.  So the
    bridge is a step relation over both, and it is a bridge rather than a
    theorem because the two halves are supplied by different things: the
    implementation supplies the protocol half and the typing derivation
    supplies the observation half.

    [xstep] carries exactly the hypotheses of the corresponding [lstep]
    constructor, plus the implementation's guard.  Nothing is assumed twice and
    nothing is smuggled: the observation conditions below are, verbatim, the
    ones [lstep] already had. *)

Record Conf (I : Impl) := MkConf {
  c_i  : I;
  c_m  : MState;
  c_Og : ObsMap;
  c_U  : Var -> TID -> Prop;
  c_T  : gset TID;
  c_F  : gmap Loc (gset TID);
}.

Arguments MkConf {_} _ _ _ _ _ _.
Arguments c_i {_} _.
Arguments c_m {_} _.
Arguments c_Og {_} _.
Arguments c_U {_} _.
Arguments c_T {_} _.
Arguments c_F {_} _.

Definition c_L {I : Impl} (c : Conf I) : LState :=
  to_LState_t (c_m c) (c_Og c) (c_U c) (c_T c) (c_F c).

Definition c_ok {I : Impl} (c : Conf I) : Prop :=
  i_wf (c_i c) /\ ISim (c_i c) (c_m c) (c_F c).

Inductive xstep {I : Impl} : Conf I -> Conf I -> Prop :=
| X_free (i : I) m Og U T F d t :
    obsv (to_LState_t m Og U T F) d (Ofree t) ->
    i_can_free i d ->
    xstep (MkConf i m Og U T F)
          (MkConf (i_free i d) (free_ms m d) Og U T (delete d F))
| X_read_begin (i : I) m Og U T F t :
    i_can_begin i t ->
    (forall lw, lk m = Some lw -> lw <> t) ->
    (forall o, ~ obsv (to_LState_t m Og U T F) o (Ounlk t)
            /\ ~ obsv (to_LState_t m Og U T F) o (Ofree t)
            /\ ~ obsv (to_LState_t m Og U T F) o (Ofresh t)) ->
    xstep (MkConf i m Og U T F)
          (MkConf (i_read_begin i t) (read_begin_ms m t) Og U T F)
| X_read_end (i : I) m Og Og' U U' T F t :
    (forall o ob, obs_tid ob = Some t ->
       ~ obsv (to_LState_t (read_end_ms m t) Og' U' T (read_end_F F t)) o ob) ->
    (forall o ob, obsv (to_LState_t m Og U T F) o ob -> obs_tid ob <> Some t ->
       obsv (to_LState_t (read_end_ms m t) Og' U' T (read_end_F F t)) o ob) ->
    (forall o ob,
       obsv (to_LState_t (read_end_ms m t) Og' U' T (read_end_F F t)) o ob ->
       obsv (to_LState_t m Og U T F) o ob) ->
    (forall x,
       undf (to_LState_t (read_end_ms m t) Og' U' T (read_end_F F t)) x t) ->
    (forall x t', undf (to_LState_t m Og U T F) x t' ->
       undf (to_LState_t (read_end_ms m t) Og' U' T (read_end_F F t)) x t') ->
    rds m t ->
    xstep (MkConf i m Og U T F)
          (MkConf (i_read_end i t) (read_end_ms m t) Og' U' T (read_end_F F t))
| X_sync_start (i : I) m Og U T F ds :
    (forall o s0, i_ss_F i F ds !! o = Some s0 -> s0 = i_snapshot i) ->
    (forall o t, obsv (to_LState_t m Og U T F) o (Ounlk t)
              \/ obsv (to_LState_t m Og U T F) o (Ofree t) ->
       exists s0, i_ss_F i F ds !! o = Some s0) ->
    (forall o s0, i_ss_F i F ds !! o = Some s0 ->
       exists t, obsv (to_LState_t m Og U T F) o (Ounlk t)
              \/ obsv (to_LState_t m Og U T F) o (Ofree t)) ->
    xstep (MkConf i m Og U T F)
          (MkConf (i_sync_start i ds) (sync_start_ms m) Og U T
                  (i_ss_F i F ds))
| X_sync_stop (i : I) m Og U T F :
    i_quiet i ->
    xstep (MkConf i m Og U T F)
          (MkConf (i_sync_stop i) (sync_stop_ms m) (sync_stop_Og Og) U T F).

(** The implementation half: a conforming implementation keeps the relation. *)
Theorem xstep_ok (I : Impl) (HR : Refines I) (c c' : Conf I) :
  xstep c c' -> c_ok c -> c_ok c'.
Proof.
  intros Hst [Hwf HS]. destruct Hst; simpl in Hwf, HS |- *.
  - split; [exact (ref_wf_free I HR i d Hwf H0)
           | exact (ref_free I HR i m F d Hwf H0 HS)].
  - split; [exact (ref_wf_begin I HR i t Hwf H)
           | exact (ref_read_begin I HR i m F t Hwf H HS)].
  - split; [exact (ref_wf_end I HR i t Hwf)
           | exact (ref_read_end I HR i m F t Hwf HS)].
  - split; [exact (ref_wf_start I HR i ds Hwf)
           | exact (ref_sync_start I HR i m F ds Hwf HS)].
  - split; [exact (ref_wf_stop I HR i Hwf)
           | exact (ref_sync_stop I HR i m F Hwf H HS)].
Qed.

(** The type system half: every such step is a step of [lstep].  The two places
    the implementation is consulted are the two guards -- \textsc{SyncStop}'s,
    which [ref_guard] turns into the model's ``no thread is still bounding'',
    and \textsc{SyncStart}'s snapshot, which [ref_snapshot] turns into ``the
    threads now reading''.  Everything else is the observation conditions,
    unchanged. *)
Theorem xstep_lstep (I : Impl) (HR : Refines I) FType (c c' : Conf I) :
  c_ok c -> xstep c c' -> lstep FType (c_L c) (c_L c').
Proof.
  intros [Hwf HS] Hst. destruct Hst; simpl in Hwf, HS |- *.
  - exact (L_free FType m Og U T F d t H).
  - exact (L_read_begin FType m Og U T F t H0 H1).
  - exact (L_read_end FType m Og Og' U U' T F t H H0 H1 H2 H3 H4).
  - exact (L_sync_start FType m Og U T F (i_ss_F i F ds) (i_snapshot i)
             (ref_snapshot I HR i m F Hwf HS) H H0 H1).
  - exact (L_sync_stop FType m Og U T F
             (proj1 (ref_guard I HR i m F Hwf HS) H)).
Qed.

Print Assumptions xstep_ok.
Print Assumptions xstep_lstep.

(** And the two halves together, over a run.  This is the statement a claim
    about a client needs: start well formed and in the relation, run the
    implementation, and every state you reach is one the type system's
    invariants hold of. *)
Theorem xrun_WellFormed (I : Impl) (HR : Refines I) FType (c c' : Conf I) :
  rtc xstep c c' -> c_ok c -> WellFormed FType (c_L c) ->
  c_ok c' /\ WellFormed FType (c_L c').
Proof.
  induction 1 as [| a b c Hab Hbc IH]; intros Hok Hwf; [by split |].
  apply IH; [exact (xstep_ok I HR a b Hab Hok) |].
  exact (lstep_preserves FType (c_L a) (c_L b)
           (xstep_lstep I HR FType a b Hok Hab) Hwf).
Qed.

Print Assumptions xrun_WellFormed.

(** ** What the bridge delivers, and what it does not

    It delivers the transfer: a run of a conforming implementation, paired with
    the observation bookkeeping a typing derivation supplies, reaches only
    states the nineteen-plus-repairs hold of --- and therefore only states in
    which a \frbl{} node has no live reference
    ([no_live_reference_to_a_freeable_node] in [Denotations.v]).  Reclamation
    under a conforming implementation is memory-safe, and that is one theorem
    rather than one argument per implementation.

    It does not deliver the *mutation* half.  [xstep] has the five protocol
    actions and not the ten heap ones, because those do not involve the
    implementation at all: they are the writer's, they touch the heap and the
    observation map and never the free list or the reader set, and [lstep]
    already has them.  Interleaving the two relations is a matter of taking
    their union, and stating it that way would suggest the composition had been
    checked; it has not, so we state what has. *)
Corollary xrun_safe (I : Impl) (HR : Refines I) FType (c c' : Conf I)
    tw x o :
  rtc xstep c c' -> c_ok c -> WellFormed FType (c_L c) ->
  D_freeable (c_L c') tw x ->
  stk (ms (c_L c')) x tw = Some o ->
  forall y t', t' <> tw -> stk (ms (c_L c')) y t' = Some o ->
    ~ undf (c_L c') y t' -> False.
Proof.
  intros Hrun Hok Hwf Hfree Hstk.
  destruct (xrun_WellFormed I HR FType c c' Hrun Hok Hwf) as [_ Hwf'].
  destruct Hwf' as (_ & HRWOW & _ & HIFL & _).
  exact (no_live_reference_to_a_freeable_node (c_L c') tw x o
           HIFL HRWOW Hfree Hstk).
Qed.

Print Assumptions xrun_safe.

(** And the instance, so that the chain is visible end to end: the counter
    model refines the published one, so a client running against the counter
    model never sees a live reference to a node it has reclaimed.  Nothing in
    this corollary is new --- it is [xrun_safe] at [EpochImpl] --- and that is
    the point of having proved the general one. *)
Corollary epoch_run_safe FType (c c' : Conf EpochImpl) tw x o :
  rtc xstep c c' -> c_ok c -> WellFormed FType (c_L c) ->
  D_freeable (c_L c') tw x ->
  stk (ms (c_L c')) x tw = Some o ->
  forall y t', t' <> tw -> stk (ms (c_L c')) y t' = Some o ->
    ~ undf (c_L c') y t' -> False.
Proof. exact (xrun_safe EpochImpl epochs_refine FType c c' tw x o). Qed.

Print Assumptions epoch_run_safe.
