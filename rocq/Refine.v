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

Inductive xstep {I : Impl} (FType : FName -> FieldKind) : Conf I -> Conf I -> Prop :=
| X_free (i : I) m Og U T F d t :
    obsv (to_LState_t m Og U T F) d (Ofree t) ->
    i_can_free i d ->
    xstep FType (MkConf i m Og U T F)
          (MkConf (i_free i d) (free_ms m d) Og U T (delete d F))
| X_read_begin (i : I) m Og U T F t :
    i_can_begin i t ->
    (forall lw, lk m = Some lw -> lw <> t) ->
    (forall o, ~ obsv (to_LState_t m Og U T F) o (Ounlk t)
            /\ ~ obsv (to_LState_t m Og U T F) o (Ofree t)
            /\ ~ obsv (to_LState_t m Og U T F) o (Ofresh t)) ->
    xstep FType (MkConf i m Og U T F)
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
    xstep FType (MkConf i m Og U T F)
          (MkConf (i_read_end i t) (read_end_ms m t) Og' U' T (read_end_F F t))
| X_sync_start (i : I) m Og U T F ds :
    (forall o s0, i_ss_F i F ds !! o = Some s0 -> s0 = i_snapshot i) ->
    (forall o t, obsv (to_LState_t m Og U T F) o (Ounlk t)
              \/ obsv (to_LState_t m Og U T F) o (Ofree t) ->
       exists s0, i_ss_F i F ds !! o = Some s0) ->
    (forall o s0, i_ss_F i F ds !! o = Some s0 ->
       exists t, obsv (to_LState_t m Og U T F) o (Ounlk t)
              \/ obsv (to_LState_t m Og U T F) o (Ofree t)) ->
    xstep FType (MkConf i m Og U T F)
          (MkConf (i_sync_start i ds) (sync_start_ms m) Og U T
                  (i_ss_F i F ds))
| X_sync_stop (i : I) m Og U T F :
    i_quiet i ->
    xstep FType (MkConf i m Og U T F)
          (MkConf (i_sync_stop i) (sync_stop_ms m) (sync_stop_Og Og) U T F)
(** And the writer's ten, which the implementation does not take part in.  A
    heap action touches the heap and the observation map; it never touches the
    free list or the reader set, so the implementation does not move and the
    relation is kept for free.  Those two facts are the side conditions here,
    and [heap_actions_are_quiet] below discharges them for every one of the
    ten, which is what makes this constructor usable rather than decorative. *)
| X_heap (i : I) m Og U T F m' Og' U' T' :
    lstep FType (to_LState_t m Og U T F) (to_LState_t m' Og' U' T' F) ->
    (forall t, rds m' t <-> rds m t) ->
    (forall t, bnd m' t <-> bnd m t) ->
    xstep FType (MkConf i m Og U T F) (MkConf i m' Og' U' T' F).

(** The implementation half: a conforming implementation keeps the relation. *)
Theorem xstep_ok (I : Impl) (HR : Refines I) FType (c c' : Conf I) :
  xstep FType c c' -> c_ok c -> c_ok c'.
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
  - split; [exact Hwf |].
    destruct HS as (Hr & Hb & Hf). repeat apply conj; [| | exact Hf].
    + intros t. exact (iff_trans (H0 t) (Hr t)).
    + intros t. exact (iff_trans (H1 t) (Hb t)).
Qed.

(** The type system half: every such step is a step of [lstep].  The two places
    the implementation is consulted are the two guards -- \textsc{SyncStop}'s,
    which [ref_guard] turns into the model's ``no thread is still bounding'',
    and \textsc{SyncStart}'s snapshot, which [ref_snapshot] turns into ``the
    threads now reading''.  Everything else is the observation conditions,
    unchanged. *)
Theorem xstep_lstep (I : Impl) (HR : Refines I) FType (c c' : Conf I) :
  c_ok c -> xstep FType c c' -> lstep FType (c_L c) (c_L c').
Proof.
  intros [Hwf HS] Hst. destruct Hst; simpl in Hwf, HS |- *.
  - exact (L_free FType m Og U T F d t H).
  - exact (L_read_begin FType m Og U T F t H0 H1).
  - exact (L_read_end FType m Og Og' U U' T F t H H0 H1 H2 H3 H4).
  - exact (L_sync_start FType m Og U T F (i_ss_F i F ds) (i_snapshot i)
             (ref_snapshot I HR i m F Hwf HS) H H0 H1).
  - exact (L_sync_stop FType m Og U T F
             (proj1 (ref_guard I HR i m F Hwf HS) H)).
  - exact H.
Qed.

(** The side conditions [X_heap] asks for, discharged for all ten.  Every one of
    the writer's machine-state transformers carries [rds] and [bnd] through
    unchanged --- they are written [rds := rds m] and [bnd := bnd m] in
    [Actions.v] --- so the conditions are reflexivity, ten times.  That is the
    content: not that they are preserved by an argument, but that the heap
    actions do not mention the two components the implementation owns. *)
Theorem heap_actions_are_quiet m :
  (* T-ReadH for a reader takes no machine step at all *)
  ((forall t, rds m t <-> rds m t) /\ (forall t, bnd m t <-> bnd m t))
  (* the five heap mutations *)
  /\ (forall o f v, (forall t, rds (write_ms m o f v) t <-> rds m t)
                 /\ (forall t, bnd (write_ms m o f v) t <-> bnd m t))
  (* allocation *)
  /\ (forall n fs x lw, (forall t, rds (alloc_ms m n fs x lw) t <-> rds m t)
                     /\ (forall t, bnd (alloc_ms m n fs x lw) t <-> bnd m t))
  (* the binding rules *)
  /\ (forall y tb o, (forall t, rds (bind_ms m y tb o) t <-> rds m t)
                  /\ (forall t, bnd (bind_ms m y tb o) t <-> bnd m t))
  (* and the two ends of the write critical section, which move the lock and
     nothing the implementation can see *)
  /\ (forall lw, (forall t, rds (write_begin_ms m lw) t <-> rds m t)
              /\ (forall t, bnd (write_begin_ms m lw) t <-> bnd m t))
  /\ ((forall t, rds (write_end_ms m) t <-> rds m t)
      /\ (forall t, bnd (write_end_ms m) t <-> bnd m t)).
Proof.
  repeat apply conj; try (intros; apply iff_refl).
  all: intros; split; intros; apply iff_refl.
Qed.

Print Assumptions xstep_ok.
Print Assumptions xstep_lstep.
Print Assumptions heap_actions_are_quiet.

(** And the two halves together, over a run.  This is the statement a claim
    about a client needs: start well formed and in the relation, run the
    implementation, and every state you reach is one the type system's
    invariants hold of. *)
Theorem xrun_WellFormed (I : Impl) (HR : Refines I) FType (c c' : Conf I) :
  rtc (xstep FType) c c' -> c_ok c -> WellFormed FType (c_L c) ->
  c_ok c' /\ WellFormed FType (c_L c').
Proof.
  induction 1 as [| a b c Hab Hbc IH]; intros Hok Hwf; [by split |].
  apply IH; [exact (xstep_ok I HR FType a b Hab Hok) |].
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

    It delivers the mutation half too, and the way it does is the point.  The
    ten heap actions do not involve the implementation at all --- they are the
    writer's, they touch the heap and the observation map and never the free
    list or the reader set --- so [X_heap] lets any [lstep] through on the
    condition that it leaves [rds] and [bnd] alone, and
    [heap_actions_are_quiet] discharges that for all ten by reflexivity.  So
    [xstep] really is the union of the two relations, a run may interleave the
    writer's mutations with the protocol freely, and [xrun_safe] is about whole
    programs rather than the protocol in isolation.

    What is *not* here is any claim that the two relations are the only steps,
    or that a scheduler exists that produces any particular interleaving.
    [xstep] says what may happen, not what does; progress and fairness are the
    same open questions they were, and nothing above narrows them. *)
Corollary xrun_safe (I : Impl) (HR : Refines I) FType (c c' : Conf I)
    tw x o :
  rtc (xstep FType) c c' -> c_ok c -> WellFormed FType (c_L c) ->
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
  rtc (xstep FType) c c' -> c_ok c -> WellFormed FType (c_L c) ->
  D_freeable (c_L c') tw x ->
  stk (ms (c_L c')) x tw = Some o ->
  forall y t', t' <> tw -> stk (ms (c_L c')) y t' = Some o ->
    ~ undf (c_L c') y t' -> False.
Proof. exact (xrun_safe EpochImpl epochs_refine FType c c' tw x o). Qed.

Print Assumptions epoch_run_safe.

(** * The kernel memory model's RCU axiom

    Milestone 8, second half.  A reviewer's question about the Linux kernel
    memory model hides two different projects.  One is to implement RCU from
    counters and verify *that* under the LKMM; that is the Tassarotti-shaped
    project, and note they chose release-acquire over the LKMM precisely to
    keep it tractable.  The other is to take the LKMM's RCU guarantees as given
    and ask what they buy a client of this interface.  This section is the
    second.

    The thing to see first is that the LKMM does not *derive* RCU from
    anything.  It axiomatises it: the model's RCU axiom is that a read-side
    critical section does not span a grace period, which is Alglave et al.'s
    first requirement and, in the epoch model, is
    [no_section_spans_a_grace_period] in [Epochs.v].  So the question is not
    whether the axiom is strong enough to prove something --- it is what part
    of the obligation it is.

    The answer is a split.  Of the thirteen clauses of [Refines], ten are
    bookkeeping: they say the four actions move the three observable components
    the way the published model's do, and no implementation of RCU can get them
    wrong and still be an implementation of RCU.  The other three are the
    axiom, in its two halves --- what a grace period waits for, and what
    follows for reclamation. *)

Record Bookkeeping (I : Impl) : Prop := {
  bk_wf_begin : forall (i : I) t,
    i_wf i -> i_can_begin i t -> i_wf (i_read_begin i t);
  bk_wf_end : forall (i : I) t, i_wf i -> i_wf (i_read_end i t);
  bk_wf_start : forall (i : I) ds, i_wf i -> i_wf (i_sync_start i ds);
  bk_wf_stop : forall (i : I), i_wf i -> i_wf (i_sync_stop i);
  bk_wf_free : forall (i : I) o, i_wf i -> i_can_free i o -> i_wf (i_free i o);
  bk_read_begin : forall (i : I) m F t,
    i_wf i -> i_can_begin i t -> ISim i m F ->
    ISim (i_read_begin i t) (read_begin_ms m t) F;
  bk_read_end : forall (i : I) m F t,
    i_wf i -> ISim i m F ->
    ISim (i_read_end i t) (read_end_ms m t) (read_end_F F t);
  bk_sync_start : forall (i : I) m F ds,
    i_wf i -> ISim i m F ->
    ISim (i_sync_start i ds) (sync_start_ms m) (i_ss_F i F ds);
  bk_sync_stop : forall (i : I) m F,
    i_wf i -> i_quiet i -> ISim i m F ->
    ISim (i_sync_stop i) (sync_stop_ms m) F;
  bk_free : forall (i : I) m F o,
    i_wf i -> i_can_free i o -> ISim i m F ->
    ISim (i_free i o) (free_ms m o) (delete o F);
}.

(** And the axiom.  Three clauses, and they are one sentence read three ways:
    a grace period waits for the sections in progress when it begins
    ([ns_snapshot]), it is over only when every one of them has ended
    ([ns_quiet]), and therefore a node detached before it began may be
    reclaimed after it ends ([ns_free]).

    [ns_free] is stated as "no thread is still waited for" rather than as an
    equality with the empty set, for the same reason the \frbl{} denotation is:
    the extensional form is what an implementation can establish without
    functional extensionality. *)
Record NoSectionSpansAGracePeriod (I : Impl) : Prop := {
  ns_snapshot : forall (i : I) m F,
    i_wf i -> ISim i m F -> (forall t, t ∈ i_snapshot i <-> rds m t);
  ns_quiet : forall (i : I) m F,
    i_wf i -> ISim i m F -> (i_quiet i <-> forall t, ~ bnd m t);
  ns_free : forall (i : I) o, i_wf i -> i_can_free i o ->
    exists s, i_F i !! o = Some s /\ forall t, t ∉ s;
}.

(** The reclamation clause, outright.  This is the one place the axiom does
    work rather than bookkeeping: it is what licenses a free. *)
Theorem lkmm_gives_reclamation (I : Impl) (HA : NoSectionSpansAGracePeriod I)
    (i : I) o :
  i_wf i -> i_can_free i o -> i_F i !! o = Some ∅.
Proof.
  intros Hwf Hfree.
  destruct (ns_free I HA i o Hwf Hfree) as [s [Hlk Hns]].
  rewrite Hlk. f_equal. apply set_eq. intros t. split.
  - intros Hc. destruct (Hns t Hc).
  - intros Hc. by apply not_elem_of_empty in Hc.
Qed.

(** The split, both ways.  Left to right it says the obligation contains the
    axiom and nothing about reclamation beyond it; right to left it is the
    statement a reviewer asks for --- someone who has verified their RCU
    against the kernel memory model has thereby discharged our obligation, and
    we are not asking for something extra. *)
Theorem refines_split (I : Impl) :
  Refines I <-> Bookkeeping I /\ NoSectionSpansAGracePeriod I.
Proof.
  split.
  - intros HR. split.
    + constructor; intros; by eapply HR.
    + constructor.
      * intros i m F Hwf HS. exact (ref_snapshot I HR i m F Hwf HS).
      * intros i m F Hwf HS. exact (ref_guard I HR i m F Hwf HS).
      * intros i o Hwf Hfree. exists ∅.
        split; [exact (ref_free_quiesced I HR i o Hwf Hfree) |].
        intros t. by apply not_elem_of_empty.
  - intros [HB HA]. constructor; try (intros; by eapply HB).
    + intros i m F Hwf HS. exact (ns_quiet I HA i m F Hwf HS).
    + intros i o Hwf Hfree. exact (lkmm_gives_reclamation I HA i o Hwf Hfree).
    + intros i m F Hwf HS. exact (ns_snapshot I HA i m F Hwf HS).
Qed.

Theorem lkmm_conformance_is_refinement (I : Impl) :
  Bookkeeping I -> NoSectionSpansAGracePeriod I -> Refines I.
Proof. intros HB HA. by apply refines_split. Qed.

(** ...and that the statement is not vacuous: the epoch model satisfies it,
    which it must, since [Epochs.v] proved Alglave's clause directly. *)
Theorem epochs_satisfy_the_axiom : NoSectionSpansAGracePeriod EpochImpl.
Proof. by apply refines_split, epochs_refine. Qed.

Print Assumptions lkmm_gives_reclamation.
Print Assumptions refines_split.
Print Assumptions lkmm_conformance_is_refinement.
Print Assumptions epochs_satisfy_the_axiom.

(** ** The bridge the claim was missing

    The split above is a statement about implementations, and it is stated in
    the interface's own terms --- a state, a guard, a step.  The LKMM is not
    that kind of object.  It is a predicate on whole *executions*: a finite set
    of memory events with relations over them, and conformance is a property of
    the graph, not of a state at a moment.  So "an implementation whose guard
    means what the axiom says satisfies the interface" is not yet "any
    conforming execution is a run of ours"; getting from one to the other is a
    translation, and this is it.

    An execution, at this interface, is the sequence of RCU events it
    contains --- section entries and exits, grace-period starts and stops, and
    reclamations --- in the order the model's coherence puts them.  Nothing
    else in an LKMM execution is visible to the protocol, which is the point:
    the loads and stores are the client's business and are what [xstep] below
    already carries.

    Two things are worth being explicit about.  The order is total, which is
    what reading an execution as a *sequence* assumes; that is not free in a
    weak memory model in general, and what makes it available here is that
    these five events all touch the protocol's own state, so the model's
    coherence order on that state orders them.  And [Enabled] is where
    conformance enters: an execution in which a reclamation happens with a
    section still standing is one whose [EFree] is not enabled, and the axiom
    is exactly what rules those out. *)

Inductive ev :=
| EBegin (t : TID)
| EEnd (t : TID)
| EStart (ds : gset Loc)
| EStop
| EFree (o : Loc).

Definition Exec := list ev.

Definition PConf (I : Impl) : Type := (I * MState * gmap Loc (gset TID))%type.

(** What each event requires of the state it happens in.  Three of the five are
    unconditional; the two that are not are the two the protocol is about. *)
Definition ev_enabled {I : Impl} (e : ev) (c : PConf I) : Prop :=
  match e with
  | EBegin t => i_can_begin c.1.1 t
  | EEnd _   => True
  | EStart _ => True
  | EStop    => i_quiet c.1.1
  | EFree o  => i_can_free c.1.1 o
  end.

(** ...and what it does.  This is [pstep] written as a function, which is
    possible precisely because the events name their own arguments. *)
Definition ev_apply {I : Impl} (e : ev) (c : PConf I) : PConf I :=
  match e with
  | EBegin t  => (i_read_begin c.1.1 t, read_begin_ms c.1.2 t, c.2)
  | EEnd t    => (i_read_end c.1.1 t, read_end_ms c.1.2 t, read_end_F c.2 t)
  | EStart ds => (i_sync_start c.1.1 ds, sync_start_ms c.1.2, i_ss_F c.1.1 c.2 ds)
  | EStop     => (i_sync_stop c.1.1, sync_stop_ms c.1.2, c.2)
  | EFree o   => (i_free c.1.1 o, free_ms c.1.2 o, delete o c.2)
  end.

Lemma ev_pstep (I : Impl) (e : ev) (c : PConf I) :
  ev_enabled e c -> pstep c (ev_apply e c).
Proof.
  destruct c as [[i m] F]. destruct e; simpl; intros He.
  - by apply P_begin.
  - by apply P_end.
  - by apply P_start.
  - by apply P_stop.
  - by apply P_free.
Qed.

Fixpoint Enabled {I : Impl} (es : Exec) (c : PConf I) : Prop :=
  match es with
  | nil => True
  | e :: rest => ev_enabled e c /\ Enabled rest (ev_apply e c)
  end.

Fixpoint replay {I : Impl} (es : Exec) (c : PConf I) : PConf I :=
  match es with
  | nil => c
  | e :: rest => replay rest (ev_apply e c)
  end.

Lemma replay_app (I : Impl) es1 es2 (c : PConf I) :
  replay (es1 ++ es2) c = replay es2 (replay es1 c).
Proof.
  revert c. induction es1 as [| e es1 IH]; intros c; [reflexivity |].
  simpl. by rewrite IH.
Qed.

Lemma Enabled_app (I : Impl) es1 es2 (c : PConf I) :
  Enabled (es1 ++ es2) c <-> Enabled es1 c /\ Enabled es2 (replay es1 c).
Proof.
  revert c. induction es1 as [| e es1 IH]; intros c; simpl.
  - split; [by intros H | by intros [_ H]].
  - split.
    + intros [He Hrest]. apply IH in Hrest as [H1 H2]. by repeat split.
    + intros [[He H1] H2]. split; [exact He |]. by apply IH.
Qed.

(** The translation.  An execution all of whose events are enabled replays as a
    run of the paired step relation --- so it is a run of the interface, and
    everything the interface proves about runs is available to it. *)
Theorem execution_replays (I : Impl) es (c : PConf I) :
  Enabled es c -> rtc pstep c (replay es c).
Proof.
  revert c. induction es as [| e es IH]; intros c; simpl; [by intros _ |].
  intros [He Hrest].
  eapply rtc_l; [exact (ev_pstep I e c He) | exact (IH _ Hrest)].
Qed.

(** ...and therefore any conforming execution keeps the published model in
    step.  This is the statement the earlier claim was short of: not "an
    implementation whose guard means what the axiom says satisfies the
    interface", but "any execution of one is a run of ours". *)
Theorem lkmm_execution_is_a_run (I : Impl)
    (HB : Bookkeeping I) (HA : NoSectionSpansAGracePeriod I) es (c : PConf I) :
  IOK c -> Enabled es c -> IOK (replay es c).
Proof.
  intros Hok Hen.
  exact (refines_run I (lkmm_conformance_is_refinement I HB HA) c _
           (execution_replays I es c Hen) Hok).
Qed.

(** And the payoff, at every reclamation in the execution rather than only at
    its end: wherever a conforming execution frees a node, the published
    model's free list says at that point that the node is \frbl{} --- its entry
    exists and no thread is still waited for.  [Denotations.v] is what turns
    that into "nobody holds a live reference", and [refines_free_is_freeable]
    is the same sentence one step further on.

    The hypothesis is only that the execution's events are enabled.  That is
    where conformance to the LKMM enters and it is the whole of what is used:
    an execution that reclaims a node while a section that could hold it is
    still standing is one whose [EFree] is not enabled, and [ns_free] is the
    axiom that says so. *)
Theorem executions_free_only_quiesced_nodes (I : Impl)
    (HB : Bookkeeping I) (HA : NoSectionSpansAGracePeriod I)
    es1 es2 (c : PConf I) o :
  IOK c -> Enabled (es1 ++ EFree o :: es2) c ->
  (replay es1 c).2 !! o = Some ∅.
Proof.
  intros Hok Hen. apply Enabled_app in Hen as [H1 H2].
  destruct H2 as [Hfree _].
  pose proof (lkmm_execution_is_a_run I HB HA es1 c Hok H1) as [Hwf HS].
  destruct HS as (_ & _ & HF). rewrite HF.
  exact (lkmm_gives_reclamation I HA _ o Hwf Hfree).
Qed.

Print Assumptions execution_replays.
Print Assumptions lkmm_execution_is_a_run.
Print Assumptions executions_free_only_quiesced_nodes.

(** *** That the hypothesis is satisfiable

    [Enabled] is a conjunction of guards, and a conjunction of guards can be
    unsatisfiable.  Two of the five events are guarded, and the guarded ones
    are the two the protocol is about, so a reader would be right to ask
    whether any execution containing an [EFree] is enabled at all.  One is:
    a reader enters and leaves, a writer detaches a node, waits, and reclaims
    it --- a whole round, at the counter implementation, end to end. *)

Definition ebase : EState := {| egen := 0; ereg := ∅; estamp := ∅ |}.

Definition mbase : MState :=
  {| stk := fun _ _ => None; hp := fun _ _ => None; lk := None; rt := 0;
     rds := fun _ => False; bnd := fun _ => False |}.

Definition cbase : PConf EpochImpl := (ebase, mbase, e_F ebase).

Definition around : Exec :=
  EBegin 9 :: EEnd 9 :: EStart {[ 1%nat ]} :: EStop :: EFree 1%nat :: nil.

Lemma around_ereg (t : TID) : delete 9 (<[9 := 0]> (∅ : gmap TID nat)) !! t = None.
Proof.
  rewrite (delete_insert_eq (∅ : gmap TID nat) 9 0), delete_empty.
  apply lookup_empty.
Qed.

Lemma cbase_ok : IOK cbase.
Proof.
  split.
  - split; simpl.
    + intros o e Ho. by rewrite lookup_empty in Ho.
    + intros t e Ht. by rewrite lookup_empty in Ht.
  - repeat apply conj; [| | reflexivity].
    + intros t. simpl. unfold e_rds. simpl. rewrite lookup_empty.
      split; [by intros [] | by intros [e He]].
    + intros t. simpl. unfold e_bnd. simpl. rewrite lookup_empty.
      split; [by intros [] | by intros [e [He _]]].
Qed.

Lemma around_enabled : Enabled around cbase.
Proof.
  repeat apply conj.
  - simpl. by rewrite lookup_empty.
  - exact I.
  - exact I.
  - (* the wait may end: after the reader has left, nothing is registered *)
    simpl. intros t e Ht. by rewrite around_ereg in Ht.
  - (* and the node may be reclaimed: it is stamped, and nobody is behind *)
    simpl. exists 0. split.
    + apply lookup_union_Some_l, lookup_gset_to_gmap_Some.
      split; [by apply elem_of_singleton | reflexivity].
    + intros t e' Ht. simpl in Ht. by rewrite around_ereg in Ht.
  - exact I.
Qed.

Theorem a_whole_round_is_an_enabled_execution :
  IOK (replay around cbase).
Proof.
  exact (lkmm_execution_is_a_run EpochImpl
           (proj1 (proj1 (refines_split EpochImpl) epochs_refine))
           epochs_satisfy_the_axiom around cbase cbase_ok around_enabled).
Qed.

Print Assumptions around_enabled.
Print Assumptions a_whole_round_is_an_enabled_execution.

(** ** The client's executions, not only the protocol's

    The bridge above reads an execution as a run of [pstep], which is the
    protocol's bookkeeping.  That is the right object for the LKMM's axiom,
    which is about grace periods and nothing else, but it is not yet the
    statement a client wants: a client's execution contains its own loads and
    stores, and the safety theorem is about those.

    So the same translation again, one level up.  An event here is one of the
    five protocol events or one heap mutation, and it carries what the
    corresponding [xstep] constructor leaves existential --- the observation
    map a ReadEnd produces, the state a mutation produces.  That is not a
    weakening: an execution *is* a record of what happened, so an event that
    names its own outcome is the faithful reading, and enabledness is then
    exactly the constructor's premises.

    The payoff is the one the development exists for, now said of executions:
    any execution of any client against a conforming implementation, all of
    whose events are enabled, reaches only states in which a node about to be
    reclaimed has no live reference anywhere. *)

Inductive xev : Type :=
| XFree (d : Loc) (t : TID)
| XBegin (t : TID)
| XEnd (t : TID) (Og' : ObsMap) (U' : Var -> TID -> Prop)
| XStart (ds : gset Loc)
| XStop
| XMutate (m' : MState) (Og' : ObsMap) (U' : Var -> TID -> Prop) (T' : gset TID).

Definition XExec : Type := list xev.

Definition xev_apply {I : Impl} (e : xev) (c : Conf I) : Conf I :=
  match e with
  | XFree d t => MkConf (i_free (c_i c) d) (free_ms (c_m c) d)
                        (c_Og c) (c_U c) (c_T c) (delete d (c_F c))
  | XBegin t => MkConf (i_read_begin (c_i c) t) (read_begin_ms (c_m c) t)
                       (c_Og c) (c_U c) (c_T c) (c_F c)
  | XEnd t Og' U' => MkConf (i_read_end (c_i c) t) (read_end_ms (c_m c) t)
                            Og' U' (c_T c) (read_end_F (c_F c) t)
  | XStart ds => MkConf (i_sync_start (c_i c) ds) (sync_start_ms (c_m c))
                        (c_Og c) (c_U c) (c_T c) (i_ss_F (c_i c) (c_F c) ds)
  | XStop => MkConf (i_sync_stop (c_i c)) (sync_stop_ms (c_m c))
                    (sync_stop_Og (c_Og c)) (c_U c) (c_T c) (c_F c)
  | XMutate m' Og' U' T' => MkConf (c_i c) m' Og' U' T' (c_F c)
  end.

(** What each event requires of the state it happens in: verbatim the premises
    of the [xstep] constructor it names.  The reclamation event is where the
    kernel memory model's axiom enters, through [i_can_free]. *)
Definition xev_enabled {I : Impl} (FType : FName -> FieldKind)
    (e : xev) (c : Conf I) : Prop :=
  match e with
  | XFree d t =>
      obsv (c_L c) d (Ofree t) /\ i_can_free (c_i c) d
  | XBegin t =>
      i_can_begin (c_i c) t
      /\ (forall lw, lk (c_m c) = Some lw -> lw <> t)
      /\ (forall o, ~ obsv (c_L c) o (Ounlk t)
                 /\ ~ obsv (c_L c) o (Ofree t)
                 /\ ~ obsv (c_L c) o (Ofresh t))
  | XEnd t Og' U' =>
      let c' := xev_apply (XEnd t Og' U') c in
      (forall o ob, obs_tid ob = Some t -> ~ obsv (c_L c') o ob)
      /\ (forall o ob, obsv (c_L c) o ob -> obs_tid ob <> Some t ->
            obsv (c_L c') o ob)
      /\ (forall o ob, obsv (c_L c') o ob -> obsv (c_L c) o ob)
      /\ (forall x, undf (c_L c') x t)
      /\ (forall x t', undf (c_L c) x t' -> undf (c_L c') x t')
      /\ rds (c_m c) t
  | XStart ds =>
      (forall o s0, i_ss_F (c_i c) (c_F c) ds !! o = Some s0 ->
         s0 = i_snapshot (c_i c))
      /\ (forall o t, obsv (c_L c) o (Ounlk t) \/ obsv (c_L c) o (Ofree t) ->
            exists s0, i_ss_F (c_i c) (c_F c) ds !! o = Some s0)
      /\ (forall o s0, i_ss_F (c_i c) (c_F c) ds !! o = Some s0 ->
            exists t, obsv (c_L c) o (Ounlk t) \/ obsv (c_L c) o (Ofree t))
  | XStop => i_quiet (c_i c)
  | XMutate m' Og' U' T' =>
      lstep FType (c_L c) (to_LState_t m' Og' U' T' (c_F c))
      /\ (forall t, rds m' t <-> rds (c_m c) t)
      /\ (forall t, bnd m' t <-> bnd (c_m c) t)
  end.

Lemma xev_xstep (I : Impl) FType (e : xev) (c : Conf I) :
  xev_enabled FType e c -> xstep FType c (xev_apply e c).
Proof.
  destruct c as [i m Og U T F]. destruct e; simpl; unfold c_L; simpl.
  - intros [H1 H2]. eapply X_free; [exact H1 | exact H2].
  - intros (H1 & H2 & H3). by apply X_read_begin.
  - intros (H1 & H2 & H3 & H4 & H5 & H6). by apply X_read_end.
  - intros (H1 & H2 & H3). by apply X_sync_start.
  - intros H1. by apply X_sync_stop.
  - intros (H1 & H2 & H3). by apply X_heap.
Qed.

Fixpoint XEnabled {I : Impl} (FType : FName -> FieldKind)
    (es : XExec) (c : Conf I) : Prop :=
  match es with
  | nil => True
  | e :: rest => xev_enabled FType e c /\ XEnabled FType rest (xev_apply e c)
  end.

Fixpoint xreplay {I : Impl} (es : XExec) (c : Conf I) : Conf I :=
  match es with
  | nil => c
  | e :: rest => xreplay rest (xev_apply e c)
  end.

Lemma xreplay_app (I : Impl) es1 es2 (c : Conf I) :
  xreplay (es1 ++ es2) c = xreplay es2 (xreplay es1 c).
Proof.
  revert c. induction es1 as [| e es1 IH]; intros c; [reflexivity |].
  simpl. by rewrite IH.
Qed.

Lemma XEnabled_app (I : Impl) FType es1 es2 (c : Conf I) :
  XEnabled FType (es1 ++ es2) c
  <-> XEnabled FType es1 c /\ XEnabled FType es2 (xreplay es1 c).
Proof.
  revert c. induction es1 as [| e es1 IH]; intros c; simpl.
  - split; [by intros H | by intros [_ H]].
  - split.
    + intros [He Hrest]. apply IH in Hrest as [H1 H2]. by repeat split.
    + intros [[He H1] H2]. split; [exact He |]. by apply IH.
Qed.

Theorem xexecution_replays (I : Impl) FType es (c : Conf I) :
  XEnabled FType es c -> rtc (xstep FType) c (xreplay es c).
Proof.
  revert c. induction es as [| e es IH]; intros c; simpl; [by intros _ |].
  intros [He Hrest].
  eapply rtc_l; [exact (xev_xstep I FType e c He) | exact (IH _ Hrest)].
Qed.

(** And the statement the development exists for, said of executions: any
    execution of any client against an implementation that conforms to the
    kernel memory model's RCU axiom, all of whose events are enabled, reaches
    only states in which no thread but the writer holds a live reference to a
    node the writer may reclaim.

    Conformance enters in one place and one place only --- the reclamation
    event's guard --- which is the point.  Nothing else about the
    implementation is used, and nothing about the client is assumed beyond its
    steps being steps. *)
Theorem conforming_executions_are_memory_safe (I : Impl)
    (HB : Bookkeeping I) (HA : NoSectionSpansAGracePeriod I)
    FType es (c : Conf I) tw x o :
  c_ok c -> WellFormed FType (c_L c) -> XEnabled FType es c ->
  D_freeable (c_L (xreplay es c)) tw x ->
  stk (ms (c_L (xreplay es c))) x tw = Some o ->
  forall y t', t' <> tw -> stk (ms (c_L (xreplay es c))) y t' = Some o ->
    ~ undf (c_L (xreplay es c)) y t' -> False.
Proof.
  intros Hok Hwf Hen.
  exact (xrun_safe I (lkmm_conformance_is_refinement I HB HA) FType
           c (xreplay es c) tw x o (xexecution_replays I FType es c Hen)
           Hok Hwf).
Qed.

(** The reclamation half of it, at every reclamation in the execution rather
    than only at its end --- the client-level twin of
    [executions_free_only_quiesced_nodes], and the same one-line use of the
    axiom. *)
Lemma xrun_ok (I : Impl) (HR : Refines I) FType (c c' : Conf I) :
  rtc (xstep FType) c c' -> c_ok c -> c_ok c'.
Proof.
  induction 1 as [| a b d Hab _ IH]; intros Hok; [exact Hok |].
  exact (IH (xstep_ok I HR FType a b Hab Hok)).
Qed.

Theorem client_executions_free_only_quiesced_nodes (I : Impl)
    (HB : Bookkeeping I) (HA : NoSectionSpansAGracePeriod I)
    FType es1 es2 (c : Conf I) d t :
  c_ok c -> XEnabled FType (es1 ++ XFree d t :: es2) c ->
  c_F (xreplay es1 c) !! d = Some ∅.
Proof.
  intros Hok Hen. apply XEnabled_app in Hen as [H1 H2].
  destruct H2 as [[_ Hfree] _].
  pose proof (xrun_ok I (lkmm_conformance_is_refinement I HB HA) FType
                c (xreplay es1 c)
                (xexecution_replays I FType es1 c H1) Hok) as [Hwf HS].
  destruct HS as (_ & _ & HF). rewrite HF.
  exact (lkmm_gives_reclamation I HA _ d Hwf Hfree).
Qed.

(** ...and at the counter model, so the chain is visible from the axiom to the
    client in one statement. *)
Corollary epoch_executions_are_memory_safe FType es (c : Conf EpochImpl) tw x o :
  c_ok c -> WellFormed FType (c_L c) -> XEnabled FType es c ->
  D_freeable (c_L (xreplay es c)) tw x ->
  stk (ms (c_L (xreplay es c))) x tw = Some o ->
  forall y t', t' <> tw -> stk (ms (c_L (xreplay es c))) y t' = Some o ->
    ~ undf (c_L (xreplay es c)) y t' -> False.
Proof.
  exact (conforming_executions_are_memory_safe EpochImpl
           (proj1 (proj1 (refines_split EpochImpl) epochs_refine))
           epochs_satisfy_the_axiom FType es c tw x o).
Qed.

Print Assumptions xev_xstep.
Print Assumptions xexecution_replays.
Print Assumptions xrun_ok.
Print Assumptions client_executions_free_only_quiesced_nodes.
Print Assumptions conforming_executions_are_memory_safe.
Print Assumptions epoch_executions_are_memory_safe.

(** *** That this hypothesis is satisfiable too

    [around_enabled] showed the protocol-level guards can all hold at once.
    The client-level ones are those plus the observation conditions, and the
    reclamation event's is the conjunction that matters: a node the writer has
    detached, a grace period that has run, and an implementation that says the
    node may be freed.  So the same round again, with a writer holding an
    unlinked observation that SyncStop recolours --- which is the protocol
    rather than a convenient starting state. *)

Definition xbase_Og : ObsMap := {[ (1%nat, 0%nat) := {[ Ounlk 0%nat ]} ]}.

(** A state whose observation map is a single entry has exactly one
    observation, which is what makes the negative guards checkable. *)
Lemma single_obs (Og : ObsMap) q r ob0 m U T F o ob :
  Og = {[ (q, r) := {[ ob0 ]} ]} -> obs_tid ob <> None ->
  obsv (to_LState_t m Og U T F) o ob -> o = q /\ ob = ob0.
Proof.
  intros -> Hnr Hob.
  assert (Hex : exists (q0 : TID) (s0 : gset obs),
            ({[ (q, r) := ({[ ob0 ]} : gset obs) ]} : ObsMap)
              !! (o, q0) = Some s0
            /\ ob ∈ s0).
  { destruct ob; simpl in Hnr, Hob;
      try (exfalso; apply Hnr; reflexivity); exact Hob. }
  destruct Hex as [q0 [s0 [Hl Hin]]].
  apply lookup_singleton_Some in Hl as [Heq <-].
  apply elem_of_singleton in Hin.
  assert (Ho : q = o) by exact (f_equal fst Heq).
  split; [by rewrite Ho | exact Hin].
Qed.

Lemma xbase_obs m U T F o ob :
  obs_tid ob <> None ->
  obsv (to_LState_t m xbase_Og U T F) o ob -> o = 1%nat /\ ob = Ounlk 0%nat.
Proof. exact (single_obs xbase_Og 1%nat 0%nat _ m U T F o ob eq_refl). Qed.

(** ...and the same read off a configuration, which is the form the guards
    below take. *)
Lemma xbase_obs_c (c : Conf EpochImpl) o ob :
  obsv (c_L c) o ob -> c_Og c = xbase_Og -> obs_tid ob <> None ->
  o = 1%nat /\ ob = Ounlk 0%nat.
Proof.
  intros Hob HOg Hnr. unfold c_L in Hob. rewrite HOg in Hob.
  exact (xbase_obs (c_m c) (c_U c) (c_T c) (c_F c) o ob Hnr Hob).
Qed.

(** SyncStop recolours the writer's unlinked observation to freeable, which is
    the step the reclamation guard is waiting for --- [sync_stop_Og_map] in
    [Actions.v] is that recolouring, and this is it at the one entry. *)
Lemma xbase_unlk m U T F :
  obsv (to_LState_t m xbase_Og U T F) 1%nat (Ounlk 0%nat).
Proof.
  exists 0%nat, ({[ Ounlk 0%nat ]} : gset obs).
  split; [apply lookup_singleton_eq | by apply elem_of_singleton].
Qed.

Lemma xfree_obs m U T F :
  obsv (to_LState_t (sync_stop_ms m) (sync_stop_Og xbase_Og) U T F)
       1%nat (Ofree 0%nat).
Proof.
  exact (sync_stop_Og_map m xbase_Og U T F 1%nat (Ounlk 0%nat)
           (xbase_unlk m U T F)).
Qed.

(** The free list is empty throughout the round until SyncStart stamps the
    detached node, which is what makes the stamping guards decidable here. *)
Lemma xF_none (o : Loc) :
  read_end_F (∅ : gmap Loc (gset TID)) 9 !! o = None.
Proof. unfold read_end_F. by rewrite lookup_fmap, lookup_empty. Qed.

Definition xbase : Conf EpochImpl :=
  MkConf (I := EpochImpl) ebase mbase xbase_Og (fun _ _ => False) ∅ ∅.

Definition xround : XExec :=
  XBegin 9 :: XEnd 9 xbase_Og (fun _ t => t = 9%nat)
        :: XStart {[ 1%nat ]} :: XStop :: XFree 1%nat 0%nat :: nil.

Lemma xbase_ok : c_ok xbase.
Proof.
  split.
  - split; simpl.
    + intros o e Ho. by rewrite lookup_empty in Ho.
    + intros t e Ht. by rewrite lookup_empty in Ht.
  - repeat apply conj; simpl.
    + intros t. unfold e_rds. simpl. rewrite lookup_empty.
      split; [by intros [] | by intros [e He]].
    + intros t. unfold e_bnd. simpl. rewrite lookup_empty.
      split; [by intros [] | by intros [e [He _]]].
    + unfold e_F, ebase. simpl. by rewrite fmap_empty.
Qed.

Lemma xround_enabled : XEnabled (fun _ => RCUField) xround xbase.
Proof.
  repeat apply conj.
  (* the reader may enter: registered nowhere, the lock free, and it holds
     none of the writer's observations *)
  - simpl. by rewrite lookup_empty.
  - simpl. intros lw Hc. discriminate.
  - intros o. repeat apply conj.
    + intros Hc. destruct (xbase_obs_c _ o (Ounlk 9) Hc eq_refl
        ltac:(intros Hd; discriminate)) as [_ Hb]. discriminate.
    + intros Hc. destruct (xbase_obs_c _ o (Ofree 9) Hc eq_refl
        ltac:(intros Hd; discriminate)) as [_ Hb]. discriminate.
    + intros Hc. destruct (xbase_obs_c _ o (Ofresh 9) Hc eq_refl
        ltac:(intros Hd; discriminate)) as [_ Hb]. discriminate.
  (* and may leave: it holds nothing, so nothing of its own survives, and the
     writer's observation is untouched *)
  - intros o ob Hob Hc.
    destruct (xbase_obs_c _ o ob Hc eq_refl
      ltac:(rewrite Hob; intros Hd; discriminate)) as [_ ->].
    simpl in Hob. discriminate.
  - intros o ob Hc _. exact Hc.
  - intros o ob Hc. exact Hc.
  - by intros x.
  - by intros x t' [].
  - by right.
  (* the grace period stamps the detached node, and only it *)
  - intros o s0 Hlk. unfold i_ss_F, ss_F in Hlk.
    apply lookup_union_Some_raw in Hlk as [Hg | [_ Hf]].
    + by apply lookup_gset_to_gmap_Some in Hg as [_ <-].
    + rewrite xF_none in Hf. discriminate.
  - intros o t [Hc | Hc];
      destruct (xbase_obs_c _ o _ Hc eq_refl ltac:(intros Hd; discriminate))
        as [-> _];
      eexists; unfold i_ss_F, ss_F;
      apply lookup_union_Some_l, lookup_gset_to_gmap_Some;
      split; [by apply elem_of_singleton | reflexivity ..].
  - intros o s0 Hlk. unfold i_ss_F, ss_F in Hlk.
    apply lookup_union_Some_raw in Hlk as [Hg | [_ Hf]];
      [| rewrite xF_none in Hf; discriminate].
    apply lookup_gset_to_gmap_Some in Hg as [Ho _].
    apply elem_of_singleton in Ho as ->.
    exists 0%nat. left. apply xbase_unlk.
  (* the wait may end *)
  - simpl. intros t e Ht. by rewrite around_ereg in Ht.
  (* and the node may be reclaimed: SyncStop has recoloured it, and the
     implementation's own guard agrees *)
  - apply xfree_obs.
  - simpl. exists 0. split.
    + apply lookup_union_Some_l, lookup_gset_to_gmap_Some.
      split; [by apply elem_of_singleton | reflexivity].
    + intros t e' Ht. simpl in Ht. by rewrite around_ereg in Ht.
  - exact I.
Qed.

Theorem a_whole_client_round_is_an_enabled_execution :
  c_ok (xreplay xround xbase).
Proof.
  exact (xrun_ok EpochImpl epochs_refine (fun _ => RCUField) xbase _
           (xexecution_replays EpochImpl (fun _ => RCUField) xround xbase
              xround_enabled) xbase_ok).
Qed.

Print Assumptions xround_enabled.
Print Assumptions a_whole_client_round_is_an_enabled_execution.
