(** * Registration with an epoch, and why the counter is incremented

    ReadEnd is the one rule in the system that writes state another thread owns.
    A reader leaving its critical section must be taken out of every free-list
    snapshot it appears in, and the snapshots belong to the writer that created
    them.

    The reason it has to is that a snapshot names threads.  This file asks what
    happens if the registration carries *when* a reader registered, and the
    snapshot carries *when* the node was unlinked, so that a snapshot names no
    threads at all.  That is what an implementation's grace-period counter does
    -- Tassarotti's QSBR verification and the comparison in the related work
    both describe it -- and the question here is what it costs and what it buys
    as a model.

    It buys three things, and each is a theorem below.  ReadEnd becomes a write
    to the departing thread's own registration and nothing else, and that single
    write removes it from the readers, from the bounding threads, and from every
    snapshot at once.  Re-entry is safe, and the reason is precisely the
    increment: a reader that leaves and starts again registers at a later epoch
    than any grace period already running, so it cannot rejoin one.  And the
    bookkeeping still satisfies the invariants the snapshot model is stated
    over, so this is a refinement of that model rather than a different system.

    [increment_is_what_makes_reentry_safe] is the contrast: without the
    increment, re-entry rejoins, which is the same failure as reading a
    snapshot against the current readers. *)

From stdpp Require Import gmap sets.
From RCU Require Import WellFormed Actions.

(** ** The state

    [egen] is the global counter, [ereg] each thread's registration -- [None]
    outside a read-side critical section, [Some e] inside one entered at epoch
    [e] -- and [estamp] records, for a node awaiting reclamation, the epoch at
    which its grace period began. *)
Record EState := {
  egen   : nat;
  ereg   : gmap TID nat;    (* registered readers, and the epoch each entered at *)
  estamp : gmap Loc nat     (* nodes awaiting reclamation, and their grace epoch *)
}.

Definition e_begin (s : EState) (t : TID) : EState :=
  {| egen := egen s; ereg := <[t := egen s]> (ereg s); estamp := estamp s |}.

Definition e_end (s : EState) (t : TID) : EState :=
  {| egen := egen s; ereg := delete t (ereg s); estamp := estamp s |}.

(** SyncStart stamps the detached nodes with the current epoch and then
    increments it.  The increment is the whole of the repair; see
    [reentry_safe] and [increment_is_what_makes_reentry_safe]. *)
Definition e_sync_start (s : EState) (ds : gset Loc) : EState :=
  {| egen := S (egen s); ereg := ereg s;
     estamp := gset_to_gmap (egen s) ds ∪ estamp s |}.

(** ** The readings

    The three components of the published model, recovered from the counters.
    A snapshot's members are the readers that registered no later than the
    grace period began: derived, not stored. *)
Definition e_rds (s : EState) (t : TID) : Prop := is_Some (ereg s !! t).

Definition e_bnd (s : EState) (t : TID) : Prop :=
  exists e, ereg s !! t = Some e /\ e < egen s.

Definition e_snapshot (s : EState) (e : nat) : gset TID :=
  dom (filter (fun kv => kv.2 <= e) (ereg s)).

Definition e_F (s : EState) : gmap Loc (gset TID) := e_snapshot s <$> estamp s.

Lemma e_snapshot_elem s e t :
  t ∈ e_snapshot s e <-> exists e', ereg s !! t = Some e' /\ e' <= e.
Proof.
  unfold e_snapshot. rewrite elem_of_dom. split.
  - intros [e' Hlk]. apply map_lookup_filter_Some in Hlk as [Hlk Hle].
    by exists e'.
  - intros [e' [Hlk Hle]]. exists e'.
    apply map_lookup_filter_Some. by split.
Qed.

Definition e_flist (s : EState) (o : Loc) : option (TID -> Prop) :=
  match estamp s !! o with
  | Some e => Some (fun t => t ∈ e_snapshot s e)
  | None   => None
  end.

(** ** The one invariant the counters need

    Stamps are in the past and registrations are not in the future.  Both hold
    by construction; the point of stating them is that [reentry_safe] is where
    they are used. *)
Definition EWF (s : EState) : Prop :=
  (forall o e, estamp s !! o = Some e -> e < egen s)
  /\ (forall t e, ereg s !! t = Some e -> e <= egen s).

Lemma EWF_begin s t : EWF s -> EWF (e_begin s t).
Proof.
  intros [Hs Hr]. split; [exact Hs |].
  intros t' e H. simpl in H.
  destruct (decide (t' = t)) as [-> | Hne].
  - rewrite lookup_insert_eq in H. injection H as <-. reflexivity.
  - rewrite lookup_insert_ne in H; [| exact (fun Hc => Hne (eq_sym Hc))].
    exact (Hr t' e H).
Qed.

Lemma EWF_end s t : EWF s -> EWF (e_end s t).
Proof.
  intros [Hs Hr]. split; [exact Hs |].
  intros t' e H. simpl in H.
  destruct (decide (t' = t)) as [-> | Hne].
  - by rewrite lookup_delete_eq in H.
  - rewrite lookup_delete_ne in H; [| exact (fun Hc => Hne (eq_sym Hc))].
    exact (Hr t' e H).
Qed.

Lemma EWF_sync_start s ds : EWF s -> EWF (e_sync_start s ds).
Proof.
  intros [Hs Hr]. split.
  - intros o e H. simpl in H.
    apply lookup_union_Some_raw in H as [H | [_ H]].
    + apply lookup_gset_to_gmap_Some in H as [_ <-]. constructor.
    + exact (Nat.lt_lt_succ_r _ _ (Hs o e H)).
  - intros t e H. exact (Nat.le_le_succ_r _ _ (Hr t e H)).
Qed.

(** ** ReadEnd is local

    It writes the departing thread's own registration and nothing else. *)
Theorem e_end_writes_only_its_own s t :
  egen (e_end s t) = egen s
  /\ estamp (e_end s t) = estamp s
  /\ (forall t', t' <> t -> ereg (e_end s t) !! t' = ereg s !! t').
Proof.
  repeat apply conj; [reflexivity | reflexivity |].
  intros t' Hne. simpl. rewrite lookup_delete_ne;
    [reflexivity | exact (fun Hc => Hne (eq_sym Hc))].
Qed.

(** And that one write is exactly the three updates the published ReadEnd
    performs as three: the thread leaves [R], leaves [B], and leaves every
    snapshot.  The third is the one it had no right to make. *)
Lemma e_snapshot_end s t e :
  e_snapshot (e_end s t) e = e_snapshot s e ∖ {[t]}.
Proof.
  apply set_eq. intros t'.
  rewrite elem_of_difference, elem_of_singleton.
  repeat rewrite e_snapshot_elem. simpl.
  destruct (decide (t' = t)) as [-> | Hne].
  - rewrite lookup_delete_eq. split.
    + by intros [e' [Hc _]].
    + intros [_ Hc]. by destruct (Hc eq_refl).
  - rewrite lookup_delete_ne; [| exact (fun Hc => Hne (eq_sym Hc))].
    split; [intros H; by split | by intros [H _]].
Qed.

Theorem e_end_is_read_end s t :
  (forall t', e_rds (e_end s t) t' <-> (e_rds s t' /\ t' <> t))
  /\ (forall t', e_bnd (e_end s t) t' <-> (e_bnd s t' /\ t' <> t))
  /\ e_F (e_end s t) = read_end_F (e_F s) t.
Proof.
  repeat apply conj.
  - intros t'. unfold e_rds. simpl.
    destruct (decide (t' = t)) as [-> | Hne].
    + rewrite lookup_delete_eq. split.
      * by intros [e Hc].
      * intros [_ Hc]. by destruct (Hc eq_refl).
    + rewrite lookup_delete_ne; [| exact (fun Hc => Hne (eq_sym Hc))].
      split; [intros H; by split | by intros [H _]].
  - intros t'. unfold e_bnd. simpl.
    destruct (decide (t' = t)) as [-> | Hne].
    + rewrite lookup_delete_eq. split.
      * by intros [e [Hc _]].
      * intros [_ Hc]. by destruct (Hc eq_refl).
    + rewrite lookup_delete_ne; [| exact (fun Hc => Hne (eq_sym Hc))].
      split; [intros H; by split | by intros [H _]].
  - unfold e_F, read_end_F. rewrite <- map_fmap_compose.
    apply map_fmap_ext. intros o e _. exact (e_snapshot_end s t e).
Qed.

(** Said against the model's own step.  [read_end_ms] and [read_end_F] are what
    the action theorem [read_end_preserves_WellFormed] is stated over; this says
    that transition is exactly what deleting the departing thread's
    registration produces.  So the epoch state is not a different system with
    similar properties -- it is a representation of the same one in which
    ReadEnd has nothing to write but its own. *)
Corollary e_end_realises_read_end m s t :
  (forall t', rds m t' <-> e_rds s t') ->
  (forall t', bnd m t' <-> e_bnd s t') ->
  (forall t', rds (read_end_ms m t) t' <-> e_rds (e_end s t) t')
  /\ (forall t', bnd (read_end_ms m t) t' <-> e_bnd (e_end s t) t')
  /\ read_end_F (e_F s) t = e_F (e_end s t).
Proof.
  intros Hr Hb.
  destruct (e_end_is_read_end s t) as (Hrds & Hbnd & HF).
  repeat apply conj; [| | exact (eq_sym HF)].
  - intros t'. rewrite Hrds. simpl. split.
    + intros [H Hne]. split; [by apply Hr | exact Hne].
    + intros [H Hne]. split; [by apply Hr | exact Hne].
  - intros t'. rewrite Hbnd. simpl. split.
    + intros [H Hne]. split; [by apply Hb | exact Hne].
    + intros [H Hne]. split; [by apply Hb | exact Hne].
Qed.

(** ReadBegin joins nothing, and so leaves the free list alone -- which is what
    the published rule does too.  A reader registers at the current epoch and
    every running grace period was stamped earlier, so it is in no snapshot.
    The published model has to arrange this by removing threads from snapshots
    as they leave. *)
Lemma e_snapshot_begin s t e :
  ereg s !! t = None -> e < egen s ->
  e_snapshot (e_begin s t) e = e_snapshot s e.
Proof.
  intros Hnone Hlt. apply set_eq. intros t'.
  repeat rewrite e_snapshot_elem. simpl.
  destruct (decide (t' = t)) as [-> | Hne].
  - rewrite lookup_insert_eq. split.
    + intros [e' [H Hle]]. injection H as <-.
      exfalso. exact (Nat.lt_irrefl e (Nat.lt_le_trans _ _ _ Hlt Hle)).
    + intros [e' [H _]]. by rewrite Hnone in H.
  - rewrite lookup_insert_ne; [reflexivity | exact (fun Hc => Hne (eq_sym Hc))].
Qed.

Theorem e_begin_keeps_the_free_list s t :
  EWF s -> ereg s !! t = None -> e_F (e_begin s t) = e_F s.
Proof.
  intros [Hs _] Hnone. unfold e_F.
  apply map_fmap_ext. intros o e Hlk.
  exact (e_snapshot_begin s t e Hnone (Hs o e Hlk)).
Qed.

Theorem e_begin_joins_nothing s t :
  EWF s -> forall o e, estamp s !! o = Some e -> t ∉ e_snapshot (e_begin s t) e.
Proof.
  intros HWF o e Hlk Hin. apply e_snapshot_elem in Hin as [e' [H Hle]].
  simpl in H. rewrite lookup_insert_eq in H. injection H as <-.
  exact (Nat.lt_irrefl e (Nat.lt_le_trans _ _ _ (proj1 HWF o e Hlk) Hle)).
Qed.

(** SyncStart's entry is the current reader set, which is what the published
    rule says it is.  So the three steps correspond exactly, and the only
    difference is which of them has to write what. *)
Theorem e_sync_start_snapshot s ds o :
  EWF s -> o ∈ ds -> e_F (e_sync_start s ds) !! o = Some (dom (ereg s)).
Proof.
  intros [_ Hr] Hin. unfold e_F. rewrite lookup_fmap. simpl.
  assert (Hst : (gset_to_gmap (egen s) ds ∪ estamp s) !! o = Some (egen s)).
  { apply lookup_union_Some_l, lookup_gset_to_gmap_Some. by split. }
  rewrite Hst. simpl. f_equal. apply set_eq. intros t.
  rewrite e_snapshot_elem, elem_of_dom. simpl. split.
  - by intros [e' [H _]].
  - intros [e' H]. exists e'. split; [exact H | exact (Hr t e' H)].
Qed.

(** ** Re-entry is safe, and the increment is why

    A reader that leaves a critical section and starts a new one registers at
    the epoch the last SyncStart moved the counter to, which is later than the
    epoch any running grace period was stamped with.  So it joins none of them.

    This is the failure of the cheaper repair, fixed: reading a snapshot against
    the current readers puts a returning thread back into every snapshot it was
    ever in, because a thread identity is reused and an epoch is not. *)
Theorem reentry_safe s ds t o e :
  EWF s ->
  estamp (e_sync_start s ds) !! o = Some e ->
  t ∉ e_snapshot (e_begin (e_end (e_sync_start s ds) t) t) e.
Proof.
  intros HWF Hst.
  apply (e_begin_joins_nothing _ t
           (EWF_end _ t (EWF_sync_start s ds HWF)) o e Hst).
Qed.

(** Without the increment the same sequence rejoins, which is the defect the
    epoch is there to remove.  One concrete state suffices. *)
Definition e_sync_start_nobump (s : EState) (ds : gset Loc) : EState :=
  {| egen := egen s; ereg := ereg s;
     estamp := gset_to_gmap (egen s) ds ∪ estamp s |}.

Definition e0 : EState :=
  {| egen := 0; ereg := {[ 9 := 0 ]}; estamp := ∅ |}.

Lemma e0_EWF : EWF e0.
Proof.
  split.
  - intros o e H. simpl in H. by rewrite lookup_empty in H.
  - intros t e H. simpl in H.
    apply lookup_singleton_Some in H as [_ <-]. constructor.
Qed.

Theorem increment_is_what_makes_reentry_safe :
  9 ∈ e_snapshot (e_begin (e_end (e_sync_start_nobump e0 {[1]}) 9) 9) 0
  /\ 9 ∉ e_snapshot (e_begin (e_end (e_sync_start e0 {[1]}) 9) 9) 0.
Proof.
  split.
  - apply e_snapshot_elem. exists 0.
    split; [simpl; by rewrite lookup_insert_eq | constructor].
  - apply (reentry_safe e0 {[1]} 9 1 0 e0_EWF).
    simpl. apply lookup_union_Some_l, lookup_gset_to_gmap_Some.
    split; [by apply elem_of_singleton | reflexivity].
Qed.

(** ** The wait, and what it licenses

    SyncStop's condition, and the conjunct [freeable]'s denotation asks for.
    Nothing here says the wait terminates -- that needs an operational
    semantics, as it did before -- but what it establishes is now a consequence
    of the counters rather than an argument about set membership. *)
Definition e_quiescent (s : EState) (e : nat) : Prop :=
  forall t e', ereg s !! t = Some e' -> e < e'.

Theorem e_quiescent_entry_empty s o e :
  estamp s !! o = Some e -> e_quiescent s e -> e_snapshot s e = ∅.
Proof.
  intros Hst Hq. apply set_eq. intros t.
  rewrite e_snapshot_elem, elem_of_empty. split; [| by intros []].
  intros [e' [Hr Hle]]. exfalso.
  exact (Nat.lt_irrefl e (Nat.lt_le_trans _ _ _ (Hq t e' Hr) Hle)).
Qed.

(** ** Quiescence is stable, which is the other half of the ownership story

    The reader's half is that ReadEnd writes only its own registration.  The
    writer's half is the converse problem: Free needs to know a snapshot is
    empty, and under the published model it knows that by *owning* the entry --
    which is what made the entry the writer's resource and the reader's write
    illegal.

    With epochs it does not have to own anything, because quiescence past an
    epoch is *stable*: once every registration is later than [e], every
    registration stays later than [e], under all four steps.  Registrations only
    ever get newer, because a reader enters at the current epoch and the counter
    never goes backwards.

    That is what makes the wait's result a fact the writer can simply keep.  In
    the resource reading a stable fact needs no exclusive ownership -- it may be
    duplicated and carried -- so SyncStop can hand Free a certificate rather
    than a resource, and the free list stops needing to be anybody's property.
    Between this and [e_end_is_read_end] the ownership objection is answered at
    both ends. *)

Lemma e_quiescent_begin s t e :
  e < egen s -> e_quiescent s e -> e_quiescent (e_begin s t) e.
Proof.
  intros Hlt Hq t' e' H. simpl in H.
  destruct (decide (t' = t)) as [-> | Hne].
  - rewrite lookup_insert_eq in H. injection H as <-. exact Hlt.
  - rewrite lookup_insert_ne in H; [| exact (fun Hc => Hne (eq_sym Hc))].
    exact (Hq t' e' H).
Qed.

Lemma e_quiescent_end s t e : e_quiescent s e -> e_quiescent (e_end s t) e.
Proof.
  intros Hq t' e' H. simpl in H.
  destruct (decide (t' = t)) as [-> | Hne].
  - by rewrite lookup_delete_eq in H.
  - rewrite lookup_delete_ne in H; [| exact (fun Hc => Hne (eq_sym Hc))].
    exact (Hq t' e' H).
Qed.

Lemma e_quiescent_sync_start s ds e :
  e_quiescent s e -> e_quiescent (e_sync_start s ds) e.
Proof. intros Hq t e' H. exact (Hq t e' H). Qed.

(** Freeing a node removes its stamp and touches no registration. *)
Definition e_free (s : EState) (o : Loc) : EState :=
  {| egen := egen s; ereg := ereg s; estamp := delete o (estamp s) |}.

Lemma e_quiescent_free s o e : e_quiescent s e -> e_quiescent (e_free s o) e.
Proof. intros Hq t e' H. exact (Hq t e' H). Qed.

(** For a node that is actually awaiting reclamation the side condition of the
    first lemma is automatic, so the certificate survives every step of the
    system without a hypothesis the writer would have to maintain. *)
Theorem quiescence_is_stable s o e :
  EWF s -> estamp s !! o = Some e -> e_quiescent s e ->
  (forall t, e_quiescent (e_begin s t) e)
  /\ (forall t, e_quiescent (e_end s t) e)
  /\ (forall ds, e_quiescent (e_sync_start s ds) e)
  /\ (forall o', e_quiescent (e_free s o') e).
Proof.
  intros HWF Hst Hq. repeat apply conj.
  - intros t. exact (e_quiescent_begin s t e (proj1 HWF o e Hst) Hq).
  - intros t. exact (e_quiescent_end s t e Hq).
  - intros ds. exact (e_quiescent_sync_start s ds e Hq).
  - intros o'. exact (e_quiescent_free s o' e Hq).
Qed.

(** And what the certificate licenses, which is exactly the conjunct the
    [freeable] denotation asks for: the snapshot is empty.  The writer reads
    this off a fact it carries, not off an entry it owns. *)
Corollary e_free_premise s o e :
  estamp s !! o = Some e -> e_quiescent s e ->
  e_F s !! o = Some ∅.
Proof.
  intros Hst Hq. unfold e_F. rewrite lookup_fmap, Hst. simpl.
  by rewrite (e_quiescent_entry_empty s o e Hst Hq).
Qed.

(** ** It is a refinement, not a replacement

    The two invariants the snapshot model states about this bookkeeping hold of
    the epoch reading, so the rules above may be read as the published ones.
    RINFL -- every thread in a snapshot is a bounding thread -- is where the
    stamp being in the past is used; BR -- every bounding thread is a reader --
    is immediate, where in the published model it is a missing invariant that
    only SyncStart establishes. *)
Theorem e_RINFL s : EWF s ->
  forall o e t, estamp s !! o = Some e -> t ∈ e_snapshot s e -> e_bnd s t.
Proof.
  intros [Hs _] o e t Hst Hin.
  apply e_snapshot_elem in Hin as [e' [Hr Hle]].
  exists e'. split; [exact Hr | exact (Nat.le_lt_trans _ _ _ Hle (Hs o e Hst))].
Qed.

Theorem e_BR s : forall t, e_bnd s t -> e_rds s t.
Proof. intros t [e [Hr _]]. by exists e. Qed.

(** And the writer never bounds its own grace period for a better reason than
    before: the lock holder is not registered at all, so the question does not
    arise. *)
Theorem e_writer_not_bounding s t :
  ereg s !! t = None -> ~ e_bnd s t.
Proof. intros H [e [Hr _]]. by rewrite H in Hr. Qed.

Print Assumptions EWF_sync_start.
Print Assumptions e_end_writes_only_its_own.
Print Assumptions e_end_is_read_end.
Print Assumptions e_end_realises_read_end.
Print Assumptions e_begin_keeps_the_free_list.
Print Assumptions e_begin_joins_nothing.
Print Assumptions e_sync_start_snapshot.
Print Assumptions reentry_safe.
Print Assumptions increment_is_what_makes_reentry_safe.
Print Assumptions e_quiescent_entry_empty.
Print Assumptions quiescence_is_stable.
Print Assumptions e_free_premise.
Print Assumptions e_RINFL.
