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
From RCU Require Import WellFormed.

(** ** The state

    [egen] is the global counter, [ereg] each thread's registration -- [None]
    outside a read-side critical section, [Some e] inside one entered at epoch
    [e] -- and [estamp] records, for a node awaiting reclamation, the epoch at
    which its grace period began. *)
Record EState := {
  egen   : nat;
  ereg   : TID -> option nat;
  estamp : Loc -> option nat
}.

Definition e_begin (s : EState) (t : TID) : EState :=
  {| egen := egen s;
     ereg := fun t' => if decide (t' = t) then Some (egen s) else ereg s t';
     estamp := estamp s |}.

Definition e_end (s : EState) (t : TID) : EState :=
  {| egen := egen s;
     ereg := fun t' => if decide (t' = t) then None else ereg s t';
     estamp := estamp s |}.

(** SyncStart stamps the detached nodes with the current epoch and then
    increments it.  The increment is the whole of the repair; see
    [reentry_safe] and [increment_is_what_makes_reentry_safe]. *)
Definition e_sync_start (s : EState) (ds : gset Loc) : EState :=
  {| egen := S (egen s);
     ereg := ereg s;
     estamp := fun o => if decide (o ∈ ds) then Some (egen s) else estamp s o |}.

(** ** The readings

    The three components of the published model, recovered from the counters.
    A snapshot's members are the readers that registered no later than the
    grace period began. *)
Definition e_rds (s : EState) (t : TID) : Prop := ereg s t <> None.

Definition e_bnd (s : EState) (t : TID) : Prop :=
  exists e, ereg s t = Some e /\ e < egen s.

Definition e_flist (s : EState) (o : Loc) : option (TID -> Prop) :=
  match estamp s o with
  | Some e => Some (fun t => exists e', ereg s t = Some e' /\ e' <= e)
  | None   => None
  end.

(** ** The one invariant the counters need

    Stamps are in the past and registrations are not in the future.  Both hold
    by construction; the point of stating them is that [reentry_safe] is where
    they are used. *)
Definition EWF (s : EState) : Prop :=
  (forall o e, estamp s o = Some e -> e < egen s)
  /\ (forall t e, ereg s t = Some e -> e <= egen s).

Lemma EWF_begin s t : EWF s -> EWF (e_begin s t).
Proof.
  intros [Hs Hr]. split.
  - intros o e H. exact (Hs o e H).
  - intros t' e H. simpl in H. destruct (decide (t' = t)) as [-> | Hne].
    + injection H as <-. reflexivity.
    + exact (Hr t' e H).
Qed.

Lemma EWF_end s t : EWF s -> EWF (e_end s t).
Proof.
  intros [Hs Hr]. split.
  - intros o e H. exact (Hs o e H).
  - intros t' e H. simpl in H. destruct (decide (t' = t)) as [-> | Hne];
      [discriminate | exact (Hr t' e H)].
Qed.

Lemma EWF_sync_start s ds : EWF s -> EWF (e_sync_start s ds).
Proof.
  intros [Hs Hr]. split.
  - intros o e H. simpl in H. destruct (decide (o ∈ ds)) as [Hin | Hni].
    + injection H as <-. constructor.
    + exact (Nat.lt_lt_succ_r _ _ (Hs o e H)).
  - intros t e H. simpl in H. exact (Nat.le_le_succ_r _ _ (Hr t e H)).
Qed.

(** ** ReadEnd is local

    It writes the departing thread's own registration and nothing else. *)
Theorem e_end_writes_only_its_own s t :
  egen (e_end s t) = egen s
  /\ (forall o, estamp (e_end s t) o = estamp s o)
  /\ (forall t', t' <> t -> ereg (e_end s t) t' = ereg s t').
Proof.
  repeat apply conj; [reflexivity | reflexivity |].
  intros t' Hne. simpl. case_decide as Hd; [by destruct (Hne Hd) | reflexivity].
Qed.

(** And that single write is all three effects the published ReadEnd performs
    as three separate updates. *)
Theorem e_end_clears s t :
  ~ e_rds (e_end s t) t
  /\ ~ e_bnd (e_end s t) t
  /\ (forall o Tr, e_flist (e_end s t) o = Some Tr -> ~ Tr t).
Proof.
  assert (Hreg : ereg (e_end s t) t = None)
    by (simpl; by case_decide).
  repeat apply conj.
  - intros H. exact (H Hreg).
  - intros [e [H _]]. rewrite Hreg in H. discriminate H.
  - intros o Tr Hfl. unfold e_flist in Hfl.
    destruct (estamp (e_end s t) o) as [e|]; [| discriminate].
    injection Hfl as <-. intros [e' [H _]].
    destruct (decide (t = t)) as [_ | Hn];
      [discriminate H | by destruct (Hn eq_refl)].
Qed.

(** Nobody else is disturbed, which is the other half of locality. *)
Theorem e_end_frames s t t' o Tr Tr' :
  t' <> t ->
  e_flist s o = Some Tr -> e_flist (e_end s t) o = Some Tr' ->
  (Tr t' <-> Tr' t').
Proof.
  intros Hne H1 H2. unfold e_flist in H1, H2. simpl in H2.
  destruct (estamp s o) as [e|]; [| discriminate].
  injection H1 as <-. injection H2 as <-.
  simpl. case_decide as Hd; [by destruct (Hne Hd) | reflexivity].
Qed.

(** One write, three updates.  The published ReadEnd performs three: the
    departing thread leaves R, leaves B, and is removed from every snapshot.
    Here the second and third are consequences of the first, which is why the
    rule becomes thread-local -- there is nothing else to write. *)
Theorem e_end_simulates s t :
  (forall t', e_rds (e_end s t) t' <-> (e_rds s t' /\ t' <> t))
  /\ (forall t', e_bnd (e_end s t) t' <-> (e_bnd s t' /\ t' <> t))
  /\ (forall o Tr Tr',
        e_flist s o = Some Tr -> e_flist (e_end s t) o = Some Tr' ->
        forall t', Tr' t' <-> (Tr t' /\ t' <> t)).
Proof.
  repeat apply conj.
  - intros t'. unfold e_rds, e_end. simpl. case_decide as Hd.
    + split; [by intros H | intros [_ H]; by destruct (H Hd)].
    + split; [by intros H | by intros [H _]].
  - intros t'. unfold e_bnd, e_end. simpl. case_decide as Hd.
    + split; [by intros [e [H _]] | intros [_ H]; by destruct (H Hd)].
    + split; [by intros H | by intros [H _]].
  - intros o Tr Tr' H1 H2 t'. unfold e_flist in H1, H2. simpl in H2.
    destruct (estamp s o) as [e|]; [| discriminate].
    injection H1 as <-. injection H2 as <-. simpl. case_decide as Hd.
    + split; [by intros [e' [H _]] | intros [_ H]; by destruct (H Hd)].
    + split; [by intros H | by intros [H _]].
Qed.

(** ReadBegin joins nothing.  A reader entering a critical section registers at
    the current epoch, and every grace period already running was stamped
    earlier, so it is in no snapshot.  This is the property the published model
    has to arrange by removing threads from snapshots as they leave; here it is
    a consequence of the counter never going backwards. *)
Theorem e_begin_joins_nothing s t :
  EWF s -> forall o Tr, e_flist (e_begin s t) o = Some Tr -> ~ Tr t.
Proof.
  intros [Hs _] o Tr Hfl. unfold e_flist in Hfl.
  destruct (estamp (e_begin s t) o) as [e|] eqn:Hst; [| discriminate].
  assert (Hst0 : estamp s o = Some e) by exact Hst.
  injection Hfl as <-. intros [e' [H Hle]]. simpl in H.
  destruct (decide (t = t)) as [_ | Hn]; [| by destruct (Hn eq_refl)].
  injection H as <-.
  exact (Nat.lt_irrefl (egen s) (Nat.le_lt_trans _ _ _ Hle (Hs o e Hst0))).
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
  estamp (e_sync_start s ds) o = Some e ->
  forall Tr, e_flist (e_begin (e_end (e_sync_start s ds) t) t) o = Some Tr
             -> ~ Tr t.
Proof.
  intros HWF Hst Tr Hfl.
  (* the stamp is at or before the epoch the grace period started in *)
  assert (Hle : e <= egen s).
  { simpl in Hst. destruct (decide (o ∈ ds)) as [Hin | Hni].
    - injection Hst as <-. constructor.
    - exact (Nat.lt_le_incl _ _ (proj1 HWF o e Hst)). }
  (* and the returning reader registers strictly after it *)
  assert (Hreg : ereg (e_begin (e_end (e_sync_start s ds) t) t) t
                   = Some (S (egen s)))
    by (simpl; by case_decide).
  assert (Hst' : estamp (e_begin (e_end (e_sync_start s ds) t) t) o = Some e)
    by exact Hst.
  unfold e_flist in Hfl; rewrite Hst' in Hfl. injection Hfl as <-.
  intros [e' [H Hle']].
  destruct (decide (t = t)) as [_ | Hn]; [| by destruct (Hn eq_refl)].
  injection H as <-.
  exact (Nat.nle_succ_diag_l (egen s) (Nat.le_trans _ _ _ Hle' Hle)).
Qed.

(** Without the increment the same sequence rejoins, which is the defect the
    epoch is there to remove.  One concrete state suffices. *)
Definition e_sync_start_nobump (s : EState) (ds : gset Loc) : EState :=
  {| egen := egen s;
     ereg := ereg s;
     estamp := fun o => if decide (o ∈ ds) then Some (egen s) else estamp s o |}.

Definition e0 : EState :=
  {| egen := 0;
     ereg := fun t => if decide (t = 9) then Some 0 else None;
     estamp := fun _ => None |}.

Lemma e0_EWF : EWF e0.
Proof.
  split.
  - intros o e H. discriminate H.
  - intros t e H. simpl in H. destruct (decide (t = 9)) as [-> | Hne];
      [injection H as <-; constructor | discriminate].
Qed.

Theorem increment_is_what_makes_reentry_safe :
  (exists Tr,
     e_flist (e_begin (e_end (e_sync_start_nobump e0 {[1]}) 9) 9) 1
       = Some Tr /\ Tr 9)
  /\ (forall Tr,
        e_flist (e_begin (e_end (e_sync_start e0 {[1]}) 9) 9) 1
          = Some Tr -> ~ Tr 9).
Proof.
  apply conj.
  - eexists. split; [reflexivity |].
    exists 0. split; [reflexivity | constructor].
  - intros Tr Hfl.
    exact (reentry_safe e0 {[1]} 9 1 0 e0_EWF eq_refl Tr Hfl).
Qed.

(** ** The wait, and what it licenses

    SyncStop's condition, and the conjunct [freeable]'s denotation asks for.
    Nothing here says the wait terminates -- that needs an operational
    semantics, as it did before -- but what it establishes is now a one-line
    consequence of the counters rather than an argument about set membership. *)
Definition e_quiescent (s : EState) (e : nat) : Prop :=
  forall t e', ereg s t = Some e' -> e < e'.

Theorem e_quiescent_entry_empty s o e Tr :
  estamp s o = Some e -> e_quiescent s e ->
  e_flist s o = Some Tr -> forall t, ~ Tr t.
Proof.
  intros Hst Hq Hfl t. unfold e_flist in Hfl; rewrite Hst in Hfl. injection Hfl as <-.
  intros [e' [Hr Hle]].
  exact (Nat.lt_irrefl e (Nat.lt_le_trans _ _ _ (Hq t e' Hr) Hle)).
Qed.

(** ** It is a refinement, not a replacement

    The two invariants the snapshot model states about this bookkeeping hold of
    the epoch reading, so the rules above may be read as the published ones.
    RINFL -- every thread in a snapshot is a bounding thread -- is where the
    stamp being in the past is used; BR -- every bounding thread is a reader --
    is immediate, where in the published model it is a missing invariant that
    only SyncStart establishes. *)
Theorem e_RINFL s : EWF s ->
  forall o Tr t, e_flist s o = Some Tr -> Tr t -> e_bnd s t.
Proof.
  intros [Hs _] o Tr t Hfl Hin. unfold e_flist in Hfl.
  destruct (estamp s o) as [e|] eqn:Hst; [| discriminate].
  injection Hfl as <-. destruct Hin as [e' [Hr Hle]].
  exists e'. split; [exact Hr |].
  exact (Nat.le_lt_trans _ _ _ Hle (Hs o e Hst)).
Qed.

Theorem e_BR s : forall t, e_bnd s t -> e_rds s t.
Proof. intros t [e [Hr _]] Hc. by rewrite Hr in Hc. Qed.

(** And the writer never bounds its own grace period for a better reason than
    before: the lock holder is not registered at all, so the question does not
    arise.  Stated as the condition on the epoch state that makes it so. *)
Theorem e_writer_not_bounding s t :
  ereg s t = None -> ~ e_bnd s t.
Proof. intros H [e [Hr _]]. by rewrite Hr in H. Qed.

Print Assumptions EWF_sync_start.
Print Assumptions e_end_writes_only_its_own.
Print Assumptions e_end_clears.
Print Assumptions e_end_frames.
Print Assumptions e_end_simulates.
Print Assumptions e_begin_joins_nothing.
Print Assumptions reentry_safe.
Print Assumptions e0_EWF.
Print Assumptions increment_is_what_makes_reentry_safe.
Print Assumptions e_quiescent_entry_empty.
Print Assumptions e_RINFL.
