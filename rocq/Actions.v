(** * Actions: joining the ghost updates to the pure state.

    Milestone 4c.  [IrisGhost.v] can change the ghost maps; [Denotations.v] can
    say what the resulting *pure* state must satisfy.  Nothing so far connects
    them: an atomic action changes the heap and the observation map together,
    and the invariant has to be re-established on the state those two
    reconstruct.

    This file is that connection.  It is short, and deliberately so -- if the
    two representations were not lined up, it would not be.  The content is that
    [to_LState] commutes with both kinds of update:

      - a field write moves through untouched, so every reachability result of
        [HeapPaths.v] applies to the post-state as stated;
      - the ghost update of [obs_add] shows up in the reconstructed state as
        exactly the observation added, and leaves the others alone.

    With those, an action lemma about the pure state is an action lemma about
    the state under the invariant.

    Checked with Rocq 9.2, axiom-free. *)

From iris.algebra Require Import auth gmap gset.
From iris.base_logic.lib Require Import own.
From iris.proofmode Require Import proofmode.
From stdpp Require Import gmap sets.
From RCU Require Import WellFormed HeapPaths IrisGhost Denotations.

(** ** The machine-state transformer for a field write *)

Definition write_ms (m : MState) (o : Loc) (f : FName) (v : Val) : MState :=
  {| stk := stk m;
     hp  := upd (hp m) o f v;
     lk  := lk m;
     rt  := rt m;
     rds := rds m;
     bnd := bnd m |}.

(** A write changes the heap and nothing else, and the reconstruction is
    transparent to it.  These are all [reflexivity]; that is the point. *)

Lemma to_LState_write_hp m O U T F o f v :
  hp (ms (to_LState (write_ms m o f v) O U T F)) = upd (hp m) o f v.
Proof. reflexivity. Qed.

Lemma to_LState_write_rt m O U T F o f v :
  rt (ms (to_LState (write_ms m o f v) O U T F)) = rt m.
Proof. reflexivity. Qed.

Lemma to_LState_write_stk m O U T F o f v :
  stk (ms (to_LState (write_ms m o f v) O U T F)) = stk m.
Proof. reflexivity. Qed.

Lemma to_LState_write_obsv m O U T F o f v :
  obsv (to_LState (write_ms m o f v) O U T F) = obsv (to_LState m O U T F).
Proof. reflexivity. Qed.

Lemma to_LState_write_flist m O U T F o f v :
  flist (to_LState (write_ms m o f v) O U T F) = flist (to_LState m O U T F).
Proof. reflexivity. Qed.

(** ** The observation update

    [obs_add] takes the authority from [O] to [{[o := {[ob]}]} . O].  What that
    means for the reconstructed state is the following two facts: the new
    observation is recorded at [o], and nothing else changes.  Together they are
    what lets an action lemma reason about the post-state's observations. *)

(** Destructing the map lookup directly does not work here: the occurrence the
    rewrite leaves in the goal elaborates at the camera level and is not the
    term [destruct] abstracts.  Stating the case analysis over a bound variable
    sidesteps it, and unification bridges the two. *)
Lemma option_op_mem (x : gset obs) (my : option (gset obs)) (ob : obs) :
  ob ∈ x -> match Some x ⋅ my with Some s => ob ∈ s | None => False end.
Proof. intros Hin. destruct my as [y|]; simpl; rewrite ?gset_op; set_solver. Qed.

Lemma option_op_mem_r (x : gset obs) (my : option (gset obs)) (ob : obs) :
  match my with Some s => ob ∈ s | None => False end ->
  match Some x ⋅ my with Some s => ob ∈ s | None => False end.
Proof. destruct my as [y|]; simpl; [rewrite ?gset_op; set_solver | done]. Qed.

Lemma to_LState_obs_added m O U T F o ob :
  obsv (to_LState m ({[o := {[ob]}]} ⋅ O) U T F) o ob.
Proof.
  unfold to_LState; simpl.
  rewrite lookup_op lookup_singleton_eq.
  apply option_op_mem. set_solver.
Qed.

Lemma to_LState_obs_kept m O U T F o ob x :
  x <> o ->
  forall obx, obsv (to_LState m ({[o := {[ob]}]} ⋅ O) U T F) x obx
          <-> obsv (to_LState m O U T F) x obx.
Proof.
  intros Hne obx. simpl.
  rewrite lookup_op lookup_singleton_ne //.
  by rewrite left_id.
Qed.

(** Observations already present survive the update. *)
Lemma to_LState_obs_mono m O U T F o ob x obx :
  obsv (to_LState m O U T F) x obx ->
  obsv (to_LState m ({[o := {[ob]}]} ⋅ O) U T F) x obx.
Proof.
  simpl. destruct (decide (x = o)) as [->|Hne].
  - rewrite lookup_op lookup_singleton_eq. apply option_op_mem_r.
  - rewrite lookup_op lookup_singleton_ne //. by rewrite left_id.
Qed.

(** ** The three mutations, on the state under the invariant

    Restating the action lemmas of [Denotations.v] over [to_LState] and
    [write_ms].  Each is the pure lemma with the reconstruction unfolded, which
    the commutation lemmas above make immediate -- so the representation change
    costs nothing, which is the property worth having. *)

Section actions.

  Variable FType : FName -> FieldKind.

  Theorem replace_post_UNQR m O U T F t xr xp xo xn f rho rho1 N Np op oo on :
    let s := to_LState m O U T F in
    (forall g, FType g = RCUField) ->
    UNQR_h (hp m) (rt m) ->
    FR s ->
    D_rcuRoot  s t xr ->
    D_rcuItr   s t xp rho  Np ->
    D_rcuItr   s t xo rho1 N ->
    D_rcuFresh FType s t xn N ->
    stk m xp t = Some op ->
    stk m xo t = Some oo ->
    stk m xn t = Some on ->
    xr <> xn ->
    Np f = Some (FVar xo) ->
    (forall g, FType g = RCUField -> N g <> None) ->
    UNQR_h (hp (ms (to_LState (write_ms m op f (VLoc on)) O U T F)))
           (rt (ms (to_LState (write_ms m op f (VLoc on)) O U T F))).
  Proof.
    intros s Hall HU HFR Hroot Hp Ho Hn Hstkp Hstko Hstkn Hne Hpf Hdom.
    rewrite to_LState_write_hp to_LState_write_rt.
    exact (replace_preserves_UNQR FType s t xr xp xo xn f rho rho1 N Np op oo on
             Hall HU HFR Hroot Hp Ho Hn Hstkp Hstko Hstkn Hne Hpf Hdom).
  Qed.

  Theorem unlink_post_UNQR m O U T F t xx xz xw f1 f2 rho Nx Nz ox oz ow :
    let s := to_LState m O U T F in
    UNQR_h (hp m) (rt m) ->
    D_rcuItr s t xx rho Nx ->
    D_rcuItr s t xz (rho ++ [f1]) Nz ->
    stk m xx t = Some ox ->
    stk m xz t = Some oz ->
    stk m xw t = Some ow ->
    Nx f1 = Some (FVar xz) ->
    Nz f2 = Some (FVar xw) ->
    UNQR_h (hp (ms (to_LState (write_ms m ox f1 (VLoc ow)) O U T F)))
           (rt (ms (to_LState (write_ms m ox f1 (VLoc ow)) O U T F))).
  Proof.
    intros s HU Hx Hz Hstkx Hstkz Hstkw Hf1 Hf2.
    rewrite to_LState_write_hp to_LState_write_rt.
    exact (unlink_preserves_UNQR s t xx xz xw f1 f2 rho Nx Nz ox oz ow
             HU Hx Hz Hstkx Hstkz Hstkw Hf1 Hf2).
  Qed.

  Theorem insert_post_UNQR m O U T F t xr xp xo xn f f4 rho N1 Np op oo on :
    let s := to_LState m O U T F in
    (forall g, FType g = RCUField) ->
    UNQR_h (hp m) (rt m) ->
    FR s ->
    D_rcuRoot  s t xr ->
    D_rcuItr   s t xp rho Np ->
    D_rcuFresh FType s t xn N1 ->
    stk m xp t = Some op ->
    stk m xo t = Some oo ->
    stk m xn t = Some on ->
    xr <> xn ->
    Np f  = Some (FVar xo) ->
    N1 f4 = Some (FVar xo) ->
    (forall g, N1 g <> None -> g <> f4 -> N1 g = Some FNull) ->
    UNQR_h (hp (ms (to_LState (write_ms m op f (VLoc on)) O U T F)))
           (rt (ms (to_LState (write_ms m op f (VLoc on)) O U T F))).
  Proof.
    intros s Hall HU HFR Hroot Hp Hn Hstkp Hstko Hstkn Hne Hpf Hnf4 Hother.
    rewrite to_LState_write_hp to_LState_write_rt.
    exact (insert_preserves_UNQR FType s t xr xp xo xn f f4 rho N1 Np op oo on
             Hall HU HFR Hroot Hp Hn Hstkp Hstko Hstkn Hne Hpf Hnf4 Hother).
  Qed.

End actions.

(** ** Revoking an observation

    This is where the first version of the ghost state failed, and it is worth
    recording what the failure was, because the shape of the fix is the
    interesting part.

    Unlinking must *withdraw* an observation: the replaced node loses
    [iterator] and gains [unlinked], and WULK makes those exclusive.  The first
    value camera was [gsetUR], whose operation is union.  All its elements are
    [CoreId], so every fragment was persistent -- an observation once handed out
    was held forever, and by [observes_mem] the authority had to go on recording
    it forever too.  No action that unlinks could then re-establish the
    invariant.  The lemma below is the positive form of what was impossible:
    holding a location's entry, a thread can replace it outright, and the
    reconstructed state afterwards records the new observations and not the old.

    The union camera is right for a quantity that only grows.  Observations are
    not one. *)

Section revocation.
  Context `{!rcuG Σ}.

  (** Unlinking, at the level of the ghost state: the writer holds the entry for
      [o], replaces its iterator observation by an unlinked one, and the
      reconstructed state reflects exactly that. *)
  Lemma obs_unlink_step γ O m U T F o lw t :
    obs_auth γ O -∗ obs_ctl γ o {[Oiter lw]} ==∗
      obs_auth γ (<[o := {[Ounlk t]}]> O)
      ∗ obs_ctl γ o {[Ounlk t]}
      ∗ ⌜obsv (to_LState m (<[o := {[Ounlk t]}]> O) U T F) o (Ounlk t)⌝
      ∗ ⌜~ obsv (to_LState m (<[o := {[Ounlk t]}]> O) U T F) o (Oiter lw)⌝.
  Proof.
    iIntros "Ha Hf".
    iMod (obs_set with "Ha Hf") as "[Ha Hf]".
    iModIntro. iFrame. iPureIntro. split.
    - simpl. rewrite lookup_insert_eq. set_solver.
    - simpl. rewrite lookup_insert_eq. set_solver.
  Qed.

  (** Entries elsewhere are untouched, which is what lets the rest of
      WellFormed survive the step. *)
  Lemma obs_unlink_step_ne m O U T F o t x ob :
    x <> o ->
    (obsv (to_LState m (<[o := {[Ounlk t]}]> O) U T F) x ob
     <-> obsv (to_LState m O U T F) x ob).
  Proof. intros Hne. simpl. by rewrite lookup_insert_ne. Qed.

End revocation.

(** ** FPI for unlinking

    The invariant whose failure forced the repair to T-Replace and T-UnlinkH.
    Now that an observation can be withdrawn, the case can be stated, and the
    repaired premise is visible as the hypothesis [Hno_fresh_pred] below: no
    fresh node points at the node being unlinked.  Without it the conclusion is
    false, which is what [FPI_not_preserved_by_replace] exhibits.

    The other hypotheses are pre-state facts.  [Hox_not_fresh] says the node
    written is not itself fresh -- it is an [rcuItr] in both rules -- and is
    what rules out the newly created edge originating at a fresh node.

    The argument does not depend on which rule caused the write: it needs only
    that one field was written and one node lost its iterator observation.  So
    it is stated once, and T-UnlinkH and T-Replace are instances -- the first
    writing [x.f1 := r] and unlinking [z], the second writing [p.f := n] and
    unlinking [o]. *)

Section fpi.

  Variable FType : FName -> FieldKind.

  Theorem write_preserves_FPI m O U T F lw ox f1 oz ow tz :
    let s  := to_LState m O U T F in
    let s' := to_LState (write_ms m ox f1 (VLoc ow))
                        (<[oz := {[Ounlk tz]}]> O) U T F in
    lk m = Some lw ->
    FPI FType s ->
    (forall tf, ~ obsv s ox (Ofresh tf)) ->
    (forall tf, ~ obsv s oz (Ofresh tf)) ->
    (forall op tf g, obsv s op (Ofresh tf) -> FType g = RCUField ->
        hp m op g <> Some (VLoc oz)) ->
    FPI FType s'.
  Proof.
    intros s s' Hlk HFPI Hox_not_fresh Hoz_not_fresh Hno_fresh_pred.
    intros o f o' t lw' Hfresh Hedge HF Hlk'.
    (* the lock is untouched by the write *)
    simpl in Hlk'. rewrite Hlk in Hlk'. injection Hlk' as <-.
    (* o is not the unlinked node, so its observations are the old ones *)
    assert (Hone : o <> oz).
    { intros ->. simpl in Hfresh. rewrite lookup_insert_eq in Hfresh.
      set_solver. }
    assert (Hfresh0 : obsv s o (Ofresh t)).
    { revert Hfresh. subst s s'. simpl. by rewrite lookup_insert_ne. }
    (* the written edge cannot start at a fresh node *)
    assert (Hedge0 : hp m o f = Some (VLoc o')).
    { unfold Edge in Hedge. subst s'.
      rewrite to_LState_write_hp in Hedge.
      destruct (Nat.eq_dec o ox) as [->|Hno].
      - exfalso. exact (Hox_not_fresh t Hfresh0).
      - rewrite upd_other in Hedge; [exact Hedge |].
        intros HH. injection HH as HH1 _. contradiction. }
    (* so the edge is one the pre-state had, and FPI applies to it *)
    assert (Hiter0 : obsv s o' (Oiter lw))
      by exact (HFPI o f o' t lw Hfresh0 Hedge0 HF Hlk).
    (* and o' is not the unlinked node, by the repaired premise *)
    assert (Ho'ne : o' <> oz)
      by (intros ->; exact (Hno_fresh_pred o t f Hfresh0 HF Hedge0)).
    subst s s'. simpl. by rewrite lookup_insert_ne.
  Qed.

  (** T-UnlinkH: writes [x.f1 := r], unlinks [z]. *)
  Corollary unlink_preserves_FPI m O U T F lw ox f1 oz ow tz :
    lk m = Some lw ->
    FPI FType (to_LState m O U T F) ->
    (forall tf, ~ obsv (to_LState m O U T F) ox (Ofresh tf)) ->
    (forall tf, ~ obsv (to_LState m O U T F) oz (Ofresh tf)) ->
    (forall op tf g, obsv (to_LState m O U T F) op (Ofresh tf) ->
        FType g = RCUField -> hp m op g <> Some (VLoc oz)) ->
    FPI FType (to_LState (write_ms m ox f1 (VLoc ow))
                         (<[oz := {[Ounlk tz]}]> O) U T F).
  Proof. apply write_preserves_FPI. Qed.

  (** T-Replace: writes [p.f := n], unlinks [o].  Same lemma, different
      instance -- the fresh node written is [n], and the node losing its
      iterator observation is the one it replaces. *)
  Corollary replace_preserves_FPI m O U T F lw op f oo on to :
    lk m = Some lw ->
    FPI FType (to_LState m O U T F) ->
    (forall tf, ~ obsv (to_LState m O U T F) op (Ofresh tf)) ->
    (forall tf, ~ obsv (to_LState m O U T F) oo (Ofresh tf)) ->
    (forall opn tf g, obsv (to_LState m O U T F) opn (Ofresh tf) ->
        FType g = RCUField -> hp m opn g <> Some (VLoc oo)) ->
    FPI FType (to_LState (write_ms m op f (VLoc on))
                         (<[oo := {[Ounlk to]}]> O) U T F).
  Proof. apply write_preserves_FPI. Qed.

End fpi.

(** ** Status

    The two representations are lined up: a field write is transparent to
    [to_LState], and a ghost observation update appears in the reconstructed
    state as exactly the observation added.  So the pure action lemmas are
    action lemmas about the state the invariant holds, and the remaining work is
    the other invariants for each action rather than any further plumbing.

    The one piece still abstract is [phys] in [rcu_inv]: it is a parameter, so
    the Hoare triple for an action cannot be stated until the language's heap
    assertion is chosen.  That is a choice about the object language, not about
    this development. *)

Print Assumptions to_LState_obs_added.
Print Assumptions to_LState_obs_kept.
Print Assumptions replace_post_UNQR.
Print Assumptions unlink_post_UNQR.
Print Assumptions insert_post_UNQR.
Print Assumptions obs_unlink_step.
Print Assumptions obs_unlink_step_ne.
Print Assumptions write_preserves_FPI.
Print Assumptions unlink_preserves_FPI.
Print Assumptions replace_preserves_FPI.

(** ** The reader side

    Reader rules are trivial as rules -- T-ReadS and T-ReadH both just produce
    another [rcuItr] -- and the content is entirely in what acquiring an
    observation obliges.  A reader following [x.f] to [z] does not already
    observe [z]; the action must add [iterator t] to *its own* entry for [z],
    which is the per-thread update.

    The obligation is IFL.  If [z] is already on the free list, some grace
    period is waiting on a set of threads before reclaiming it, and a reader
    acquiring a reference to [z] must be in that set -- otherwise it could hold
    the reference past the reclamation it is not delaying.  This is the
    condition RCU implementations discharge by having a reader that entered its
    critical section after SyncStart not reach unlinked nodes at all. *)

Section readers.

  Variable FType : FName -> FieldKind.

  (** Acquiring an observation preserves IFL exactly when the acquiring thread
      already bounds any pending reclamation of the node. *)
  Theorem reader_acquire_preserves_IFL m Og U T F t z sz :
    let s  := to_LState_t m Og U T F in
    let s' := to_LState_t m (<[(z, t) := sz ∪ {[Oiter t]}]> Og) U T F in
    IFL s ->
    Og !! (z, t) = Some sz ->
    (forall Tr, flist s z = Some Tr -> Tr t) ->
    IFL s'.
  Proof.
    intros s s' HIFL Hlk Hbound t' o Tr Hiter Hfl.
    (* the free list is untouched *)
    assert (Hfl0 : flist s o = Some Tr) by exact Hfl.
    destruct Hiter as [t'' [s'' [Hlk'' Hin]]].
    destruct (decide ((o, t'') = (z, t))) as [Heq|Hne].
    - injection Heq as -> ->.
      rewrite lookup_insert_eq in Hlk''. injection Hlk'' as <-.
      apply elem_of_union in Hin as [Hin | Hin].
      + (* an observation that was already there *)
        exact (HIFL t' z Tr (ex_intro _ t (ex_intro _ sz (conj Hlk Hin))) Hfl0).
      + (* the one just acquired *)
        apply elem_of_singleton in Hin. injection Hin as <-.
        exact (Hbound Tr Hfl0).
    - rewrite lookup_insert_ne // in Hlk''.
      exact (HIFL t' o Tr (ex_intro _ t'' (ex_intro _ s'' (conj Hlk'' Hin))) Hfl0).
  Qed.

  (** And it preserves RITR unconditionally: a reader acquires an [iterator]
      observation, which is the only kind RITR permits it. *)
  Theorem reader_acquire_preserves_RITR m Og U T F t z sz :
    let s  := to_LState_t m Og U T F in
    let s' := to_LState_t m (<[(z, t) := sz ∪ {[Oiter t]}]> Og) U T F in
    RITR s ->
    Og !! (z, t) = Some sz ->
    RITR s'.
  Proof.
    intros s s' HR Hlk o t' Hrd.
    (* readers are unchanged by the update *)
    assert (Hrd0 : rds (ms s) t') by exact Hrd.
    destruct (HR o t' Hrd0) as (Hu & Hf & Hfr).
    (* an observation in the post-state is either old, or the acquired iterator *)
    assert (Hback : forall ob, obsv s' o ob -> obsv s o ob \/ ob = Oiter t).
    { intros ob [t'' [s'' [Hlk'' Hin]]].
      destruct (decide ((o, t'') = (z, t))) as [Heq|Hne].
      - injection Heq as -> ->.
        rewrite lookup_insert_eq in Hlk''. injection Hlk'' as <-.
        apply elem_of_union in Hin as [Hin | Hin].
        + left. by exists t, sz.
        + right. by apply elem_of_singleton in Hin.
      - rewrite lookup_insert_ne // in Hlk''. left. by exists t'', s''. }
    repeat split; intros Hbad;
      destruct (Hback _ Hbad) as [Hold | Heq]; try discriminate;
      [exact (Hu Hold) | exact (Hf Hold) | exact (Hfr Hold)].
  Qed.

End readers.

Print Assumptions reader_acquire_preserves_IFL.
Print Assumptions reader_acquire_preserves_RITR.

(** ** ReadEnd

    A reader leaving its critical section stops being a reader, stops bounding
    any pending reclamation, drops its observations, and is removed from every
    free-list entry.  This is where the free list actually shrinks, and so where
    Free eventually becomes possible.

    The four have to happen together, and the proofs say why.  IFL needs the
    observations dropped in the same step as the free-list removal: a thread
    removed from an entry while still observing that node as an iterator is
    exactly the state IFL forbids.  RINFL needs the bounding-thread set narrowed
    with the entries, since it says every thread in an entry is a bounding
    thread.  Neither is a step that can be taken on its own. *)

Definition read_end_ms (m : MState) (t : TID) : MState :=
  {| stk := stk m; hp := hp m; lk := lk m; rt := rt m;
     rds := fun t' => rds m t' /\ t' <> t;
     bnd := fun t' => bnd m t' /\ t' <> t |}.

Definition read_end_F (F : gmap Loc (gset TID)) (t : TID) : gmap Loc (gset TID) :=
  (fun s => s ∖ {[t]}) <$> F.

Section readend.

  (** [Og'] is [Og] with thread [t]'s entries gone; stated by its two defining
      properties rather than as a filter, which keeps the proofs about what
      matters. *)
  Theorem read_end_preserves_IFL m Og Og' U T F t :
    ObsWF Og' ->
    (forall o, Og' !! (o, t) = None) ->
    (forall o t', t' <> t -> Og' !! (o, t') = Og !! (o, t')) ->
    IFL (to_LState_t m Og U T F) ->
    IFL (to_LState_t (read_end_ms m t) Og' U T (read_end_F F t)).
  Proof.
    intros HWF Hgone Hkept HIFL t' o Tr Hiter Hfl.
    (* the observation is thread t''s own, and t' is not the departing thread *)
    destruct (obsv_t_locates _ _ _ _ _ o t' (Oiter t') HWF eq_refl Hiter)
      as [s [Hlk Hin]].
    assert (Hne : t' <> t) by (intros ->; rewrite Hgone in Hlk; discriminate).
    (* the free-list entry is the old one minus t *)
    unfold read_end_F in Hfl. simpl in Hfl.
    rewrite lookup_fmap in Hfl.
    destruct (F !! o) as [s0|] eqn:Hs0; [| discriminate].
    simpl in Hfl. injection Hfl as <-.
    (* so it suffices that t' was in the old entry *)
    assert (Hold : IFL (to_LState_t m Og U T F)) by exact HIFL.
    assert (Hiter0 : obsv (to_LState_t m Og U T F) o (Oiter t'))
      by (exists t', s; rewrite -(Hkept o t' Hne); done).
    assert (Hfl0 : flist (to_LState_t m Og U T F) o = Some (fun x => x ∈ s0))
      by (simpl; by rewrite Hs0).
    pose proof (Hold t' o _ Hiter0 Hfl0) as Hmem.
    set_solver.
  Qed.

  (** RINFL: every thread in a free-list entry is a bounding thread.  Narrowing
      the entries and the bounding set together preserves it. *)
  Theorem read_end_preserves_RINFL m Og' U T F t :
    RINFL (to_LState_t m Og' U T F) ->
    RINFL (to_LState_t (read_end_ms m t) Og' U T (read_end_F F t)).
  Proof.
    intros HR o Tr t' Hfl Hin.
    unfold read_end_F in Hfl. simpl in Hfl.
    rewrite lookup_fmap in Hfl.
    destruct (F !! o) as [s0|] eqn:Hs0; [| discriminate].
    simpl in Hfl. injection Hfl as <-.
    assert (Hne : t' <> t) by set_solver.
    assert (Hin0 : t' ∈ s0) by set_solver.
    assert (Hfl0 : flist (to_LState_t m Og' U T F) o = Some (fun x => x ∈ s0))
      by (simpl; by rewrite Hs0).
    split; [exact (HR o _ t' Hfl0 Hin0) | exact Hne].
  Qed.

End readend.

Print Assumptions read_end_preserves_IFL.
Print Assumptions read_end_preserves_RINFL.

(** ** Free

    The endpoint the reclamation argument exists to justify, and the case the
    report calls trivial.

    Under the published HD it is not provable at all: HD constrains every edge,
    and an unlinked node retains a pointer to its old child, so freeing that
    child leaves a dangling edge ([HD_not_preserved_by_free]).  Under the
    corrected HD it goes through by exactly the argument the write-up claimed --
    ULKR is what supplies it.

    The shape is worth noting.  The obligation is that nothing *live* points at
    the freed node.  ULKR gives that every predecessor of a freeable node is
    itself unlinked or freeable, hence detached; the corrected HD asks only
    about non-detached sources; so the two meet exactly.  The published HD asked
    about detached sources too, where ULKR has nothing to offer. *)

Definition free_ms (m : MState) (d : Loc) : MState :=
  {| stk := stk m; hp := free (hp m) d; lk := lk m; rt := rt m;
     rds := rds m; bnd := bnd m |}.

Section freeing.

  Theorem free_preserves_HD m Og U T F d t :
    let s  := to_LState_t m Og U T F in
    let s' := to_LState_t (free_ms m d) Og U T F in
    HD s -> ULKR s -> obsv s d (Ofree t) -> HD s'.
  Proof.
    intros s s' HHD HULKR Hfree o f o' Hedge Hlive.
    (* the edge survived the free, so its source is not the freed node *)
    unfold Edge in Hedge. subst s'. simpl in Hedge.
    destruct (Nat.eq_dec o d) as [->|Hod];
      [rewrite free_same in Hedge; discriminate |].
    rewrite free_other in Hedge; [| exact Hod].
    (* observations are untouched, so the source is live in the old state too *)
    assert (Hlive0 : ~ Detached s o) by exact Hlive.
    (* the target is not the freed node: ULKR would make the source detached *)
    assert (Hne : o' <> d).
    { intros ->. apply Hlive0.
      destruct (HULKR d o f t (or_intror Hfree) Hedge) as [Hu | Hf];
        [exists t; by left | exists t; right; by left]. }
    (* so HD in the old state gives what we need, and the free did not touch it *)
    destruct (HHD o f o' Hedge Hlive0) as [g [v Hv]].
    exists g, v. simpl. by rewrite free_other.
  Qed.

End freeing.

Print Assumptions free_preserves_HD.

(** ** SyncStart and SyncStop

    The grace period.  SyncStart sets the bounding threads to the current
    readers and populates a free-list entry for each unlinked node with that
    same set; SyncStop blocks until the bounding set is empty, after which the
    unlinked nodes become freeable.

    Two facts carry the whole thing, and each is short once the invariants are
    right.

    The first is where the FLR direction settled earlier is used.  Every entry
    created by one SyncStart holds the *same* set, so along a chain of unlinked
    nodes the inclusion FLR demands holds with equality -- which is the
    same-critical-section case of the argument that fixed the direction.  ULKR
    is what supplies that a predecessor of an entry holder is an entry holder.

    The second is what makes Free possible at all: after SyncStop the bounding
    set is empty, and RINFL says every thread in an entry is a bounding thread,
    so every entry is empty.  That is exactly the conjunct the [freeable]
    denotation asks for. *)

Section grace.

  (** SyncStart: one snapshot, so all entries agree, so FLR holds with
      equality rather than mere inclusion. *)
  Theorem sync_start_FLR m Og U T F Rs :
    let s := to_LState_t m Og U T F in
    ULKR s ->
    (forall o s0, F !! o = Some s0 -> s0 = Rs) ->
    (forall o t, (obsv s o (Ounlk t) \/ obsv s o (Ofree t)) ->
        exists s0, F !! o = Some s0) ->
    (forall o s0, F !! o = Some s0 ->
        exists t, obsv s o (Ounlk t) \/ obsv s o (Ofree t)) ->
    FLR s.
  Proof.
    intros s HULKR Hsame Hcovers Honly o o' f' Tr Hfl Hedge.
    simpl in Hfl. destruct (F !! o) as [s0|] eqn:Hs0; [| discriminate].
    injection Hfl as <-.
    (* o is detached, so by ULKR so is its predecessor *)
    destruct (Honly o s0 Hs0) as [t Hdet].
    pose proof (HULKR o o' f' t Hdet Hedge) as Hdet'.
    (* hence the predecessor has an entry, and it is the same snapshot *)
    destruct (Hcovers o' t Hdet') as [s1 Hs1].
    exists (fun x => x ∈ s1). split; [simpl; by rewrite Hs1 |].
    rewrite (Hsame o' s1 Hs1) (Hsame o s0 Hs0). done.
  Qed.

  (** SyncStop: the bounding set is empty, so every entry is. *)
  Theorem sync_stop_entries_empty m Og U T F :
    RINFL (to_LState_t m Og U T F) ->
    (forall t, ~ bnd m t) ->
    forall o s0 t, F !! o = Some s0 -> t ∉ s0.
  Proof.
    intros HR Hb o s0 t Hlk Hin.
    assert (Hfl : flist (to_LState_t m Og U T F) o = Some (fun x => x ∈ s0))
      by (simpl; by rewrite Hlk).
    exact (Hb t (HR o _ t Hfl Hin)).
  Qed.


  (** The conjunct FNR gained (change 10b) is discharged by the conjunct it
      already had, so strengthening it costs nothing.  SyncStop's only effect on
      observations is to turn [unlinked] into [freeable]; a node observed
      [fresh] holds no [unlinked] observation, so it gains no [freeable] one.

      Stated over the observation *step* rather than a SyncStop transformer:
      what the argument needs is only that [freeable] arrives from [unlinked],
      and saying so keeps the lemma independent of how the grace period is
      encoded. *)
  Theorem sync_stop_preserves_FNR (s s' : LState) :
    FNR s ->
    (forall o ob, obsv s' o ob ->
       obsv s o ob \/ exists t, ob = Ofree t /\ obsv s o (Ounlk t)) ->
    FNR s'.
  Proof.
    intros HF Hstep o t t' Hfr'.
    assert (Hfr : obsv s o (Ofresh t)).
    { destruct (Hstep o (Ofresh t) Hfr') as [H | [t0 [Hc _]]];
        [exact H | discriminate Hc]. }
    destruct (HF o t t' Hfr) as [H1 [H2 H3]].
    repeat apply conj; intros Hbad;
      destruct (Hstep _ _ Hbad) as [H | [t0 [Hc Hu]]].
    - exact (H1 H).
    - discriminate Hc.
    - exact (H2 H).
    - discriminate Hc.
    - exact (H3 H).
    - injection Hc as <-. exact (H2 Hu).
  Qed.

End grace.

Print Assumptions sync_start_FLR.
Print Assumptions sync_stop_entries_empty.
Print Assumptions sync_stop_preserves_FNR.

(** ** The invariants a heap write cannot touch

    Most of WellFormed does not mention the heap.  A field write changes [hp]
    and nothing else, so those invariants transfer definitionally -- each proof
    below is the identity.  Recording it as nine one-line lemmas rather than
    leaving it implicit is worth the space: it says precisely which cases of an
    atomic-action lemma have content and which do not, and the report's habit of
    calling a case trivial without saying why is what hid three defects.

    The eight that are *not* here -- OW, ULKR, FLR, FPI, FR, HD, and the two
    halves of UNQRT -- all mention the heap, and every one of them needed a real
    argument. *)

Section untouched.

  Variable FType : FName -> FieldKind.
  Variables (m : MState) (Og : ObsMap) (U : gset (Var * TID))
            (T : gset TID) (F : gmap Loc (gset TID)).
  Variables (o : Loc) (f : FName) (v : Val).

  Let s  := to_LState_t m Og U T F.
  Let s' := to_LState_t (write_ms m o f v) Og U T F.

  Lemma write_RWOW   : RWOW s   -> RWOW s'.   Proof. exact (fun H => H). Qed.
  Lemma write_AWRT   : AWRT s   -> AWRT s'.   Proof. exact (fun H => H). Qed.
  Lemma write_IFL    : IFL s    -> IFL s'.    Proof. exact (fun H => H). Qed.
  Lemma write_WULK   : WULK s   -> WULK s'.   Proof. exact (fun H => H). Qed.
  Lemma write_WFresh : WFresh s -> WFresh s'. Proof. exact (fun H => H). Qed.
  Lemma write_FNR    : FNR s    -> FNR s'.    Proof. exact (fun H => H). Qed.
  Lemma write_RITR   : RITR s   -> RITR s'.   Proof. exact (fun H => H). Qed.
  Lemma write_RINFL  : RINFL s  -> RINFL s'.  Proof. exact (fun H => H). Qed.
  Lemma write_WNR    : WNR s    -> WNR s'.    Proof. exact (fun H => H). Qed.

End untouched.

(** ** OW for a field write

    In-degree at most one, for live nodes.  A write creates one edge, so the
    obligation is that the node written was not already pointed at -- which for
    the two rules that write a fresh node is FR, the same hypothesis their UNQR
    cases use.  Nothing is needed about the edge that was overwritten: removing
    an edge cannot raise anyone's in-degree. *)

Section sharing.

  Variable FType : FName -> FieldKind.

  Theorem write_preserves_OW m Og U T F op f on :
    let s  := to_LState_t m Og U T F in
    let s' := to_LState_t (write_ms m op f (VLoc on)) Og U T F in
    OW FType s ->
    (forall o g, hp m o g <> Some (VLoc on)) ->
    OW FType s'.
  Proof.
    intros s s' HOW Hno o o' g g' x He He' Hg Hg'.
    assert (Hsplit : forall a b y,
              hp (ms s') a b = Some (VLoc y) ->
              ((a, b) = (op, f) /\ y = on) \/ hp m a b = Some (VLoc y)).
    { intros a b y Hab. subst s'. simpl in Hab.
      destruct (edge_eq_dec a b op f) as [Heq|Hne].
      - left. injection Heq as -> ->. rewrite upd_same in Hab.
        injection Hab as <-. split; reflexivity.
      - right. by rewrite upd_other in Hab. }
    destruct (Hsplit o g x He) as [[Hoe Hx] | Hold];
    destruct (Hsplit o' g' x He') as [[Hoe' Hx'] | Hold'].
    - injection Hoe as -> ->. injection Hoe' as -> ->. by left.
    - exfalso. rewrite Hx in Hold'. exact (Hno o' g' Hold').
    - exfalso. rewrite Hx' in Hold. exact (Hno o g Hold).
    - exact (HOW o o' g g' x Hold Hold' Hg Hg').
  Qed.

End sharing.

Print Assumptions write_WULK.
Print Assumptions write_preserves_OW.

(** ** The rest of the invariants a field write does touch

    [write_preserves_OW] settled the first of the eight; this settles five more.
    HD, UNQRT_a, ULKR, FLR and FR each mention the heap, so each has a real case
    at the written edge -- and in every one of them the case at the *old* edge is
    empty, because a write only removes that edge and no invariant here is
    endangered by an edge going away.  What is left is one obligation per
    invariant about the edge created, and each turns out to be a premise the
    rules already carry, or -- once, for ULKR -- an invariant they do not.

    The eighth, UNQRT_b, is not a write lemma: its hypothesis is [Reaches], so it
    needs the path characterizations of [HeapPaths.v] and belongs with the
    per-rule UNQR theorems above rather than here.

    FR is the one whose statement has to say less than one might hope.  A write
    that stores a *fresh* node destroys FR outright -- the node acquires an
    in-edge -- and no side condition repairs that, because FR is not meant to
    survive: T-Replace and T-Insert re-establish it by revoking the [fresh]
    observation in the same step.  So the write lemma covers the writes that
    store something else, which is T-WriteFH, and the linking rules get FR from
    the observation update instead. *)

Section heapinv.

  Variables (m : MState) (Og : ObsMap) (U : gset (Var * TID))
            (T : gset TID) (F : gmap Loc (gset TID)).
  Variables (op : Loc) (fw : FName) (on : Loc).

  Let s  := to_LState_t m Og U T F.
  Let s' := to_LState_t (write_ms m op fw (VLoc on)) Og U T F.

  (** Every edge after the write is either the one written or one that was
      there before.  Both directions of the case split used below. *)
  Lemma write_edge_split o g x :
    Edge s' o g x -> ((o, g) = (op, fw) /\ x = on) \/ Edge s o g x.
  Proof.
    unfold Edge; simpl; intros He.
    destruct (edge_eq_dec o g op fw) as [Heq | Hne].
    - left. injection Heq as -> ->. rewrite upd_same in He.
      injection He as <-. split; reflexivity.
    - right. by rewrite upd_other in He.
  Qed.

  (** A write never deallocates: it assigns one field, so anything allocated
      stays allocated. *)
  Lemma write_InHeap o : InHeap s o -> InHeap s' o.
  Proof.
    intros [g [v Hv]]. unfold InHeap; simpl.
    destruct (edge_eq_dec o g op fw) as [Heq | Hne].
    - injection Heq as -> ->. exists fw, (VLoc on). apply upd_same.
    - exists g, v. by rewrite upd_other.
  Qed.

  (** ** HD

      Heap-domain closure, in the corrected form with the [Detached] exemption
      (change 7).  The hypothesis is under that exemption, and deliberately so:
      what a *detached* node's fields point at is nobody's business, since the
      node is unreachable and OW and HD both excuse it.  A write through a live
      node has to store something allocated; a write through an unlinked one
      need not. *)
  Theorem write_preserves_HD :
    HD s -> (~ Detached s op -> InHeap s on) -> HD s'.
  Proof.
    intros HHD Hon o g x He Hnd.
    destruct (write_edge_split o g x He) as [[Heq ->] | Hold].
    - injection Heq as -> ->. exact (write_InHeap on (Hon Hnd)).
    - exact (write_InHeap x (HHD o g x Hold Hnd)).
  Qed.

  (** ** UNQRT_a

      Nothing points at the root.  The obligation is that the write does not
      make the root a target, and every rule supplies it: the node stored is an
      [rcuItr] at a non-empty path or an [rcuFresh], and the root is neither. *)
  Theorem write_preserves_UNQRT_a :
    UNQRT_a s -> on <> rt m -> UNQRT_a s'.
  Proof.
    intros HU Hne o g He.
    destruct (write_edge_split o g (rt (ms s')) He) as [[_ Hx] | Hold].
    - exact (Hne (eq_sym Hx)).
    - exact (HU o g Hold).
  Qed.

  (** ** ULKR

      Detachment propagates upwards: a predecessor of an unlinked-or-freeable
      node is itself unlinked or freeable.  The new edge makes [op] a
      predecessor of [on], so the obligation is that [on] being detached forces
      [op] to be. *)
  Theorem write_preserves_ULKR :
    ULKR s ->
    (forall t, (obsv s on (Ounlk t) \/ obsv s on (Ofree t)) ->
               obsv s op (Ounlk t) \/ obsv s op (Ofree t)) ->
    ULKR s'.
  Proof.
    intros HU Hnew o o' f' t Hobs He.
    destruct (write_edge_split o' f' o He) as [[Heq ->] | Hold].
    - injection Heq as -> ->. exact (Hnew t Hobs).
    - exact (HU o o' f' t Hobs Hold).
  Qed.

  (** ** FLR

      The same shape, on the free list rather than the observations. *)
  Theorem write_preserves_FLR :
    FLR s ->
    (forall Tr, flist s on = Some Tr ->
       exists Tr', flist s op = Some Tr' /\ (forall t, Tr' t -> Tr t)) ->
    FLR s'.
  Proof.
    intros HF Hnew o o' f' Tr Hfl He.
    destruct (write_edge_split o' f' o He) as [[Heq ->] | Hold].
    - injection Heq as -> ->. exact (Hnew Tr Hfl).
    - exact (HF o o' f' Tr Hfl Hold).
  Qed.

  (** ** FR

      For a write that stores a node nobody observes as fresh.  The second
      conjunct of FR is about the stack, which a write does not touch, so only
      the in-edge obligation has content. *)
  Theorem write_preserves_FR :
    FR s -> (forall t, ~ obsv s on (Ofresh t)) -> FR s'.
  Proof.
    intros HFR Hnf t x o Hstk Hfresh.
    destruct (HFR t x o Hstk Hfresh) as [Hin Halias].
    split; [| exact Halias].
    intros o' g He.
    destruct (write_edge_split o' g o He) as [[_ ->] | Hold].
    - exact (Hnf t Hfresh).
    - exact (Hin o' g Hold).
  Qed.

  (** ** Linking a fresh node, and what ULKR costs there

      This is the case the two linking rules are in, and it is where FNR's third
      conjunct (change 10b) is spent.  [on] is fresh, so FNR denies it both
      [unlinked] and [freeable], and the ULKR obligation is discharged without
      any premise on [op] at all. *)
  Corollary link_fresh_ULKR t0 :
    ULKR s -> FNR s -> obsv s on (Ofresh t0) -> ULKR s'.
  Proof.
    intros HU HF Hfr. apply write_preserves_ULKR; [exact HU |].
    intros t [Hu | Hf]; exfalso.
    - exact (proj1 (proj2 (HF on t0 t Hfr)) Hu).
    - exact (proj2 (proj2 (HF on t0 t Hfr)) Hf).
  Qed.

  (** And the published FNR does not pay for it.  Its two conjuncts leave [on]
      free to be [freeable]; [op] is the writer's iterator, which WULK denies
      both observations, so the obligation fails outright -- there is no weaker
      premise to fall back on.  [WellFormed.fresh_freeable] is a state
      satisfying the other seventeen invariants and the published FNR in which
      this applies. *)
  Theorem link_freeable_breaks_ULKR lw t :
    WULK s -> lk (ms s) = Some lw ->
    obsv s op (Oiter lw) -> obsv s on (Ofree t) ->
    ~ ULKR s'.
  Proof.
    intros HW Hlk Hit Hfr HU.
    assert (He : Edge s' op fw on) by (unfold Edge; simpl; apply upd_same).
    destruct (HW lw op t Hlk Hit) as [Hnu Hnf].
    destruct (HU on op fw t (or_intror Hfr) He) as [H | H];
      [exact (Hnu H) | exact (Hnf H)].
  Qed.

End heapinv.

Print Assumptions write_preserves_HD.
Print Assumptions write_preserves_UNQRT_a.
Print Assumptions write_preserves_ULKR.
Print Assumptions write_preserves_FLR.
Print Assumptions write_preserves_FR.
Print Assumptions link_fresh_ULKR.
Print Assumptions link_freeable_breaks_ULKR.

(** ** UNQRT_b, the eighth

    The last of the eight, and the one that is not a write lemma.  UNQRT_b says
    the writer observes every reachable node as an iterator, so its hypothesis
    is [Reaches] and it has to be discharged against the path characterizations
    of [HeapPaths.v] rather than against the written edge.  It is also the only
    invariant that couples the heap change to the observation change: each of
    the three rules updates both, and UNQRT_b is where the two have to agree.

    Doing it makes the asymmetry between the rules visible, and it is not the
    asymmetry the report's case structure suggests.

      - T-Insert is the easy one.  Nothing loses an observation, and everything
        reachable afterwards was either reachable before or is the inserted node
        itself, which the step observes as an iterator.

      - T-UnlinkH and T-Replace each revoke an iterator observation, so for them
        the invariant needs something UNQR does not say: that the node losing it
        is gone from the structure.  That is [unlink_unreachable] and
        [replace_unreachable].  UNQR alone is not enough -- it says the result
        is still a tree, not which nodes are in it -- and this is the one case
        where the difference bites. *)

Section roots.

  (** T-UnlinkH: writes [x.f1 := r] and unlinks [z].  No node is added, so the
      whole content is that [z] left. *)
  Theorem unlink_preserves_UNQRT_b m O U T F lw ox f1 oz f2 ow tz rho :
    let s  := to_LState m O U T F in
    let s' := to_LState (write_ms m ox f1 (VLoc ow))
                        (<[oz := {[Ounlk tz]}]> O) U T F in
    lk m = Some lw ->
    UNQRT_b s ->
    UNQR_h (hp m) (rt m) ->
    hstar (hp m) (rt m) rho = Some ox ->
    hp m ox f1 = Some (VLoc oz) ->
    hp m oz f2 = Some (VLoc ow) ->
    UNQRT_b s'.
  Proof.
    intros s s' Hlk HB HU Hrho HXf1 Hzf2 p x lw' Hlk' Hreach.
    simpl in Hlk'. rewrite Hlk in Hlk'. injection Hlk' as <-.
    assert (Hnoback : forall tau, hstar (hp m) ow tau <> Some ox).
    { apply (UNQR_no_back (hp m) (rt m) ox rho [f1; f2] ow HU Hrho);
        [discriminate |].
      rewrite hstar_app Hrho /=. rewrite HXf1 /=. by rewrite Hzf2. }
    (* the unlinked node is no longer in the structure *)
    assert (Hnz : x <> oz).
    { intros ->.
      exact (unlink_unreachable (hp m) (rt m) ox f1 oz f2 ow rho
               HU Hrho HXf1 Hzf2 p Hreach). }
    (* and everything that is was there before *)
    assert (Hpre : exists q, hstar (hp m) (rt m) q = Some x).
    { destruct (hstar_unlink_char (hp m) (rt m) ox f1 oz f2 ow p x
                  HXf1 Hzf2 Hnoback Hreach)
        as [[Ha _] | [p1 [s2 [_ [_ Hr]]]]].
      - exists p. exact Ha.
      - exists (p1 ++ f1 :: f2 :: s2). exact Hr. }
    destruct Hpre as [q Hq].
    assert (Htr : forall ob, obsv s x ob -> obsv s' x ob).
    { intros ob. subst s s'. simpl. by rewrite lookup_insert_ne. }
    destruct (HB q x lw Hlk Hq) as [Hit | Hrt];
      [left; exact (Htr _ Hit) | right; exact (Htr _ Hrt)].
  Qed.

  (** T-Replace: writes [p.f := n] and unlinks [o].  Both halves at once -- [n]
      arrives as an iterator, [o] leaves -- so both [replace_unreachable] and
      the added observation are used. *)
  Theorem replace_preserves_UNQRT_b m O U T F lw op f oo on to rho :
    let s  := to_LState m O U T F in
    let s' := to_LState (write_ms m op f (VLoc on))
                        (<[on := {[Oiter lw]}]> (<[oo := {[Ounlk to]}]> O))
                        U T F in
    lk m = Some lw ->
    UNQRT_b s ->
    UNQR_h (hp m) (rt m) ->
    Mirrors (hp m) on oo ->
    hstar (hp m) (rt m) rho = Some op ->
    hp m op f = Some (VLoc oo) ->
    (forall sigma, hstar (hp m) (rt m) sigma <> Some on) ->
    UNQRT_b s'.
  Proof.
    intros s s' Hlk HB HU Hmir Hrho HPf Hfresh p x lw' Hlk' Hreach.
    simpl in Hlk'. rewrite Hlk in Hlk'. injection Hlk' as <-.
    destruct (Nat.eq_dec x on) as [-> | Hxn].
    - (* the node written in: the step observes it as the writer's iterator *)
      left. subst s'. simpl. rewrite lookup_insert_eq. set_solver.
    - assert (Hnp : on <> op) by (intros ->; exact (Hfresh rho Hrho)).
      assert (Hnoback : forall tau, hstar (hp m) oo tau <> Some op)
        by exact (UNQR_no_back_edge (hp m) (rt m) op f oo rho HU Hrho HPf).
      (* not the replaced node, which left the structure *)
      assert (Hxo : x <> oo).
      { intros ->.
        exact (replace_unreachable (hp m) (rt m) op f oo on rho
                 HU Hmir Hrho HPf Hfresh p Hreach). }
      (* so it was reachable before, by the same path *)
      assert (Hq : hstar (hp m) (rt m) p = Some x).
      { destruct (hstar_replace_char (hp m) (rt m) op f oo on p x
                    Hmir Hnp HPf Hnoback Hreach) as [Ha | [Hx _]];
          [exact Ha | contradiction]. }
      assert (Htr : forall ob, obsv s x ob -> obsv s' x ob).
      { intros ob. subst s s'. simpl. by rewrite !lookup_insert_ne. }
      destruct (HB p x lw Hlk Hq) as [Hit | Hrt];
        [left; exact (Htr _ Hit) | right; exact (Htr _ Hrt)].
  Qed.

  (** T-Insert: writes [p.f := n], unlinks nothing.  No unreachability result is
      needed, which is exactly the difference. *)
  Theorem insert_preserves_UNQRT_b m O U T F lw op f oo on f4 rho :
    let s  := to_LState m O U T F in
    let s' := to_LState (write_ms m op f (VLoc on))
                        (<[on := {[Oiter lw]}]> O) U T F in
    lk m = Some lw ->
    UNQRT_b s ->
    UNQR_h (hp m) (rt m) ->
    PointsOnlyAt (hp m) on f4 oo ->
    hstar (hp m) (rt m) rho = Some op ->
    hp m op f = Some (VLoc oo) ->
    (forall sigma, hstar (hp m) (rt m) sigma <> Some on) ->
    UNQRT_b s'.
  Proof.
    intros s s' Hlk HB HU Hpo Hrho HPf Hfresh p x lw' Hlk' Hreach.
    simpl in Hlk'. rewrite Hlk in Hlk'. injection Hlk' as <-.
    destruct (Nat.eq_dec x on) as [-> | Hxn].
    - left. subst s'. simpl. rewrite lookup_insert_eq. set_solver.
    - assert (Hnp : on <> op) by (intros ->; exact (Hfresh rho Hrho)).
      assert (Hnoback : forall tau, hstar (hp m) oo tau <> Some op)
        by exact (UNQR_no_back_edge (hp m) (rt m) op f oo rho HU Hrho HPf).
      assert (Hq : exists q, hstar (hp m) (rt m) q = Some x).
      { destruct (hstar_insert_char (hp m) (rt m) op f oo on f4 p x
                    Hpo Hnp HPf Hnoback Hreach)
          as [[Ha _] | [[Hx _] | [p1 [tau [_ [_ Hr]]]]]].
        - exists p. exact Ha.
        - contradiction.
        - exists (p1 ++ f :: tau). exact Hr. }
      destruct Hq as [q Hq].
      assert (Htr : forall ob, obsv s x ob -> obsv s' x ob).
      { intros ob. subst s s'. simpl. by rewrite lookup_insert_ne. }
      destruct (HB q x lw Hlk Hq) as [Hit | Hrt];
        [left; exact (Htr _ Hit) | right; exact (Htr _ Hrt)].
  Qed.

End roots.

Print Assumptions unlink_preserves_UNQRT_b.
Print Assumptions replace_preserves_UNQRT_b.
Print Assumptions insert_preserves_UNQRT_b.

(** ** Free, all eighteen

    The first action taken end to end: not one invariant at a time, but
    [WellFormed] itself, for the whole step.  Free is the right one to do first
    for two reasons.  It needs no type denotations -- it is a state transition,
    not a typing rule -- so nothing outside this file has to be assumed.  And it
    is the action the report handled worst: its HD case is the one dismissed as
    trivial along with everything else, and it is the one case that is not.

    Doing the whole thing shows how lopsided it is.  Seventeen of the eighteen
    fall out of [hstar_free_sub] and [free_edge_inv] -- free removes edges, so
    every invariant with an [Edge] or [Reaches] hypothesis gets *weaker*, and
    the ten that do not mention the heap are untouched outright.  The
    eighteenth, HD, is the only one whose conclusion is about the heap, and it
    is the only one that needs an argument.  It also needs the corrected
    statement: under the published HD the theorem below is false, which
    [HD_not_preserved_by_free] exhibits.

    That is the whole content of the case, and it is a sentence long once the
    invariants are right.  It is worth having the other seventeen written out
    anyway: "trivial" is the claim that hid three defects, and the difference
    between an identity proof and a proof that inverts an edge is exactly what
    the report never recorded. *)

Section reclamation.

  Variable FType : FName -> FieldKind.
  Variables (m : MState) (Og : ObsMap) (U : gset (Var * TID))
            (T : gset TID) (F : gmap Loc (gset TID)) (d : Loc).

  Let s  := to_LState_t m Og U T F.
  Let s' := to_LState_t (free_ms m d) Og U T F.

  (** Edges and paths only go away. *)
  Lemma free_edge_inv o f o' : Edge s' o f o' -> Edge s o f o'.
  Proof.
    unfold Edge; simpl; intros He.
    destruct (Nat.eq_dec o d) as [->|Hne].
    - rewrite free_same in He. discriminate.
    - by rewrite (free_other (hp m) d o f Hne) in He.
  Qed.

  Lemma free_reaches_inv p o : Reaches s' p o -> Reaches s p o.
  Proof. unfold Reaches; simpl. apply hstar_free_sub. Qed.

  (** The ten that do not mention the heap.  Free changes [hp] and nothing
      else, so each is the identity -- as for a write, and for the same
      reason. *)
  Lemma free_RWOW   : RWOW s   -> RWOW s'.   Proof. exact (fun H => H). Qed.
  Lemma free_AWRT   : AWRT s   -> AWRT s'.   Proof. exact (fun H => H). Qed.
  Lemma free_IFL    : IFL s    -> IFL s'.    Proof. exact (fun H => H). Qed.
  Lemma free_WULK   : WULK s   -> WULK s'.   Proof. exact (fun H => H). Qed.
  Lemma free_WFresh : WFresh s -> WFresh s'. Proof. exact (fun H => H). Qed.
  Lemma free_FNR    : FNR s    -> FNR s'.    Proof. exact (fun H => H). Qed.
  Lemma free_WNR    : WNR s    -> WNR s'.    Proof. exact (fun H => H). Qed.
  Lemma free_RITR   : RITR s   -> RITR s'.   Proof. exact (fun H => H). Qed.
  Lemma free_RINFL  : RINFL s  -> RINFL s'.  Proof. exact (fun H => H). Qed.
  Lemma free_WUNLK  : WUNLK s  -> WUNLK s'.  Proof. exact (fun H => H). Qed.

  (** The seven with an [Edge] or [Reaches] hypothesis.  Each is the old
      invariant applied to the inverted hypothesis; none needs a side
      condition, because a vanishing edge can only discharge an obligation. *)
  Lemma free_OW : OW FType s -> OW FType s'.
  Proof.
    intros H o o' f f' x He He'.
    exact (H o o' f f' x (free_edge_inv o f x He) (free_edge_inv o' f' x He')).
  Qed.

  Lemma free_ULKR : ULKR s -> ULKR s'.
  Proof.
    intros H o o' f' t Hobs He.
    exact (H o o' f' t Hobs (free_edge_inv o' f' o He)).
  Qed.

  Lemma free_FLR : FLR s -> FLR s'.
  Proof.
    intros H o o' f' Tr Hfl He.
    exact (H o o' f' Tr Hfl (free_edge_inv o' f' o He)).
  Qed.

  Lemma free_FPI : FPI FType s -> FPI FType s'.
  Proof.
    intros H o f o' t lw Hfr He Hft Hlk.
    exact (H o f o' t lw Hfr (free_edge_inv o f o' He) Hft Hlk).
  Qed.

  Lemma free_FR : FR s -> FR s'.
  Proof.
    intros H t x o Hstk Hfr.
    destruct (H t x o Hstk Hfr) as [Hin Hal].
    split; [| exact Hal].
    intros o' f' He. exact (Hin o' f' (free_edge_inv o' f' o He)).
  Qed.

  Lemma free_UNQRT_a : UNQRT_a s -> UNQRT_a s'.
  Proof. intros H o f He. exact (H o f (free_edge_inv o f (rt m) He)). Qed.

  Lemma free_UNQRT_b : UNQRT_b s -> UNQRT_b s'.
  Proof.
    intros H p o lw Hlk Hr. exact (H p o lw Hlk (free_reaches_inv p o Hr)).
  Qed.

  Lemma free_UNQR : UNQR s -> UNQR s'.
  Proof.
    intros H p p' o H1 H2.
    exact (H p p' o (free_reaches_inv p o H1) (free_reaches_inv p' o H2)).
  Qed.

  (** The action lemma.  [obsv s d (Ofree t)] is the rule's premise -- the
      variable freed is typed [freeable] -- and it is used in exactly one place,
      the HD case, through ULKR. *)
  Theorem free_preserves_WellFormed t :
    WellFormed FType s -> obsv s d (Ofree t) -> WellFormed FType s'.
  Proof.
    intros (HOW & HRWOW & HAWRT & HIFL & HULKR & HFLR & HWULK & HFR & HWFresh
            & HFNR & HFPI & HWNR & HRITR & HRINFL & HHD & HUa & HUb & HWU
            & HU) Hfree.
    repeat apply conj.
    - exact (free_OW HOW).
    - exact (free_RWOW HRWOW).
    - exact (free_AWRT HAWRT).
    - exact (free_IFL HIFL).
    - exact (free_ULKR HULKR).
    - exact (free_FLR HFLR).
    - exact (free_WULK HWULK).
    - exact (free_FR HFR).
    - exact (free_WFresh HWFresh).
    - exact (free_FNR HFNR).
    - exact (free_FPI HFPI).
    - exact (free_WNR HWNR).
    - exact (free_RITR HRITR).
    - exact (free_RINFL HRINFL).
    - exact (free_preserves_HD m Og U T F d t HHD HULKR Hfree).
    - exact (free_UNQRT_a HUa).
    - exact (free_UNQRT_b HUb).
    - exact (free_WUNLK HWU).
    - exact (free_UNQR HU).
  Qed.

End reclamation.

Print Assumptions free_edge_inv.
Print Assumptions free_reaches_inv.
Print Assumptions free_preserves_WellFormed.

(** ** SyncStop, all eighteen

    The second action taken whole, and the one that pays for the FNR repair.

    SyncStop does two things: it returns once the bounding set is empty, and it
    turns every [unlinked] observation into the matching [freeable] one.  Both
    halves are needed and each carries different invariants -- the empty
    bounding set is the whole of RINFL, and the observation change is everything
    else.

    The change is stated by what it does to observations rather than as a map
    operation, which is the choice ReadEnd already makes and for the same
    reason: two properties suffice, and they are the two directions.  Nothing
    appears that was not there, except [freeable] arriving from [unlinked]
    ([Hfwd]); and everything survives, [unlinked] as [freeable] ([Hmap]).  Every
    one of the eighteen cases is one of those two applied once, which is worth
    seeing -- the invariants that look like they should care about a grace
    period ending mostly do not, and the ones that do are not the ones the
    protocol's informal story points at.

    Two cases have content beyond the bookkeeping.  RINFL is where the empty
    bounding set is spent: it says every thread in a free-list entry bounds a
    reclamation, and after SyncStop there are no bounding threads, so the
    entries must be empty -- which is exactly the conjunct the [freeable]
    denotation asks for, obtained rather than assumed.  And FNR is
    [sync_stop_preserves_FNR]: the conjunct added to FNR to make T-Insert and
    T-Replace preserve ULKR is discharged here from the conjunct FNR already
    had, so the repair costs nothing at the one action that could have paid for
    it. *)

Definition sync_obs (ob : obs) : obs :=
  match ob with Ounlk t => Ofree t | _ => ob end.

Definition sync_stop_ms (m : MState) : MState :=
  {| stk := stk m; hp := hp m; lk := lk m; rt := rt m;
     rds := rds m; bnd := fun _ => False |}.

Section quiescence.

  Variable FType : FName -> FieldKind.
  Variables (m : MState) (Og Og' : ObsMap) (U : gset (Var * TID))
            (T : gset TID) (F : gmap Loc (gset TID)).

  Let s  := to_LState_t m Og U T F.
  Let s' := to_LState_t (sync_stop_ms m) Og' U T F.

  (** Nothing appears that was not there, except [freeable] from [unlinked]. *)
  Hypothesis Hfwd : forall o ob,
    obsv s' o ob ->
    obsv s o ob \/ exists t, ob = Ofree t /\ obsv s o (Ounlk t).

  (** And everything survives, [unlinked] as [freeable]. *)
  Hypothesis Hmap : forall o ob, obsv s o ob -> obsv s' o (sync_obs ob).

  (** SyncStop returns only once the grace period has completed. *)
  Hypothesis Hquiet : forall t, ~ bnd m t.

  (** The inversions [Hfwd] gives, once each.  Note the one that is missing:
      nothing maps *to* [unlinked], so after SyncStop no location is observed
      unlinked at all -- which is why [ss_detach] can collapse the disjunction
      the detachment invariants quantify over. *)
  Lemma ss_iter o t : obsv s' o (Oiter t) -> obsv s o (Oiter t).
  Proof.
    intros H. destruct (Hfwd o _ H) as [Ho | [t0 [Hc _]]];
      [exact Ho | discriminate].
  Qed.

  Lemma ss_fresh o t : obsv s' o (Ofresh t) -> obsv s o (Ofresh t).
  Proof.
    intros H. destruct (Hfwd o _ H) as [Ho | [t0 [Hc _]]];
      [exact Ho | discriminate].
  Qed.

  Lemma ss_root o : obsv s' o Oroot -> obsv s o Oroot.
  Proof.
    intros H. destruct (Hfwd o _ H) as [Ho | [t0 [Hc _]]];
      [exact Ho | discriminate].
  Qed.

  Lemma ss_detach o t :
    obsv s' o (Ounlk t) \/ obsv s' o (Ofree t) ->
    obsv s o (Ounlk t) \/ obsv s o (Ofree t).
  Proof.
    intros [H | H]; destruct (Hfwd o _ H) as [Ho | [t0 [Hc Hu]]].
    - by left.
    - discriminate.
    - by right.
    - injection Hc as <-. by left.
  Qed.

  Lemma ss_detached o : Detached s o -> Detached s' o.
  Proof.
    intros [t [H | [H | H]]]; exists t.
    - right; left.  exact (Hmap o (Ounlk t) H).
    - right; left.  exact (Hmap o (Ofree t) H).
    - right; right. exact (Hmap o (Ofresh t) H).
  Qed.

  (** The four the grace period cannot reach: heap, stack, lock and readers are
      all untouched, and neither the free list nor its [Edge] hypotheses move. *)
  Lemma ss_FLR     : FLR s     -> FLR s'.     Proof. exact (fun H => H). Qed.
  Lemma ss_WNR     : WNR s     -> WNR s'.     Proof. exact (fun H => H). Qed.
  Lemma ss_UNQRT_a : UNQRT_a s -> UNQRT_a s'. Proof. exact (fun H => H). Qed.
  Lemma ss_UNQR    : UNQR s    -> UNQR s'.    Proof. exact (fun H => H). Qed.

  (** The rest, each one application of [Hmap] or of an inversion. *)
  Lemma ss_OW : OW FType s -> OW FType s'.
  Proof.
    intros H o o' f f' x He He' Hf Hf'.
    destruct (H o o' f f' x He He' Hf Hf') as [Heq | [Hd | Hd]].
    - by left.
    - right; left.  exact (ss_detached o Hd).
    - right; right. exact (ss_detached o' Hd).
  Qed.

  Lemma ss_RWOW : RWOW s -> RWOW s'.
  Proof.
    intros H x t o Hstk Hundf.
    destruct (H x t o Hstk Hundf) as [Hit | [Hlk [Hu | [Hfr | Hfs]]]].
    - left. exact (Hmap o (Oiter t) Hit).
    - right. split; [exact Hlk |]. right; left.  exact (Hmap o (Ounlk t) Hu).
    - right. split; [exact Hlk |]. right; left.  exact (Hmap o (Ofree t) Hfr).
    - right. split; [exact Hlk |]. right; right. exact (Hmap o (Ofresh t) Hfs).
  Qed.

  Lemma ss_AWRT : AWRT s -> AWRT s'.
  Proof. intros H y t Hstk Hundf. exact (Hmap _ (Oiter t) (H y t Hstk Hundf)). Qed.

  Lemma ss_IFL : IFL s -> IFL s'.
  Proof. intros H t o Tr Hit Hfl. exact (H t o Tr (ss_iter o t Hit) Hfl). Qed.

  Lemma ss_ULKR : ULKR s -> ULKR s'.
  Proof.
    intros H o o' f' t Hobs He.
    destruct (H o o' f' t (ss_detach o t Hobs) He) as [Hu | Hf]; right.
    - exact (Hmap o' (Ounlk t) Hu).
    - exact (Hmap o' (Ofree t) Hf).
  Qed.

  Lemma ss_WULK : WULK s -> WULK s'.
  Proof.
    intros H lw o t Hlk Hit.
    destruct (H lw o t Hlk (ss_iter o lw Hit)) as [Hnu Hnf].
    split; intros Hbad.
    - destruct (ss_detach o t (or_introl Hbad)) as [X | X];
        [exact (Hnu X) | exact (Hnf X)].
    - destruct (ss_detach o t (or_intror Hbad)) as [X | X];
        [exact (Hnu X) | exact (Hnf X)].
  Qed.

  Lemma ss_FR : FR s -> FR s'.
  Proof. intros H t x o Hstk Hfr. exact (H t x o Hstk (ss_fresh o t Hfr)). Qed.

  Lemma ss_WFresh : WFresh s -> WFresh s'.
  Proof. intros H t x o Hstk Hfr. exact (H t x o Hstk (ss_fresh o t Hfr)). Qed.

  Lemma ss_FNR : FNR s -> FNR s'.
  Proof. intros H. exact (sync_stop_preserves_FNR s s' H Hfwd). Qed.

  Lemma ss_FPI : FPI FType s -> FPI FType s'.
  Proof.
    intros H o f o' t lw Hfr He Hft Hlk.
    exact (Hmap o' (Oiter lw) (H o f o' t lw (ss_fresh o t Hfr) He Hft Hlk)).
  Qed.

  Lemma ss_RITR : RITR s -> RITR s'.
  Proof.
    intros H o t Hrd. destruct (H o t Hrd) as (Hnu & Hnf & Hnfr).
    repeat apply conj; intros Hbad.
    - destruct (ss_detach o t (or_introl Hbad)) as [X | X];
        [exact (Hnu X) | exact (Hnf X)].
    - destruct (ss_detach o t (or_intror Hbad)) as [X | X];
        [exact (Hnu X) | exact (Hnf X)].
    - exact (Hnfr (ss_fresh o t Hbad)).
  Qed.

  (** Where the empty bounding set is spent: no thread bounds anything, and
      RINFL says every thread in an entry does, so no entry has a thread in
      it. *)
  Lemma ss_RINFL : RINFL s -> RINFL s'.
  Proof. intros H o Tr t Hfl Hin. exact (Hquiet t (H o Tr t Hfl Hin)). Qed.

  Lemma ss_HD : HD s -> HD s'.
  Proof.
    intros H o f o' He Hnd. apply (H o f o' He).
    intros Hd. exact (Hnd (ss_detached o Hd)).
  Qed.

  Lemma ss_UNQRT_b : UNQRT_b s -> UNQRT_b s'.
  Proof.
    intros H p o lw Hlk Hr. destruct (H p o lw Hlk Hr) as [Hit | Hrt].
    - left.  exact (Hmap o (Oiter lw) Hit).
    - right. exact (Hmap o Oroot Hrt).
  Qed.

  Lemma ss_WUNLK : WUNLK s -> WUNLK s'.
  Proof. intros H o t lw Hlk Hobs. exact (H o t lw Hlk (ss_detach o t Hobs)). Qed.

  Theorem sync_stop_preserves_WellFormed :
    WellFormed FType s -> WellFormed FType s'.
  Proof.
    intros (HOW & HRWOW & HAWRT & HIFL & HULKR & HFLR & HWULK & HFR & HWFresh
            & HFNR & HFPI & HWNR & HRITR & HRINFL & HHD & HUa & HUb & HWU
            & HU).
    repeat apply conj.
    - exact (ss_OW HOW).
    - exact (ss_RWOW HRWOW).
    - exact (ss_AWRT HAWRT).
    - exact (ss_IFL HIFL).
    - exact (ss_ULKR HULKR).
    - exact (ss_FLR HFLR).
    - exact (ss_WULK HWULK).
    - exact (ss_FR HFR).
    - exact (ss_WFresh HWFresh).
    - exact (ss_FNR HFNR).
    - exact (ss_FPI HFPI).
    - exact (ss_WNR HWNR).
    - exact (ss_RITR HRITR).
    - exact (ss_RINFL HRINFL).
    - exact (ss_HD HHD).
    - exact (ss_UNQRT_a HUa).
    - exact (ss_UNQRT_b HUb).
    - exact (ss_WUNLK HWU).
    - exact (ss_UNQR HU).
  Qed.

End quiescence.

(** The two hypotheses are not vacuous: the obvious map does satisfy them.
    Worth checking, for the reason RITR gives -- an abstractly stated step can
    be one no concrete step implements, and then the theorem above says
    nothing. *)
Definition sync_stop_Og (Og : ObsMap) : ObsMap := (set_map sync_obs) <$> Og.

Lemma sync_stop_Og_map m Og U T F o ob :
  obsv (to_LState_t m Og U T F) o ob ->
  obsv (to_LState_t (sync_stop_ms m) (sync_stop_Og Og) U T F) o (sync_obs ob).
Proof.
  intros (t & S & Hlk & Hin). exists t, (set_map sync_obs S).
  split; [by rewrite /sync_stop_Og lookup_fmap Hlk | set_solver].
Qed.

Lemma sync_stop_Og_fwd m Og U T F o ob :
  obsv (to_LState_t (sync_stop_ms m) (sync_stop_Og Og) U T F) o ob ->
  obsv (to_LState_t m Og U T F) o ob
  \/ exists t, ob = Ofree t /\ obsv (to_LState_t m Og U T F) o (Ounlk t).
Proof.
  intros (t & S' & Hlk & Hin).
  rewrite /sync_stop_Og lookup_fmap in Hlk.
  apply fmap_Some in Hlk as (S & HS & ->).
  apply elem_of_map in Hin as (ob0 & -> & Hin0).
  destruct ob0 as [t0|t0|t0|t0|]; simpl.
  - left. by exists t, S.
  - right. exists t0. split; [reflexivity | by exists t, S].
  - left. by exists t, S.
  - left. by exists t, S.
  - left. by exists t, S.
Qed.

Corollary sync_stop_WellFormed FType m Og U T F :
  (forall t, ~ bnd m t) ->
  WellFormed FType (to_LState_t m Og U T F) ->
  WellFormed FType (to_LState_t (sync_stop_ms m) (sync_stop_Og Og) U T F).
Proof.
  intros Hq.
  exact (sync_stop_preserves_WellFormed FType m Og (sync_stop_Og Og) U T F
           (sync_stop_Og_fwd m Og U T F) (sync_stop_Og_map m Og U T F) Hq).
Qed.

Print Assumptions sync_stop_preserves_WellFormed.
Print Assumptions sync_stop_WellFormed.

(** ** ReadEnd, all eighteen

    The third action taken whole, and the one where doing it whole changes the
    statement rather than confirming it.  Two things had to be added that the
    per-invariant lemmas above did not need, and neither is a detail.

    The first is the departing thread's variables.  RWOW says a live variable's
    referent carries an observation; ReadEnd drops the thread's observations; so
    unless the thread's variables stop being live in the same step, RWOW fails
    immediately.  The type system does supply this -- \textsc{ToRCURead} types
    the read critical section as a *block*, and the reader's [rcuItr] variables
    are scoped to it, so they are gone at the end and never appear in the
    outer environment.  But that is a fact about the rule, and it has to be
    carried into the action's statement to be usable: hence [Hundf_t].  The
    earlier [read_end_preserves_IFL] and [read_end_preserves_RINFL] did not
    need it because neither invariant mentions the stack.

    The second is [Oroot], and it is the more interesting one -- see
    [read_end_naive_breaks_UNQRT_b] below.

    With those, the step is characterized by three properties of the
    observations, the same shape SyncStop uses: the thread's own observations
    are gone, everything else survives, and nothing new appears.  The pivotal
    hypothesis is [Hrd] -- ReadEnd is a *reader's* -- because RITR then says the
    departing thread held no detaching observation, so nothing that any
    detachment invariant depends on is among what is dropped.  Without RITR the
    action would be unsound, and this is the only place it is load-bearing. *)

Section departure.

  Variable FType : FName -> FieldKind.
  Variables (m : MState) (Og Og' : ObsMap) (U U' : gset (Var * TID))
            (T : gset TID) (F : gmap Loc (gset TID)) (t : TID).

  Let s  := to_LState_t m Og U T F.
  Let s' := to_LState_t (read_end_ms m t) Og' U' T (read_end_F F t).

  (** The departing thread's own observations are gone, ... *)
  Hypothesis Hself : forall o ob, obs_tid ob = Some t -> ~ obsv s' o ob.
  (** ... everything that is not its own survives -- [Oroot] included, which is
      the whole of the second addition, ... *)
  Hypothesis Hkeep : forall o ob,
    obsv s o ob -> obs_tid ob <> Some t -> obsv s' o ob.
  (** ... and nothing new appears. *)
  Hypothesis Hshrink : forall o ob, obsv s' o ob -> obsv s o ob.

  (** The thread's variables leave scope, which ToRCURead's block supplies. *)
  Hypothesis Hundf_t    : forall x, undf s' x t.
  Hypothesis Hundf_grow : forall x t', undf s x t' -> undf s' x t'.

  (** And the departing thread is a reader. *)
  Hypothesis Hrd : rds m t.

  (** RITR is what makes the step safe: a reader holds no detaching
      observation, so dropping its entries drops nothing any detachment
      invariant relies on. *)
  Lemma re_detach_kept o ob :
    RITR s -> obsv s o ob ->
    (exists t0, ob = Ounlk t0 \/ ob = Ofree t0 \/ ob = Ofresh t0) ->
    obsv s' o ob.
  Proof.
    intros HR Hob [t0 [-> | [-> | ->]]]; apply (Hkeep o _ Hob); simpl;
      intros Hc; injection Hc as ->;
      destruct (HR o t Hrd) as (Hu & Hf & Hfr);
      [exact (Hu Hob) | exact (Hf Hob) | exact (Hfr Hob)].
  Qed.

  Lemma re_detached_fwd o : RITR s -> Detached s o -> Detached s' o.
  Proof.
    intros HR [t0 [H | [H | H]]]; exists t0.
    - left. apply (re_detach_kept o (Ounlk t0) HR H). by exists t0; left.
    - right; left. apply (re_detach_kept o (Ofree t0) HR H).
      by exists t0; right; left.
    - right; right. apply (re_detach_kept o (Ofresh t0) HR H).
      by exists t0; right; right.
  Qed.

  Lemma re_detached_bwd o : Detached s' o -> Detached s o.
  Proof.
    intros [t0 [H | [H | H]]]; exists t0;
      [left | right; left | right; right]; exact (Hshrink _ _ H).
  Qed.

  (** The writer is not the departing thread, so its observations are among
      those that survive.  This is WNR's only use in the development. *)
  Lemma re_writer_ne lw : WNR s -> lk m = Some lw -> lw <> t.
  Proof. intros HW Hlk ->. exact (HW t Hlk Hrd). Qed.

  (** A live variable of the departing thread is a contradiction. *)
  Lemma re_not_t x t' : ~ undf s' x t' -> t' <> t.
  Proof. intros Hnu ->. exact (Hnu (Hundf_t x)). Qed.

  (** The free list loses [t] from every entry and keeps its domain. *)
  Lemma re_flist_inv o Tr :
    flist s' o = Some Tr ->
    exists s0, F !! o = Some s0 /\ Tr = (fun x => x ∈ s0 ∖ {[t]}).
  Proof.
    simpl. rewrite /read_end_F lookup_fmap.
    destruct (F !! o) as [s0|] eqn:HS; simpl; [| discriminate].
    intros H. injection H as <-. by exists s0.
  Qed.

  Lemma re_flist o s0 :
    F !! o = Some s0 -> flist s' o = Some (fun x => x ∈ s0 ∖ {[t]}).
  Proof. intros H. simpl. by rewrite /read_end_F lookup_fmap H. Qed.

  (** The four the departure cannot reach. *)
  Lemma re_UNQRT_a : UNQRT_a s -> UNQRT_a s'. Proof. exact (fun H => H). Qed.
  Lemma re_UNQR    : UNQR s    -> UNQR s'.    Proof. exact (fun H => H). Qed.

  Lemma re_WNR : WNR s -> WNR s'.
  Proof. intros H t0 Hlk [Hrd0 _]. exact (H t0 Hlk Hrd0). Qed.

  Lemma re_HD : RITR s -> HD s -> HD s'.
  Proof.
    intros HR H o f o' He Hnd. apply (H o f o' He).
    intros Hd. exact (Hnd (re_detached_fwd o HR Hd)).
  Qed.

  Lemma re_OW : RITR s -> OW FType s -> OW FType s'.
  Proof.
    intros HR H o o' f f' x He He' Hf Hf'.
    destruct (H o o' f f' x He He' Hf Hf') as [Heq | [Hd | Hd]].
    - by left.
    - right; left.  exact (re_detached_fwd o HR Hd).
    - right; right. exact (re_detached_fwd o' HR Hd).
  Qed.

  Lemma re_RWOW : RWOW s -> RWOW s'.
  Proof.
    intros H x t0 o Hstk Hnu.
    assert (Hne : t0 <> t) by exact (re_not_t x t0 Hnu).
    assert (Hnu0 : ~ undf s x t0) by (intros Hc; exact (Hnu (Hundf_grow x t0 Hc))).
    destruct (H x t0 o Hstk Hnu0) as [Hit | [Hlk [Hu | [Hfr | Hfs]]]].
    - left. apply (Hkeep o _ Hit). simpl. by injection 1 as ->.
    - right. split; [exact Hlk |]. left.
      apply (Hkeep o _ Hu). simpl. by injection 1 as ->.
    - right. split; [exact Hlk |]. right; left.
      apply (Hkeep o _ Hfr). simpl. by injection 1 as ->.
    - right. split; [exact Hlk |]. right; right.
      apply (Hkeep o _ Hfs). simpl. by injection 1 as ->.
  Qed.

  Lemma re_AWRT : AWRT s -> AWRT s'.
  Proof.
    intros H y t0 Hstk Hnu.
    assert (Hne : t0 <> t) by exact (re_not_t y t0 Hnu).
    assert (Hnu0 : ~ undf s y t0) by (intros Hc; exact (Hnu (Hundf_grow y t0 Hc))).
    apply (Hkeep _ _ (H y t0 Hstk Hnu0)). simpl. by injection 1 as ->.
  Qed.

  Lemma re_IFL : IFL s -> IFL s'.
  Proof.
    intros H t0 o Tr Hit Hfl.
    assert (Hne : t0 <> t) by (intros ->; exact (Hself o (Oiter t) eq_refl Hit)).
    destruct (re_flist_inv o Tr Hfl) as [s0 [HS ->]].
    assert (Hfl0 : flist (to_LState_t m Og U T F) o = Some (fun x => x ∈ s0))
      by (simpl; by rewrite HS).
    assert (Hin : t0 ∈ s0) by exact (H t0 o _ (Hshrink _ _ Hit) Hfl0).
    set_solver.
  Qed.

  Lemma re_ULKR : ULKR s -> RITR s -> ULKR s'.
  Proof.
    intros H HR o o' f' t0 Hobs He.
    assert (Hobs0 : obsv s o (Ounlk t0) \/ obsv s o (Ofree t0))
      by (destruct Hobs as [X | X]; [left | right]; exact (Hshrink _ _ X)).
    destruct (H o o' f' t0 Hobs0 He) as [Hu | Hf].
    - left.  apply (re_detach_kept o' (Ounlk t0) HR Hu). by exists t0; left.
    - right. apply (re_detach_kept o' (Ofree t0) HR Hf).
      by exists t0; right; left.
  Qed.

  Lemma re_FLR : FLR s -> FLR s'.
  Proof.
    intros H o o' f' Tr Hfl He.
    destruct (re_flist_inv o Tr Hfl) as [s0 [HS ->]].
    assert (Hfl0 : flist (to_LState_t m Og U T F) o = Some (fun x => x ∈ s0))
      by (simpl; by rewrite HS).
    destruct (H o o' f' _ Hfl0 He) as [Tr' [Hfl' Hsub]].
    simpl in Hfl'. destruct (F !! o') as [s1|] eqn:HS'; [| discriminate].
    injection Hfl' as <-.
    exists (fun x => x ∈ s1 ∖ {[t]}). split; [exact (re_flist o' s1 HS') |].
    intros t0 Hin. assert (t0 ∈ s1) by set_solver.
    assert (t0 <> t) by set_solver. set_solver.
  Qed.

  Lemma re_WULK : WULK s -> WULK s'.
  Proof.
    intros H lw o t0 Hlk Hit.
    destruct (H lw o t0 Hlk (Hshrink _ _ Hit)) as [Hnu Hnf].
    split; intros Hbad; [exact (Hnu (Hshrink _ _ Hbad))
                        | exact (Hnf (Hshrink _ _ Hbad))].
  Qed.

  Lemma re_FR : FR s -> FR s'.
  Proof. intros H t0 x o Hstk Hfr. exact (H t0 x o Hstk (Hshrink _ _ Hfr)). Qed.

  Lemma re_WFresh : WFresh s -> WFresh s'.
  Proof. intros H t0 x o Hstk Hfr. exact (H t0 x o Hstk (Hshrink _ _ Hfr)). Qed.

  Lemma re_FNR : FNR s -> FNR s'.
  Proof.
    intros H o t0 t1 Hfr.
    destruct (H o t0 t1 (Hshrink _ _ Hfr)) as (H1 & H2 & H3).
    repeat apply conj; intros Hbad; [exact (H1 (Hshrink _ _ Hbad))
                                    | exact (H2 (Hshrink _ _ Hbad))
                                    | exact (H3 (Hshrink _ _ Hbad))].
  Qed.

  Lemma re_FPI : WNR s -> FPI FType s -> FPI FType s'.
  Proof.
    intros HW H o f o' t0 lw Hfr He Hft Hlk.
    apply (Hkeep o' _ (H o f o' t0 lw (Hshrink _ _ Hfr) He Hft Hlk)).
    simpl. intros Hc. injection Hc as Heq. exact (re_writer_ne lw HW Hlk Heq).
  Qed.

  Lemma re_RITR : RITR s -> RITR s'.
  Proof.
    intros H o t0 [Hrd0 _]. destruct (H o t0 Hrd0) as (H1 & H2 & H3).
    repeat apply conj; intros Hbad; [exact (H1 (Hshrink _ _ Hbad))
                                    | exact (H2 (Hshrink _ _ Hbad))
                                    | exact (H3 (Hshrink _ _ Hbad))].
  Qed.

  Lemma re_RINFL : RINFL s -> RINFL s'.
  Proof.
    intros H o Tr t0 Hfl Hin.
    destruct (re_flist_inv o Tr Hfl) as [s0 [HS ->]].
    assert (Hin0 : t0 ∈ s0) by set_solver.
    assert (Hfl0 : flist (to_LState_t m Og U T F) o = Some (fun x => x ∈ s0))
      by (simpl; by rewrite HS).
    split; [exact (H o _ t0 Hfl0 Hin0) |]. set_solver.
  Qed.

  Lemma re_UNQRT_b : WNR s -> UNQRT_b s -> UNQRT_b s'.
  Proof.
    intros HW H p o lw Hlk Hr.
    destruct (H p o lw Hlk Hr) as [Hit | Hrt].
    - left. apply (Hkeep o _ Hit). simpl. intros Hc. injection Hc as Heq.
      exact (re_writer_ne lw HW Hlk Heq).
    - right. apply (Hkeep o _ Hrt). simpl. discriminate.
  Qed.

  Lemma re_WUNLK : WUNLK s -> WUNLK s'.
  Proof.
    intros H o t0 lw Hlk [X | X];
      [exact (H o t0 lw Hlk (or_introl (Hshrink _ _ X)))
      |exact (H o t0 lw Hlk (or_intror (Hshrink _ _ X)))].
  Qed.

  Theorem read_end_preserves_WellFormed :
    WellFormed FType s -> WellFormed FType s'.
  Proof.
    intros (HOW & HRWOW & HAWRT & HIFL & HULKR & HFLR & HWULK & HFR & HWFresh
            & HFNR & HFPI & HWNR & HRITR & HRINFL & HHD & HUa & HUb & HWU
            & HU).
    repeat apply conj.
    - exact (re_OW HRITR HOW).
    - exact (re_RWOW HRWOW).
    - exact (re_AWRT HAWRT).
    - exact (re_IFL HIFL).
    - exact (re_ULKR HULKR HRITR).
    - exact (re_FLR HFLR).
    - exact (re_WULK HWULK).
    - exact (re_FR HFR).
    - exact (re_WFresh HWFresh).
    - exact (re_FNR HFNR).
    - exact (re_FPI HWNR HFPI).
    - exact (re_WNR HWNR).
    - exact (re_RITR HRITR).
    - exact (re_RINFL HRINFL).
    - exact (re_HD HRITR HHD).
    - exact (re_UNQRT_a HUa).
    - exact (re_UNQRT_b HWNR HUb).
    - exact (re_WUNLK HWU).
    - exact (re_UNQR HU).
  Qed.

End departure.

Print Assumptions read_end_preserves_WellFormed.

(** ** Why the observation change is [Hkeep] and not "drop the thread's entries"

    The obvious way to say what ReadEnd does to the observation map is the one
    [read_end_preserves_IFL] uses: [Og'] has no entry at [(o, t)].  For every
    invariant about a *thread's* observations that is right, because an
    observation names its observer and [ObsWF] puts it in that observer's entry.

    [Oroot] does not name an observer.  It is anonymous by design -- change C0
    keeps it so, being the root being a property of the structure rather than of
    anyone looking -- and [ObsWF] accordingly permits it in any entry, a
    reader's included.  Dropping that reader's entries then destroys it, and
    UNQRT_b, the one invariant that asks about [Oroot], fails.

    So this is an encoding mismatch rather than a defect in a rule: the map is
    keyed by observer so that a thread can own its fragment, and [Oroot] has no
    owner to be filed under.  Either the encoding gives it a home no ReadEnd can
    remove, or the action has to be stated so as to keep it.  [Hkeep] is the
    second, and it is the smaller change -- it costs one hypothesis and no
    change to [ObsWF], which every other lemma in [IrisGhost.v] depends on.

    The state below is the witness.  It is well formed, its root observation is
    recorded in the reader's entry, and the naive step breaks UNQRT_b. *)

Definition ce_ms : MState :=
  {| stk := fun _ _ => None;
     hp  := fun o _ => if Nat.eqb o 0 then Some VNull else None;
     lk  := Some 1;
     rt  := 0;
     rds := fun t => t = 2;
     bnd := fun _ => False |}.

(** The root observation, filed under reader 2 -- which [ObsWF] permits. *)
Definition ce_Og : ObsMap := {[ (0%nat, 2%nat) := {[Oroot]} ]}.

Definition ce_pre  : LState := to_LState_t ce_ms ce_Og ∅ ∅ ∅.
Definition ce_post : LState :=
  to_LState_t (read_end_ms ce_ms 2) ∅ ∅ ∅ (read_end_F ∅ 2).

Lemma ce_ObsWF : ObsWF ce_Og.
Proof.
  intros o t S ob Hlk Hin.
  destruct (decide ((o, t) = (0%nat, 2%nat))) as [Heq | Hne].
  - injection Heq as -> ->. rewrite lookup_singleton_eq in Hlk.
    injection Hlk as <-. apply elem_of_singleton in Hin. by right.
  - assert (Hnone : ce_Og !! (o, t) = None)
      by (apply lookup_singleton_ne; intros Hc; exact (Hne (eq_sym Hc))).
    rewrite Hnone in Hlk. discriminate.
Qed.

Lemma ce_obs o ob : obsv ce_pre o ob <-> (o = 0%nat /\ ob = Oroot).
Proof.
  split.
  - intros [t [S [Hlk Hin]]].
    destruct (decide ((o, t) = (0%nat, 2%nat))) as [Heq | Hne].
    + injection Heq as -> ->. rewrite lookup_singleton_eq in Hlk.
      injection Hlk as <-. apply elem_of_singleton in Hin. by split.
    + assert (Hnone : ce_Og !! (o, t) = None)
        by (apply lookup_singleton_ne; intros Hc; exact (Hne (eq_sym Hc))).
      rewrite Hnone in Hlk. discriminate.
  - intros [-> ->]. exists 2%nat, {[Oroot]}.
    split; [by rewrite lookup_singleton_eq | set_solver].
Qed.

Lemma ce_no_edges o f o' : ~ Edge ce_pre o f o'.
Proof.
  unfold Edge. simpl. destruct (Nat.eqb o 0); discriminate.
Qed.

Lemma ce_reaches p o : Reaches ce_pre p o -> p = [] /\ o = 0%nat.
Proof.
  destruct p as [|f p]; unfold Reaches; simpl.
  - intros H. injection H as <-. by split.
  - discriminate.
Qed.

Lemma ce_WellFormed FType : WellFormed FType ce_pre.
Proof.
  repeat apply conj.
  - intros o o' f f' x He. exfalso. exact (ce_no_edges o f x He).
  - intros x t o H. simpl in H. discriminate.
  - intros y t H. simpl in H. discriminate.
  - intros t o Tr Hit. exfalso.
    destruct (proj1 (ce_obs o (Oiter t)) Hit) as [_ Hc]. discriminate.
  - intros o o' f' t _ He. exfalso. exact (ce_no_edges o' f' o He).
  - intros o o' f' Tr Hfl. simpl in Hfl. discriminate.
  - intros lw o t _ Hit. exfalso.
    destruct (proj1 (ce_obs o (Oiter lw)) Hit) as [_ Hc]. discriminate.
  - intros t x o H. simpl in H. discriminate.
  - intros t x o H. simpl in H. discriminate.
  - intros o t t' Hfr. exfalso.
    destruct (proj1 (ce_obs o (Ofresh t)) Hfr) as [_ Hc]. discriminate.
  - intros o f o' t lw _ He. exfalso. exact (ce_no_edges o f o' He).
  - intros t Hlk. simpl in Hlk. injection Hlk as <-. discriminate.
  - intros o t Hrd. simpl in Hrd. subst t.
    repeat apply conj; intros Hbad;
      apply ce_obs in Hbad as [_ Hc]; discriminate.
  - intros o Tr t Hfl. simpl in Hfl. discriminate.
  - intros o f o' He. exfalso. exact (ce_no_edges o f o' He).
  - intros o f He. exact (ce_no_edges o f (rt (ms ce_pre)) He).
  - intros p o lw Hlk Hr.
    destruct (ce_reaches p o Hr) as [_ ->]. right.
    by apply ce_obs.
  - intros o t lw _ [H | H]; apply ce_obs in H as [_ Hc]; discriminate.
  - intros p p' o H1 H2.
    destruct (ce_reaches p o H1) as [-> _].
    destruct (ce_reaches p' o H2) as [-> _]. reflexivity.
Qed.

(** The naive step: thread 2's entries are gone, which is exactly the
    characterization the per-invariant ReadEnd lemmas use. *)
Lemma ce_naive_gone o : (∅ : ObsMap) !! (o, 2%nat) = None.
Proof. by rewrite lookup_empty. Qed.

Lemma ce_post_no_obs o ob : ~ obsv ce_post o ob.
Proof. intros [t [S [Hlk _]]]. rewrite lookup_empty in Hlk. discriminate. Qed.

Theorem read_end_naive_breaks_UNQRT_b :
  (forall FType, WellFormed FType ce_pre)
  /\ ObsWF ce_Og
  /\ rds (ms ce_pre) 2
  /\ (forall o, (∅ : ObsMap) !! (o, 2%nat) = None)
  /\ ~ UNQRT_b ce_post.
Proof.
  repeat apply conj;
    [exact ce_WellFormed | exact ce_ObsWF | reflexivity | exact ce_naive_gone |].
  intros H.
  destruct (H [] 0%nat 1%nat eq_refl eq_refl) as [Hbad | Hbad];
    [exact (ce_post_no_obs _ _ Hbad) | exact (ce_post_no_obs _ _ Hbad)].
Qed.

Print Assumptions ce_WellFormed.
Print Assumptions read_end_naive_breaks_UNQRT_b.

(** * The heap mutations, whole

    The three rules the paper is about, each taken as a step rather than one
    invariant at a time.  They are harder than Free, SyncStop and ReadEnd for a
    reason that only shows up when the whole action is attempted: each writes a
    field *and* changes the writer's observations, and for those three actions
    the ten heap-free invariants were identities precisely because nothing
    touched the observation map.  Here they are not.  T-Insert promotes a node
    from [fresh] to [iterator], T-UnlinkH demotes one from [iterator] to
    [unlinked], and T-Replace does both at once, so RWOW, AWRT, IFL, WULK,
    WFresh, FNR, RITR and RINFL all acquire content.

    The observation change is given by properties rather than by a map
    operation, as for SyncStop and ReadEnd.  That is not only for uniformity.
    The revocation an unlink performs is of *the writer's* iterator observation
    and of nothing else -- the readers still holding the node must keep theirs,
    which is the entire point of the structure -- so an update that replaced a
    location's whole observation set would be wrong, and wrong in a way FPI
    cannot see and RWOW can.  [write_preserves_FPI] above uses exactly such an
    update; it is sound there because its conclusion never asks about a reader's
    observation, and it would not be sound here. *)

(** ** T-Insert

    [p.f := n] with [n] fresh and [n.f4] already pointing at [o].  Nothing is
    revoked, which makes this the least entangled of the three: the only
    observation that disappears is the freshness the step consumes.

    Two cases have content past the bookkeeping.  OW is one, and it is the case
    that shows why a fresh node cannot simply be treated as detached throughout:
    the pre-state discharges some of OW by [n]'s detachment, and after the step
    [n] is live, so those cases have to be re-discharged from the edge the write
    *removed*.  WULK is the other, and it spends FNR's third conjunct -- the one
    the ULKR obligation forced -- for the second time. *)

Section insertion.

  Variable FType : FName -> FieldKind.
  Variables (m : MState) (Og Og' : ObsMap) (U : gset (Var * TID))
            (T : gset TID) (F : gmap Loc (gset TID)).
  Variables (lw : TID) (op : Loc) (f : FName) (on oo : Loc) (f4 : FName)
            (rho : list FName).

  Let s  := to_LState_t m Og U T F.
  Let s' := to_LState_t (write_ms m op f (VLoc on)) Og' U T F.

  Hypothesis Hlk : lk m = Some lw.

  (** The observation change: [n] becomes the writer's iterator and stops being
      fresh; nothing else appears, and nothing else is lost. *)
  Hypothesis Hpromote : obsv s' on (Oiter lw).
  Hypothesis Hnofresh : forall t, ~ obsv s' on (Ofresh t).
  Hypothesis Hnew : forall o ob,
    obsv s' o ob -> obsv s o ob \/ (o = on /\ ob = Oiter lw).
  Hypothesis Hkeep : forall o ob,
    obsv s o ob -> (o, ob) <> (on, Ofresh lw) -> obsv s' o ob.

  (** The rule's premises, and what the denotations make of them. *)
  Hypothesis Hallrcu  : forall g, FType g = RCUField.
  Hypothesis Hedge    : hp m op f = Some (VLoc oo).
  Hypothesis Hfresh   : obsv s on (Ofresh lw).
  Hypothesis Hitr_op  : obsv s op (Oiter lw).
  Hypothesis Hpo      : PointsOnlyAt (hp m) on f4 oo.
  Hypothesis Hno_in   : forall o g, hp m o g <> Some (VLoc on).
  Hypothesis Hin_on   : InHeap s on.
  Hypothesis Hnrt     : on <> rt m.
  Hypothesis Hfl_on   : flist s on = None.
  Hypothesis Hrho     : hstar (hp m) (rt m) rho = Some op.
  Hypothesis HU       : UNQR_h (hp m) (rt m).

  (** [n] is unreachable: nothing points at it and it is not the root. *)
  Lemma ins_unreach : forall sigma, hstar (hp m) (rt m) sigma <> Some on.
  Proof.
    apply (no_incoming_unreachable (hp m) (rt m) on Hno_in).
    intros Hc. exact (Hnrt (eq_sym Hc)).
  Qed.

  Lemma ins_np : on <> op.
  Proof. intros Hc. apply (ins_unreach rho). by rewrite Hrho Hc. Qed.

  (** The edge split, recording that an old edge is not at the written
      position -- which the OW case needs and a pure write lemma does not. *)
  Lemma ins_edge_split o g x :
    Edge s' o g x ->
    ((o, g) = (op, f) /\ x = on) \/ (Edge s o g x /\ (o, g) <> (op, f)).
  Proof.
    unfold Edge; simpl; intros He.
    destruct (edge_eq_dec o g op f) as [Heq | Hne].
    - left. injection Heq as -> ->. rewrite upd_same in He.
      injection He as <-. split; reflexivity.
    - right. rewrite upd_other in He; [| exact Hne]. by split.
  Qed.

  Lemma ins_InHeap o : InHeap s o -> InHeap s' o.
  Proof.
    intros [g [v Hv]]. unfold InHeap; simpl.
    destruct (edge_eq_dec o g op f) as [Heq | Hne].
    - injection Heq as -> ->. exists f, (VLoc on). apply upd_same.
    - exists g, v. by rewrite upd_other.
  Qed.

  (** Transfer, in both directions, for everything but [n]'s freshness. *)
  Lemma ins_keep_ob o ob : obsv s o ob -> ob <> Ofresh lw -> obsv s' o ob.
  Proof.
    intros Hob Hne. apply (Hkeep o ob Hob). intros Hc.
    injection Hc as _ Hc2. exact (Hne Hc2).
  Qed.

  Lemma ins_keep_iter o t : obsv s o (Oiter t) -> obsv s' o (Oiter t).
  Proof. intros H. apply (ins_keep_ob o _ H). discriminate. Qed.
  Lemma ins_keep_unlk o t : obsv s o (Ounlk t) -> obsv s' o (Ounlk t).
  Proof. intros H. apply (ins_keep_ob o _ H). discriminate. Qed.
  Lemma ins_keep_free o t : obsv s o (Ofree t) -> obsv s' o (Ofree t).
  Proof. intros H. apply (ins_keep_ob o _ H). discriminate. Qed.
  Lemma ins_keep_root o : obsv s o Oroot -> obsv s' o Oroot.
  Proof. intros H. apply (ins_keep_ob o _ H). discriminate. Qed.

  Lemma ins_keep_ne o ob : o <> on -> obsv s o ob -> obsv s' o ob.
  Proof. intros Hne Hob. apply (Hkeep o ob Hob). by injection 1 as ->. Qed.

  Lemma ins_back_ne o ob : o <> on -> obsv s' o ob -> obsv s o ob.
  Proof.
    intros Hne Hob. destruct (Hnew o ob Hob) as [X | [-> _]];
      [exact X | by contradiction].
  Qed.

  Lemma ins_detached_keep o : o <> on -> Detached s o -> Detached s' o.
  Proof.
    intros Hne [t0 [Hb | [Hb | Hb]]]; exists t0;
      [left | right; left | right; right]; exact (ins_keep_ne o _ Hne Hb).
  Qed.

  Lemma ins_fresh_inv o t : obsv s' o (Ofresh t) -> o <> on /\ obsv s o (Ofresh t).
  Proof.
    intros Hob.
    assert (Hne : o <> on) by (intros ->; exact (Hnofresh t Hob)).
    split; [exact Hne | exact (ins_back_ne o _ Hne Hob)].
  Qed.

  (** [n]'s only edge is the one the rule names. *)
  Lemma ins_fresh_edge g x : Edge s on g x -> g = f4 /\ x = oo.
  Proof.
    intros He. destruct Hpo as [Hf4 Hother].
    destruct (decide (g = f4)) as [-> | Hne].
    - split; [reflexivity |]. unfold Edge in He; simpl in He.
      rewrite Hf4 in He. by injection He as <-.
    - exfalso. exact (Hother g x Hne He).
  Qed.

  (** The writer's iterator is not detached: WULK denies it [unlinked] and
      [freeable], FNR denies it [fresh]. *)
  Lemma ins_op_live : FNR s -> WULK s -> ~ Detached s op.
  Proof.
    intros HF HW [t0 [Hb | [Hb | Hb]]].
    - exact (proj1 (HW lw op t0 Hlk Hitr_op) Hb).
    - exact (proj2 (HW lw op t0 Hlk Hitr_op) Hb).
    - exact (proj1 (HF op t0 lw Hb) Hitr_op).
  Qed.

  Lemma ins_op_not_fresh : FNR s -> forall t, ~ obsv s op (Ofresh t).
  Proof. intros HF t Hob. exact (proj1 (HF op t lw Hob) Hitr_op). Qed.

  (** Any predecessor of [o] other than [p] is detached.  This is OW applied to
      that edge against [p.f], and it is what re-discharges the OW cases the
      pre-state settled by [n]'s detachment. *)
  Lemma ins_other_pred_detached w h :
    FNR s -> WULK s -> OW FType s ->
    Edge s w h oo -> (w, h) <> (op, f) -> Detached s w.
  Proof.
    intros HF HW H He Hne.
    destruct (H op w f h oo Hedge He (Hallrcu f) (Hallrcu h))
      as [Hsame | [Hd | Hd]].
    - exfalso. apply Hne. destruct Hsame as [H1 H2]. by subst.
    - exfalso. exact (ins_op_live HF HW Hd).
    - exact Hd.
  Qed.

  (** *** The cases the observation change carries *)

  Lemma ins_RWOW : RWOW s -> RWOW s'.
  Proof.
    intros H x t o Hstk Hnu.
    destruct (H x t o Hstk Hnu) as [Hit | [Hlk' [Hu | [Hfr | Hfs]]]].
    - left. exact (ins_keep_iter o t Hit).
    - right. split; [exact Hlk' |]. left. exact (ins_keep_unlk o t Hu).
    - right. split; [exact Hlk' |]. right; left. exact (ins_keep_free o t Hfr).
    - destruct (decide (o = on)) as [-> | Hne].
      + (* the freshness the step consumes is replaced by the iterator *)
        rewrite Hlk in Hlk'. injection Hlk' as <-. by left.
      + right. split; [exact Hlk' |]. right; right.
        exact (ins_keep_ne o _ Hne Hfs).
  Qed.

  Lemma ins_AWRT : AWRT s -> AWRT s'.
  Proof. intros H y t Hstk Hnu. exact (ins_keep_iter _ t (H y t Hstk Hnu)). Qed.

  Lemma ins_IFL : IFL s -> IFL s'.
  Proof.
    intros H t o Tr Hit Hfl.
    destruct (Hnew o _ Hit) as [Hit0 | [-> _]].
    - exact (H t o Tr Hit0 Hfl).
    - exfalso. rewrite Hfl_on in Hfl. discriminate.
  Qed.

  Lemma ins_WULK : FNR s -> WULK s -> WULK s'.
  Proof.
    intros HF H lw' o t Hlk' Hit.
    simpl in Hlk'. rewrite Hlk in Hlk'. injection Hlk' as <-.
    destruct (decide (o = on)) as [-> | Hne].
    - (* fresh before, so FNR denied it both -- the third conjunct included *)
      destruct (HF on lw t Hfresh) as (_ & Hnu & Hnf).
      split; intros Hbad; destruct (Hnew on _ Hbad) as [Y | [_ Hc]];
        try discriminate; [exact (Hnu Y) | exact (Hnf Y)].
    - destruct (H lw o t Hlk (ins_back_ne o _ Hne Hit)) as [Hnu Hnf].
      split; intros Hbad; [exact (Hnu (ins_back_ne o _ Hne Hbad))
                          | exact (Hnf (ins_back_ne o _ Hne Hbad))].
  Qed.

  Lemma ins_FR : FR s -> FR s'.
  Proof.
    intros H t x o Hstk Hob.
    destruct (ins_fresh_inv o t Hob) as [Hne Hob0].
    destruct (H t x o Hstk Hob0) as [Hin Hal].
    split; [| exact Hal].
    intros o' g He. destruct (ins_edge_split o' g o He) as [[_ Hx] | [Hold _]].
    - exact (Hne Hx).
    - exact (Hin o' g Hold).
  Qed.

  Lemma ins_WFresh : WFresh s -> WFresh s'.
  Proof.
    intros H t x o Hstk Hob.
    exact (H t x o Hstk (proj2 (ins_fresh_inv o t Hob))).
  Qed.

  Lemma ins_FNR : FNR s -> FNR s'.
  Proof.
    intros H o t t' Hob.
    destruct (ins_fresh_inv o t Hob) as [Hne Hob0].
    destruct (H o t t' Hob0) as (H1 & H2 & H3).
    repeat apply conj; intros Hbad;
      [exact (H1 (ins_back_ne o _ Hne Hbad))
      |exact (H2 (ins_back_ne o _ Hne Hbad))
      |exact (H3 (ins_back_ne o _ Hne Hbad))].
  Qed.

  Lemma ins_RITR : RITR s -> RITR s'.
  Proof.
    intros H o t Hrd. destruct (H o t Hrd) as (H1 & H2 & H3).
    repeat apply conj; intros Hbad;
      destruct (Hnew o _ Hbad) as [X | [_ Hc]]; try discriminate.
    - exact (H1 X).
    - exact (H2 X).
    - exact (H3 X).
  Qed.

  Lemma ins_RINFL : RINFL s -> RINFL s'. Proof. exact (fun H => H). Qed.
  Lemma ins_WNR   : WNR s   -> WNR s'.   Proof. exact (fun H => H). Qed.

  (** *** The cases the write carries *)

  Lemma ins_OW : FNR s -> WULK s -> OW FType s -> OW FType s'.
  Proof.
    intros HF HW H o o' g g' x He He' Hg Hg'.
    destruct (ins_edge_split o  g  x He)  as [[Heq  Hx ] | [Hold  Hnep ]];
    destruct (ins_edge_split o' g' x He') as [[Heq' Hx'] | [Hold' Hnep']].
    - injection Heq as -> ->. injection Heq' as -> ->. by left.
    - exfalso. rewrite Hx in Hold'. exact (Hno_in o' g' Hold').
    - exfalso. rewrite Hx' in Hold. exact (Hno_in o g Hold).
    - destruct (decide (o = on)) as [-> | Hne].
      + destruct (ins_fresh_edge g x Hold) as [-> ->].
        destruct (decide (o' = on)) as [-> | Hne'].
        * destruct (ins_fresh_edge g' oo Hold') as [-> _].
          left. split; reflexivity.
        * right; right. apply (ins_detached_keep o' Hne').
          exact (ins_other_pred_detached o' g' HF HW H Hold' Hnep').
      + destruct (decide (o' = on)) as [-> | Hne'].
        * destruct (ins_fresh_edge g' x Hold') as [-> ->].
          right; left. apply (ins_detached_keep o Hne).
          exact (ins_other_pred_detached o g HF HW H Hold Hnep).
        * destruct (H o o' g g' x Hold Hold' Hg Hg') as [Hsame | [Hd | Hd]].
          -- by left.
          -- right; left.  exact (ins_detached_keep o Hne Hd).
          -- right; right. exact (ins_detached_keep o' Hne' Hd).
  Qed.

  Lemma ins_ULKR : FNR s -> ULKR s -> ULKR s'.
  Proof.
    intros HF H o o' g t Hobs He.
    assert (Hobs0 : obsv s o (Ounlk t) \/ obsv s o (Ofree t)).
    { destruct Hobs as [X | X].
      - destruct (Hnew o _ X) as [Y | [_ Hc]]; [by left | discriminate].
      - destruct (Hnew o _ X) as [Y | [_ Hc]]; [by right | discriminate]. }
    destruct (ins_edge_split o' g o He) as [[_ Hx] | [Hold _]].
    - exfalso. subst o. destruct Hobs0 as [Y | Y];
        [exact (proj1 (proj2 (HF on lw t Hfresh)) Y)
        |exact (proj2 (proj2 (HF on lw t Hfresh)) Y)].
    - destruct (H o o' g t Hobs0 Hold) as [Y | Y];
        [left; exact (ins_keep_unlk o' t Y) | right; exact (ins_keep_free o' t Y)].
  Qed.

  Lemma ins_FLR : FLR s -> FLR s'.
  Proof.
    intros H o o' g Tr Hfl He.
    destruct (ins_edge_split o' g o He) as [[_ Hx] | [Hold _]].
    - exfalso. subst o. rewrite Hfl_on in Hfl. discriminate.
    - exact (H o o' g Tr Hfl Hold).
  Qed.

  Lemma ins_FPI : FNR s -> FPI FType s -> FPI FType s'.
  Proof.
    intros HF H o g x t lw' Hob He Hft Hlk'.
    destruct (ins_fresh_inv o t Hob) as [Hne Hob0].
    simpl in Hlk'. rewrite Hlk in Hlk'. injection Hlk' as <-.
    destruct (ins_edge_split o g x He) as [[Heq _] | [Hold _]].
    - exfalso. injection Heq as -> ->. exact (ins_op_not_fresh HF t Hob0).
    - exact (ins_keep_iter x lw (H o g x t lw Hob0 Hold Hft Hlk)).
  Qed.

  Lemma ins_HD : FNR s -> WULK s -> HD s -> HD s'.
  Proof.
    intros HF HW H o g x He Hnd.
    destruct (ins_edge_split o g x He) as [[_ ->] | [Hold _]].
    - exact (ins_InHeap on Hin_on).
    - destruct (decide (o = on)) as [-> | Hne].
      + destruct (ins_fresh_edge g x Hold) as [-> ->].
        apply ins_InHeap. exact (H op f oo Hedge (ins_op_live HF HW)).
      + apply ins_InHeap. apply (H o g x Hold).
        intros Hd. exact (Hnd (ins_detached_keep o Hne Hd)).
  Qed.

  Lemma ins_UNQRT_a : UNQRT_a s -> UNQRT_a s'.
  Proof.
    intros H o g He.
    destruct (ins_edge_split o g (rt (ms s')) He) as [[_ Hx] | [Hold _]].
    - exact (Hnrt (eq_sym Hx)).
    - exact (H o g Hold).
  Qed.

  Lemma ins_UNQRT_b : UNQRT_b s -> UNQRT_b s'.
  Proof.
    intros H p x lw' Hlk' Hr.
    simpl in Hlk'. rewrite Hlk in Hlk'. injection Hlk' as <-.
    destruct (decide (x = on)) as [-> | Hne].
    - by left.
    - assert (Hnoback : forall tau, hstar (hp m) oo tau <> Some op)
        by exact (UNQR_no_back_edge (hp m) (rt m) op f oo rho HU Hrho Hedge).
      assert (Hq : exists q, hstar (hp m) (rt m) q = Some x).
      { destruct (hstar_insert_char (hp m) (rt m) op f oo on f4 p x
                    Hpo ins_np Hedge Hnoback Hr)
          as [[Ha _] | [[Hx _] | [p1 [tau [_ [_ Hr2]]]]]].
        - exists p. exact Ha.
        - by contradiction.
        - exists (p1 ++ f :: tau). exact Hr2. }
      destruct Hq as [q Hq]. destruct (H q x lw Hlk Hq) as [Hit | Hrt].
      + left.  exact (ins_keep_iter x lw Hit).
      + right. exact (ins_keep_root x Hrt).
  Qed.

  Lemma ins_WUNLK : WUNLK s -> WUNLK s'.
  Proof.
    intros H o t lw' Hlk' Hobs. apply (H o t lw' Hlk').
    destruct Hobs as [X | X]; destruct (Hnew o _ X) as [Y | [_ Hc]];
      [by left | discriminate | by right | discriminate].
  Qed.

  Lemma ins_UNQR : UNQR s -> UNQR s'.
  Proof.
    intros _ p p' x H1 H2.
    exact (UNQR_insert_reachable (hp m) (rt m) op f oo on f4 rho HU Hpo Hrho
             Hedge ins_unreach p p' x H1 H2).
  Qed.

  Theorem insert_preserves_WellFormed :
    WellFormed FType s -> WellFormed FType s'.
  Proof.
    intros (HOW & HRWOW & HAWRT & HIFL & HULKR & HFLR & HWULK & HFR & HWFresh
            & HFNR & HFPI & HWNR & HRITR & HRINFL & HHD & HUa & HUb & HWU
            & HUq).
    repeat apply conj.
    - exact (ins_OW HFNR HWULK HOW).
    - exact (ins_RWOW HRWOW).
    - exact (ins_AWRT HAWRT).
    - exact (ins_IFL HIFL).
    - exact (ins_ULKR HFNR HULKR).
    - exact (ins_FLR HFLR).
    - exact (ins_WULK HFNR HWULK).
    - exact (ins_FR HFR).
    - exact (ins_WFresh HWFresh).
    - exact (ins_FNR HFNR).
    - exact (ins_FPI HFNR HFPI).
    - exact (ins_WNR HWNR).
    - exact (ins_RITR HRITR).
    - exact (ins_RINFL HRINFL).
    - exact (ins_HD HFNR HWULK HHD).
    - exact (ins_UNQRT_a HUa).
    - exact (ins_UNQRT_b HUb).
    - exact (ins_WUNLK HWU).
    - exact (ins_UNQR HUq).
  Qed.

End insertion.

Print Assumptions insert_preserves_WellFormed.

(** ** T-UnlinkH

    [x.f1 := r], where [x.f1] was [z] and [z.f2] is [r]: [z] leaves the
    structure and becomes [unlinked].  The revocation is what makes this harder
    than T-Insert, and it is a revocation of *the writer's* iterator observation
    only -- the readers still traversing [z] keep theirs, which is what the RWOW
    case turns on and what a whole-entry update would have destroyed.

    Two of the rule's premises are spent here, and both were added by earlier
    repairs.  The premise excluding a [rcuFresh] predecessor of [z] -- the repair
    that [FPI_not_preserved_by_replace] forced -- is used twice, once in ULKR and
    once in FPI.  And ULKR needs one thing more, which the invariant set does not
    supply; see [Hunlk_writer] and the discussion at
    [unlinked_observations_need_not_be_the_writers] below. *)

Section unlinking.

  Variable FType : FName -> FieldKind.
  Variables (m : MState) (Og Og' : ObsMap) (U : gset (Var * TID))
            (T : gset TID) (F : gmap Loc (gset TID)).
  Variables (lw : TID) (ox : Loc) (f1 : FName) (oz : Loc) (f2 : FName)
            (ow : Loc) (rho : list FName).

  Let s  := to_LState_t m Og U T F.
  Let s' := to_LState_t (write_ms m ox f1 (VLoc ow)) Og' U T F.

  Hypothesis Hlk : lk m = Some lw.

  (** The observation change: the writer's iterator on [z] becomes an unlinked
      observation.  Everything else -- including every reader's iterator on [z]
      -- is untouched. *)
  Hypothesis Hdemote : obsv s' oz (Ounlk lw).
  Hypothesis Hnoiter : ~ obsv s' oz (Oiter lw).
  Hypothesis Hnew : forall o ob,
    obsv s' o ob -> obsv s o ob \/ (o = oz /\ ob = Ounlk lw).
  Hypothesis Hkeep : forall o ob,
    obsv s o ob -> (o, ob) <> (oz, Oiter lw) -> obsv s' o ob.

  (** The rule's premises. *)
  Hypothesis Hallrcu : forall g, FType g = RCUField.
  Hypothesis Hedge1  : hp m ox f1 = Some (VLoc oz).
  Hypothesis Hedge2  : hp m oz f2 = Some (VLoc ow).
  Hypothesis Hitr_ox : obsv s ox (Oiter lw).
  Hypothesis Hitr_oz : obsv s oz (Oiter lw).
  Hypothesis Hitr_ow : obsv s ow (Oiter lw).
  Hypothesis Hfl_ow  : flist s ow = None.
  Hypothesis Hrho    : hstar (hp m) (rt m) rho = Some ox.
  Hypothesis HU      : UNQR_h (hp m) (rt m).

  (** The repaired premise of T-UnlinkH: no fresh reference points at [z]. *)
  Hypothesis Hno_fresh_pred :
    forall q t g, obsv s q (Ofresh t) -> hp m q g <> Some (VLoc oz).

  Lemma unl_oz_reach : hstar (hp m) (rt m) (rho ++ [f1]) = Some oz.
  Proof. rewrite hstar_app Hrho /=. by rewrite Hedge1. Qed.

  (** Nothing below [r] reaches back to [z], nor to [x]: the tree shape, at the
      two depths the characterisation and the disequality need. *)
  Lemma unl_noback_z : forall tau, hstar (hp m) ow tau <> Some oz.
  Proof.
    apply (UNQR_no_back (hp m) (rt m) oz (rho ++ [f1]) [f2] ow HU unl_oz_reach);
      [discriminate |].
    rewrite hstar_app unl_oz_reach /=. by rewrite Hedge2.
  Qed.

  Lemma unl_noback_x : forall tau, hstar (hp m) ow tau <> Some ox.
  Proof.
    apply (UNQR_no_back (hp m) (rt m) ox rho [f1; f2] ow HU Hrho); [discriminate |].
    rewrite hstar_app Hrho /=. rewrite Hedge1 /=. by rewrite Hedge2.
  Qed.

  Lemma unl_wz : ow <> oz.
  Proof. intros Hc. apply (unl_noback_z []). by rewrite /= Hc. Qed.

  Lemma unl_edge_split o g x :
    Edge s' o g x ->
    ((o, g) = (ox, f1) /\ x = ow) \/ (Edge s o g x /\ (o, g) <> (ox, f1)).
  Proof.
    unfold Edge; simpl; intros He.
    destruct (edge_eq_dec o g ox f1) as [Heq | Hne].
    - left. injection Heq as -> ->. rewrite upd_same in He.
      injection He as <-. split; reflexivity.
    - right. rewrite upd_other in He; [| exact Hne]. by split.
  Qed.

  Lemma unl_InHeap o : InHeap s o -> InHeap s' o.
  Proof.
    intros [g [v Hv]]. unfold InHeap; simpl.
    destruct (edge_eq_dec o g ox f1) as [Heq | Hne].
    - injection Heq as -> ->. exists f1, (VLoc ow). apply upd_same.
    - exists g, v. by rewrite upd_other.
  Qed.

  Lemma unl_keep_ne o ob : o <> oz -> obsv s o ob -> obsv s' o ob.
  Proof. intros Hne Hob. apply (Hkeep o ob Hob). by injection 1 as ->. Qed.

  Lemma unl_back_ne o ob : o <> oz -> obsv s' o ob -> obsv s o ob.
  Proof.
    intros Hne Hob. destruct (Hnew o ob Hob) as [X | [-> _]];
      [exact X | by contradiction].
  Qed.

  Lemma unl_keep_ob o ob : obsv s o ob -> ob <> Oiter lw -> obsv s' o ob.
  Proof.
    intros Hob Hne. apply (Hkeep o ob Hob). intros Hc.
    injection Hc as _ Hc2. exact (Hne Hc2).
  Qed.

  (** Detachment only grows: [z] acquires it and nothing loses it. *)
  Lemma unl_detached_keep o : Detached s o -> Detached s' o.
  Proof.
    intros [t0 [Hb | [Hb | Hb]]]; exists t0;
      [left | right; left | right; right]; apply unl_keep_ob;
      [exact Hb | discriminate | exact Hb | discriminate | exact Hb | discriminate].
  Qed.

  (** The writer's iterators are not detached. *)
  Lemma unl_live q : FNR s -> WULK s -> obsv s q (Oiter lw) -> ~ Detached s q.
  Proof.
    intros HF HW Hit [t0 [Hb | [Hb | Hb]]].
    - exact (proj1 (HW lw q t0 Hlk Hit) Hb).
    - exact (proj2 (HW lw q t0 Hlk Hit) Hb).
    - exact (proj1 (HF q t0 lw Hb) Hit).
  Qed.

  (** Any predecessor of [z] other than [x] is detached -- OW against the edge
      the rule names -- and, not being fresh, is unlinked or freeable. *)
  Lemma unl_other_pred q g :
    FNR s -> WULK s -> OW FType s -> WUNLK s ->
    Edge s q g oz -> (q, g) <> (ox, f1) ->
    obsv s q (Ounlk lw) \/ obsv s q (Ofree lw).
  Proof.
    intros HF HW H HWU He Hne.
    destruct (H ox q f1 g oz Hedge1 He (Hallrcu f1) (Hallrcu g))
      as [Hsame | [Hd | Hd]].
    - exfalso. apply Hne. destruct Hsame as [H1 H2]. by subst.
    - exfalso. exact (unl_live ox HF HW Hitr_ox Hd).
    - destruct Hd as [t0 [Hb | [Hb | Hb]]].
      + assert (Ht : t0 = lw) by exact (HWU q t0 lw Hlk (or_introl Hb)).
        rewrite Ht in Hb. by left.
      + assert (Ht : t0 = lw) by exact (HWU q t0 lw Hlk (or_intror Hb)).
        rewrite Ht in Hb. by right.
      + exfalso. exact (Hno_fresh_pred q t0 g Hb He).
  Qed.

  (** *** The cases the observation change carries *)

  Lemma unl_RWOW : RWOW s -> RWOW s'.
  Proof.
    intros H x t o Hstk Hnu.
    destruct (H x t o Hstk Hnu) as [Hit | [Hlk' [Hu | [Hfr | Hfs]]]].
    - destruct (decide ((o, Oiter t) = (oz, Oiter lw))) as [Heq | Hne].
      + (* the writer's own reference to the node it just unlinked: it is
           typed [unlinked] after the step, and RWOW's second disjunct is
           exactly that.  A *reader's* iterator on [z] is not this case. *)
        injection Heq as -> ->. right. split; [exact Hlk | left; exact Hdemote].
      + left. exact (Hkeep o _ Hit Hne).
    - right. split; [exact Hlk' |]. left. apply unl_keep_ob; [exact Hu | discriminate].
    - right. split; [exact Hlk' |]. right; left.
      apply unl_keep_ob; [exact Hfr | discriminate].
    - right. split; [exact Hlk' |]. right; right.
      apply unl_keep_ob; [exact Hfs | discriminate].
  Qed.

  Lemma unl_oz_not_root : UNQRT_a s -> oz <> rt m.
  Proof.
    intros H Hc. apply (H ox f1). unfold Edge; simpl. rewrite -Hc. exact Hedge1.
  Qed.

  Lemma unl_ow_not_root : UNQRT_a s -> ow <> rt m.
  Proof.
    intros H Hc. apply (H oz f2). unfold Edge; simpl. rewrite -Hc. exact Hedge2.
  Qed.

  Lemma unl_AWRT : UNQRT_a s -> AWRT s -> AWRT s'.
  Proof.
    intros Ha H y t Hstk Hnu. apply (Hkeep _ _ (H y t Hstk Hnu)).
    injection 1 as Hc _. exact (unl_oz_not_root Ha (eq_sym Hc)).
  Qed.

  Lemma unl_IFL : IFL s -> IFL s'.
  Proof.
    intros H t o Tr Hit Hfl.
    destruct (Hnew o _ Hit) as [Hit0 | [_ Hc]]; [| discriminate].
    exact (H t o Tr Hit0 Hfl).
  Qed.

  Lemma unl_WULK : WULK s -> WULK s'.
  Proof.
    intros H lw' o t Hlk' Hit.
    simpl in Hlk'. rewrite Hlk in Hlk'. injection Hlk' as <-.
    assert (Hne : o <> oz) by (intros ->; exact (Hnoiter Hit)).
    destruct (H lw o t Hlk (unl_back_ne o _ Hne Hit)) as [Hnu Hnf].
    split; intros Hbad; [exact (Hnu (unl_back_ne o _ Hne Hbad))
                        | exact (Hnf (unl_back_ne o _ Hne Hbad))].
  Qed.

  Lemma unl_fresh_inv o t : obsv s' o (Ofresh t) -> obsv s o (Ofresh t).
  Proof.
    intros Hob. destruct (Hnew o _ Hob) as [X | [_ Hc]]; [exact X | discriminate].
  Qed.

  Lemma unl_FR : FR s -> FR s'.
  Proof.
    intros H t x o Hstk Hob.
    destruct (H t x o Hstk (unl_fresh_inv o t Hob)) as [Hin Hal].
    split; [| exact Hal].
    intros o' g He. destruct (unl_edge_split o' g o He) as [[_ Hx] | [Hold _]].
    - subst o. exact (Hin oz f2 Hedge2).
    - exact (Hin o' g Hold).
  Qed.

  Lemma unl_WFresh : WFresh s -> WFresh s'.
  Proof. intros H t x o Hstk Hob. exact (H t x o Hstk (unl_fresh_inv o t Hob)). Qed.

  Lemma unl_FNR : FNR s -> FNR s'.
  Proof.
    intros H o t t' Hob.
    assert (Hob0 : obsv s o (Ofresh t)) by exact (unl_fresh_inv o t Hob).
    assert (Hne : o <> oz) by (intros ->; exact (proj1 (H oz t lw Hob0) Hitr_oz)).
    destruct (H o t t' Hob0) as (H1 & H2 & H3).
    repeat apply conj; intros Hbad;
      [exact (H1 (unl_back_ne o _ Hne Hbad))
      |exact (H2 (unl_back_ne o _ Hne Hbad))
      |exact (H3 (unl_back_ne o _ Hne Hbad))].
  Qed.

  Lemma unl_RITR : WNR s -> RITR s -> RITR s'.
  Proof.
    intros HW H o t Hrd. destruct (H o t Hrd) as (H1 & H2 & H3).
    repeat apply conj; intros Hbad;
      destruct (Hnew o _ Hbad) as [X | [_ Hc]].
    - exact (H1 X).
    - injection Hc as Ht. rewrite Ht in Hrd. exact (HW lw Hlk Hrd).
    - exact (H2 X).
    - discriminate.
    - exact (H3 X).
    - discriminate.
  Qed.

  Lemma unl_RINFL : RINFL s -> RINFL s'. Proof. exact (fun H => H). Qed.
  Lemma unl_WNR   : WNR s   -> WNR s'.   Proof. exact (fun H => H). Qed.

  (** *** The cases the write carries *)

  Lemma unl_OW : FNR s -> WULK s -> OW FType s -> OW FType s'.
  Proof.
    intros HF HW H o o' g g' x He He' Hg Hg'.
    destruct (unl_edge_split o  g  x He)  as [[Heq  Hx ] | [Hold  Hnep ]];
    destruct (unl_edge_split o' g' x He') as [[Heq' Hx'] | [Hold' Hnep']].
    - injection Heq as -> ->. injection Heq' as -> ->. by left.
    - (* the new edge into [r], against an old one: the old source is [z],
         which is now detached, or is detached already by OW *)
      injection Heq as -> ->. subst x. right; right.
      destruct (decide (o' = oz)) as [-> | Hne'].
      + exists lw. by left.
      + apply unl_detached_keep.
        destruct (H oz o' f2 g' ow Hedge2 Hold' (Hallrcu f2) Hg')
          as [Hsame | [Hd | Hd]].
        * exfalso. destruct Hsame as [H1 _]. exact (Hne' (eq_sym H1)).
        * exfalso. exact (unl_live oz HF HW Hitr_oz Hd).
        * exact Hd.
    - injection Heq' as -> ->. subst x. right; left.
      destruct (decide (o = oz)) as [-> | Hne].
      + exists lw. by left.
      + apply unl_detached_keep.
        destruct (H oz o f2 g ow Hedge2 Hold (Hallrcu f2) Hg)
          as [Hsame | [Hd | Hd]].
        * exfalso. destruct Hsame as [H1 _]. exact (Hne (eq_sym H1)).
        * exfalso. exact (unl_live oz HF HW Hitr_oz Hd).
        * exact Hd.
    - destruct (H o o' g g' x Hold Hold' Hg Hg') as [Hsame | [Hd | Hd]].
      + by left.
      + right; left.  exact (unl_detached_keep o Hd).
      + right; right. exact (unl_detached_keep o' Hd).
  Qed.

  Lemma unl_ULKR : FNR s -> WULK s -> OW FType s -> WUNLK s -> ULKR s -> ULKR s'.
  Proof.
    intros HF HW HOW HWU H o o' g t Hobs He.
    assert (Hcase : (obsv s o (Ounlk t) \/ obsv s o (Ofree t))
                    \/ (o = oz /\ t = lw)).
    { destruct Hobs as [X | X]; destruct (Hnew o _ X) as [Y | [Ho Hc]].
      - left; by left.
      - injection Hc as Ht. right. by split.
      - left; by right.
      - discriminate. }
    destruct Hcase as [Hpre | [-> Ht]].
    - destruct (unl_edge_split o' g o He) as [[_ Hx] | [Hold _]].
      + (* the edge the write created points at [r], which the writer still
           holds as an iterator, so it is neither unlinked nor freeable *)
        exfalso. subst o. destruct Hpre as [Y | Y];
          [exact (proj1 (HW lw ow t Hlk Hitr_ow) Y)
          |exact (proj2 (HW lw ow t Hlk Hitr_ow) Y)].
      + destruct (H o o' g t Hpre Hold) as [Y | Y];
          [left | right]; apply unl_keep_ob;
          [exact Y | discriminate | exact Y | discriminate].
    - (* the node just unlinked: its remaining predecessors are the detached
         ones OW allows, and the repaired premise says none of them is fresh *)
      subst t.
      destruct (unl_edge_split o' g oz He) as [[_ Hx] | [Hold Hnep]].
      + exfalso. exact (unl_wz (eq_sym Hx)).
      + destruct (unl_other_pred o' g HF HW HOW HWU Hold Hnep) as [Y | Y];
          [left | right]; apply unl_keep_ob;
          [exact Y | discriminate | exact Y | discriminate].
  Qed.

  Lemma unl_FLR : FLR s -> FLR s'.
  Proof.
    intros H o o' g Tr Hfl He.
    destruct (unl_edge_split o' g o He) as [[_ Hx] | [Hold _]].
    - exfalso. subst o. rewrite Hfl_ow in Hfl. discriminate.
    - exact (H o o' g Tr Hfl Hold).
  Qed.

  Lemma unl_FPI : FNR s -> FPI FType s -> FPI FType s'.
  Proof.
    intros HF H o g x t lw' Hob He Hft Hlk'.
    assert (Hob0 : obsv s o (Ofresh t)) by exact (unl_fresh_inv o t Hob).
    simpl in Hlk'. rewrite Hlk in Hlk'. injection Hlk' as <-.
    destruct (unl_edge_split o g x He) as [[Heq _] | [Hold _]].
    - exfalso. injection Heq as -> ->. exact (proj1 (HF ox t lw Hob0) Hitr_ox).
    - assert (Hxne : x <> oz)
        by (intros ->; exact (Hno_fresh_pred o t g Hob0 Hold)).
      exact (unl_keep_ne x _ Hxne (H o g x t lw Hob0 Hold Hft Hlk)).
  Qed.

  Lemma unl_HD : FNR s -> WULK s -> HD s -> HD s'.
  Proof.
    intros HF HW H o g x He Hnd.
    destruct (unl_edge_split o g x He) as [[_ ->] | [Hold _]].
    - apply unl_InHeap. exact (H oz f2 ow Hedge2 (unl_live oz HF HW Hitr_oz)).
    - apply unl_InHeap. apply (H o g x Hold).
      intros Hd. exact (Hnd (unl_detached_keep o Hd)).
  Qed.

  Lemma unl_UNQRT_a : UNQRT_a s -> UNQRT_a s'.
  Proof.
    intros H o g He.
    destruct (unl_edge_split o g (rt (ms s')) He) as [[_ Hx] | [Hold _]].
    - exact (unl_ow_not_root H (eq_sym Hx)).
    - exact (H o g Hold).
  Qed.

  Lemma unl_UNQRT_b : UNQRT_b s -> UNQRT_b s'.
  Proof.
    intros H p x lw' Hlk' Hr.
    simpl in Hlk'. rewrite Hlk in Hlk'. injection Hlk' as <-.
    assert (Hne : x <> oz).
    { intros ->. exact (unlink_unreachable (hp m) (rt m) ox f1 oz f2 ow rho
                          HU Hrho Hedge1 Hedge2 p Hr). }
    assert (Hq : exists q, hstar (hp m) (rt m) q = Some x).
    { destruct (hstar_unlink_char (hp m) (rt m) ox f1 oz f2 ow p x
                  Hedge1 Hedge2 unl_noback_x Hr)
        as [[Ha' _] | [p1 [s2 [_ [_ Hr2]]]]].
      - exists p. exact Ha'.
      - exists (p1 ++ f1 :: f2 :: s2). exact Hr2. }
    destruct Hq as [q Hq]. destruct (H q x lw Hlk Hq) as [Hit | Hrt].
    - left.  exact (unl_keep_ne x _ Hne Hit).
    - right. exact (unl_keep_ne x _ Hne Hrt).
  Qed.

  Lemma unl_WUNLK : WUNLK s -> WUNLK s'.
  Proof.
    intros H o t lw' Hlk' Hobs.
    simpl in Hlk'. rewrite Hlk in Hlk'. injection Hlk' as <-.
    destruct Hobs as [X | X]; destruct (Hnew o _ X) as [Y | [_ Hc]].
    - exact (H o t lw Hlk (or_introl Y)).
    - injection Hc as Ht. exact Ht.
    - exact (H o t lw Hlk (or_intror Y)).
    - discriminate.
  Qed.

  Lemma unl_UNQR : UNQR s -> UNQR s'.
  Proof.
    intros _ p p' x H1 H2.
    exact (UNQR_unlink_reachable (hp m) (rt m) ox f1 oz f2 ow rho
             HU Hrho Hedge1 Hedge2 p p' x H1 H2).
  Qed.

  Theorem unlink_preserves_WellFormed :
    WellFormed FType s -> WellFormed FType s'.
  Proof.
    intros (HOW & HRWOW & HAWRT & HIFL & HULKR & HFLR & HWULK & HFR & HWFresh
            & HFNR & HFPI & HWNR & HRITR & HRINFL & HHD & HUa & HUb & HWU
            & HUq).
    repeat apply conj.
    - exact (unl_OW HFNR HWULK HOW).
    - exact (unl_RWOW HRWOW).
    - exact (unl_AWRT HUa HAWRT).
    - exact (unl_IFL HIFL).
    - exact (unl_ULKR HFNR HWULK HOW HWU HULKR).
    - exact (unl_FLR HFLR).
    - exact (unl_WULK HWULK).
    - exact (unl_FR HFR).
    - exact (unl_WFresh HWFresh).
    - exact (unl_FNR HFNR).
    - exact (unl_FPI HFNR HFPI).
    - exact (unl_WNR HWNR).
    - exact (unl_RITR HWNR HRITR).
    - exact (unl_RINFL HRINFL).
    - exact (unl_HD HFNR HWULK HHD).
    - exact (unl_UNQRT_a HUa).
    - exact (unl_UNQRT_b HUb).
    - exact (unl_WUNLK HWU).
    - exact (unl_UNQR HUq).
  Qed.

End unlinking.

Print Assumptions unlink_preserves_WellFormed.

(** ** T-Replace

    [p.f := n] with [n] fresh and mirroring [o], which the write unlinks.  Both
    of the previous two at once: [n] is promoted from [fresh] to the writer's
    iterator and [o] is demoted from it to [unlinked], so every case has to keep
    two locations apart rather than one.

    The rule's two repairs both earn their place here.  The premise excluding a
    [rcuFresh] predecessor of [o] is spent in ULKR and again in FPI; and
    [Mirrors], which the added side condition on the field map is what makes
    derivable, is what carries OW and HD through the case where [n] -- detached
    before the step and live after it -- is the source of the edge under
    consideration. *)

Section replacement.

  Variable FType : FName -> FieldKind.
  Variables (m : MState) (Og Og' : ObsMap) (U : gset (Var * TID))
            (T : gset TID) (F : gmap Loc (gset TID)).
  Variables (lw : TID) (op : Loc) (f : FName) (oo on : Loc) (rho : list FName).

  Let s  := to_LState_t m Og U T F.
  Let s' := to_LState_t (write_ms m op f (VLoc on)) Og' U T F.

  Hypothesis Hlk : lk m = Some lw.

  (** The observation change: [n] is promoted, [o] demoted, and every other
      observation of either -- a reader's iterator on [o], above all -- stays. *)
  Hypothesis Hpromote : obsv s' on (Oiter lw).
  Hypothesis Hnofresh : forall t, ~ obsv s' on (Ofresh t).
  Hypothesis Hdemote  : obsv s' oo (Ounlk lw).
  Hypothesis Hnoiter  : ~ obsv s' oo (Oiter lw).
  Hypothesis Hnew : forall o ob,
    obsv s' o ob ->
    obsv s o ob \/ (o = on /\ ob = Oiter lw) \/ (o = oo /\ ob = Ounlk lw).
  Hypothesis Hkeep : forall o ob,
    obsv s o ob -> (o, ob) <> (on, Ofresh lw) -> (o, ob) <> (oo, Oiter lw) ->
    obsv s' o ob.

  (** The rule's premises. *)
  Hypothesis Hallrcu : forall g, FType g = RCUField.
  Hypothesis Hedge   : hp m op f = Some (VLoc oo).
  Hypothesis Hmir    : Mirrors (hp m) on oo.
  Hypothesis Hfresh  : obsv s on (Ofresh lw).
  Hypothesis Hitr_op : obsv s op (Oiter lw).
  Hypothesis Hitr_oo : obsv s oo (Oiter lw).
  Hypothesis Hno_in  : forall o g, hp m o g <> Some (VLoc on).
  Hypothesis Hin_on  : InHeap s on.
  Hypothesis Hnrt    : on <> rt m.
  Hypothesis Hfl_on  : flist s on = None.
  Hypothesis Hrho    : hstar (hp m) (rt m) rho = Some op.
  Hypothesis HU      : UNQR_h (hp m) (rt m).
  Hypothesis Hno_fresh_pred :
    forall q t g, obsv s q (Ofresh t) -> hp m q g <> Some (VLoc oo).

  Lemma rep_unreach : forall sigma, hstar (hp m) (rt m) sigma <> Some on.
  Proof.
    apply (no_incoming_unreachable (hp m) (rt m) on Hno_in).
    intros Hc. exact (Hnrt (eq_sym Hc)).
  Qed.

  Lemma rep_np : on <> op.
  Proof. intros Hc. apply (rep_unreach rho). by rewrite Hrho Hc. Qed.

  Lemma rep_oo_reach : hstar (hp m) (rt m) (rho ++ [f]) = Some oo.
  Proof. rewrite hstar_app Hrho /=. by rewrite Hedge. Qed.

  Lemma rep_no : on <> oo.
  Proof. intros Hc. apply (rep_unreach (rho ++ [f])). by rewrite rep_oo_reach Hc. Qed.

  Lemma rep_noback : forall tau, hstar (hp m) oo tau <> Some op.
  Proof. exact (UNQR_no_back_edge (hp m) (rt m) op f oo rho HU Hrho Hedge). Qed.

  Lemma rep_edge_split o g x :
    Edge s' o g x ->
    ((o, g) = (op, f) /\ x = on) \/ (Edge s o g x /\ (o, g) <> (op, f)).
  Proof.
    unfold Edge; simpl; intros He.
    destruct (edge_eq_dec o g op f) as [Heq | Hne].
    - left. injection Heq as -> ->. rewrite upd_same in He.
      injection He as <-. split; reflexivity.
    - right. rewrite upd_other in He; [| exact Hne]. by split.
  Qed.

  Lemma rep_InHeap o : InHeap s o -> InHeap s' o.
  Proof.
    intros [g [v Hv]]. unfold InHeap; simpl.
    destruct (edge_eq_dec o g op f) as [Heq | Hne].
    - injection Heq as -> ->. exists f, (VLoc on). apply upd_same.
    - exists g, v. by rewrite upd_other.
  Qed.

  (** [n]'s edges are [o]'s, which is what [Mirrors] says. *)
  Lemma rep_mirror_edge g x : Edge s on g x -> Edge s oo g x.
  Proof. unfold Edge; simpl. by rewrite Hmir. Qed.

  Lemma rep_keep_ne o ob : o <> on -> o <> oo -> obsv s o ob -> obsv s' o ob.
  Proof.
    intros H1 H2 Hob. apply (Hkeep o ob Hob);
      [by injection 1 as -> | by injection 1 as ->].
  Qed.

  (** At [n] itself, everything but the granted iterator came from before. *)
  Lemma rep_back_on ob : ob <> Oiter lw -> obsv s' on ob -> obsv s on ob.
  Proof.
    intros Hne Hob. destruct (Hnew on ob Hob) as [X | [[_ Hc] | [Hc _]]].
    - exact X.
    - by contradiction.
    - exfalso. exact (rep_no Hc).
  Qed.

  Lemma rep_back_ne o ob : o <> on -> o <> oo -> obsv s' o ob -> obsv s o ob.
  Proof.
    intros H1 H2 Hob.
    destruct (Hnew o ob Hob) as [X | [[-> _] | [-> _]]];
      [exact X | by contradiction | by contradiction].
  Qed.

  (** Detaching observations survive; [n]'s freshness and [o]'s iterator are the
      only two things that do not. *)
  Lemma rep_keep_det o ob : obsv s o ob -> ob <> Ofresh lw -> ob <> Oiter lw ->
    obsv s' o ob.
  Proof.
    intros Hob H1 H2. apply (Hkeep o ob Hob);
      [intros Hc; injection Hc as _ Hc2; exact (H1 Hc2)
      |intros Hc; injection Hc as _ Hc2; exact (H2 Hc2)].
  Qed.

  Lemma rep_detached_keep o : o <> on -> Detached s o -> Detached s' o.
  Proof.
    intros Hne Hd. destruct (decide (o = oo)) as [-> | Hno].
    - exists lw. by left.
    - destruct Hd as [t0 [Hb | [Hb | Hb]]]; exists t0;
        [left | right; left | right; right]; exact (rep_keep_ne o _ Hne Hno Hb).
  Qed.

  Lemma rep_live q : FNR s -> WULK s -> obsv s q (Oiter lw) -> ~ Detached s q.
  Proof.
    intros HF HW Hit [t0 [Hb | [Hb | Hb]]].
    - exact (proj1 (HW lw q t0 Hlk Hit) Hb).
    - exact (proj2 (HW lw q t0 Hlk Hit) Hb).
    - exact (proj1 (HF q t0 lw Hb) Hit).
  Qed.

  Lemma rep_other_pred q g :
    FNR s -> WULK s -> OW FType s -> WUNLK s ->
    Edge s q g oo -> (q, g) <> (op, f) ->
    obsv s q (Ounlk lw) \/ obsv s q (Ofree lw).
  Proof.
    intros HF HW H HWU He Hne.
    destruct (H op q f g oo Hedge He (Hallrcu f) (Hallrcu g))
      as [Hsame | [Hd | Hd]].
    - exfalso. apply Hne. destruct Hsame as [H1 H2]. by subst.
    - exfalso. exact (rep_live op HF HW Hitr_op Hd).
    - destruct Hd as [t0 [Hb | [Hb | Hb]]].
      + assert (Ht : t0 = lw) by exact (HWU q t0 lw Hlk (or_introl Hb)).
        rewrite Ht in Hb. by left.
      + assert (Ht : t0 = lw) by exact (HWU q t0 lw Hlk (or_intror Hb)).
        rewrite Ht in Hb. by right.
      + exfalso. exact (Hno_fresh_pred q t0 g Hb He).
  Qed.

  (** *** The cases the observation change carries *)

  Lemma rep_RWOW : RWOW s -> RWOW s'.
  Proof.
    intros H x t o Hstk Hnu.
    destruct (H x t o Hstk Hnu) as [Hit | [Hlk' [Hu | [Hfr | Hfs]]]].
    - destruct (decide ((o, Oiter t) = (oo, Oiter lw))) as [Heq | Hne].
      + (* the writer's own reference to the node it replaced *)
        injection Heq as -> ->. right. split; [exact Hlk | left; exact Hdemote].
      + left. apply (Hkeep o _ Hit); [by injection 1 | exact Hne].
    - right. split; [exact Hlk' |]. left.
      apply rep_keep_det; [exact Hu | discriminate | discriminate].
    - right. split; [exact Hlk' |]. right; left.
      apply rep_keep_det; [exact Hfr | discriminate | discriminate].
    - destruct (decide (o = on)) as [-> | Hne].
      + (* the freshness the step consumes, replaced by the iterator *)
        rewrite Hlk in Hlk'. injection Hlk' as <-. by left.
      + right. split; [exact Hlk' |]. right; right.
        apply (Hkeep o _ Hfs); [by injection 1 as -> | by injection 1].
  Qed.

  Lemma rep_oo_not_root : UNQRT_a s -> oo <> rt m.
  Proof.
    intros H Hc. apply (H op f). unfold Edge; simpl. rewrite -Hc. exact Hedge.
  Qed.

  Lemma rep_AWRT : UNQRT_a s -> AWRT s -> AWRT s'.
  Proof.
    intros Ha H y t Hstk Hnu. apply (Hkeep _ _ (H y t Hstk Hnu)).
    - by injection 1.
    - injection 1 as Hc _. exact (rep_oo_not_root Ha (eq_sym Hc)).
  Qed.

  Lemma rep_IFL : IFL s -> IFL s'.
  Proof.
    intros H t o Tr Hit Hfl.
    destruct (Hnew o _ Hit) as [Hit0 | [[-> _] | [_ Hc]]].
    - exact (H t o Tr Hit0 Hfl).
    - exfalso. rewrite Hfl_on in Hfl. discriminate.
    - discriminate.
  Qed.

  Lemma rep_WULK : FNR s -> WULK s -> WULK s'.
  Proof.
    intros HF H lw' o t Hlk' Hit.
    simpl in Hlk'. rewrite Hlk in Hlk'. injection Hlk' as <-.
    assert (Hno : o <> oo) by (intros ->; exact (Hnoiter Hit)).
    destruct (decide (o = on)) as [-> | Hne].
    - destruct (HF on lw t Hfresh) as (_ & Hnu & Hnf).
      split; intros Hbad.
      + apply Hnu. apply rep_back_on; [discriminate | exact Hbad].
      + apply Hnf. apply rep_back_on; [discriminate | exact Hbad].
    - destruct (H lw o t Hlk (rep_back_ne o _ Hne Hno Hit)) as [Hnu Hnf].
      split; intros Hbad; [exact (Hnu (rep_back_ne o _ Hne Hno Hbad))
                          | exact (Hnf (rep_back_ne o _ Hne Hno Hbad))].
  Qed.

  Lemma rep_fresh_inv o t : obsv s' o (Ofresh t) -> o <> on /\ obsv s o (Ofresh t).
  Proof.
    intros Hob.
    assert (Hne : o <> on) by (intros ->; exact (Hnofresh t Hob)).
    split; [exact Hne |].
    destruct (Hnew o _ Hob) as [X | [[-> _] | [_ Hc]]];
      [exact X | by contradiction | discriminate].
  Qed.

  Lemma rep_FR : FR s -> FR s'.
  Proof.
    intros H t x o Hstk Hob.
    destruct (rep_fresh_inv o t Hob) as [Hne Hob0].
    destruct (H t x o Hstk Hob0) as [Hin Hal].
    split; [| exact Hal].
    intros o' g He. destruct (rep_edge_split o' g o He) as [[_ Hx] | [Hold _]].
    - exact (Hne Hx).
    - exact (Hin o' g Hold).
  Qed.

  Lemma rep_WFresh : WFresh s -> WFresh s'.
  Proof.
    intros H t x o Hstk Hob. exact (H t x o Hstk (proj2 (rep_fresh_inv o t Hob))).
  Qed.

  Lemma rep_FNR : FNR s -> FNR s'.
  Proof.
    intros H o t t' Hob.
    destruct (rep_fresh_inv o t Hob) as [Hne Hob0].
    assert (Hno : o <> oo) by (intros ->; exact (proj1 (H oo t lw Hob0) Hitr_oo)).
    destruct (H o t t' Hob0) as (H1 & H2 & H3).
    repeat apply conj; intros Hbad;
      [exact (H1 (rep_back_ne o _ Hne Hno Hbad))
      |exact (H2 (rep_back_ne o _ Hne Hno Hbad))
      |exact (H3 (rep_back_ne o _ Hne Hno Hbad))].
  Qed.

  Lemma rep_RITR : WNR s -> RITR s -> RITR s'.
  Proof.
    intros HW H o t Hrd. destruct (H o t Hrd) as (H1 & H2 & H3).
    repeat apply conj; intros Hbad;
      destruct (Hnew o _ Hbad) as [X | [[_ Hc] | [_ Hc]]].
    - exact (H1 X).
    - discriminate.
    - injection Hc as Ht. rewrite Ht in Hrd. exact (HW lw Hlk Hrd).
    - exact (H2 X).
    - discriminate.
    - discriminate.
    - exact (H3 X).
    - discriminate.
    - discriminate.
  Qed.

  Lemma rep_RINFL : RINFL s -> RINFL s'. Proof. exact (fun H => H). Qed.
  Lemma rep_WNR   : WNR s   -> WNR s'.   Proof. exact (fun H => H). Qed.

  (** *** The cases the write carries *)

  Lemma rep_OW : FNR s -> WULK s -> OW FType s -> OW FType s'.
  Proof.
    intros HF HW H o o' g g' x He He' Hg Hg'.
    destruct (rep_edge_split o  g  x He)  as [[Heq  Hx ] | [Hold  Hnep ]];
    destruct (rep_edge_split o' g' x He') as [[Heq' Hx'] | [Hold' Hnep']].
    - injection Heq as -> ->. injection Heq' as -> ->. by left.
    - exfalso. rewrite Hx in Hold'. exact (Hno_in o' g' Hold').
    - exfalso. rewrite Hx' in Hold. exact (Hno_in o g Hold).
    - (* both edges predate the write.  [n] was detached then and is not now, so
         a case OW discharged by [n]'s detachment is re-discharged through the
         node [n] mirrors. *)
      destruct (decide (o = on)) as [-> | Hne].
      + destruct (decide (o' = on)) as [-> | Hne'].
        * destruct (H oo oo g g' x (rep_mirror_edge g x Hold)
                      (rep_mirror_edge g' x Hold') Hg Hg')
            as [[_ ->] | [Hd | Hd]].
          -- left. by split.
          -- exfalso. exact (rep_live oo HF HW Hitr_oo Hd).
          -- exfalso. exact (rep_live oo HF HW Hitr_oo Hd).
        * destruct (H oo o' g g' x (rep_mirror_edge g x Hold) Hold' Hg Hg')
            as [[H1 _] | [Hd | Hd]].
          -- right; right. rewrite -H1. exists lw. by left.
          -- exfalso. exact (rep_live oo HF HW Hitr_oo Hd).
          -- right; right. exact (rep_detached_keep o' Hne' Hd).
      + destruct (decide (o' = on)) as [-> | Hne'].
        * destruct (H o oo g g' x Hold (rep_mirror_edge g' x Hold') Hg Hg')
            as [[H1 _] | [Hd | Hd]].
          -- right; left. rewrite H1. exists lw. by left.
          -- right; left. exact (rep_detached_keep o Hne Hd).
          -- exfalso. exact (rep_live oo HF HW Hitr_oo Hd).
        * destruct (H o o' g g' x Hold Hold' Hg Hg') as [Hsame | [Hd | Hd]].
          -- by left.
          -- right; left.  exact (rep_detached_keep o Hne Hd).
          -- right; right. exact (rep_detached_keep o' Hne' Hd).
  Qed.

  Lemma rep_ULKR : FNR s -> WULK s -> OW FType s -> WUNLK s -> ULKR s -> ULKR s'.
  Proof.
    intros HF HW HOW HWU H o o' g t Hobs He.
    assert (Hcase : (obsv s o (Ounlk t) \/ obsv s o (Ofree t))
                    \/ (o = oo /\ t = lw)).
    { destruct Hobs as [X | X];
        destruct (Hnew o _ X) as [Y | [[_ Hc] | [Ho Hc]]].
      - left; by left.
      - discriminate.
      - injection Hc as Ht. right. by split.
      - left; by right.
      - discriminate.
      - discriminate. }
    destruct Hcase as [Hpre | [-> Ht]].
    - destruct (rep_edge_split o' g o He) as [[_ Hx] | [Hold _]].
      + exfalso. subst o. destruct Hpre as [Y | Y];
          [exact (proj1 (proj2 (HF on lw t Hfresh)) Y)
          |exact (proj2 (proj2 (HF on lw t Hfresh)) Y)].
      + destruct (H o o' g t Hpre Hold) as [Y | Y];
          [left | right]; apply rep_keep_det;
          [exact Y | discriminate | discriminate
          |exact Y | discriminate | discriminate].
    - subst t.
      destruct (rep_edge_split o' g oo He) as [[_ Hx] | [Hold Hnep]].
      + exfalso. exact (rep_no (eq_sym Hx)).
      + destruct (rep_other_pred o' g HF HW HOW HWU Hold Hnep) as [Y | Y];
          [left | right]; apply rep_keep_det;
          [exact Y | discriminate | discriminate
          |exact Y | discriminate | discriminate].
  Qed.

  Lemma rep_FLR : FLR s -> FLR s'.
  Proof.
    intros H o o' g Tr Hfl He.
    destruct (rep_edge_split o' g o He) as [[_ Hx] | [Hold _]].
    - exfalso. subst o. rewrite Hfl_on in Hfl. discriminate.
    - exact (H o o' g Tr Hfl Hold).
  Qed.

  Lemma rep_FPI : FNR s -> FPI FType s -> FPI FType s'.
  Proof.
    intros HF H o g x t lw' Hob He Hft Hlk'.
    destruct (rep_fresh_inv o t Hob) as [Hne Hob0].
    simpl in Hlk'. rewrite Hlk in Hlk'. injection Hlk' as <-.
    destruct (rep_edge_split o g x He) as [[Heq _] | [Hold _]].
    - exfalso. injection Heq as -> ->. exact (proj1 (HF op t lw Hob0) Hitr_op).
    - assert (Hxne : x <> oo)
        by (intros ->; exact (Hno_fresh_pred o t g Hob0 Hold)).
      apply (Hkeep x _ (H o g x t lw Hob0 Hold Hft Hlk));
        [by injection 1 | by injection 1 as ->].
  Qed.

  Lemma rep_HD : FNR s -> WULK s -> HD s -> HD s'.
  Proof.
    intros HF HW H o g x He Hnd.
    destruct (rep_edge_split o g x He) as [[_ ->] | [Hold _]].
    - exact (rep_InHeap on Hin_on).
    - destruct (decide (o = on)) as [-> | Hne].
      + apply rep_InHeap.
        exact (H oo g x (rep_mirror_edge g x Hold) (rep_live oo HF HW Hitr_oo)).
      + apply rep_InHeap. apply (H o g x Hold).
        intros Hd. exact (Hnd (rep_detached_keep o Hne Hd)).
  Qed.

  Lemma rep_UNQRT_a : UNQRT_a s -> UNQRT_a s'.
  Proof.
    intros H o g He.
    destruct (rep_edge_split o g (rt (ms s')) He) as [[_ Hx] | [Hold _]].
    - exact (Hnrt (eq_sym Hx)).
    - exact (H o g Hold).
  Qed.

  Lemma rep_UNQRT_b : UNQRT_b s -> UNQRT_b s'.
  Proof.
    intros H p x lw' Hlk' Hr.
    simpl in Hlk'. rewrite Hlk in Hlk'. injection Hlk' as <-.
    destruct (hstar_replace_char (hp m) (rt m) op f oo on p x
                Hmir rep_np Hedge rep_noback Hr) as [Hpre | [-> _]].
    - assert (Hno : x <> oo).
      { intros ->. exact (replace_unreachable (hp m) (rt m) op f oo on rho
                            HU Hmir Hrho Hedge rep_unreach p Hr). }
      destruct (H p x lw Hlk Hpre) as [Hit | Hrt].
      + left. apply (Hkeep x _ Hit); [by injection 1 | by injection 1 as ->].
      + right. apply (Hkeep x _ Hrt); [by injection 1 | by injection 1].
    - by left.
  Qed.

  Lemma rep_WUNLK : WUNLK s -> WUNLK s'.
  Proof.
    intros H o t lw' Hlk' Hobs.
    simpl in Hlk'. rewrite Hlk in Hlk'. injection Hlk' as <-.
    destruct Hobs as [X | X];
      destruct (Hnew o _ X) as [Y | [[_ Hc] | [_ Hc]]].
    - exact (H o t lw Hlk (or_introl Y)).
    - discriminate.
    - injection Hc as Ht. exact Ht.
    - exact (H o t lw Hlk (or_intror Y)).
    - discriminate.
    - discriminate.
  Qed.

  Lemma rep_UNQR : UNQR s -> UNQR s'.
  Proof.
    intros _ p p' x H1 H2.
    exact (UNQR_replace (hp m) (rt m) op f oo on HU Hmir rep_np Hedge
             rep_noback rep_unreach p p' x H1 H2).
  Qed.

  Theorem replace_preserves_WellFormed :
    WellFormed FType s -> WellFormed FType s'.
  Proof.
    intros (HOW & HRWOW & HAWRT & HIFL & HULKR & HFLR & HWULK & HFR & HWFresh
            & HFNR & HFPI & HWNR & HRITR & HRINFL & HHD & HUa & HUb & HWU
            & HUq).
    repeat apply conj.
    - exact (rep_OW HFNR HWULK HOW).
    - exact (rep_RWOW HRWOW).
    - exact (rep_AWRT HUa HAWRT).
    - exact (rep_IFL HIFL).
    - exact (rep_ULKR HFNR HWULK HOW HWU HULKR).
    - exact (rep_FLR HFLR).
    - exact (rep_WULK HFNR HWULK).
    - exact (rep_FR HFR).
    - exact (rep_WFresh HWFresh).
    - exact (rep_FNR HFNR).
    - exact (rep_FPI HFNR HFPI).
    - exact (rep_WNR HWNR).
    - exact (rep_RITR HWNR HRITR).
    - exact (rep_RINFL HRINFL).
    - exact (rep_HD HFNR HWULK HHD).
    - exact (rep_UNQRT_a HUa).
    - exact (rep_UNQRT_b HUb).
    - exact (rep_WUNLK HWU).
    - exact (rep_UNQR HUq).
  Qed.

End replacement.

Print Assumptions replace_preserves_WellFormed.
