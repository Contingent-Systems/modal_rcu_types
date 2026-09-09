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
      satisfying the other sixteen invariants and the published FNR in which
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
