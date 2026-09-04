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
