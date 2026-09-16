(** * The binary search tree delete, as a chain of typed rules

    The two-child case of the BST delete is the paper's hardest worked example
    and the one the appendix annotates by hand.  The checker already replays it;
    this file replays the *write side* of it through the mechanized rules.

    The point is not the example.  It is that the six typed rules have never
    been chained: each was proved in isolation, and nothing has yet forced one
    rule's postcondition to *be* the next one's precondition.  Interface
    mismatches are the class of defect that only appears under composition, and
    this is the first thing that looks for them.

    What it reaches: the allocation and the splice --

        currentF = new;  currentF.Right = lmParent;
        currentF.Left = currentL;  parent.Left = currentF

    What it does not reach: [sync; free(current)].  SyncStart and SyncStop are
    not closed triples at all, and \textsc{T-Free}, which is one, has no typed
    form because its post-type is [undef] -- the one type with no reading as a
    resource.  So this is the allocation-and-splice half of the delete, not the
    reclamation half.

    Checked with Rocq 9.2, axiom-free. *)

From iris.algebra Require Import auth gmap gset excl local_updates.
From iris.algebra.lib Require Import excl_auth.
From iris.base_logic.lib Require Import invariants own.
From iris.proofmode Require Import proofmode.
From stdpp Require Import gmap sets.
From RCU Require Import WellFormed HeapPaths IrisGhost Denotations Actions
                        Triples.

(** ** The state the example runs in

    The tree is four nodes: the parent (which is the root of the fragment the
    rules see), the node being deleted, and its two children.  Two RCU fields,
    which is the class declaration the allocation rule needs. *)

Definition Lft : FName := 0.
Definition Rgt : FName := 1.
Definition Fs  : list FName := [Lft; Rgt].

Definition Rt   : Loc := 10.
Definition Cur  : Loc := 11.
Definition CurL : Loc := 12.
Definition LmP  : Loc := 13.

Definition vParent   : Var := 0.
Definition vCurrent  : Var := 1.
Definition vCurrentL : Var := 2.
Definition vLmParent : Var := 3.
Definition vCurrentF : Var := 4.

Definition W : TID := 7.

Definition C0 : gmap (Loc * FName) Val :=
  <[(Rt, Lft) := VLoc Cur]>
  (<[(Rt, Rgt) := VNull]>
  (<[(Cur, Lft) := VLoc CurL]>
  (<[(Cur, Rgt) := VLoc LmP]>
  (<[(CurL, Lft) := VNull]>
  (<[(CurL, Rgt) := VNull]>
  (<[(LmP, Lft) := VNull]>
  (<[(LmP, Rgt) := VNull]> ∅))))))).

Definition Ob0 : gmap Loc (gset obs) :=
  <[Rt := {[Oiter W]}]>
  (<[Cur := {[Oiter W]}]>
  (<[CurL := {[Oiter W]}]>
  (<[LmP := {[Oiter W]}]> ∅))).

Definition Sm0 : gmap (Var * TID) Loc :=
  <[(vParent, W) := Rt]>
  (<[(vCurrent, W) := Cur]>
  (<[(vCurrentL, W) := CurL]>
  (<[(vLmParent, W) := LmP]>
  (<[(vCurrentF, W) := Rt]> ∅)))).

Definition U0 : Var -> TID -> Prop := fun _ _ => False.

Definition G0 : Env :=
  [(vParent,   TItr [] (fun _ => None));
   (vCurrent,  TItr [Lft] (fun _ => None));
   (vCurrentL, TItr [Lft; Lft] (fun _ => None));
   (vLmParent, TItr [Lft; Rgt] (fun _ => None))].

(** Enumerating the prefixes of a short path, which is what the iterator
    denotation's chain condition quantifies over. *)
Lemma prefix1 {A : Type} (a : A) (p q : list A) :
  p ++ q = [a] -> p = [] \/ p = [a].
Proof.
  destruct p as [|c p]; [by left |]. simpl. injection 1 as <- Hp.
  destruct p; [by right | discriminate].
Qed.

Lemma prefix2 {A : Type} (a b : A) (p q : list A) :
  p ++ q = [a; b] -> p = [] \/ p = [a] \/ p = [a; b].
Proof.
  destruct p as [|c p]; [by left |]. simpl. injection 1 as <- Hp.
  destruct p as [|d p]; [by right; left |].
  simpl in Hp. injection Hp as <- Hp.
  destruct p; [by right; right | discriminate].
Qed.

(** The entry environment is what the rules will read.  Everything in it is a
    lookup in a concrete map, so the proof is computation. *)
Lemma G0_ok FType : EnvOK Rt W U0 FType Fs Sm0 Ob0 C0 ∅ G0.
Proof.
  intros x ty Hin.
  destruct Hin as [Heq | [Heq | [Heq | [Heq | []]]]];
    injection Heq as Hv1 Hv2; rewrite -Hv1 -Hv2; simpl.
  - (* parent, at the empty path *)
    exists Rt, {[Oiter W]}. repeat apply conj;
      [reflexivity | reflexivity | by apply elem_of_singleton
       | intros Hc; exact Hc | intros f w Hc; discriminate Hc | reflexivity |].
    intros rho1 rho2 Happ. apply app_eq_nil in Happ as [-> ->].
    exists Rt, {[Oiter W]}. repeat apply conj;
      [reflexivity | reflexivity | by apply elem_of_singleton].
  - (* current, one step left *)
    exists Cur, {[Oiter W]}. repeat apply conj;
      [reflexivity | reflexivity | by apply elem_of_singleton
       | intros Hc; exact Hc | intros f w Hc; discriminate Hc | reflexivity |].
    intros rho1 rho2 Happ. destruct (prefix1 Lft rho1 rho2 Happ) as [-> | ->].
    + exists Rt, {[Oiter W]}. repeat apply conj;
        [reflexivity | reflexivity | by apply elem_of_singleton].
    + exists Cur, {[Oiter W]}. repeat apply conj;
        [reflexivity | reflexivity | by apply elem_of_singleton].
  - (* current's left child *)
    exists CurL, {[Oiter W]}. repeat apply conj;
      [reflexivity | reflexivity | by apply elem_of_singleton
       | intros Hc; exact Hc | intros f w Hc; discriminate Hc | reflexivity |].
    intros rho1 rho2 Happ.
    destruct (prefix2 Lft Lft rho1 rho2 Happ) as [-> | [-> | ->]].
    + exists Rt, {[Oiter W]}. repeat apply conj;
        [reflexivity | reflexivity | by apply elem_of_singleton].
    + exists Cur, {[Oiter W]}. repeat apply conj;
        [reflexivity | reflexivity | by apply elem_of_singleton].
    + exists CurL, {[Oiter W]}. repeat apply conj;
        [reflexivity | reflexivity | by apply elem_of_singleton].
  - (* the leftmost node of current's right subtree *)
    exists LmP, {[Oiter W]}. repeat apply conj;
      [reflexivity | reflexivity | by apply elem_of_singleton
       | intros Hc; exact Hc | intros f w Hc; discriminate Hc | reflexivity |].
    intros rho1 rho2 Happ.
    destruct (prefix2 Lft Rgt rho1 rho2 Happ) as [-> | [-> | ->]].
    + exists Rt, {[Oiter W]}. repeat apply conj;
        [reflexivity | reflexivity | by apply elem_of_singleton].
    + exists Cur, {[Oiter W]}. repeat apply conj;
        [reflexivity | reflexivity | by apply elem_of_singleton].
    + exists LmP, {[Oiter W]}. repeat apply conj;
        [reflexivity | reflexivity | by apply elem_of_singleton].
Qed.

Print Assumptions G0_ok.

(** ** Step one: build the replacement

    [currentF = new].  The allocation hands back the environment with the
    variable rebound to [rcuFresh], and -- this is what chaining needed and
    what proving it in isolation did not -- four facts saying the new location
    is none of the ones the caller's maps already mention.  Without those the
    environment comes back but nothing can be looked up in the maps it is
    stated over, and the next rule cannot start. *)

Section bst.
  Context `{!rcuG Σ, !physG Σ, !heapG Σ, !lockG Σ, !stackG Σ, !freshG Σ,
            !invGS_gen hlc Σ}.
  Context (FType : FName -> FieldKind).
  Hypothesis HFs : forall g, FType g = RCUField -> In g Fs.
  (** The two declared fields are the RCU ones.  With the mutation rules no
      longer assuming that *every* field is an RCU field, this is consistent
      with the class declaration above -- which is the whole point of the
      repair, and what lets the chain continue past the allocation. *)
  Hypothesis HFrcu : forall g, In g Fs -> FType g = RCUField.

  Definition U1 : Var -> TID -> Prop :=
    fun y t => U0 y t /\ (y, t) <> (vCurrentF, W).

  Lemma bst_alloc N γm γh γl γs γo γf γr E :
    ↑N ⊆ E ->
    rcu_invT FType (phys γm γh γl γs Rt Fs) N γo γf γr -∗
    writer γo γs γh γl γf W Sm0 Ob0 C0 ∅ -∗
    fr_frag γr ∅
    ={E}=∗ ∃ n,
      ⌜n <> Rt⌝
      ∗ ⌜forall k v, C0 !! k = Some v -> k.1 <> n⌝
      ∗ ⌜forall o sg, Ob0 !! o = Some sg -> o <> n⌝
      ∗ ⌜forall k o, Sm0 !! k = Some o -> o <> n⌝
      ∗ writer γo γs γh γl γf W
          (<[(vCurrentF, W) := n]> Sm0) (<[n := {[Ofresh W]}]> Ob0)
          (newcells Fs n ∪ C0) ∅
      ∗ fr_frag γr ({[n]} : gset Loc)
      ∗ ⌜EnvOK Rt W U1 FType Fs
           (<[(vCurrentF, W) := n]> Sm0) (<[n := {[Ofresh W]}]> Ob0)
           (newcells Fs n ∪ C0) ∅
           ((vCurrentF, TFresh (fun _ => None)) :: G0)⌝.
  Proof.
    iIntros (HN) "#Hinv Hw Hfr".
    iMod (alloc_typed FType Rt Fs N γm γh γl γs γo γf γr E W vCurrentF Rt
            U0 Sm0 Ob0 C0 ∅ ∅ (fun _ _ => VNull) G0 HN
            with "Hinv Hw Hfr")
      as (n) "(Hw & Hfr & %Hnr & %Hcn & %Hon & %Hsn & %HFrC & %Hok)".
    { (* the two RCU fields are distinct *)
      rewrite /Fs. apply NoDup_cons; split; [| apply NoDup_singleton].
      intros Hc. apply elem_of_cons in Hc.
      destruct Hc as [Hc | Hc]; [discriminate | by apply not_elem_of_nil in Hc]. }
    { exact HFs. }
    { intros q g Hq. by apply not_elem_of_empty in Hq. }
    { reflexivity. }
    { intros y ty f Hin.
      destruct Hin as [Heq | [Heq | [Heq | [Heq | []]]]];
        injection Heq as Hv1 Hv2; rewrite -Hv2; discriminate. }
    { exact (G0_ok FType). }
    iModIntro. iExists n. iFrame.
    (* the empty set the allocation started from, and the filter it applied,
       are both identities here *)
    rewrite union_empty_l_L.
    iFrame. iPureIntro.
    repeat split; [exact Hnr | exact Hcn | exact Hon | exact Hsn |].
    intros y ty Hin. apply Hok. destruct Hin as [Heq | Hin]; [by left |].
    right. by rewrite /G0 /=.
  Qed.

  (** ** Step two: write the replacement's right field

      [currentF.Right = lmParent].  Everything the rule asks is a lookup in the
      post-allocation maps, and every one of those reduces to a lookup in the
      caller's own maps because the allocated location is none of theirs --
      which is what step one now exports. *)

  (** Named lookups, so the path computation stays in terms of the node names
      rather than unfolding them to numerals. *)
  Lemma C0_RtL : C0 !! (Rt, Lft) = Some (VLoc Cur).
  Proof. reflexivity. Qed.
  Lemma C0_CurL : C0 !! (Cur, Lft) = Some (VLoc CurL).
  Proof. reflexivity. Qed.
  Lemma C0_CurR : C0 !! (Cur, Rgt) = Some (VLoc LmP).
  Proof. reflexivity. Qed.

  Lemma C1_old n k : k.1 <> n -> (newcells Fs n ∪ C0) !! k = C0 !! k.
  Proof. intros Hk. apply lookup_union_r. exact (newcells_other Fs n k Hk). Qed.

  Lemma C1_new n g : In g Fs -> (newcells Fs n ∪ C0) !! (n, g) = Some VNull.
  Proof.
    intros Hg. apply lookup_union_Some_l. apply (newcells_at Fs n g); [| exact Hg].
    apply NoDup_cons; split; [| apply NoDup_singleton].
    intros Hc. apply elem_of_cons in Hc.
    destruct Hc as [Hc | Hc]; [discriminate | by apply not_elem_of_nil in Hc].
  Qed.

  Lemma bst_write_right N γm γh γl γs γo γf γr E n :
    ↑N ⊆ E ->
    n <> Rt ->
    (forall k v, C0 !! k = Some v -> k.1 <> n) ->
    (forall o sg, Ob0 !! o = Some sg -> o <> n) ->
    rcu_invT FType (phys γm γh γl γs Rt Fs) N γo γf γr -∗
    writer γo γs γh γl γf W
      (<[(vCurrentF, W) := n]> Sm0) (<[n := {[Ofresh W]}]> Ob0)
      (newcells Fs n ∪ C0) ∅ -∗
    ⌜EnvOK Rt W U1 FType Fs
       (<[(vCurrentF, W) := n]> Sm0) (<[n := {[Ofresh W]}]> Ob0)
       (newcells Fs n ∪ C0) ∅
       ((vCurrentF, TFresh (fun _ => None)) :: G0)⌝
    ={E}=∗ writer γo γs γh γl γf W
             (<[(vCurrentF, W) := n]> Sm0) (<[n := {[Ofresh W]}]> Ob0)
             (<[(n, Rgt) := VLoc LmP]> (newcells Fs n ∪ C0)) ∅
           ∗ ⌜EnvOK Rt W U1 FType Fs
                (<[(vCurrentF, W) := n]> Sm0) (<[n := {[Ofresh W]}]> Ob0)
                (<[(n, Rgt) := VLoc LmP]> (newcells Fs n ∪ C0)) ∅
                ([(vCurrentF, TFresh (fun h => if decide (h = Rgt)
                                               then Some (FVar vLmParent)
                                               else None))] ++ G0)⌝.
  Proof.
    iIntros (HN Hnr Hcn Hon) "#Hinv Hw %Hok".
    assert (HnL : n <> LmP)
      by (intros ->; by apply (Hon LmP {[Oiter W]} eq_refl)).
    iMod (write_fresh_typed FType Rt Fs N γm γh γl γs γo γf γr E W
            vCurrentF vLmParent n Rgt LmP Lft U1
            (<[(vCurrentF, W) := n]> Sm0) (<[n := {[Ofresh W]}]> Ob0)
            (newcells Fs n ∪ C0) ∅ {[Ofresh W]} {[Oiter W]} VNull VNull
            (fun _ => None) G0 HN (HFrcu Rgt (or_intror (or_introl eq_refl))) Hnr
            with "Hinv Hw") as "(Hw & %Hok')".
    { discriminate. }
    { exact HnL. }
    { by rewrite lookup_insert_eq. }
    { by rewrite lookup_insert_eq. }
    { by apply elem_of_singleton. }
    { by intros [Hc _]. }
    { rewrite lookup_insert_ne; [reflexivity | discriminate]. }
    { rewrite lookup_insert_ne; [reflexivity | exact HnL]. }
    { by apply elem_of_singleton. }
    { apply C1_new. by right; left. }
    { rewrite (C1_old n (LmP, Lft)); [reflexivity | exact (fun Hc => HnL (eq_sym Hc))]. }
    { intros h w _ Hc. discriminate Hc. }
    { intros h Hh _. by apply C1_new. }
    { (* the write touches no cell the rest of the environment reads *)
      repeat split.
      - intros y rho Ny Hin.
        assert (HnC : n <> Cur)
          by (intros ->; by apply (Hon Cur {[Oiter W]} eq_refl)).
        destruct Hin as [Heq | [Heq | [Heq | [Heq | []]]]];
          injection Heq as Hv1 Hv2; rewrite -Hv2; simpl.
        + by intros [].
        + cbn [pathcells]. rewrite (C1_old n (Rt, Lft));
            [| exact (fun Hc => Hnr (eq_sym Hc))].
          rewrite C0_RtL. cbn [pathcells].
          intros [Hc | []]. injection Hc as Hc. by apply Hnr.
        + cbn [pathcells]. rewrite (C1_old n (Rt, Lft));
            [| exact (fun Hc => Hnr (eq_sym Hc))].
          rewrite C0_RtL. cbn [pathcells].
          rewrite (C1_old n (Cur, Lft));
            [| exact (fun Hc => HnC (eq_sym Hc))].
          rewrite C0_CurL. cbn [pathcells].
          intros [Hc | [Hc | []]]; injection Hc as Hc;
            [by apply Hnr | by apply HnC].
        + cbn [pathcells]. rewrite (C1_old n (Rt, Lft));
            [| exact (fun Hc => Hnr (eq_sym Hc))].
          rewrite C0_RtL. cbn [pathcells].
          rewrite (C1_old n (Cur, Rgt));
            [| exact (fun Hc => HnC (eq_sym Hc))].
          rewrite C0_CurR. cbn [pathcells].
          intros [Hc | [Hc | []]]; injection Hc as Hc;
            [by apply Hnr | by apply HnC].
      - intros y Ny o Hin _.
        destruct Hin as [Heq | [Heq | [Heq | [Heq | []]]]];
          injection Heq as _ Hc; discriminate Hc.
      - intros y ty o Hin Hstk Hc. destruct Hin as
          [Heq | [Heq | [Heq | [Heq | []]]]];
          injection Heq as Hv1 Hv2; rewrite -Hv2; reflexivity. }
    { apply (EnvOK_incl Rt W U1 FType Fs _ _ _ ∅
               ((vCurrentF, TFresh (fun _ => None)) :: G0));
        [intros y ty Hin; by right | exact Hok]. }
    iModIntro. iFrame. by iPureIntro.
  Qed.

  (** ** Step three: write the replacement's left field

      [currentF.Left = currentL].  The same rule again, and this time its field
      map is not empty -- the entry written in step two has to be carried
      across, which is what the field-map condition is for. *)
  Lemma bst_write_left N γm γh γl γs γo γf γr E n :
    ↑N ⊆ E ->
    n <> Rt ->
    (forall k v, C0 !! k = Some v -> k.1 <> n) ->
    (forall o sg, Ob0 !! o = Some sg -> o <> n) ->
    rcu_invT FType (phys γm γh γl γs Rt Fs) N γo γf γr -∗
    writer γo γs γh γl γf W
      (<[(vCurrentF, W) := n]> Sm0) (<[n := {[Ofresh W]}]> Ob0)
      (<[(n, Rgt) := VLoc LmP]> (newcells Fs n ∪ C0)) ∅ -∗
    ⌜EnvOK Rt W U1 FType Fs
       (<[(vCurrentF, W) := n]> Sm0) (<[n := {[Ofresh W]}]> Ob0)
       (<[(n, Rgt) := VLoc LmP]> (newcells Fs n ∪ C0)) ∅
       ([(vCurrentF, TFresh (fun h => if decide (h = Rgt)
                                      then Some (FVar vLmParent) else None))]
        ++ G0)⌝
    ={E}=∗ writer γo γs γh γl γf W
             (<[(vCurrentF, W) := n]> Sm0) (<[n := {[Ofresh W]}]> Ob0)
             (<[(n, Lft) := VLoc CurL]>
                (<[(n, Rgt) := VLoc LmP]> (newcells Fs n ∪ C0))) ∅
           ∗ ⌜EnvOK Rt W U1 FType Fs
                (<[(vCurrentF, W) := n]> Sm0) (<[n := {[Ofresh W]}]> Ob0)
                (<[(n, Lft) := VLoc CurL]>
                   (<[(n, Rgt) := VLoc LmP]> (newcells Fs n ∪ C0))) ∅
                ([(vCurrentF,
                   TFresh (fun h => if decide (h = Lft)
                                    then Some (FVar vCurrentL)
                                    else if decide (h = Rgt)
                                         then Some (FVar vLmParent)
                                         else None))] ++ G0)⌝.
  Proof.
    iIntros (HN Hnr Hcn Hon) "#Hinv Hw %Hok".
    assert (HnC : n <> Cur) by (intros ->; by apply (Hon Cur {[Oiter W]} eq_refl)).
    assert (HnL : n <> LmP) by (intros ->; by apply (Hon LmP {[Oiter W]} eq_refl)).
    assert (HnCL : n <> CurL)
      by (intros ->; by apply (Hon CurL {[Oiter W]} eq_refl)).
    iMod (write_fresh_typed FType Rt Fs N γm γh γl γs γo γf γr E W
            vCurrentF vCurrentL n Lft CurL Lft U1
            (<[(vCurrentF, W) := n]> Sm0) (<[n := {[Ofresh W]}]> Ob0)
            (<[(n, Rgt) := VLoc LmP]> (newcells Fs n ∪ C0)) ∅
            {[Ofresh W]} {[Oiter W]} VNull VNull
            (fun h => if decide (h = Rgt) then Some (FVar vLmParent) else None)
            G0 HN (HFrcu Lft (or_introl eq_refl)) Hnr
            with "Hinv Hw") as "(Hw & %Hok')".
    { discriminate. }
    { exact HnCL. }
    { by rewrite lookup_insert_eq. }
    { by rewrite lookup_insert_eq. }
    { by apply elem_of_singleton. }
    { by intros [Hc _]. }
    { rewrite lookup_insert_ne; [reflexivity | discriminate]. }
    { rewrite lookup_insert_ne; [reflexivity | exact HnCL]. }
    { by apply elem_of_singleton. }
    { rewrite lookup_insert_ne; [| intros Hc; injection Hc as Hc; discriminate].
      apply C1_new. by left. }
    { rewrite lookup_insert_ne;
        [| intros Hc; injection Hc as Hc; by apply HnCL].
      rewrite (C1_old n (CurL, Lft));
        [reflexivity | exact (fun Hc => HnCL (eq_sym Hc))]. }
    { (* the field written in step two is carried across *)
      intros h w Hne Hw.
      destruct (decide (h = Rgt)) as [Hhr | Hhr]; [| discriminate Hw].
      injection Hw as <-. subst h.
      exists LmP, {[Oiter W]}. repeat apply conj.
      - rewrite lookup_insert_ne; [reflexivity | discriminate].
      - by rewrite lookup_insert_eq.
      - rewrite lookup_insert_ne; [reflexivity | exact HnL].
      - by apply elem_of_singleton. }
    { intros h Hh Hnone. exfalso.
      destruct (decide (h = Lft)) as [Hhl | Hhl]; [discriminate Hnone |].
      destruct (decide (h = Rgt)) as [Hhr | Hhr]; [discriminate Hnone |].
      destruct Hh as [Hc | [Hc | []]];
        [apply Hhl; by rewrite -Hc | apply Hhr; by rewrite -Hc]. }
    { repeat split.
      - intros y rho Ny Hin.
        destruct Hin as [Heq | [Heq | [Heq | [Heq | []]]]];
          injection Heq as Hv1 Hv2; rewrite -Hv2; cbn [pathcells].
        + by intros [].
        + rewrite lookup_insert_ne;
            [| intros Hc; injection Hc as Hc; by apply Hnr].
          rewrite (C1_old n (Rt, Lft)); [| exact (fun Hc => Hnr (eq_sym Hc))].
          rewrite C0_RtL. cbn [pathcells].
          intros [Hc | []]. injection Hc as Hc. by apply Hnr.
        + rewrite lookup_insert_ne;
            [| intros Hc; injection Hc as Hc; by apply Hnr].
          rewrite (C1_old n (Rt, Lft)); [| exact (fun Hc => Hnr (eq_sym Hc))].
          rewrite C0_RtL. cbn [pathcells].
          rewrite lookup_insert_ne;
            [| intros Hc; injection Hc as Hc; by apply HnC].
          rewrite (C1_old n (Cur, Lft)); [| exact (fun Hc => HnC (eq_sym Hc))].
          rewrite C0_CurL. cbn [pathcells].
          intros [Hc | [Hc | []]]; injection Hc as Hc;
            [by apply Hnr | by apply HnC].
        + rewrite lookup_insert_ne;
            [| intros Hc; injection Hc as Hc; by apply Hnr].
          rewrite (C1_old n (Rt, Lft)); [| exact (fun Hc => Hnr (eq_sym Hc))].
          rewrite C0_RtL. cbn [pathcells].
          rewrite lookup_insert_ne;
            [| intros Hc; injection Hc as Hc; by apply HnC].
          rewrite (C1_old n (Cur, Rgt)); [| exact (fun Hc => HnC (eq_sym Hc))].
          rewrite C0_CurR. cbn [pathcells].
          intros [Hc | [Hc | []]]; injection Hc as Hc;
            [by apply Hnr | by apply HnC].
      - intros y Ny o Hin _.
        destruct Hin as [Heq | [Heq | [Heq | [Heq | []]]]];
          injection Heq as _ Hc; discriminate Hc.
      - intros y ty o Hin Hstk Hc.
        destruct Hin as [Heq | [Heq | [Heq | [Heq | []]]]];
          injection Heq as Hv1 Hv2; rewrite -Hv2; reflexivity. }
    { apply (EnvOK_incl Rt W U1 FType Fs _ _ _ ∅
               ([(vCurrentF, TFresh (fun h => if decide (h = Rgt)
                                              then Some (FVar vLmParent)
                                              else None))] ++ G0));
        [intros y ty Hin; by right | exact Hok]. }
    iModIntro. iFrame. by iPureIntro.
  Qed.

  (** ** The three steps, chained

      This is what the exercise was for: one rule's postcondition handed
      directly to the next. *)
  Lemma bst_build_replacement N γm γh γl γs γo γf γr E :
    ↑N ⊆ E ->
    rcu_invT FType (phys γm γh γl γs Rt Fs) N γo γf γr -∗
    writer γo γs γh γl γf W Sm0 Ob0 C0 ∅ -∗
    fr_frag γr ∅
    ={E}=∗ ∃ n,
      ⌜n <> Rt⌝
      ∗ ⌜forall k v, C0 !! k = Some v -> k.1 <> n⌝
      ∗ writer γo γs γh γl γf W
        (<[(vCurrentF, W) := n]> Sm0) (<[n := {[Ofresh W]}]> Ob0)
        (<[(n, Lft) := VLoc CurL]>
           (<[(n, Rgt) := VLoc LmP]> (newcells Fs n ∪ C0))) ∅
      ∗ fr_frag γr ({[n]} : gset Loc)
      ∗ ⌜EnvOK Rt W U1 FType Fs
           (<[(vCurrentF, W) := n]> Sm0) (<[n := {[Ofresh W]}]> Ob0)
           (<[(n, Lft) := VLoc CurL]>
              (<[(n, Rgt) := VLoc LmP]> (newcells Fs n ∪ C0))) ∅
           ([(vCurrentF,
              TFresh (fun h => if decide (h = Lft)
                               then Some (FVar vCurrentL)
                               else if decide (h = Rgt)
                                    then Some (FVar vLmParent)
                                    else None))] ++ G0)⌝.
  Proof.
    iIntros (HN) "#Hinv Hw Hfr".
    iMod (bst_alloc N γm γh γl γs γo γf γr E HN with "Hinv Hw Hfr")
      as (n) "(%Hnr & %Hcn & %Hon & %Hsn & Hw & Hfr & %Hok)".
    iMod (bst_write_right N γm γh γl γs γo γf γr E n HN Hnr Hcn Hon
            with "Hinv Hw []") as "(Hw & %Hok2)".
    { iPureIntro. intros y ty Hin. apply Hok.
      destruct Hin as [Heq | Hin]; [by left | by right]. }
    iMod (bst_write_left N γm γh γl γs γo γf γr E n HN Hnr Hcn Hon
            with "Hinv Hw []") as "(Hw & %Hok3)".
    { by iPureIntro. }
    iModIntro. iExists n. iFrame. by iPureIntro.
  Qed.

End bst.

(** ** What blocked the fourth step, and the repair

    The splice is \textsc{T-Replace}, and for a while it could not be chained
    onto the three above -- not because of any interface mismatch, but because
    its hypotheses were inconsistent with the allocation's.

    \textsc{T-Replace} was stated with "every field is an RCU field", the
    simplification the mutation rules inherit from the report.
    \textsc{T-Alloc} needs the class declaration the finite heap forced: every
    RCU field is one of the node's declared fields.  Together those say every
    field name is declared, and there are infinitely many field names and two
    declared ones.  [class_excludes_all_rcu] is the two-line proof, and it is
    kept because the incompatibility is a fact about the published rules.

    Tracing where the assumption was actually used said what the repair is.  The
    mutation proofs reach for it in six places, and every one of them applies it
    to an edge already in hand -- they are proving something about a node that
    some field points at.  So what they need is not that every field is an RCU
    field but that every field *holding a reference* is: the heap's reference
    structure lives in RCU fields, and a scalar field holds a scalar.  That is
    [RefsRCU], it is carried where the other physical-state conditions are, and
    it is consistent with a class declaration -- which is what unblocks this
    chain.

    The weakening costs nothing: all-RCU implies it, so every proof that used
    the old hypothesis still goes through, and the two rules that write a field
    which did not previously hold a reference -- \textsc{T-WriteFH} and
    \textsc{T-LinkF-Null} -- now say so, which they should have all along. *)

Lemma class_excludes_all_rcu (FType : FName -> FieldKind) :
  (forall g, FType g = RCUField) ->
  (forall g, FType g = RCUField -> In g Fs) ->
  False.
Proof.
  intros Hall Hcls. pose proof (Hcls 2 (Hall 2)) as Hc.
  destruct Hc as [Hc | [Hc | []]]; discriminate.
Qed.

Print Assumptions class_excludes_all_rcu.

Print Assumptions bst_alloc.
Print Assumptions bst_write_right.
Print Assumptions bst_write_left.
Print Assumptions bst_build_replacement.

(** ** The fourth step, and the second thing chaining found

    With the repair in place \textsc{T-Replace} and \textsc{T-Alloc} can appear
    in one program, so the splice is no longer blocked by their premises.  It is
    blocked by something else, and the something else is in this development
    rather than in the rules.

    Replacing [current] by the fresh node re-routes every path that ran through
    [current]: [currentL] is still at $l.l$ afterwards, because the fresh node
    mirrors what it replaces, but the *intermediate* node on that path is now
    the fresh one.  The chain-of-iterators condition in [rcuItr] is about those
    intermediate nodes, so it has to be re-derived rather than framed.

    The framing lemmas do not do that.  [EnvOK_obs] frames a variable across a
    change to one location's observations provided no path in the environment
    passes through that location -- and here two of them do.  The condition is
    not merely unproved, it is false, which is what the lemma below says.

    So the splice needs a framing lemma that knows about mirroring: the paths
    are unchanged as paths, and the nodes they pass through are swapped one for
    one.  That is [EnvOK_mirror], built for this, and \textsc{T-Replace} is
    stated against it rather than against the other two.  [C3_sole_Cur] below
    is the one thing it asks of the concrete tree -- that the deleted node has a
    single predecessor, which is No-Sharing in general and a finite check
    here. *)

Section bst4.
  Context `{!rcuG Σ, !physG Σ, !heapG Σ, !lockG Σ, !stackG Σ, !freshG Σ,
            !invGS_gen hlc Σ}.
  Context (FType : FName -> FieldKind).

  Definition Sm1 (n : Loc) : gmap (Var * TID) Loc :=
    <[(vCurrentF, W) := n]> Sm0.

  Definition C3 (n : Loc) : gmap (Loc * FName) Val :=
    <[(n, Lft) := VLoc CurL]>
      (<[(n, Rgt) := VLoc LmP]> (newcells Fs n ∪ C0)).

  (** What is left of the environment once the three variables the splice
      touches -- the parent, the fresh node and the node it replaces -- are
      taken out. *)
  Definition Grest : Env :=
    [(vCurrentL, TItr [Lft; Lft] (fun _ => None));
     (vLmParent, TItr [Lft; Rgt] (fun _ => None))].

  Lemma C3_RtL n : n <> Rt -> C3 n !! (Rt, Lft) = Some (VLoc Cur).
  Proof.
    intros Hn. rewrite /C3.
    rewrite lookup_insert_ne; [| intros Hc; injection Hc as Hc; by apply Hn].
    rewrite lookup_insert_ne; [| intros Hc; injection Hc as Hc; by apply Hn].
    rewrite (C1_old n (Rt, Lft)); [exact C0_RtL |].
    exact (fun Hc => Hn (eq_sym Hc)).
  Qed.

  Definition Ob1 (n : Loc) : gmap Loc (gset obs) :=
    <[n := {[Ofresh W]}]> Ob0.

  (** The value the two writes left in the replacement's fields, which is also
      what the node it replaces holds -- that is the mirroring. *)
  Definition Valo : FName -> Val :=
    fun g => if decide (g = Lft) then VLoc CurL else VLoc LmP.

  Lemma C3_CurL n : n <> Cur -> C3 n !! (Cur, Lft) = Some (VLoc CurL).
  Proof.
    intros Hn. rewrite /C3.
    rewrite lookup_insert_ne; [| intros Hc; injection Hc as Hc; by apply Hn].
    rewrite lookup_insert_ne; [| intros Hc; injection Hc as Hc; by apply Hn].
    rewrite (C1_old n (Cur, Lft)); [exact C0_CurL |].
    exact (fun Hc => Hn (eq_sym Hc)).
  Qed.

  Lemma C3_CurR n : n <> Cur -> C3 n !! (Cur, Rgt) = Some (VLoc LmP).
  Proof.
    intros Hn. rewrite /C3.
    rewrite lookup_insert_ne; [| intros Hc; injection Hc as Hc; by apply Hn].
    rewrite lookup_insert_ne; [| intros Hc; injection Hc as Hc; by apply Hn].
    rewrite (C1_old n (Cur, Rgt)); [exact C0_CurR |].
    exact (fun Hc => Hn (eq_sym Hc)).
  Qed.

  Lemma C3_new n g : In g Fs -> C3 n !! (n, g) = Some (Valo g).
  Proof.
    intros Hg. rewrite /C3 /Valo.
    destruct Hg as [Hc | [Hc | []]]; rewrite -Hc.
    - rewrite lookup_insert_eq. by case_decide.
    - rewrite lookup_insert_ne; [| intros Hc'; by injection Hc' as Hc'].
      rewrite lookup_insert_eq. case_decide as Hd; [discriminate Hd | reflexivity].
  Qed.

  Lemma C3_old n g : n <> Cur -> In g Fs -> C3 n !! (Cur, g) = Some (Valo g).
  Proof.
    intros Hn Hg. rewrite /Valo. destruct Hg as [Hc | [Hc | []]]; rewrite -Hc.
    - case_decide as Hd; [exact (C3_CurL n Hn) | by destruct Hd].
    - case_decide as Hd; [discriminate Hd | exact (C3_CurR n Hn)].
  Qed.

  (** The deleted node has one predecessor.  In the concrete tree this is a
      finite check, and it is what the mirror framing lemma asks for -- the
      general fact behind it is No-Sharing. *)
  Lemma C0_sole_Cur b h : C0 !! (b, h) = Some (VLoc Cur) -> (b, h) = (Rt, Lft).
  Proof.
    rewrite /C0. intros H.
    do 8 (apply lookup_insert_Some in H;
          destruct H as [[Heq Hv] | [_ H]];
          [ first [exact (eq_sym Heq) | discriminate Hv
                   | (injection Hv as Hv; discriminate Hv)] | ]).
    rewrite lookup_empty in H. discriminate H.
  Qed.

  Lemma C1_miss n h :
    ~ In h Fs -> (newcells Fs n ∪ C0) !! (n, h) = C0 !! (n, h).
  Proof.
    intros Hh. apply lookup_union_r. rewrite /newcells.
    apply not_elem_of_list_to_map_1. intros Hc.
    apply list_elem_of_fmap_1 in Hc. destruct Hc as [p [Hp1 Hpin]].
    apply list_elem_of_fmap_1 in Hpin. destruct Hpin as [g [-> Hg]].
    simpl in Hp1. injection Hp1 as Hb. apply Hh.
    apply list_elem_of_In. by rewrite Hb.
  Qed.

  Lemma C3_sole_Cur n :
    n <> Rt -> n <> Cur -> n <> CurL -> n <> LmP ->
    forall b h, C3 n !! (b, h) = Some (VLoc Cur) -> (b, h) = (Rt, Lft).
  Proof.
    intros Hr Hc Hcl Hlm b h H. rewrite /C3 in H.
    apply lookup_insert_Some in H. destruct H as [[Heq Hv] | [Hne1 H]];
      [by injection Hv |].
    apply lookup_insert_Some in H. destruct H as [[Heq Hv] | [Hne2 H]];
      [by injection Hv |].
    destruct (decide (b = n)) as [-> | Hbn].
    - destruct (in_dec Nat.eq_dec h Fs) as [Hin | Hni].
      + rewrite (C1_new n h Hin) in H. discriminate.
      + rewrite (C1_miss n h Hni) in H.
        exfalso. pose proof (C0_sole_Cur n h H) as Hc'.
        injection Hc' as Hc'. by apply Hr.
    - rewrite (C1_old n (b, h)) in H; [| by simpl].
      exact (C0_sole_Cur b h H).
  Qed.

  (** The framing condition the splice would need is false: both surviving
      variables reach the replaced node on the way to their own. *)
  Lemma replace_cannot_frame n :
    n <> Rt -> ~ ReadsObs Rt (C3 n) (Sm1 n) W Grest Cur.
  Proof.
    intros Hn (_ & Hpaths & _ & _).
    apply (Hpaths vCurrentL [Lft; Lft] (fun _ => None) [Lft] [Lft]);
      [by left | reflexivity |].
    cbn [hstarC]. rewrite (C3_RtL n Hn). reflexivity.
  Qed.

  (** The fields the two writes left behind, as the value function the
      free-list side of \textsc{T-Replace} asks for: every cell of the fresh
      node holds what the node it replaces holds. *)
  Definition Val3 (n : Loc) : Loc -> FName -> Val :=
    fun q g => if decide (q = n) then Valo g else VNull.

  Lemma C0_CurLL : C0 !! (CurL, Lft) = Some VNull.
  Proof. reflexivity. Qed.
  Lemma C0_LmPL : C0 !! (LmP, Lft) = Some VNull.
  Proof. reflexivity. Qed.

  (** The four distinctness facts the splice needs, all of them consequences of
      the single freshness fact the allocation exports. *)
  Lemma n_fresh n :
    (forall k v, C0 !! k = Some v -> k.1 <> n) ->
    n <> Cur /\ n <> CurL /\ n <> LmP.
  Proof.
    intros Hcn. repeat apply conj; intros ->.
    - exact (Hcn (Cur, Lft) _ C0_CurL eq_refl).
    - exact (Hcn (CurL, Lft) _ C0_CurLL eq_refl).
    - exact (Hcn (LmP, Lft) _ C0_LmPL eq_refl).
  Qed.

  Lemma C3_star1 n : n <> Rt -> hstarC (C3 n) Rt [Lft] = Some Cur.
  Proof. intros Hn. cbn [hstarC]. rewrite (C3_RtL n Hn). reflexivity. Qed.

  Lemma C3_star2L n : n <> Rt -> n <> Cur ->
    hstarC (C3 n) Rt [Lft; Lft] = Some CurL.
  Proof.
    intros Hr Hc. cbn [hstarC]. rewrite (C3_RtL n Hr).
    rewrite (C3_CurL n Hc). reflexivity.
  Qed.

  Lemma C3_star2R n : n <> Rt -> n <> Cur ->
    hstarC (C3 n) Rt [Lft; Rgt] = Some LmP.
  Proof.
    intros Hr Hc. cbn [hstarC]. rewrite (C3_RtL n Hr).
    rewrite (C3_CurR n Hc). reflexivity.
  Qed.

  (** What survives the splice, and why.  Neither surviving variable is the
      parent, the replaced node or the replacement; neither names a field; both
      run on declared fields; and no prefix of either path reaches the fresh
      node.  That last clause is the one the framing lemma could not get from
      the other two shapes -- the paths *do* pass through the replaced node, so
      what frames them is that the replacement is indistinguishable from it. *)
  Lemma Grest_mirror n :
    n <> Rt -> n <> Cur -> n <> CurL -> n <> LmP ->
    MirrorOK Rt (C3 n) (Sm1 n) W Grest Rt Lft Cur n Fs.
  Proof.
    intros Hr Hc Hcl Hlm.
    assert (Hsm : forall x ty, In (x, ty) Grest ->
                    Sm1 n !! (x, W) = Some CurL \/ Sm1 n !! (x, W) = Some LmP).
    { intros x ty Hin. destruct Hin as [Heq | [Heq | []]];
        injection Heq as Hv1 Hv2; rewrite -Hv1; [by left | by right]. }
    repeat apply conj.
    - intros x ty Hin. destruct (Hsm x ty Hin) as [H | H]; rewrite H;
        intros Hc'; injection Hc' as Hc'; discriminate Hc'.
    - intros x ty Hin. destruct (Hsm x ty Hin) as [H | H]; rewrite H;
        intros Hc'; injection Hc' as Hc'; [by apply Hcl | by apply Hlm].
    - intros x ty g z Hin Hty. exfalso.
      destruct Hin as [Heq | [Heq | []]];
        injection Heq as Hv1 Hv2; rewrite -Hv2 in Hty; discriminate Hty.
    - intros x rho Nf Hin g Hg.
      destruct Hin as [Heq | [Heq | []]]; injection Heq as Hv1 Hv2 Hv3;
        rewrite -Hv2 in Hg;
        destruct Hg as [<- | [<- | []]]; [by left | by left | by left | by right; left].
    - intros x rho Nf rho1 rho2 Hin Happ.
      destruct Hin as [Heq | [Heq | []]]; injection Heq as Hv1 Hv2 Hv3;
        rewrite -Hv2 in Happ.
      + destruct (prefix2 Lft Lft rho1 rho2 Happ) as [-> | [-> | ->]].
        * intros Hc'; injection Hc' as Hc'; by apply Hr.
        * rewrite (C3_star1 n Hr). intros Hc'; injection Hc' as Hc'; by apply Hc.
        * rewrite (C3_star2L n Hr Hc).
          intros Hc'; injection Hc' as Hc'; by apply Hcl.
      + destruct (prefix2 Lft Rgt rho1 rho2 Happ) as [-> | [-> | ->]].
        * intros Hc'; injection Hc' as Hc'; by apply Hr.
        * rewrite (C3_star1 n Hr). intros Hc'; injection Hc' as Hc'; by apply Hc.
        * rewrite (C3_star2R n Hr Hc).
          intros Hc'; injection Hc' as Hc'; by apply Hlm.
    - intros x ty Hin. destruct (Hsm x ty Hin) as [H | H]; rewrite H;
        intros Hc'; injection Hc' as Hc'; discriminate Hc'.
  Qed.

  (** ** Step four: the splice

      [parent.Left = currentF].  Every side condition is a lookup in a concrete
      map or one of the three distinctness facts above. *)
  Lemma bst_replace N γm γh γl γs γo γf γr E n :
    ↑N ⊆ E ->
    n <> Rt ->
    (forall k v, C0 !! k = Some v -> k.1 <> n) ->
    EnvOK Rt W U1 FType Fs (Sm1 n) (Ob1 n) (C3 n) ∅ Grest ->
    rcu_invT FType (phys γm γh γl γs Rt Fs) N γo γf γr -∗
    writer γo γs γh γl γf W (Sm1 n) (Ob1 n) (C3 n) ∅ -∗
    fr_frag γr ({[n]} : gset Loc)
    ={E}=∗ writer γo γs γh γl γf W (Sm1 n)
             (<[n := {[Oiter W]}]> (<[Cur := {[Ounlk W]}]> (Ob1 n)))
             (<[(Rt, Lft) := VLoc n]> (C3 n)) ∅
           ∗ fr_frag γr ({[n]} : gset Loc)
           ∗ ⌜EnvOK Rt W U1 FType Fs (Sm1 n)
                (<[n := {[Oiter W]}]> (<[Cur := {[Ounlk W]}]> (Ob1 n)))
                (<[(Rt, Lft) := VLoc n]> (C3 n)) ∅
                ([(vParent, TItr [] (fun g => if decide (g = Lft)
                                             then Some (FVar vCurrentF)
                                             else None));
                  (vCurrentF, TItr [Lft] (fun _ => None));
                  (vCurrent, TUnlinked)] ++ Grest)⌝.
  Proof.
    iIntros (HN Hr Hcn Hrest) "#Hinv Hw Hfr".
    destruct (n_fresh n Hcn) as (Hc & Hcl & Hlm).
    iApply (replace_typed FType Rt Fs N γm γh γl γs γo γf γr E W
              vParent vCurrentF vCurrent Rt Lft Cur n [] Lft
              U1 (Sm1 n) (Ob1 n) (C3 n) ∅ {[n]} (Val3 n) Valo
              {[Oiter W]} Grest
              with "Hinv Hw Hfr").
    - exact HN.
    - exact Hc.
    - exact Hr.
    - by left.
    - exact (fun Hc' => Hr (eq_sym Hc')).
    - discriminate.
    - rewrite /Sm1 lookup_insert_ne; [reflexivity | discriminate].
    - rewrite /Ob1 lookup_insert_ne;
        [reflexivity | intros Hc'; by apply Hr].
    - by apply elem_of_singleton.
    - intros [Hu _]; exact Hu.
    - rewrite /Sm1. apply lookup_insert_eq.
    - rewrite /Ob1. apply lookup_insert_eq.
    - intros [Hu _]; exact Hu.
    - rewrite /Sm1 lookup_insert_ne; [reflexivity | discriminate].
    - rewrite /Ob1 lookup_insert_ne;
        [reflexivity | intros Hc'; by apply Hc].
    - intros [Hu _]; exact Hu.
    - exact (C3_RtL n Hr).
    - intros g Hg. exact (C3_new n g Hg).
    - intros g Hg. exact (C3_old n g Hc Hg).
    - reflexivity.
    - intros [].
    - intros rho1 rho2 Happ. apply app_eq_nil in Happ as [-> ->].
      exists Rt, {[Oiter W]}. repeat apply conj;
        [reflexivity | | by apply elem_of_singleton].
      rewrite /Ob1 lookup_insert_ne; [reflexivity | intros Hc'; by apply Hr].
    - intros rho1 rho2 Happ. apply app_eq_nil in Happ as [-> ->].
      intros Hc'; injection Hc' as Hc'; by apply Hr.
    - intros rho1 rho2 Happ. apply app_eq_nil in Happ as [-> ->].
      discriminate.
    - intros q g Hq Hg. apply elem_of_singleton in Hq as ->.
      rewrite /Val3 decide_True; [| reflexivity]. exact (C3_new n g Hg).
    - intros q g. rewrite /Val3. case_decide as Hd; [| discriminate].
      rewrite /Valo. case_decide; intros Hc'; injection Hc' as Hc';
        discriminate Hc'.
    - exact (C3_sole_Cur n Hr Hc Hcl Hlm).
    - discriminate.
    - exact (Grest_mirror n Hr Hc Hcl Hlm).
    - exact Hrest.
  Qed.

  Print Assumptions bst_replace.

  (** ** The chain

      The four steps composed: allocate the replacement, fill in its two
      fields, splice it in.  This is the write half of the two-child delete the
      paper uses as its worked example, and it is the shape the isolated
      triples could not be read off from -- each step's output is the next
      step's input, including the freshness facts the allocation has to export
      and the mirror condition the splice has to be handed. *)
  Lemma bst_delete_two_child N γm γh γl γs γo γf γr E :
    (forall g, FType g = RCUField -> In g Fs) ->
    (forall g, In g Fs -> FType g = RCUField) ->
    ↑N ⊆ E ->
    rcu_invT FType (phys γm γh γl γs Rt Fs) N γo γf γr -∗
    writer γo γs γh γl γf W Sm0 Ob0 C0 ∅ -∗
    fr_frag γr ∅
    ={E}=∗ ∃ n,
      writer γo γs γh γl γf W (Sm1 n)
        (<[n := {[Oiter W]}]> (<[Cur := {[Ounlk W]}]> (Ob1 n)))
        (<[(Rt, Lft) := VLoc n]> (C3 n)) ∅
      ∗ fr_frag γr ({[n]} : gset Loc)
      ∗ ⌜EnvOK Rt W U1 FType Fs (Sm1 n)
           (<[n := {[Oiter W]}]> (<[Cur := {[Ounlk W]}]> (Ob1 n)))
           (<[(Rt, Lft) := VLoc n]> (C3 n)) ∅
           ([(vParent, TItr [] (fun g => if decide (g = Lft)
                                        then Some (FVar vCurrentF)
                                        else None));
             (vCurrentF, TItr [Lft] (fun _ => None));
             (vCurrent, TUnlinked)] ++ Grest)⌝.
  Proof.
    iIntros (HFs HFrcu HN) "#Hinv Hw Hfr".
    iMod (bst_build_replacement FType HFs HFrcu N γm γh γl γs γo γf γr E HN
            with "Hinv Hw Hfr") as (n) "(%Hr & %Hcn & Hw & Hfr & %Hok)".
    assert (Hrest : EnvOK Rt W U1 FType Fs (Sm1 n) (Ob1 n) (C3 n) ∅ Grest).
    { intros x ty Hin. apply Hok.
      destruct Hin as [Heq | [Heq | []]]; rewrite -Heq;
        [ by right; right; right; left
        | by right; right; right; right; left ]. }
    iMod (bst_replace N γm γh γl γs γo γf γr E n HN Hr Hcn Hrest
            with "Hinv Hw Hfr") as "Hres".
    iModIntro. by iExists n.
  Qed.

  Print Assumptions bst_delete_two_child.

End bst4.

Print Assumptions replace_cannot_frame.
