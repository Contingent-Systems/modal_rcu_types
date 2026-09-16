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
            (fun _ => None) G0 HN Hnr
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
            G0 HN Hnr
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
      writer γo γs γh γl γf W
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
    iModIntro. iExists n. by iFrame.
  Qed.

End bst.

(** ** Why the fourth step cannot join them

    The splice is \textsc{T-Replace}, and it cannot be chained onto the three
    above -- not because of any interface mismatch, but because its hypotheses
    are inconsistent with the allocation's.

    \textsc{T-Replace} is stated with "every field is an RCU field", the
    simplification the mutation rules inherit from the report.  \textsc{T-Alloc}
    needs the class declaration the finite heap forced: every RCU field is one
    of the node's declared fields.  Together those say every field name is
    declared, and there are infinitely many field names and two declared ones.

    So the two rules cannot both apply in one program, and the binary search
    tree delete -- which allocates a replacement and then splices it in -- is
    exactly a program that needs both.  This is the incompatibility reported
    with the field-list repair, and it is worth having it as a concrete
    obstruction rather than a caveat: the paper's own worked example cannot be
    typed until No-Sharing's field conditions are restricted to declared
    fields.  The chain stops here, and it stops for a reason that is about the
    invariant rather than about the mechanization. *)

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
