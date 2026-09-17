(** * The second worked example: deleting from an RCU linked list

    The binary search tree in [BST.v] is the harder of the paper's two
    examples, and running it through the rules found three things.  This is the
    other one, and the reason to do it is different: it is a check that the
    machinery is about the rules rather than about trees.  The paper claims the
    types are reusable across singly-linked and tree structures, and the two
    files differ in what one would want them to differ in -- the tree needs four
    steps and the mirror framing lemma, the list needs one step and the ordinary
    one -- while the rule being applied is the same rule, at the same interface,
    with no list-specific machinery.

    The delete is a single unlinking: [prev.Next = current.Next].  What follows
    it is the grace period and the reclamation, which is the half the
    development does not yet close for either example. *)

From iris.algebra Require Import auth gmap gset excl local_updates.
From iris.algebra.lib Require Import excl_auth.
From iris.base_logic.lib Require Import invariants own.
From iris.proofmode Require Import proofmode.
From stdpp Require Import gmap sets.
From RCU Require Import WellFormed HeapPaths IrisGhost Denotations Actions
                        Triples.

(** One field, which is the class declaration the allocation rule needs -- not
    used here, since a delete allocates nothing, but the same shape. *)
Definition Nx  : FName := 0.
Definition LFs : list FName := [Nx].

Definition LHd  : Loc := 20.
Definition LPrv : Loc := 21.
Definition LCur : Loc := 22.
Definition LNxt : Loc := 23.

Definition vHead : Var := 0.
Definition vPrev : Var := 1.
Definition vCurr : Var := 2.
Definition vNext : Var := 3.

Definition LW : TID := 7.

Definition LC0 : gmap (Loc * FName) Val :=
  <[(LHd,  Nx) := VLoc LPrv]>
  (<[(LPrv, Nx) := VLoc LCur]>
  (<[(LCur, Nx) := VLoc LNxt]>
  (<[(LNxt, Nx) := VNull]> ∅))).

Definition LOb : gmap Loc (gset obs) :=
  <[LHd  := {[Oiter LW]}]>
  (<[LPrv := {[Oiter LW]}]>
  (<[LCur := {[Oiter LW]}]>
  (<[LNxt := {[Oiter LW]}]> ∅))).

Definition LSm : gmap (Var * TID) Loc :=
  <[(vHead, LW) := LHd]>
  (<[(vPrev, LW) := LPrv]>
  (<[(vCurr, LW) := LCur]>
  (<[(vNext, LW) := LNxt]> ∅))).

Definition LU : Var -> TID -> Prop := fun _ _ => False.

Definition LG : Env :=
  [(vHead, TItr [] (fun _ => None));
   (vPrev, TItr [Nx] (fun _ => None));
   (vCurr, TItr [Nx; Nx] (fun _ => None));
   (vNext, TItr [Nx; Nx; Nx] (fun _ => None))].

(** What survives the unlinking: the head, which the deleted node is not on the
    path to.  In the tree the surviving variables were *below* the replaced
    node, which is why that example needed the mirror lemma and this one does
    not. *)
Definition LGrest : Env := [(vHead, TItr [] (fun _ => None))].

(** Enumerating the prefixes of the three paths.  Named apart from [BST.v]'s so
    that a file requiring both is not ambiguous. *)
Lemma lprefix1 {A : Type} (a : A) (p q : list A) :
  p ++ q = [a] -> p = [] \/ p = [a].
Proof.
  destruct p as [|c p]; [by left |]. simpl. injection 1 as <- Hp.
  destruct p; [by right | discriminate].
Qed.

Lemma lprefix2 {A : Type} (a b : A) (p q : list A) :
  p ++ q = [a; b] -> p = [] \/ p = [a] \/ p = [a; b].
Proof.
  destruct p as [|c p]; [by left |]. simpl. injection 1 as <- Hp.
  destruct p as [|d p]; [by right; left |].
  simpl in Hp. injection Hp as <- Hp.
  destruct p; [by right; right | discriminate].
Qed.

Lemma lprefix3 {A : Type} (a b c : A) (p q : list A) :
  p ++ q = [a; b; c] ->
  p = [] \/ p = [a] \/ p = [a; b] \/ p = [a; b; c].
Proof.
  destruct p as [|d p]; [by left |]. simpl. injection 1 as <- Hp.
  destruct p as [|e p]; [by right; left |].
  simpl in Hp. injection Hp as <- Hp.
  destruct p as [|f p]; [by right; right; left |].
  simpl in Hp. injection Hp as <- Hp.
  destruct p; [by right; right; right | discriminate].
Qed.

(** The entry environment, which is computation in a concrete map exactly as it
    was for the tree. *)
Lemma LG_ok FType : EnvOK LHd LW LU FType LFs LSm LOb LC0 ∅ LG.
Proof.
  intros x ty Hin.
  destruct Hin as [Heq | [Heq | [Heq | [Heq | []]]]];
    injection Heq as Hv1 Hv2; rewrite -Hv1 -Hv2; simpl.
  - (* the head, at the empty path *)
    exists LHd, {[Oiter LW]}. repeat apply conj;
      [reflexivity | reflexivity | by apply elem_of_singleton
       | intros Hc; exact Hc | intros f w Hc; discriminate Hc | reflexivity |].
    intros rho1 rho2 Happ. apply app_eq_nil in Happ as [-> ->].
    exists LHd, {[Oiter LW]}. repeat apply conj;
      [reflexivity | reflexivity | by apply elem_of_singleton].
  - (* the predecessor *)
    exists LPrv, {[Oiter LW]}. repeat apply conj;
      [reflexivity | reflexivity | by apply elem_of_singleton
       | intros Hc; exact Hc | intros f w Hc; discriminate Hc | reflexivity |].
    intros rho1 rho2 Happ. destruct (lprefix1 Nx rho1 rho2 Happ) as [-> | ->].
    + exists LHd, {[Oiter LW]}. repeat apply conj;
        [reflexivity | reflexivity | by apply elem_of_singleton].
    + exists LPrv, {[Oiter LW]}. repeat apply conj;
        [reflexivity | reflexivity | by apply elem_of_singleton].
  - (* the node being deleted *)
    exists LCur, {[Oiter LW]}. repeat apply conj;
      [reflexivity | reflexivity | by apply elem_of_singleton
       | intros Hc; exact Hc | intros f w Hc; discriminate Hc | reflexivity |].
    intros rho1 rho2 Happ.
    destruct (lprefix2 Nx Nx rho1 rho2 Happ) as [-> | [-> | ->]].
    + exists LHd, {[Oiter LW]}. repeat apply conj;
        [reflexivity | reflexivity | by apply elem_of_singleton].
    + exists LPrv, {[Oiter LW]}. repeat apply conj;
        [reflexivity | reflexivity | by apply elem_of_singleton].
    + exists LCur, {[Oiter LW]}. repeat apply conj;
        [reflexivity | reflexivity | by apply elem_of_singleton].
  - (* and its successor, which the delete relinks the predecessor to *)
    exists LNxt, {[Oiter LW]}. repeat apply conj;
      [reflexivity | reflexivity | by apply elem_of_singleton
       | intros Hc; exact Hc | intros f w Hc; discriminate Hc | reflexivity |].
    intros rho1 rho2 Happ.
    destruct (lprefix3 Nx Nx Nx rho1 rho2 Happ) as [-> | [-> | [-> | ->]]].
    + exists LHd, {[Oiter LW]}. repeat apply conj;
        [reflexivity | reflexivity | by apply elem_of_singleton].
    + exists LPrv, {[Oiter LW]}. repeat apply conj;
        [reflexivity | reflexivity | by apply elem_of_singleton].
    + exists LCur, {[Oiter LW]}. repeat apply conj;
        [reflexivity | reflexivity | by apply elem_of_singleton].
    + exists LNxt, {[Oiter LW]}. repeat apply conj;
        [reflexivity | reflexivity | by apply elem_of_singleton].
Qed.

Print Assumptions LG_ok.

(** The framing conditions, and they are the ordinary ones.  The head is not the
    deleted node, no prefix of its path reaches it, it names no field, and the
    cell the step writes is not on its path -- which is empty. *)
Lemma LGrest_obs : ReadsObs LHd LC0 LSm LW LGrest LCur.
Proof.
  repeat apply conj.
  - intros x ty Hin. destruct Hin as [Heq | []].
    injection Heq as Hv1 Hv2. rewrite -Hv1. discriminate.
  - intros x rho N rho1 rho2 Hin Happ.
    destruct Hin as [Heq | []]. injection Heq as Hv1 Hv2 Hv3.
    rewrite -Hv2 in Happ. apply app_eq_nil in Happ as [-> ->]. discriminate.
  - intros x Hin. destruct Hin as [Heq | []]. discriminate Heq.
  - intros x ty f z Hin Hty. destruct Hin as [Heq | []].
    injection Heq as Hv1 Hv2. rewrite -Hv2 in Hty. discriminate Hty.
Qed.

Lemma LGrest_cell : ReadsCell LHd LC0 LSm LW LGrest (LPrv, Nx).
Proof.
  repeat apply conj.
  - intros x rho N Hin. destruct Hin as [Heq | []].
    injection Heq as Hv1 Hv2 Hv3. rewrite -Hv2. by intros [].
  - intros x N o Hin. destruct Hin as [Heq | []]. discriminate Heq.
  - intros x ty o Hin Hstk Hk1. destruct Hin as [Heq | []].
    injection Heq as Hv1 Hv2. rewrite -Hv1 in Hstk.
    injection Hstk as <-. discriminate Hk1.
Qed.

Lemma LGrest_ok FType : EnvOK LHd LW LU FType LFs LSm LOb LC0 ∅ LGrest.
Proof.
  intros x ty Hin. apply (LG_ok FType).
  destruct Hin as [Heq | []]. rewrite -Heq. by left.
Qed.

Section list_delete.
  Context `{!rcuG Σ, !physG Σ, !readerG Σ, !heapG Σ, !lockG Σ, !stackG Σ,
            !freshG Σ, !invGS_gen hlc Σ}.
  Context (FType : FName -> FieldKind).

  (** [prev.Next = current.Next].  One application of \textsc{T-UnlinkH} at the
      concrete list, with every side condition a lookup in a concrete map --
      which is the point: nothing here is about lists. *)
  Lemma list_delete N γm γh γl γs γd γo γf γr E :
    ↑N ⊆ E ->
    rcu_invT FType (phys γm γh γl γs γd LHd LFs) N γo γf γr -∗
    writer γo γs γh γl γf LW LSm LOb LC0 ∅ -∗
    fr_frag γr (∅ : gset Loc)
    ={E}=∗ writer γo γs γh γl γf LW LSm
             (<[LCur := {[Ounlk LW]}]> LOb)
             (<[(LPrv, Nx) := VLoc LNxt]> LC0) ∅
           ∗ fr_frag γr (∅ : gset Loc)
           ∗ ⌜EnvOK LHd LW LU FType LFs LSm
                (<[LCur := {[Ounlk LW]}]> LOb)
                (<[(LPrv, Nx) := VLoc LNxt]> LC0) ∅
                ([(vPrev, TItr [Nx]
                     (fun g => if decide (g = Nx)
                               then Some (FVar vNext) else None));
                  (vCurr, TUnlinked);
                  (vNext, TItr ([Nx] ++ [Nx]) (fun _ => None))] ++ LGrest)⌝.
  Proof.
    iIntros (HN) "#Hinv Hw Hfr".
    iApply (unlink_typed FType LHd LFs N γm γh γl γs γd γo γf γr E LW
              vPrev vCurr vNext LPrv Nx LCur Nx LNxt [Nx]
              LU LSm LOb LC0 ∅ ∅ (fun _ _ => VNull)
              {[Oiter LW]} {[Oiter LW]} LGrest
              with "Hinv Hw Hfr").
    - exact HN.
    - discriminate.
    - discriminate.
    - discriminate.
    - reflexivity.
    - reflexivity.
    - by apply elem_of_singleton.
    - reflexivity.
    - reflexivity.
    - intros Hc; exact Hc.
    - reflexivity.
    - reflexivity.
    - by apply elem_of_singleton.
    - intros Hc; exact Hc.
    - intros Hc; exact Hc.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - intros [Hc | []]. discriminate Hc.
    - intros rho1 rho2 Happ.
      destruct (lprefix1 Nx rho1 rho2 Happ) as [-> | ->].
      + exists LHd, {[Oiter LW]}. repeat apply conj;
          [reflexivity | reflexivity | by apply elem_of_singleton].
      + exists LPrv, {[Oiter LW]}. repeat apply conj;
          [reflexivity | reflexivity | by apply elem_of_singleton].
    - intros rho1 rho2 Happ.
      destruct (lprefix1 Nx rho1 rho2 Happ) as [-> | ->]; discriminate.
    - intros q g Hq. by apply elem_of_empty in Hq.
    - intros q g. discriminate.
    - exact LGrest_obs.
    - exact LGrest_cell.
    - exact (LGrest_ok FType).
  Qed.

  Print Assumptions list_delete.

End list_delete.
