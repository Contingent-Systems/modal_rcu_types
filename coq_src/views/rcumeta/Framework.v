Require Import Language.
Require Export Relations Morphisms Setoid Equalities SetoidClass.
Require Import Basics.

Require Import Monoids.
Require Import Setof.
Require Import Tactics.

Local Notation "e \u2208 s" := (elem s e) (at level 50).

Module Type SafetyParams
    (Import ats : Atomics)
    (Import sts : StateTransformers ats).
  Parameter V : Type.
  Declare Instance V_setoid : Setoid V.
  Parameter op : V -> V -> V.
  Declare Instance op_monoid : SemiGroup op.
  Declare Instance op_comm : Commutative op.
  Infix "*" := op.

  Parameter erase : V -> (Setof (A:=State)).
  Declare Instance erase_morphism :
      Proper (equiv ==> equiv) erase.
End SafetyParams.


Module Safety
   (Import ats : Atomics)
   (Import bs : BasicSyntaxT ats)
   (Import st : StateTransformers ats)
   (Import sp : SafetyParams ats st).

  Module Import myOpSem := OperationalSemantics ats bs st.

  Class ZeroErase := {
     my_zero :> Zero op;
     erase_zero : erase zero == emptyset
  }.

  Class ZerosErase := {
     my_zeros :> Zeros op;
     erase_zeros : forall z, zeros z -> erase z == emptyset
  }.
  Program Instance ze_zse (z : ZeroErase) : ZerosErase :=  
  { my_zeros := zeros_zero op}.
  Next Obligation. 
    intro. ssubst. ssubst. 
    rewrite erase_zero. reflexivity. 
  Qed.  

  Definition asat_wm p a q :=
      subsetof (so_map_rel (st_trans a) (erase p)
                     (R_morphism:=st_morph a))
           (erase q)
  /\ forall r, 
      subsetof (so_map_rel (st_trans a) (erase (p * r))
                     (R_morphism:=st_morph a))
           (erase (q * r)).

  Instance asat_morph : Proper (equiv ==> eq ==> equiv ==> iff) asat_wm.
   unfold asat_wm.
   repeat intro.
   rewr intuition.
  Qed.

  Lemma asat_frame : forall p a q r, asat_wm p a q ->
          asat_wm (p * r) a (q * r).
   intros.
   unfold asat_wm in H; splitup. 
   split.
   eauto. 
   intros; repeat rewrite op_assoc. eauto.  
  Qed.
  Hint Resolve asat_frame.

  Lemma asat_stequiv : forall p, asat_wm p st_equiv p.
   cbv - [equiv elem]. simpl. firstorder.
   rewr trivial.
   rewr trivial.
  Qed.
  Hint Resolve asat_stequiv.

  Definition aimpl_wm p q :=
    subsetof (erase p) (erase q)
   /\   
    forall r,
      subsetof (erase (p * r)) (erase (q * r)).
  Infix "=]]" := aimpl_wm (at level 40).

  Instance aimpl_wm_morph : Proper (equiv ==> equiv ==> iff) aimpl_wm.
   unfold aimpl_wm; repeat intro; rewr intuition.
  Qed.

  Instance aimpl_preorder : PreOrder aimpl_wm.
   firstorder.
  Qed.

  Instance asat_aimpl_morph : 
      Proper (aimpl_wm --> eq ==> aimpl_wm ++> impl) asat_wm.
   intros p' p Hp s s' Hs q' q Hq Ha. subst.
   unfold aimpl_wm in *.
   unfold asat_wm in *. compute [flip] in Hp. 
   repeat  splitup. 
   split.
   rewr trivial. 

   intro r. 
   rewrite <- H2.
   rewrite H4. auto. 
  Qed.

  Lemma asat_aimpl : forall p q,
     asat_wm p st_equiv q <-> p =]] q.
   compute [asat_wm aimpl_wm st_equiv so_map_rel subsetof].
   simpl. intuition; firstorder; repeat ssubst; firstorder. 
  Qed.
  Hint Rewrite asat_aimpl.

  Instance op_aimpl_lmorph :
     Proper (aimpl_wm ==> eq ==> aimpl_wm) op.
   intros p p' Hp q q' Hq; subst.
   rewrite <- asat_aimpl in *.
   auto with *.
  Qed.

  Instance op_aimpl_morph :
     Proper (aimpl_wm ==> aimpl_wm ==> aimpl_wm) op.
   intros p p' Hp q q' Hq.
   set (op_commut p' q); set (op_commut p' q').
   rewr intuition.
  Qed.

  Instance erase_aimpl_mono :
     Proper (aimpl_wm ++> subsetof) erase.
    repeat intro. firstorder. 
  Qed.

  CoInductive Safe : V -> Syntax -> V -> Prop :=
    mk_Safe : forall p c q,
        (c = skip -> p =]] q) ->
        (forall a c', c -[ a ]-> c' ->
           exists r, asat_wm p a r /\ Safe r c' q) ->
              Safe p c q.

  Instance Safe_morph : Proper 
      (equiv ==> eq ==> equiv ==> impl) Safe.
   cofix.
   constructor; intros; subst.
    inversion H2; intuition; rewr trivial.
    inversion H2.
    destruct (H4 a c') as [r]; intuition.
    exists r; split.
     rewr trivial.
     apply Safe_morph with r c' x1; auto with *.
  Qed.

  Ltac susestep :=
  match goal with
     [F : forall a c', ?cn -[ a ]-> c' -> ?Q,
      G : ?cn -[ ?a ]-> ?cc |- _]
          => induction (F a cc G)
  end.


  Lemma Safe_sound : forall p c q, Safe p c q ->
      forall s, s \u2208 erase p ->
      forall s', (osms c s skip s') ->
        s' \u2208 erase q .
   intros.
   remember skip as c'.
   generalize dependent p.
   induction H1; intros.
    inversion H; subst; intuition.
    rewr trivial.

    inversion H2; subst.
    susestep; intuition.
    apply H6 with x; intuition.
    elim H7. intros Hflat Hframe. clear H7.
    eapply Hflat. 
    eexists; split; eauto. 
  Qed.


  Lemma Safe_skip : forall p, Safe p skip p.
   constructor; intuition.
   inversion H.
  Qed.
  Hint Resolve Safe_skip.

  Lemma Safe_asat_wm : forall p (a : Atomic) q,
          asat_wm p (interp a) q -> Safe p a q.
   constructor; intros.
    inversion H0.
    inversion H0; subst.
    exists q.
    intuition.
  Qed.


  Lemma Safe_seq : forall p c1 r c2 q, Safe p c1 r ->
      Safe r c2 q -> Safe p (c1;;c2) q.
   cofix.
   constructor; intros.
    inversion H1.
    inversion H1; inversion H; subst.
     susestep.
     exists x; intuition.
     apply Safe_seq with r; intuition.
    
     exists r; intuition.
     rewrite asat_aimpl.
     trivial.
  Qed.
  Hint Resolve Safe_seq.


  Lemma Safe_frame : forall p c q r,
    Safe p c q -> Safe (p * r) c (q * r).
   cofix.
   intros.
   inversion H.
   constructor;
        intuition.
    rewrite H6; reflexivity.
    susestep.
    exists (x * r); intuition.
  Qed.
   Hint Resolve Safe_frame.

  Lemma Safe_para :
      forall p1 c1 q1 p2 c2 q2,
        Safe p1 c1 q1 -> Safe p2 c2 q2 ->
          Safe (p1 * p2) (c1 || c2) (q1 * q2).
   cofix.
   intros.
   inversion H; inversion H0.
   apply mk_Safe; intuition.
    inversion H11.
    inversion H11; subst; try (susestep); intuition.
     exists (x * p2).
     intuition.

     exists (p1 * x); intuition.
     rewrite op_commut, (op_commut p1 x).
     auto.

    exists (q1 * p2); intuition.
     rewr intuition.
     
     rewrite op_commut, (op_commut q1 q2).
     intuition.

    exists (p1 * q2); intuition.
     rewrite H3.
     intuition.
  Qed.
  Hint Resolve Safe_para.

  Lemma Safe_para_equiv :
      forall p q p1 c1 q1 p2 c2 q2, p ==(p1 * p2) -> q ==(q1 * q2) ->
        Safe p1 c1 q1 -> Safe p2 c2 q2 ->
          Safe p (c1 || c2) q.
  intros; repeat ssubst; eauto. 
  Qed. 


  Lemma Safe_choice : forall p q c1 c2,
    Safe p c1 q -> Safe p c2 q -> Safe p (c1 + c2) q.
   intros; apply mk_Safe; intros.
    inversion H1.
    inversion H1; subst; exists p; intuition.
  Qed.
  Hint Resolve Safe_choice.


  (* Because Coq is persnickety about how coinductive proofs
     are constructed, we use the following lemma to justify
     the loop rule *)

  Lemma Safe_preloop : forall p c, Safe p c p ->
      forall r c', Safe r c' p -> Safe r (c' ;; (c)*) p.
   intros p c H.
   cofix Hco; intros.
   apply mk_Safe; intros.
    inversion H1.
    inversion H1; subst.
     inversion H0; subst; susestep.
     exists x; intuition.
    
     exists p; intuition.
     inversion H0; subst.
     rewrite H2; auto.
     apply mk_Safe; intros.
      inversion H2.
      inversion H2; subst.
      exists p; intuition.
      
      exists p; intuition.
  Qed.
  Hint Resolve Safe_preloop.

  Lemma Safe_loop : forall p c,
    Safe p c p -> Safe p (c)* p.
   intros; apply mk_Safe; intros.
    inversion H0.
    inversion H0; subst;
    exists p; intuition.
  Qed.
  Hint Resolve Safe_loop.

  Lemma Safe_laimpl : forall p p' c q,
     p =]] p' -> Safe p' c q -> Safe p c q.
   intros.
   inversion H0; apply mk_Safe; intuition.
    rewrite H; trivial.
    induction (H2 a c' H6).
    exists x; rewrite H; intuition.
  Qed.

  Lemma Safe_raimpl : forall p c q q',
    Safe p c q' -> q' =]] q -> Safe p c q.
   cofix.
   intros.
   inversion H; apply mk_Safe; intuition.
   rewrite H7; trivial.
   induction (H2 a c' H6).
   exists x; intuition.
   apply Safe_raimpl with q'; intuition.
  Qed.

  Instance Safe_aimpl : Proper (aimpl_wm --> eq ==> aimpl_wm ++> impl) Safe.
   intros p p' H c c' H0 q q' H1 H2; subst.
   apply Safe_laimpl with p; trivial.
   apply Safe_raimpl with q; trivial.
  Qed.

  Infix "\u2286" := subsetof (at level 40).

  Section Disjunction.
    

    Variable mjoin : Setof (A:=V) -> V.
    Hypothesis op_mjoin_dist : forall p P,
      p * (mjoin P) == mjoin (so_map (op p) P).
    (*
    Hypothesis erase_jmonotone : forall P,
      erase (mjoin P) \u2286 setof_union (elem (so_map erase P)).
    Hypothesis mjoin_bound : forall P p,
          p \u2208 P -> p =]] mjoin P.
    Lemma mjoin_lub : forall P q,
          (forall p, p \u2208 P -> p =]] q) ->
              mjoin P =]] q.
     intros.
     intro.
     rewrite op_commut, op_mjoin_dist, erase_jmonotone.
     apply setof_union_lub.
     intros.
     repeat destruct H0.
     rewrite H1, H2, op_commut, (H x1 H0).
     reflexivity.
    Qed.
    Lemma erase_jantitone : forall P, 
      setof_union (elem (so_map erase P)) \u2286 erase (mjoin P).
     intros P s H.
     repeat destruct H.
     rewrite <- (mjoin_bound P x); rewr trivial.
    Qed. *)
    Hypothesis erase_jmorphism : forall P,
      erase (mjoin P) == setof_union (elem (so_map erase P)).
    Lemma mjoin_lub : forall P q,
          (forall p, p \u2208 P -> p =]] q) ->
              mjoin P =]] q.
     intros.
     split. intro.
     rewrite erase_jmorphism.
     apply setof_union_lub.
     intros.
     repeat destruct H0.
     ssubst. rewrite H; eauto. reflexivity.  
     intro;
     rewrite op_commut, op_mjoin_dist, erase_jmorphism.
     apply setof_union_lub.
     intros.
     repeat destruct H0.
     rewrite H1, H2, op_commut, (H x1 H0).
     reflexivity.
    Qed.
    Lemma mjoin_bound : forall P p,
          p \u2208 P -> p =]] mjoin P.
     intros P p H. split; intro r.
     rewrite erase_jmorphism. 
     apply setof_union_bound.
     eexists; split; eauto; reflexivity.
 
     rewrite (op_commut (mjoin P)), op_mjoin_dist, erase_jmorphism.
     apply setof_union_bound.
     exists (p * r); intuition.
     rewrite op_commut.
     exists p; intuition.
    Qed.

    Lemma asat_disj : forall P a q,
        (forall p, p \u2208 P -> asat_wm p a q) ->
           asat_wm (mjoin P) a q.
     intros. split.
     rewrite erase_jmorphism.
     intros s H0.
     destruct H0. intuition. 
     destruct H1. 
     destruct H0. intuition. 
     generalize (H _ H3).  
     intros [Hflat Hframe].
     rewrite <- Hflat.
     exists x. ssubst; intuition.  
     
     intros r s H0.
     rewrite op_commut,
             op_mjoin_dist,
             erase_jmorphism in H0.
     destruct H0.
     intuition.
     destruct H1.
     destruct H0.
     intuition.
     destruct H3.
     intuition.
     generalize (H _ H3).  
     intros [Hflat Hframe].
     rewrite <- Hframe.
     rewrite op_commut.
     rewrite <- H5, <- H4.
     exists x; auto.
    Qed.

    Lemma Safe_disj : forall P c q,
        (forall p, p \u2208 P -> Safe p c q) ->
           Safe (mjoin P) c q.
     cofix.
     intros.
     apply mk_Safe; intuition.
      apply mjoin_lub.
      intros.
      set (H2:=H p H1).
      inversion H2; subst.
      intuition.
     
      set (J := fun r => exists p, p \u2208 P /\
                              asat_wm p a r /\
                              Safe r c' q).
      exists (mjoin (mkSetof J)).
      split.
       apply asat_disj; intros.
       set (H2:=H p H1).
       inversion H2; subst.
       induction (H4 a c' H0); intuition.
       assert (x =]] mjoin (mkSetof J)).
        rewrite (mjoin_bound); try reflexivity.
        exists x; intuition.
        eexists; eauto.
       rewrite <- H5; trivial.
      
       apply Safe_disj.
       intros.
       inversion H1; intuition.
       rewrite H4; inversion H3.
       intuition.
    Qed.
  End Disjunction.


  Section Conjunction.

   Variable A : Set. 

    Variable mmeet : (A -> V) -> V.
(*
    Hypothesis asat_conju : forall {A} {b:Setoid A} a (index : Setof (A:=A)) pre post,
      (forall i, index i ->  asat_wm (pre i) a (post i)) ->
         asat_wm (mmeet (family index pre )) a (mmeet (family index post)).
*)
    Hypothesis asat_conju : forall (a : Label) pre post,
      (forall i : A, asat_wm (pre i) a (post i)) ->
         asat_wm (mmeet pre) a (mmeet post).

    Hint Resolve asat_conju.
    Lemma Safe_conj : 
    forall C pre post,
      (forall i :A, Safe (pre i) C (post i)) ->
        Safe (mmeet pre) C (mmeet post).
   cofix.
   intros C pre post Hprem. 
   apply mk_Safe.
   (* Skip case*)
    intros.  
    apply asat_aimpl.
    apply (asat_conju id).
    subst.
    generalize Hprem; clear. 
    automatcher.
    intro H; inversion H.  subst. 
    apply asat_aimpl.
    intuition.
  (* Step case *) 
    intros a c' Hstep. 
    cut 
    (forall i, exists ri, asat_wm (pre i) a ri 
                        /\ Safe ri c' (post i)).
    Focus 2. 
       generalize Hprem. clear -Hstep.
       automatcher.
       intro H; inversion H. 
       subst.
       firstorder. 
    clear Hprem Hstep. intro Hprem.
    cut
     (exists r, forall i, asat_wm (pre i) a (r i) 
                        /\ Safe (r i) c' (post i)).
    clear Hprem; intro Hprem. 
    splitup. 
    exists (mmeet x).
    split.
      eapply asat_conju. firstorder.
      eapply Safe_conj. firstorder.
    (* Back to the cut formula *) 
Require Import    Coq.Logic.ClassicalChoice.
    generalize Hprem. apply choice.
    Qed. 
    Lemma Safe_conj_eq : 
    forall p q C pre post, p =(mmeet pre) -> q =  (mmeet post) ->
      (forall i :A, Safe (pre i) C (post i)) ->
        Safe p C q.
    intros; subst; eapply Safe_conj; auto.
    Qed.

  End Conjunction.

  Inductive Unit := Elem.
  (* Amazingly this rule is a special
     case of the general conjunction rule above. 
     Need to rewrite part of the paper to explain this.  
  *)
  Lemma simulation_rule_fun_wm :
     forall (f : V -> V), 
      (forall x y (a : Label),
                asat_wm x a y 
                 -> asat_wm (f x) a (f y)) 
      -> forall x y c, 
           Safe x c  y
           -> Safe (f x) c (f y).
  intro f. intros.
  set (lift := fun (x : V) => fun (u:Unit) => x).
  assert (x=lift x Elem). compute; intuition.
  assert (y=lift y Elem ). compute; intuition.
  rewrite H1. rewrite H2.   

  eapply (Safe_conj Unit (fun p => f (p Elem))).
  (* Asat part *)
  intros. eapply (H (pre Elem) (post Elem) a). 
  firstorder.
  (* Safe *)
  compute. trivial. 
  Qed. 
   

  Definition asat p a q :=
   forall r, 
      subsetof (so_map_rel (st_trans a) (erase (p * r))
                     (R_morphism:=st_morph a))
           (erase (q * r)).

  Lemma asat_wm_to_asat {_: Monoid op}: 
     forall p a q, asat p a q <-> asat_wm p a q.
  unfold asat; unfold asat_wm. intros p a q. split; intro Hasat.
  split; eauto. 
  rewrite <- (unit_runit p); rewrite <- (unit_runit q). 
  eapply (Hasat unit).
  intuition. 
  Qed.  

  Lemma asat_wm_to_asat2 {_ : ZerosErase} {_: ManyUnits op}: 
     forall p a q, asat p a q <-> asat_wm p a q.
  unfold asat; unfold asat_wm. intros p a q. split; intro Hasat.
  split; eauto. 
  generalize (many_units p).
  intros; repeat splitup.
  generalize (H2 q). 
  rewrite <- H0.
  rewrite Hasat. 
  intros; casesplit.
  rewrite  H1. reflexivity.
  rewrite erase_zeros; firstorder. 
  
  splitup; trivial. 
  Qed.  


  Lemma simulation_rule_fun {_: Monoid op} :
     forall (f : V -> V), 
      (forall x y (a : Label),
                 asat x a y 
                 -> asat (f x) a (f y)) 
      -> forall x y c, 
           Safe x c  y
           -> Safe (f x) c (f y).
    setoid_rewrite asat_wm_to_asat.
    eapply simulation_rule_fun_wm.
    Qed.     

  Lemma simulation_rule_fun2 {_ : ZerosErase} {_: ManyUnits op}: 
     forall (f : V -> V), 
      (forall x y (a : Label),
                 asat x a y 
                 -> asat (f x) a (f y)) 
      -> forall x y c, 
           Safe x c  y
           -> Safe (f x) c (f y).
    intro. setoid_rewrite (asat_wm_to_asat2).
    eapply simulation_rule_fun_wm.
    Qed.     


  Lemma Safe_asat {_ : Monoid op} :
    forall p (a : Atomic) q,
          asat p (interp a) q -> Safe p a q.
    setoid_rewrite asat_wm_to_asat.
    eapply Safe_asat_wm.
  Qed.

  Lemma Safe_asat2 {_ : ZerosErase} {_ : ManyUnits op} :
    forall p (a : Atomic) q,
          asat p (interp a) q -> Safe p a q.
    intro Hz. 
    setoid_rewrite (asat_wm_to_asat2).
    eapply Safe_asat_wm.
  Qed.

  Instance asat_morph2 : Proper (equiv ==> eq ==> equiv ==> iff) asat.
   unfold asat.
   repeat intro.
   rewr intuition.
  Qed.

  Definition aimpl p q :=
    forall r,
      subsetof (erase (p * r)) (erase (q * r)).
  
  Instance aimpl_morph : Proper (equiv ==> equiv ==> iff) aimpl.
   unfold aimpl; repeat intro; rewr intuition.
  Qed.


  Lemma aimpl_wm_to_aimpl {_ : Monoid op} : 
    forall p q,  aimpl p q <-> aimpl_wm p q.
    unfold aimpl; unfold aimpl_wm. intuition. 
    generalize (H unit). 
    repeat rewrite unit_runit. intuition.  
   Qed.

End Safety.