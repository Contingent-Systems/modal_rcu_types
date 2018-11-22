Require Export Coq.Logic.Epsilon.
Require Export Classical. 
Require Import Tactics. 

Definition to_bool (P : Prop) : bool :=
     (epsilon (inhabits true) (fun i => P <-> i = true)).
Lemma to_bool_defn : 
      forall P, to_bool P = true <-> P. 
   intros P. unfold to_bool. unfold epsilon.
   generalize (classic P).
   match goal with |- context C [proj1_sig ?x = true]
      => destruct x end. simpl. 
   intro; casesplit; symmetry; eapply i.
     exists true. intuition.  
     exists false. intuition. 
Qed.