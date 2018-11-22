Require Import SetoidClass.

Ltac splitup := 
  match goal with 
  | H : exists _, _ |- _ => elim H; intro; intro; clear H
  | H : _ /\ _ |- _ => elim H; intro; intro; clear H
  end.

Ltac alreadyexists t := 
  try (assert t;
       [(assumption || reflexivity) | fail 1]).

Definition my_all T P := forall x: T, P x.
Definition my_all2 T P := forall x: T, P x.


Lemma fold_all : forall T (P : T -> Prop),  
    (forall x: T, P x) -> my_all T P.
trivial.
Qed.

Lemma fold_all2 : forall T (P : T -> Prop),  
    my_all T P -> my_all2 T P.
trivial.
Qed.

Ltac convert_to_all := 
  match goal with 
  | H : forall _, _ |- _ => generalize (fold_all _ _ H); clear H; intro H
  end. 


Ltac use_forall_once := 
  repeat convert_to_all;
  match goal with 
  | x : ?T , H : my_all ?T ?B |- _ 
    => alreadyexists (B x);
      generalize (H x); intro
  | H : my_all ?T _ |- _ 
    => generalize (fold_all2 _ _  H); clear H; intro H
  end   
  .

Ltac use_foralls := 
  repeat use_forall_once;
  unfold my_all2 in *. 

Ltac casesplit := match goal with | H : _ \/ _ |- _ => elim H; clear H; intro H; subst  end.

Ltac push := repeat (split || intro || splitup || casesplit).

Ltac autodestruct := 
  match goal with 
  |  |- context C [if ?foo then _ else _] => 
	match foo with 
        | context D [if _ then _ else _] => fail 1
	| _ => let Heq := fresh in case_eq foo; intro Heq; try rewrite Heq in *; subst        
        end
  |  H : context C [if ?foo then _ else _] |- _ => 
	match foo with 
        | context D [if _ then _ else _] => fail 1
	| _ => let Heq := fresh in case_eq foo; intro Heq; try rewrite Heq in * ; subst
        end
  |  |- context C [let (_, _) := ?foo in _] => case_eq foo; intros; subst
  end.

Ltac useoptions := 
  match goal with 
  | H : ?a = ?a |- _ => clear H
  | H : Some _ = Some _ |- _ => inversion H; clear H; subst
  | H : Some _ = None |- _ => elim H
  | H : None = Some _ |- _ => elim H
  | H : Some _ = ?a |- _ => rewrite <- H in *
  | H : None = ?a |- _ => rewrite <- H in *
  | H : ?a = Some _ |- _ => rewrite H in *
  | H : ?a = None |- _ => rewrite H in *
  end. 

Ltac optiondestruct := 
  match goal with 
  | x : option _ |- _ => destruct x
  | f : _ -> option _ |- _ => 
     match goal with 
     | |- context C [f ?y] => 
         let H:= fresh in 
         case_eq (f y); [intro; intro H | intro H]; rewrite H in *
     | _ => fail 1
     end
  end.

Ltac destructpair := match goal with | a : prod _ _ |- _ => destruct a end. 


Ltac tidy := 
  subst;
  repeat match goal with 
  | H1 : ?a, H2: ?a |- _ => clear H2
  end.

Ltac desintro := let H := fresh in intro H; destruct H.

Ltac focusguess 
  := repeat 
         match goal with 
         | H: forall _: ?T, _ , x : ?T |- _ => clear H 
         end.

Lemma exists_pair : forall T S P, 
  (exists x : T, exists y : S, P(x,y)) -> 
     (exists p, P p).
firstorder. Qed.




Ltac triv := 
  match goal with 
  | |- _ \/ _ => (left; triv) || (right; triv)
  | _ => trivial; fail || reflexivity || congruence
  end.

Ltac optionstac := repeat useoptions; repeat optiondestruct.

Ltac pushhard := 
    repeat (subst; (split || (intro; subst) || splitup || casesplit 
                 || useoptions || autodestruct || use_forall_once 
                 || triv ||  optiondestruct ))
                 (*; unfold my_all2 in **).



Ltac obvious := trivial; try contradiction; try congruence.
Ltac ielim := let H := fresh in intro H; elim H; clear H. 
Ltac ides := let H := fresh in intro H; destruct H.
Ltac use foo := let H := fresh in generalize foo; intro H; use_foralls; clear H.
Ltac guessexists := 
  match goal with 
  | H : ?t |- exists _ : ?t, _ => 
        exists H
  end. 

Ltac ssubst :=
 match goal with 
  | H : ?x == _ |- context [?x] => rewrite H in *; clear H 
  | H : ?x == _, H1 : context [?x] |- _ => rewrite H in *; clear H 
  | H : _ == ?x, H1 : context [?x] |- _ => rewrite <- H in *; clear H 
  | H : _ == ?x |- context [?x] => rewrite <- H in *; clear H
  end.

  Ltac rewr_ subs other :=
    match goal with
     | _ => progress other; rewr_ subs other
     | [H : ?R ?X ?Y |- context [?X]] =>
        lazymatch subs with
         | context [(Y,X,tt)] => fail
         | _ => rewrite H; rewr_ (subs,(X,Y,tt)) other
        end
     | [H : ?R ?Y ?X |- context [?X]] =>
        lazymatch subs with
         | context [(Y,X,tt)] => fail
         | _ => rewrite <- H; rewr_ (subs,(X,Y,tt)) other
        end
    end.
  Ltac rewr other := rewr_ tt other.


Ltac automatcher :=     
    let H := fresh "H" in  let H1 := fresh "H" in 
    let x := fresh "x" in     
    ((intro H; intro x; generalize (H x))
    || (intros [x H]; exists x; generalize H) 
    || (intros [H H1]; split; [generalize H | generalize H1]; clear H1) 
    ); clear H.

