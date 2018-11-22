Require Import Heaps.
Require Import Tactics.
Require Import SeparationAlgebras.
Require Import Morphisms.
Require Import SetoidClass.
Require Import Setof.

Module HeapSA (Import ht : HeapTypes) (Import h : THeaps ht).
  (* First, overwrite is a setoid morphism. *)
  Instance overwrite_morphism : Proper
      (equiv ==> equiv ==> equiv) overwrite.
(*   split; intro; simpl; apply fun_equiv; rewr auto.*)
  Admitted.

  (* Pointwise disjointness of partial functions. *)
  Definition pw_disjoint {A B} (f1 f2 : A -> option B) :=
    forall a, f1 a = None \/ f2 a = None.

  (* Which is a setoid morphism, wrt extensional
      equivalence.
  *)
  Instance pw_disjoint_morphism {A B} :
    Proper (equiv ==> equiv ==> iff)
      (pw_disjoint (A:=A) (B:=B)).
   cbv; intuition; use_foralls; rewr trivial.
  Qed.

  (* Disjointness of stores *)
  Definition st_disjoint (s1 s2 : store) :=
    pw_disjoint (heap s1) (heap s2) /\
    pw_disjoint (vars s1) (vars s2).

  Instance st_disjoint_morphism :
    Proper (equiv ==> equiv ==> iff)
      st_disjoint.
   repeat intro.
   unfold st_disjoint.
   (* rewr auto.*)
   
 Admitted.

  (* Disjoint union of stores. *)
  Definition sepop : partial_op store :=
    fun s1 s2 =>
      {|
        defined := st_disjoint s1 s2;
        val := overwrite s1 s2
      |}.

  Instance sepop_morph :
    Proper (equiv ==> equiv ==> equiv)
      sepop.
   unfold sepop.
(*   split; simpl; rewr auto.*)
  Admitted.

  (* Overwrite is commutative when disjoint *)
  Lemma disjoint_over_comm {A B} :
    forall x y : A -> option B,
      pw_disjoint x y ->
        pw_over x y == pw_over y x.
   cbv; intros.
   use_foralls.
   intuition.
    rewrite H1; destruct (y a); reflexivity.
    rewrite H1; destruct (x a); reflexivity.
  Qed.

  (* Disjoint union is commutative. *)
  Lemma sepop_comm : forall x y,
    sepop x y == sepop y x.
   split.
    cbv; firstorder.
   
    simpl; unfold st_disjoint.
    intuition; apply disjoint_over_comm;
    trivial.
  Qed.

  (* And associative. *)
  Lemma sepop_assoc : forall m1 m2 m3,
          lift_op sepop (sepop m1 m2) (lift_val m3) 
           == lift_op sepop (lift_val m1) (sepop m2 m3).
   intros; split.
   simpl;unfold st_disjoint; intuition;
   intro a;
   repeat match goal with
   | [H: pw_disjoint _ _ |- _] => generalize (H a); clear H; intro H; intuition idtac
   | [H: pw_disjoint _ _ |- _] => clear H end;
   cbv [overwrite pw_over] in *; simpl in *;
   repeat match goal with 
       [H : ?X = None, H0 : context [?X] |- _] => rewrite H in H0
     | [H : context [match ?X with Some b => Some b | None => None end] |- _] => destruct X; intuition idtac
     | [ |- context [match ?X with Some b => _ | None => _ end]] => destruct X; intuition idtac
     end; intuition idtac.

   intros; split; intro a;
   simpl; unfold pw_over.
   destruct (heap m1 a); intuition.
   destruct (vars m1 a); intuition.
  Qed.

  (* The unit is the empty store. *)
  Definition is_unit :=
    (fun s => (forall a, heap s a = None) /\ (forall b, vars s b = None)).

  Instance is_unit_morph : Proper (equiv ==> iff) is_unit.
   repeat intro.
   unfold is_unit;
   split; intros;
   use_foralls;
   rewr intuition.
  Qed.

  Definition sepop_unit : Setof (A:=store) :=
    {| elem := is_unit |}.

  Local Notation "a ∈ u" := (elem u a) (at level 50).

  (* There is only one unit, up to equivalence: *)
  Definition the_unit : store :=
   {|
     heap := fun _ : Loc => None;
     vars := fun _ : Var => None;
     heapBound := 0;
     heapFree := fun (m : nat) (_ : 0 <= m) => eq_refl
   |}.

  Lemma the_unit_is_unit : the_unit ∈ sepop_unit.
   cbv; easy.
  Qed.

  Hint Resolve the_unit_is_unit.

  (* There is a unit for every store *)
  Lemma sepop_unit_exists : forall m, exists i, i ∈ sepop_unit /\
                                          sepop i m == lift_val m.
   exists the_unit.
   cbv; intuition.
  Qed.

  (* There are no other units *)
  Lemma sepop_unit_min : forall m1 m2 i, i ∈ sepop_unit ->
                            (sepop i m1) == lift_val m2 ->
                             m1 == m2.
   cbv; intuition;
   use_foralls;
   rewr trivial.
  Qed.

  (* We now have a separation algebra *)
  Instance store_separationAlgebra : SepAlg sepop :=
    { sa_comm := sepop_comm;
      sa_assoc := sepop_assoc;
      sa_unit := sepop_unit;
      sa_unit_exists := sepop_unit_exists;
      sa_unit_min := sepop_unit_min
    }.
End HeapSA.