Require Import Language.
Require Import Relations.
Require Import Morphisms SetoidClass.
Require Import Tactics.


Section StateTransformerConstructions.

Context {S} {S_setoid : Setoid S}.

Definition STS := ST (A:=S).

Definition stid : STS := {| st_trans := equiv |}.


Definition relseq {A} (t1 t2 : relation A) : relation A :=
  fun s s'' => exists s', t1 s s' /\ t2 s' s''.

Section RelSeqMorph.
Variables t1 t2 : relation S.
Context {t1_morph : Proper (equiv ==> equiv ==> iff) t1}.
Context {t2_morph : Proper (equiv ==> equiv ==> iff) t2}.

Instance relseq_morphism : Proper (equiv ==> equiv ==> iff)
       (relseq t1 t2).
repeat intro.
cbv.
split;
destruct 1 as [z]; exists z; rewr intuition.
Qed.
End RelSeqMorph.

(* Sequential composition of State Transformers *)
(*
Definition STseq : STS -> STS -> STS.
intros X X0.
destruct X as [t1].
destruct X0 as [t2].
apply Build_ST with
  (relseq t1 t2).
apply relseq_morphism; trivial.
Defined.
*)

Definition STseq (X X0 : STS) : STS.
apply Build_ST with (relseq (st_trans X) (st_trans X0)).
apply relseq_morphism;
apply st_morph.
Defined.

(* Guard *)

Record Guard :=
  {
    selector :> S -> Prop;
    selector_morph :> Proper (equiv ==> iff) selector
  }.

Definition guard_st (g : Guard) : relation S :=
  fun s s' => s == s' /\ g s.

Instance guard_st_morphism (g : Guard) :
    Proper (equiv ==> equiv ==> iff) (guard_st g).
repeat intro.
destruct g.
firstorder; rewr trivial.
Qed.

Definition STguard (g : Guard) : STS :=
   {| st_trans := guard_st g |}.

Definition equiv_guard (s : S) : Guard :=
  {| selector := equiv s |}.

Definition STeguard (s : S) : STS :=
    STguard (equiv_guard s).

Definition makep_st (g : Guard) : relation S :=
  fun s s' => g s'.

Instance makep_st_morphism (g : Guard) :
    Proper (equiv ==> equiv ==> iff) (makep_st g).
repeat intro; destruct g.
cbv; firstorder; rewr trivial.
Qed.

Definition STmakep (g : Guard) : STS :=
  {| st_trans := makep_st g |}.

Definition STmp (s : S) : STS :=
    STmakep (equiv_guard s).

(* Choice *)

Definition gchoice_st {A} (c : A -> Prop * STS) : relation S :=
  fun s s' => exists a, fst (c a) /\ snd (c a) s s'.

Instance gchoice_st_morphism {A} (c : A -> Prop * STS) :
    Proper (equiv ==> equiv ==> iff) (gchoice_st c).
repeat intro.
unfold gchoice_st.
split; destruct 1 as [a];
exists a;
intuition;
destruct (snd (c a));
simpl in *;
rewr intuition.
Qed.

Definition STgchoice {A} (c : A -> Prop * STS) : STS :=
   {| st_trans := gchoice_st c |}.

Definition choice_st {A} (c : A -> STS) : relation S :=
  fun s s' => exists a, c a s s'.

Instance choice_st_morphism {A} (c : A -> STS) :
    Proper (equiv ==> equiv ==> iff) (choice_st c).
repeat intro; unfold choice_st.
split; destruct 1 as [a];
exists a; intuition;
destruct (c a); simpl in *;
rewr intuition.
Qed.

Definition STchoice {A} (c : A -> STS) : STS :=
   {| st_trans := choice_st c |}.


End StateTransformerConstructions.
