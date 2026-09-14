(** * Compose: the separation algebra on logical states.

    Milestone 6.  The action lemmas say what one thread's step does to the
    global invariants and to its own types.  Framing is the other half of the
    Views obligation: a step must also behave when composed with whatever other
    threads hold, which the framework expresses by requiring views to form a
    partial commutative monoid and by requiring the validity predicate to be
    closed under that composition.

    Section [sec:soundness] of the technical report gives the operation --
    Figure [fig:comp] -- and asserts the closure: "WellFormed states are closed
    under both composition (with another WellFormed state) and interference".

    That assertion is false, and this file exhibits why.  The heap component of
    the composition is not separating: it is defined at *every* location, taking
    the common value where the two agree and undefined where they differ.  Two
    views may therefore each hold one edge into a node and compose to a view
    holding both, which is exactly what OW forbids.

    Checked with Rocq 9.2, axiom-free. *)

From Stdlib Require Import List Arith Lia.
Import ListNotations.
From RCU Require Import WellFormed.

(** ** The operation

    Transcribed from Figure [fig:comp].  Observations, undefinedness and the
    thread set compose by union; the stack and the free list by union of
    domain-disjoint partial maps; and the heap by agreement. *)

Definition val_eq_dec (v v' : Val) : {v = v'} + {v <> v'}.
Proof. decide equality; apply Nat.eq_dec. Defined.

Definition comp_h (h1 h2 : Loc -> FName -> option Val)
  : Loc -> FName -> option Val :=
  fun o f =>
    match h1 o f, h2 o f with
    | Some v, Some v' => if val_eq_dec v v' then Some v else None
    | Some v, None    => Some v
    | None,   Some v  => Some v
    | None,   None    => None
    end.

Definition comp_stk (s1 s2 : Var -> TID -> option Loc)
  : Var -> TID -> option Loc :=
  fun x t => match s1 x t with Some o => Some o | None => s2 x t end.

Definition comp_flist (F1 F2 : Loc -> option (TID -> Prop))
  : Loc -> option (TID -> Prop) :=
  fun o => match F1 o with Some Tr => Some Tr | None => F2 o end.

Definition comp (s1 s2 : LState) : LState :=
  {| ms := {| stk := comp_stk (stk (ms s1)) (stk (ms s2));
              hp  := comp_h (hp (ms s1)) (hp (ms s2));
              lk  := lk (ms s1);
              rt  := rt (ms s1);
              rds := rds (ms s1);
              bnd := bnd (ms s1) |};
     obsv  := fun o ob => obsv s1 o ob \/ obsv s2 o ob;
     undf  := fun x t => undf s1 x t \/ undf s2 x t;
     thrd  := fun t => thrd s1 t \/ thrd s2 t;
     flist := comp_flist (flist s1) (flist s2) |}.

(** The side conditions the figure attaches: the stack and free-list domains are
    disjoint, and the two views agree on the machine components the operation
    does not split. *)
Definition comp_ok (s1 s2 : LState) : Prop :=
  (forall x t, stk (ms s1) x t = None \/ stk (ms s2) x t = None)
  /\ (forall o, flist s1 o = None \/ flist s2 o = None)
  /\ lk (ms s1) = lk (ms s2) /\ rt (ms s1) = rt (ms s2)
  /\ (forall t, rds (ms s1) t <-> rds (ms s2) t)
  /\ (forall t, bnd (ms s1) t <-> bnd (ms s2) t).

(** ** Two views that compose badly

    Each holds one edge into node 2, from a different node, and each is well
    formed.  Their composition holds both. *)

Definition ow1 : LState :=
  {| ms := {| stk := fun _ _ => None;
              hp  := fun o f => if Nat.eqb o 0
                                then (if Nat.eqb f 0 then Some (VLoc 2) else None)
                                else if Nat.eqb o 2 then Some VNull else None;
              lk  := Some 0;
              rt  := 0;
              rds := fun _ => False;
              bnd := fun _ => False |};
     obsv  := fun o ob => (o = 0 /\ ob = Oroot) \/ (o = 2 /\ ob = Oiter 0);
     undf  := fun _ _ => False;
     thrd  := fun t => t = 0;
     flist := fun _ => None |}.

Definition ow2 : LState :=
  {| ms := {| stk := fun _ _ => None;
              hp  := fun o f => if Nat.eqb o 1
                                then (if Nat.eqb f 0 then Some (VLoc 2) else None)
                                else if Nat.eqb o 2 then Some VNull else None;
              lk  := Some 0;
              rt  := 0;
              rds := fun _ => False;
              bnd := fun _ => False |};
     obsv  := fun o ob => (o = 0 /\ ob = Oroot)
                          \/ (o = 1 /\ ob = Oiter 0)
                          \/ (o = 2 /\ ob = Oiter 0);
     undf  := fun _ _ => False;
     thrd  := fun t => t = 0;
     flist := fun _ => None |}.

Definition allrcu : FName -> FieldKind := fun _ => RCUField.

(** *** Edges and reachability in each view *)

Lemma ow1_edge o f o' : Edge ow1 o f o' -> o = 0 /\ f = 0 /\ o' = 2.
Proof.
  unfold Edge, ow1. simpl. destruct (Nat.eqb o 0) eqn:Ho.
  - destruct (Nat.eqb f 0) eqn:Hf; [| discriminate].
    intros H. injection H as <-. apply Nat.eqb_eq in Ho, Hf. auto.
  - destruct (Nat.eqb o 2); discriminate.
Qed.

Lemma ow2_edge o f o' : Edge ow2 o f o' -> o = 1 /\ f = 0 /\ o' = 2.
Proof.
  unfold Edge, ow2. simpl. destruct (Nat.eqb o 1) eqn:Ho.
  - destruct (Nat.eqb f 0) eqn:Hf; [| discriminate].
    intros H. injection H as <-. apply Nat.eqb_eq in Ho, Hf. auto.
  - destruct (Nat.eqb o 2); discriminate.
Qed.

Lemma ow1_reach p o : Reaches ow1 p o -> (p = [] /\ o = 0) \/ (p = [0] /\ o = 2).
Proof.
  destruct p as [|g p]; unfold Reaches; simpl.
  - intros H. injection H as <-. left. auto.
  - destruct (Nat.eqb g 0) eqn:Hg; simpl.
    + destruct p as [|g' p']; simpl.
      * intros H. injection H as <-. apply Nat.eqb_eq in Hg. subst g. right. auto.
      * discriminate.
    + discriminate.
Qed.

Lemma ow2_reach p o : Reaches ow2 p o -> p = [] /\ o = 0.
Proof.
  destruct p as [|g p]; unfold Reaches; simpl.
  - intros H. injection H as <-. auto.
  - discriminate.
Qed.

(** *** Each view is well formed *)

Lemma ow1_WellFormed : WellFormed allrcu ow1.
Proof.
  repeat apply conj.
  - (* OW *) intros o o' f f' x H1 H2 _ _.
    destruct (ow1_edge o f x H1) as (-> & -> & _).
    destruct (ow1_edge o' f' x H2) as (-> & -> & _). left. auto.
  - intros x t o H. simpl in H. discriminate H.
  - intros y t H. simpl in H. discriminate H.
  - intros t o Tr H1 H2. simpl in H2. discriminate H2.
  - intros o o' f' t H1 _. simpl in H1.
    destruct H1 as [[[_ H] | [_ H]] | [[_ H] | [_ H]]]; discriminate H.
  - intros o o' f' Tr H1 H2. simpl in H1. discriminate H1.
  - (* WULK *) intros lw o t H1 H2. simpl in H1. injection H1 as <-.
    simpl in H2. destruct H2 as [[_ H] | [-> _]]; [discriminate H |].
    split; intros [[_ H] | [_ H]]; discriminate H.
  - intros t x o H. simpl in H. discriminate H.
  - intros t x o H. simpl in H. discriminate H.
  - intros o t t' H. simpl in H.
    destruct H as [[_ H] | [_ H]]; discriminate H.
  - intros o f o' t lw H _ _ _. simpl in H.
    destruct H as [[_ H] | [_ H]]; discriminate H.
  - intros t H1 H2. exact H2.
  - intros o t H. destruct H.
  - intros o Tr t H1 H2. simpl in H1. discriminate H1.
  - (* HD *) intros o f o' H _.
    destruct (ow1_edge o f o' H) as (_ & _ & ->).
    exists 0, VNull. reflexivity.
  - (* UNQRT_a *) intros o f H.
    destruct (ow1_edge o f (rt (ms ow1)) H) as (_ & _ & Hc). discriminate Hc.
  - (* UNQRT_b *) intros p o lw H1 H2. simpl in H1. injection H1 as <-.
    destruct (ow1_reach p o H2) as [[_ ->] | [_ ->]].
    + right. left. auto.
    + left. right. auto.
  - (* WUNLK *) intros o t lw _ [H | H]; simpl in H;
      destruct H as [[_ H] | [_ H]]; discriminate H.
  - (* WITR *) intros o t H. simpl in H.
    destruct H as [[_ H] | [_ H]]; [discriminate H |].
    injection H as ->. left. reflexivity.
  - (* UNQR *) intros p p' o H1 H2.
    destruct (ow1_reach p o H1) as [[Hp Ho] | [Hp Ho]];
    destruct (ow1_reach p' o H2) as [[Hp' Ho'] | [Hp' Ho']];
      subst p p'.
    + reflexivity.
    + rewrite Ho in Ho'. discriminate Ho'.
    + rewrite Ho in Ho'. discriminate Ho'.
    + reflexivity.
Qed.

Lemma ow2_WellFormed : WellFormed allrcu ow2.
Proof.
  repeat apply conj.
  - intros o o' f f' x H1 H2 _ _.
    destruct (ow2_edge o f x H1) as (-> & -> & _).
    destruct (ow2_edge o' f' x H2) as (-> & -> & _). left. auto.
  - intros x t o H. simpl in H. discriminate H.
  - intros y t H. simpl in H. discriminate H.
  - intros t o Tr H1 H2. simpl in H2. discriminate H2.
  - intros o o' f' t H1 _. simpl in H1.
    destruct H1 as [[[_ H] | [[_ H] | [_ H]]] | [[_ H] | [[_ H] | [_ H]]]];
      discriminate H.
  - intros o o' f' Tr H1 H2. simpl in H1. discriminate H1.
  - intros lw o t H1 H2. simpl in H1. injection H1 as <-.
    simpl in H2. destruct H2 as [[_ H] | [[-> _] | [-> _]]];
      [discriminate H | |];
      split; intros [[_ H] | [[_ H] | [_ H]]]; discriminate H.
  - intros t x o H. simpl in H. discriminate H.
  - intros t x o H. simpl in H. discriminate H.
  - intros o t t' H. simpl in H.
    destruct H as [[_ H] | [[_ H] | [_ H]]]; discriminate H.
  - intros o f o' t lw H _ _ _. simpl in H.
    destruct H as [[_ H] | [[_ H] | [_ H]]]; discriminate H.
  - intros t H1 H2. exact H2.
  - intros o t H. destruct H.
  - intros o Tr t H1 H2. simpl in H1. discriminate H1.
  - intros o f o' H _.
    destruct (ow2_edge o f o' H) as (_ & _ & ->).
    exists 0, VNull. reflexivity.
  - intros o f H.
    destruct (ow2_edge o f (rt (ms ow2)) H) as (_ & _ & Hc). discriminate Hc.
  - intros p o lw H1 H2. simpl in H1. injection H1 as <-.
    destruct (ow2_reach p o H2) as [_ ->]. right. left. auto.
  - intros o t lw _ [H | H]; simpl in H;
      destruct H as [[_ H] | [[_ H] | [_ H]]]; discriminate H.
  - intros o t H. simpl in H.
    destruct H as [[_ H] | [[_ H] | [_ H]]]; [discriminate H | |];
      injection H as ->; left; reflexivity.
  - intros p p' o H1 H2.
    destruct (ow2_reach p o H1) as [-> _]. destruct (ow2_reach p' o H2) as [-> _].
    reflexivity.
Qed.

(** *** ... and their composition is not

    The two edges the composition holds have distinct, live sources, which is
    exactly what No-Sharing denies. *)

Lemma comp_ok_ow : comp_ok ow1 ow2.
Proof.
  repeat apply conj; try reflexivity; try (intros; tauto).
Qed.

(** Nothing in the composed view is detached: every observation either view
    holds is [root] or an [iterator]. *)
Lemma comp_not_detached o : ~ Detached (comp ow1 ow2) o.
Proof.
  intros [t [H | [H | H]]]; simpl in H;
    destruct H as [[[_ H] | [_ H]] | [[_ H] | [[_ H] | [_ H]]]]; discriminate H.
Qed.

Theorem composition_does_not_preserve_WellFormed :
  WellFormed allrcu ow1
  /\ WellFormed allrcu ow2
  /\ comp_ok ow1 ow2
  /\ ~ WellFormed allrcu (comp ow1 ow2).
Proof.
  split; [exact ow1_WellFormed |].
  split; [exact ow2_WellFormed |].
  split; [exact comp_ok_ow |].
  intros (HOW & _).
  assert (He1 : Edge (comp ow1 ow2) 0 0 2) by reflexivity.
  assert (He2 : Edge (comp ow1 ow2) 1 0 2) by reflexivity.
  destruct (HOW 0 1 0 0 2 He1 He2 eq_refl eq_refl) as [[Hc _] | [Hd | Hd]].
  - discriminate Hc.
  - exact (comp_not_detached 0 Hd).
  - exact (comp_not_detached 1 Hd).
Qed.

(** ** What this shows

    The Views framework requires the views to form a partial commutative monoid
    and the validity predicate to be closed under the operation; framing is
    unsound without it.  The operation of Figure [fig:comp] does not have that
    property, and the reason is structural rather than incidental: its heap
    component is not separating.  [comp_h] is defined at every location, taking
    the common value where the two views agree, so two views may each hold one
    edge into a node and compose to a view holding both -- which is precisely
    what OW denies.

    The counterexample is small and uses nothing exotic: two heaps that agree
    wherever both are defined, no shared stack, no shared free list, the same
    lock, root, readers and bounding threads.  Every side condition the figure
    attaches is met.

    Three ways out, and which is right is a design question this file does not
    settle.  Make the heap composition separating, i.e. partial with disjoint
    domains, and re-examine the actions -- several read the whole structure and
    would no longer see it.  Or keep the operation and weaken OW to hold only of
    views that are complete in some sense, which means finding that sense.  Or
    restrict the monoid to composable pairs, and then the framing lemma must say
    which pairs those are, which is the obligation the framework was supposed to
    discharge.

    What is settled is that the assertion in Section [sec:soundness] -- that
    WellFormed states are closed under composition -- does not hold as written,
    and that framing cannot be taken as read. *)

Print Assumptions ow1_WellFormed.
Print Assumptions ow2_WellFormed.
Print Assumptions composition_does_not_preserve_WellFormed.

(** * The repair

    The counterexample says the operation is wrong, not that framing is
    impossible.  This section gives a composition under which WellFormed *is*
    closed, and the conditions it needs are the interesting part.

    Two changes.  First, the heap is shared rather than split: composable views
    agree on it.  That is the right reading for this structure -- every thread
    reads the whole of it, and a separating heap would leave a reader unable to
    see the path it is traversing -- and it disposes of the counterexample,
    since agreeing views cannot between them hold two edges into one node
    unless one of them already did.

    That alone is not enough, and the five invariants it leaves broken have a
    common shape.  IFL relates an observation to a free-list entry; WULK and FNR
    relate two observations; FR and WFresh relate a stack binding to an
    observation.  Each is a relation between two pieces of *per-thread* state
    about one location, and composition is exactly the operation that can put
    those two pieces in different views.  The other fourteen either relate the
    shared heap to per-thread state, or are monotone in the observations, and
    they survive untouched.

    So the second change is locality: a location's auxiliary state may not be
    split, and a view's stack names only locations it owns.  Those are the
    conditions below, and they are what the published figure is missing. *)

(** A view owns a location if it holds any observation of it, or its free-list
    entry. *)
Definition owns (s : LState) (o : Loc) : Prop :=
  (exists ob, obsv s o ob) \/ flist s o <> None.

Definition comp_ok' (s1 s2 : LState) : Prop :=
  (* the heap and the machine's shared components agree *)
  (forall o f, hp (ms s1) o f = hp (ms s2) o f)
  /\ lk (ms s1) = lk (ms s2) /\ rt (ms s1) = rt (ms s2)
  /\ (forall t, rds (ms s1) t <-> rds (ms s2) t)
  /\ (forall t, bnd (ms s1) t <-> bnd (ms s2) t)
  (* per-location auxiliary state is not split *)
  /\ (forall o, ~ (owns s1 o /\ owns s2 o))
  (* and a view's stack names only locations it owns *)
  /\ (forall x t o, stk (ms s1) x t = Some o -> ~ owns s2 o)
  /\ (forall x t o, stk (ms s2) x t = Some o -> ~ owns s1 o)
  /\ (forall x t, stk (ms s1) x t = None \/ stk (ms s2) x t = None).

Section Closure.

  Variable FType : FName -> FieldKind.
  Variables (s1 s2 : LState).
  Hypothesis Hok : comp_ok' s1 s2.
  Hypothesis HW1 : WellFormed FType s1.
  Hypothesis HW2 : WellFormed FType s2.

  Lemma ok_hp o f : hp (ms s1) o f = hp (ms s2) o f.
  Proof. apply Hok. Qed.

  Lemma ok_disj o : ~ (owns s1 o /\ owns s2 o).
  Proof. apply Hok. Qed.

  (** The composed heap is either view's. *)
  Lemma comp_hp o f : hp (ms (comp s1 s2)) o f = hp (ms s1) o f.
  Proof.
    unfold comp, comp_h. simpl. rewrite <- (ok_hp o f).
    destruct (hp (ms s1) o f) as [v|]; [| reflexivity].
    destruct (val_eq_dec v v); congruence.
  Qed.

  Lemma comp_Edge o f o' : Edge (comp s1 s2) o f o' <-> Edge s1 o f o'.
  Proof. unfold Edge. rewrite comp_hp. reflexivity. Qed.

  Lemma comp_InHeap o : InHeap (comp s1 s2) o <-> InHeap s1 o.
  Proof.
    unfold InHeap. split.
    - intros [f [v Hv]]. exists f, v. rewrite <- comp_hp. exact Hv.
    - intros [f [v Hv]]. exists f, v. rewrite comp_hp. exact Hv.
  Qed.

  Lemma comp_hstar p o : hstar (hp (ms (comp s1 s2))) o p = hstar (hp (ms s1)) o p.
  Proof.
    revert o. induction p as [|g q IH]; intros o.
    - reflexivity.
    - cbn [hstar]. rewrite comp_hp.
      destruct (hp (ms s1) o g) as [[o1|]|]; [apply IH | reflexivity | reflexivity].
  Qed.

  Lemma comp_Reaches p o : Reaches (comp s1 s2) p o <-> Reaches s1 p o.
  Proof.
    unfold Reaches. rewrite comp_hstar. reflexivity.
  Qed.

  (** A location the other view does not own carries none of its state. *)
  Lemma unowned_obs o : ~ owns s2 o -> forall ob, ~ obsv s2 o ob.
  Proof. intros H ob Hc. apply H. left. exists ob. exact Hc. Qed.

  Lemma unowned_fl o : ~ owns s2 o -> flist s2 o = None.
  Proof.
    intros H. destruct (flist s2 o) eqn:E; [| reflexivity].
    exfalso. apply H. right. rewrite E. discriminate.
  Qed.

  Lemma unowned_obs1 o : ~ owns s1 o -> forall ob, ~ obsv s1 o ob.
  Proof. intros H ob Hc. apply H. left. exists ob. exact Hc. Qed.

  Lemma unowned_fl1 o : ~ owns s1 o -> flist s1 o = None.
  Proof.
    intros H. destruct (flist s1 o) eqn:E; [| reflexivity].
    exfalso. apply H. right. rewrite E. discriminate.
  Qed.

  Lemma obs_owns1 o ob : obsv s1 o ob -> owns s1 o.
  Proof. intros H. left. exists ob. exact H. Qed.

  Lemma obs_owns2 o ob : obsv s2 o ob -> owns s2 o.
  Proof. intros H. left. exists ob. exact H. Qed.

  (** So a location's observations all come from one view. *)
  Lemma obs_one_view o ob ob' :
    obsv s1 o ob -> obsv (comp s1 s2) o ob' -> obsv s1 o ob'.
  Proof.
    intros H1 [H | H]; [exact H |].
    exfalso. exact (ok_disj o (conj (obs_owns1 o ob H1) (obs_owns2 o ob' H))).
  Qed.

  Lemma obs_one_view2 o ob ob' :
    obsv s2 o ob -> obsv (comp s1 s2) o ob' -> obsv s2 o ob'.
  Proof.
    intros H1 [H | H]; [| exact H].
    exfalso. exact (ok_disj o (conj (obs_owns1 o ob' H) (obs_owns2 o ob H1))).
  Qed.

  Lemma comp_lk : lk (ms (comp s1 s2)) = lk (ms s1).
  Proof. reflexivity. Qed.

  Lemma comp_rt : rt (ms (comp s1 s2)) = rt (ms s1).
  Proof. reflexivity. Qed.

  Lemma comp_Edge2 o f o' : Edge (comp s1 s2) o f o' <-> Edge s2 o f o'.
  Proof. unfold Edge. rewrite comp_hp. rewrite (ok_hp o f). reflexivity. Qed.

  Lemma comp_stk_inv x t o :
    stk (ms (comp s1 s2)) x t = Some o ->
    stk (ms s1) x t = Some o \/ stk (ms s2) x t = Some o.
  Proof.
    simpl. unfold comp_stk. destruct (stk (ms s1) x t) as [o'|].
    - intros H. left. exact H.
    - intros H. right. exact H.
  Qed.

  Lemma comp_fl_inv o Tr :
    flist (comp s1 s2) o = Some Tr ->
    flist s1 o = Some Tr \/ (flist s1 o = None /\ flist s2 o = Some Tr).
  Proof.
    simpl. unfold comp_flist. destruct (flist s1 o) as [Tr'|] eqn:E.
    - intros H. left. exact H.
    - intros H. right. split; [reflexivity | exact H].
  Qed.

  Lemma comp_fl_1 o Tr : flist s1 o = Some Tr -> flist (comp s1 s2) o = Some Tr.
  Proof. intros H. simpl. unfold comp_flist. rewrite H. reflexivity. Qed.

  Lemma comp_fl_2 o Tr :
    flist s2 o = Some Tr -> flist (comp s1 s2) o = Some Tr.
  Proof.
    intros H. simpl. unfold comp_flist.
    assert (Hno1 : ~ owns s1 o).
    { intros Hc. apply (ok_disj o). split; [exact Hc |]. right. rewrite H. discriminate. }
    rewrite (unowned_fl1 o Hno1). exact H.
  Qed.

  Lemma comp_det_1 o : Detached s1 o -> Detached (comp s1 s2) o.
  Proof.
    intros [t [X | [X | X]]]; exists t;
      [left | right; left | right; right]; left; exact X.
  Qed.

  Lemma comp_det_2 o : Detached s2 o -> Detached (comp s1 s2) o.
  Proof.
    intros [t [X | [X | X]]]; exists t;
      [left | right; left | right; right]; right; exact X.
  Qed.

  (** The closure theorem. *)
  Theorem WellFormed_comp : WellFormed FType (comp s1 s2).
  Proof.
    destruct HW1 as (OW1 & RWOW1 & AWRT1 & IFL1 & ULKR1 & FLR1 & WULK1 & FR1
                     & WF1 & FNR1 & FPI1 & WNR1 & RITR1 & RINFL1 & HD1 & Ua1
                     & Ub1 & WU1 & WI1 & UQ1).
    destruct HW2 as (OW2 & RWOW2 & AWRT2 & IFL2 & ULKR2 & FLR2 & WULK2 & FR2
                     & WF2 & FNR2 & FPI2 & WNR2 & RITR2 & RINFL2 & HD2 & Ua2
                     & Ub2 & WU2 & WI2 & UQ2).
    destruct Hok as (Hhp & Hlk & Hrt & Hrds & Hbnd & Hdisj & Hstk1 & Hstk2 & _).
    repeat apply conj.
    - (* OW *) intros o o' f f' x He He' Hf Hf'.
      destruct (OW1 o o' f f' x (proj1 (comp_Edge o f x) He)
                  (proj1 (comp_Edge o' f' x) He') Hf Hf') as [Hs | [Hd | Hd]].
      + left. exact Hs.
      + right. left. exact (comp_det_1 o Hd).
      + right. right. exact (comp_det_1 o' Hd).
    - (* RWOW *) intros x t o Hstk Hnu.
      destruct (comp_stk_inv x t o Hstk) as [H1 | H2].
      + destruct (RWOW1 x t o H1 (fun Hc => Hnu (or_introl Hc)))
          as [Hit | [Hl [X | [X | X]]]].
        * left. left. exact Hit.
        * right. split; [exact Hl |]. left. left. exact X.
        * right. split; [exact Hl |]. right. left. left. exact X.
        * right. split; [exact Hl |]. right. right. left. exact X.
      + destruct (RWOW2 x t o H2 (fun Hc => Hnu (or_intror Hc)))
          as [Hit | [Hl [X | [X | X]]]].
        * left. right. exact Hit.
        * right. split; [rewrite comp_lk, Hlk; exact Hl |]. left. right. exact X.
        * right. split; [rewrite comp_lk, Hlk; exact Hl |].
          right. left. right. exact X.
        * right. split; [rewrite comp_lk, Hlk; exact Hl |].
          right. right. right. exact X.
    - (* AWRT *) intros y t Hstk Hnu.
      destruct (comp_stk_inv y t _ Hstk) as [H1 | H2].
      + left. exact (AWRT1 y t H1 (fun Hc => Hnu (or_introl Hc))).
      + assert (Hr2 : stk (ms s2) y t = Some (rt (ms s2)))
          by (rewrite <- Hrt; exact H2).
        right. rewrite comp_rt, Hrt.
        exact (AWRT2 y t Hr2 (fun Hc => Hnu (or_intror Hc))).
    - (* IFL *) intros t o Tr Hit Hfl.
      destruct Hit as [H1 | H2].
      + assert (Hno2 : ~ owns s2 o)
          by (intros Hc; exact (Hdisj o (conj (obs_owns1 o _ H1) Hc))).
        destruct (comp_fl_inv o Tr Hfl) as [Hf1 | [_ Hf2]].
        * exact (IFL1 t o Tr H1 Hf1).
        * exfalso. rewrite (unowned_fl o Hno2) in Hf2. discriminate.
      + assert (Hno1 : ~ owns s1 o)
          by (intros Hc; exact (Hdisj o (conj Hc (obs_owns2 o _ H2)))).
        destruct (comp_fl_inv o Tr Hfl) as [Hf1 | [_ Hf2]].
        * exfalso. rewrite (unowned_fl1 o Hno1) in Hf1. discriminate.
        * exact (IFL2 t o Tr H2 Hf2).
    - (* ULKR *) intros o o' f' t Hobs He.
      destruct Hobs as [[X | X] | [X | X]].
      + destruct (ULKR1 o o' f' t (or_introl X) (proj1 (comp_Edge o' f' o) He))
          as [Y | Y]; [left | right]; left; exact Y.
      + destruct (ULKR2 o o' f' t (or_introl X) (proj1 (comp_Edge2 o' f' o) He))
          as [Y | Y]; [left | right]; right; exact Y.
      + destruct (ULKR1 o o' f' t (or_intror X) (proj1 (comp_Edge o' f' o) He))
          as [Y | Y]; [left | right]; left; exact Y.
      + destruct (ULKR2 o o' f' t (or_intror X) (proj1 (comp_Edge2 o' f' o) He))
          as [Y | Y]; [left | right]; right; exact Y.
    - (* FLR *) intros o o' f' Tr Hfl He.
      destruct (comp_fl_inv o Tr Hfl) as [Hf1 | [_ Hf2]].
      + destruct (FLR1 o o' f' Tr Hf1 (proj1 (comp_Edge o' f' o) He))
          as [Tr' [Hf' Hsub]].
        exists Tr'. split; [exact (comp_fl_1 o' Tr' Hf') | exact Hsub].
      + destruct (FLR2 o o' f' Tr Hf2 (proj1 (comp_Edge2 o' f' o) He))
          as [Tr' [Hf' Hsub]].
        exists Tr'. split; [exact (comp_fl_2 o' Tr' Hf') | exact Hsub].
    - (* WULK *) intros lw o t Hl Hit.
      destruct Hit as [H1 | H2].
      + destruct (WULK1 lw o t Hl H1) as [Hnu Hnf].
        split; intros [X | X];
          [exact (Hnu X)
          |exact (Hdisj o (conj (obs_owns1 o _ H1) (obs_owns2 o _ X)))
          |exact (Hnf X)
          |exact (Hdisj o (conj (obs_owns1 o _ H1) (obs_owns2 o _ X)))].
      + destruct (WULK2 lw o t ltac:(rewrite <- Hlk; exact Hl) H2) as [Hnu Hnf].
        split; intros [X | X];
          [exact (Hdisj o (conj (obs_owns1 o _ X) (obs_owns2 o _ H2)))
          |exact (Hnu X)
          |exact (Hdisj o (conj (obs_owns1 o _ X) (obs_owns2 o _ H2)))
          |exact (Hnf X)].
    - (* FR *) intros t x o Hstk Hob.
      destruct (comp_stk_inv x t o Hstk) as [H1 | H2].
      + assert (Hno2 : ~ owns s2 o) by exact (Hstk1 x t o H1).
        assert (Hob1 : obsv s1 o (Ofresh t))
          by (destruct Hob as [X | X];
              [exact X | exfalso; exact (unowned_obs o Hno2 _ X)]).
        destruct (FR1 t x o H1 Hob1) as [Hin Hal]. split.
        * intros o' g He. exact (Hin o' g (proj1 (comp_Edge o' g o) He)).
        * intros y t' Hne Hc. destruct (comp_stk_inv y t' o Hc) as [K1 | K2].
          -- exact (Hal y t' Hne K1).
          -- exact (Hstk2 y t' o K2 (obs_owns1 o _ Hob1)).
      + assert (Hno1 : ~ owns s1 o) by exact (Hstk2 x t o H2).
        assert (Hob2 : obsv s2 o (Ofresh t))
          by (destruct Hob as [X | X];
              [exfalso; exact (unowned_obs1 o Hno1 _ X) | exact X]).
        destruct (FR2 t x o H2 Hob2) as [Hin Hal]. split.
        * intros o' g He. exact (Hin o' g (proj1 (comp_Edge2 o' g o) He)).
        * intros y t' Hne Hc. destruct (comp_stk_inv y t' o Hc) as [K1 | K2].
          -- exact (Hstk1 y t' o K1 (obs_owns2 o _ Hob2)).
          -- exact (Hal y t' Hne K2).
    - (* WFresh *) intros t x o Hstk Hob.
      destruct (comp_stk_inv x t o Hstk) as [H1 | H2].
      + assert (Hno2 : ~ owns s2 o) by exact (Hstk1 x t o H1).
        assert (Hob1 : obsv s1 o (Ofresh t))
          by (destruct Hob as [X | X];
              [exact X | exfalso; exact (unowned_obs o Hno2 _ X)]).
        exact (WF1 t x o H1 Hob1).
      + assert (Hno1 : ~ owns s1 o) by exact (Hstk2 x t o H2).
        assert (Hob2 : obsv s2 o (Ofresh t))
          by (destruct Hob as [X | X];
              [exfalso; exact (unowned_obs1 o Hno1 _ X) | exact X]).
        rewrite comp_lk, Hlk. exact (WF2 t x o H2 Hob2).
    - (* FNR *) intros o t t' Hob.
      destruct Hob as [H1 | H2].
      + destruct (FNR1 o t t' H1) as (A & B & C).
        repeat apply conj; intros [X | X];
          [exact (A X) | exact (Hdisj o (conj (obs_owns1 o _ H1) (obs_owns2 o _ X)))
          |exact (B X) | exact (Hdisj o (conj (obs_owns1 o _ H1) (obs_owns2 o _ X)))
          |exact (C X) | exact (Hdisj o (conj (obs_owns1 o _ H1) (obs_owns2 o _ X)))].
      + destruct (FNR2 o t t' H2) as (A & B & C).
        repeat apply conj; intros [X | X];
          [exact (Hdisj o (conj (obs_owns1 o _ X) (obs_owns2 o _ H2))) | exact (A X)
          |exact (Hdisj o (conj (obs_owns1 o _ X) (obs_owns2 o _ H2))) | exact (B X)
          |exact (Hdisj o (conj (obs_owns1 o _ X) (obs_owns2 o _ H2))) | exact (C X)].
    - (* FPI *) intros o f o' t lw Hob He Hft Hl.
      destruct Hob as [H1 | H2].
      + left. exact (FPI1 o f o' t lw H1 (proj1 (comp_Edge o f o') He) Hft Hl).
      + right. apply (FPI2 o f o' t lw H2 (proj1 (comp_Edge2 o f o') He) Hft).
        rewrite <- Hlk. exact Hl.
    - (* WNR *) intros t Hl Hrd. exact (WNR1 t Hl Hrd).
    - (* RITR *) intros o t Hrd.
      destruct (RITR1 o t Hrd) as (A & B & C).
      destruct (RITR2 o t (proj1 (Hrds t) Hrd)) as (A' & B' & C').
      repeat apply conj; intros [X | X];
        [exact (A X) | exact (A' X) | exact (B X) | exact (B' X)
        |exact (C X) | exact (C' X)].
    - (* RINFL *) intros o Tr t Hfl Hin.
      destruct (comp_fl_inv o Tr Hfl) as [Hf1 | [_ Hf2]].
      + exact (RINFL1 o Tr t Hf1 Hin).
      + apply (proj2 (Hbnd t)). exact (RINFL2 o Tr t Hf2 Hin).
    - (* HD *) intros o f o' He Hnd.
      apply (proj2 (comp_InHeap o')).
      apply (HD1 o f o' (proj1 (comp_Edge o f o') He)).
      intros Hd. exact (Hnd (comp_det_1 o Hd)).
    - (* UNQRT_a *) intros o f He.
      exact (Ua1 o f (proj1 (comp_Edge o f _) He)).
    - (* UNQRT_b *) intros p o lw Hl Hr.
      destruct (Ub1 p o lw Hl (proj1 (comp_Reaches p o) Hr)) as [X | X];
        [left | right]; left; exact X.
    - (* WUNLK *) intros o t lw Hl [X | X].
      + destruct X as [Y | Y]; [exact (WU1 o t lw Hl (or_introl Y))
                               |exact (WU2 o t lw ltac:(rewrite <- Hlk; exact Hl)
                                         (or_introl Y))].
      + destruct X as [Y | Y]; [exact (WU1 o t lw Hl (or_intror Y))
                               |exact (WU2 o t lw ltac:(rewrite <- Hlk; exact Hl)
                                         (or_intror Y))].
    - (* WITR *) intros o t [X | X].
      + exact (WI1 o t X).
      + destruct (WI2 o t X) as [Hl | Hrd];
          [left; rewrite comp_lk, Hlk; exact Hl
          |right; exact (proj2 (Hrds t) Hrd)].
    - (* UNQR *) intros p p' o H1 H2.
      exact (UQ1 p p' o (proj1 (comp_Reaches p o) H1)
               (proj1 (comp_Reaches p' o) H2)).
  Qed.

End Closure.

Print Assumptions WellFormed_comp.

(** ** The repaired conditions are satisfiable

    A guard against the failure mode RITR exhibits.  [comp_ok'] is more
    demanding than the published conditions, and a composition operator defined
    on nothing would make [WellFormed_comp] true and useless.  Two views that do
    compose: one holding the root observation, one holding no auxiliary state at
    all, over the same heap. *)

Definition base_h : Loc -> FName -> option Val :=
  fun o _ => if Nat.eqb o 0 then Some VNull else None.

Definition cv1 : LState :=
  {| ms := {| stk := fun _ _ => None; hp := base_h; lk := None; rt := 0;
              rds := fun _ => False; bnd := fun _ => False |};
     obsv  := fun o ob => o = 0 /\ ob = Oroot;
     undf  := fun _ _ => False;
     thrd  := fun t => t = 0;
     flist := fun _ => None |}.

Definition cv2 : LState :=
  {| ms := {| stk := fun _ _ => None; hp := base_h; lk := None; rt := 0;
              rds := fun _ => False; bnd := fun _ => False |};
     obsv  := fun _ _ => False;
     undf  := fun _ _ => False;
     thrd  := fun t => t = 0;
     flist := fun _ => None |}.

Lemma cv_no_edges s : (forall o f, hp (ms s) o f = base_h o f) ->
  forall o f o', ~ Edge s o f o'.
Proof.
  intros Hh o f o'. unfold Edge. rewrite Hh. unfold base_h.
  destruct (Nat.eqb o 0); discriminate.
Qed.

Lemma cv_reach s : (forall o f, hp (ms s) o f = base_h o f) -> rt (ms s) = 0 ->
  forall p o, Reaches s p o -> p = [] /\ o = 0.
Proof.
  intros Hh Hr [|g p] o; unfold Reaches; rewrite Hr; simpl.
  - intros H. injection H as <-. split; reflexivity.
  - rewrite Hh. unfold base_h. simpl. discriminate.
Qed.

Lemma cv1_WellFormed FType : WellFormed FType cv1.
Proof.
  repeat apply conj.
  - intros o o' f f' x H. exfalso. exact (cv_no_edges cv1 (fun _ _ => eq_refl) o f x H).
  - intros x t o H. discriminate H.
  - intros y t H. discriminate H.
  - intros t o Tr H1 H2. discriminate H2.
  - intros o o' f' t _ H. exfalso.
    exact (cv_no_edges cv1 (fun _ _ => eq_refl) o' f' o H).
  - intros o o' f' Tr H1 H2. discriminate H1.
  - intros lw o t H. discriminate H.
  - intros t x o H. discriminate H.
  - intros t x o H. discriminate H.
  - intros o t t' [_ H]. discriminate H.
  - intros o f o' t lw [_ H]. discriminate H.
  - intros t H. discriminate H.
  - intros o t H. destruct H.
  - intros o Tr t H1 H2. discriminate H1.
  - intros o f o' H _. exfalso.
    exact (cv_no_edges cv1 (fun _ _ => eq_refl) o f o' H).
  - intros o f H. exact (cv_no_edges cv1 (fun _ _ => eq_refl) o f _ H).
  - intros p o lw H. discriminate H.
  - intros o t lw H. discriminate H.
  - intros o t [_ H]. discriminate H.
  - intros p p' o H1 H2.
    destruct (cv_reach cv1 (fun _ _ => eq_refl) eq_refl p o H1) as [-> _].
    destruct (cv_reach cv1 (fun _ _ => eq_refl) eq_refl p' o H2) as [-> _].
    reflexivity.
Qed.

Lemma cv2_WellFormed FType : WellFormed FType cv2.
Proof.
  repeat apply conj.
  - intros o o' f f' x H. exfalso.
    exact (cv_no_edges cv2 (fun _ _ => eq_refl) o f x H).
  - intros x t o H. discriminate H.
  - intros y t H. discriminate H.
  - intros t o Tr H1 H2. discriminate H2.
  - intros o o' f' t _ H. exfalso.
    exact (cv_no_edges cv2 (fun _ _ => eq_refl) o' f' o H).
  - intros o o' f' Tr H1 H2. discriminate H1.
  - intros lw o t H. discriminate H.
  - intros t x o H. discriminate H.
  - intros t x o H. discriminate H.
  - intros o t t' H. destruct H.
  - intros o f o' t lw H. destruct H.
  - intros t H. discriminate H.
  - intros o t H. destruct H.
  - intros o Tr t H1 H2. discriminate H1.
  - intros o f o' H _. exfalso.
    exact (cv_no_edges cv2 (fun _ _ => eq_refl) o f o' H).
  - intros o f H. exact (cv_no_edges cv2 (fun _ _ => eq_refl) o f _ H).
  - intros p o lw H. discriminate H.
  - intros o t lw H. discriminate H.
  - intros o t H. destruct H.
  - intros p p' o H1 H2.
    destruct (cv_reach cv2 (fun _ _ => eq_refl) eq_refl p o H1) as [-> _].
    destruct (cv_reach cv2 (fun _ _ => eq_refl) eq_refl p' o H2) as [-> _].
    reflexivity.
Qed.

Lemma cv_comp_ok : comp_ok' cv1 cv2.
Proof.
  unfold comp_ok'. repeat apply conj.
  - intros o f. reflexivity.
  - reflexivity.
  - reflexivity.
  - intros t. split; intros H; exact H.
  - intros t. split; intros H; exact H.
  - intros o [_ [[ob H] | H]]; [destruct H | apply H; reflexivity].
  - intros x t o H. discriminate H.
  - intros x t o H. discriminate H.
  - intros x t. left. reflexivity.
Qed.

Theorem repaired_composition_is_not_vacuous :
  (forall FType, WellFormed FType cv1)
  /\ (forall FType, WellFormed FType cv2)
  /\ comp_ok' cv1 cv2
  /\ (forall FType, WellFormed FType (comp cv1 cv2)).
Proof.
  split; [exact cv1_WellFormed |].
  split; [exact cv2_WellFormed |].
  split; [exact cv_comp_ok |].
  intros FType.
  exact (WellFormed_comp FType cv1 cv2 cv_comp_ok
           (cv1_WellFormed FType) (cv2_WellFormed FType)).
Qed.

Print Assumptions repaired_composition_is_not_vacuous.

(** * Interference

    The framework's other requirement.  Views must be closed under the
    interference relation as well as under composition, and Section
    [sec:soundness] asserts both in the same sentence.  Figure [fig:comp] gives
    the relation; this is it, transcribed. *)

Definition R0 (s s' : LState) : Prop :=
  (* the lock holder's own view sees no heap or lock change *)
  (forall lw, lk (ms s) = Some lw -> thrd s lw ->
     (forall o f, hp (ms s) o f = hp (ms s') o f) /\ lk (ms s) = lk (ms s'))
  /\ (forall lw, lk (ms s) = Some lw -> thrd s lw ->
     forall o, flist s o = flist s' o)
  (* observed nodes stay allocated, before and after *)
  /\ (forall t o, obsv s o (Oiter t) -> InHeap s o)
  /\ (forall t o, obsv s o (Oiter t) -> InHeap s' o)
  /\ (forall o, obsv s o Oroot -> InHeap s o)
  /\ (forall o, obsv s o Oroot -> InHeap s' o)
  (* and the auxiliary state, the readers and the root are fixed *)
  /\ (forall o ob, obsv s o ob <-> obsv s' o ob)
  /\ (forall x t, undf s x t <-> undf s' x t)
  /\ (forall t, thrd s t <-> thrd s' t)
  /\ (forall t, rds (ms s) t <-> rds (ms s') t)
  /\ rt (ms s) = rt (ms s')
  /\ (forall x t, thrd s t -> stk (ms s) x t = stk (ms s') x t).

(** ** The formula for interference does not entail WellFormed

    Not a defect, and the difference from the composition case is worth stating.
    Composition is declared a *function* into [M], so landing in [M] is an
    obligation, and the counterexample above discharges it negatively.
    Interference is declared a *relation* on [M], so it relates well-formed
    states to well-formed states by construction; the report's parenthetical
    restates that typing rather than adding to it.

    What is true is that the formula alone does not entail it, so [R0] must be
    read as intersected with [M x M] -- and a reader mechanizing from the figure
    will get that wrong.  The relation
    constrains the successor heap only by requiring that nodes already observed
    as iterators or as the root stay allocated.  A view holding no such
    observation therefore permits *any* successor heap, and in particular one
    that is not a tree.

    The witness reuses the shape of the composition counterexample: a view with
    no observations at all, stepping to the same view over a heap with two edges
    into one node.  Every clause of the relation is satisfied vacuously. *)

Definition bad_h : Loc -> FName -> option Val :=
  fun o f =>
    if Nat.eqb o 0 then (if Nat.eqb f 0 then Some (VLoc 2) else None)
    else if Nat.eqb o 1 then (if Nat.eqb f 0 then Some (VLoc 2) else None)
    else if Nat.eqb o 2 then Some VNull else None.

Definition cv2' : LState :=
  {| ms := {| stk := fun _ _ => None; hp := bad_h; lk := None; rt := 0;
              rds := fun _ => False; bnd := fun _ => False |};
     obsv  := fun _ _ => False;
     undf  := fun _ _ => False;
     thrd  := fun t => t = 0;
     flist := fun _ => None |}.

Lemma cv2'_not_WellFormed : ~ WellFormed allrcu cv2'.
Proof.
  intros (HOW & _).
  assert (He1 : Edge cv2' 0 0 2) by reflexivity.
  assert (He2 : Edge cv2' 1 0 2) by reflexivity.
  destruct (HOW 0 1 0 0 2 He1 He2 eq_refl eq_refl) as [[Hc _] | [Hd | Hd]].
  - discriminate Hc.
  - destruct Hd as [t [H | [H | H]]]; destruct H.
  - destruct Hd as [t [H | [H | H]]]; destruct H.
Qed.

Lemma cv2_R0_cv2' : R0 cv2 cv2'.
Proof.
  unfold R0. repeat apply conj.
  - intros lw H. discriminate H.
  - intros lw H. discriminate H.
  - intros t o H. destruct H.
  - intros t o H. destruct H.
  - intros o H. destruct H.
  - intros o H. destruct H.
  - intros o ob. split; intros H; destruct H.
  - intros x t. split; intros H; destruct H.
  - intros t. split; intros H; exact H.
  - intros t. split; intros H; exact H.
  - reflexivity.
  - intros x t _. reflexivity.
Qed.

Theorem interference_does_not_preserve_WellFormed :
  (forall FType, WellFormed FType cv2)
  /\ R0 cv2 cv2'
  /\ ~ WellFormed allrcu cv2'.
Proof.
  split; [exact cv2_WellFormed |].
  split; [exact cv2_R0_cv2' |].
  exact cv2'_not_WellFormed.
Qed.

(** ** What the relation is missing

    The two failures are the same failure.  Composition lets two views disagree
    about how many edges reach a node; interference lets one view change its
    mind about it.  In both cases the heap is treated as something each view
    holds a piece or a copy of, and the invariants are about the heap as a
    whole.

    The repair is the same in shape as well.  The heap is shared, so a frame
    must see the lock holder's writes rather than being free to invent its own:
    the first clause has to hold unconditionally, not only when the lock holder
    is among this view's threads.  With [hp] and [lk] fixed, and [obsv], [undf],
    [thrd], [rds] and [rt] already fixed by the relation as written, what is
    left free is the bounding set and the free list -- and RINFL relates those
    two, so they have to move together, which is exactly what SyncStart and
    SyncStop do and what [sync_start_preserves_WellFormed] proves.

    We stop here rather than fixing it, and deliberately.  Composition had one
    defensible reading and we took it; interference has a real choice in it --
    how much of another thread's behaviour a frame is allowed to assume -- and
    that choice determines what the framing lemma can say.  It belongs to
    whoever owns the proof architecture, not to the mechanization. *)

Print Assumptions cv2'_not_WellFormed.
Print Assumptions interference_does_not_preserve_WellFormed.
