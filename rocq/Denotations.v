(** * Denotations: the type denotations of Figure [denotingtypeenviroment].

    Milestone 4, first half.  [IrisGhost.v] made the observation map and free
    list into resources; this file says what the *types* mean over a logical
    state.  It is deliberately Iris-free, for the same reason [WellFormed.v] is:
    the denotations are sets of logical states in the Views encoding, so they
    are predicates, and keeping them so means they can be checked against the
    figure directly and reused by the Iris layer without restatement.

    The payoff is at the end.  The three heap-mutation theorems of
    [HeapPaths.v] take hypotheses -- [Mirrors], [PointsOnlyAt] -- that were
    justified in prose against the type rules.  Here those justifications become
    proofs: the denotation of the pre-environment, together with the rule's
    premises, *implies* them.  That closes the loop between the type system and
    the reachability results, and it is where the two side conditions added to
    T-Replace and the strengthened [rcuFresh] denotation earn their place.

    Checked with Rocq 9.2, axiom-free. *)

From Stdlib Require Import List Arith Lia.
Import ListNotations.
From RCU Require Import WellFormed HeapPaths.

(** ** Field maps

    A field map records, for the fields that have been read or written, what
    they hold: a local variable, or null.  Fields outside its domain are not
    tracked -- which is the gap the [rcuFresh] denotation now closes. *)

Inductive FieldVal := FVar (y : Var) | FNull.

Definition FieldMap := FName -> option FieldVal.

Definition FMdom (N : FieldMap) (f : FName) : Prop := N f <> None.

(** ** The denotations *)

Section Denotations.

  Variable FType : FName -> FieldKind.

  (** What a field map entry asserts about the heap at [o]. *)
  Definition FieldHolds (s : LState) (t : TID) (o : Loc) (f : FName)
                        (v : FieldVal) : Prop :=
    match v with
    | FVar y => exists oy, stk (ms s) y t = Some oy
                        /\ hp (ms s) o f = Some (VLoc oy)
                        /\ obsv s oy (Oiter t)
                        /\ flist s oy = None
    | FNull  => hp (ms s) o f = Some VNull
    end.

  (** [rcuItr rho N] for the writer.  Every prefix of the path is observed as
      an iterator, the path from the root lands on the object, and the object is
      not awaiting reclamation. *)
  Definition D_rcuItr (s : LState) (t : TID) (x : Var)
                      (rho : list FName) (N : FieldMap) : Prop :=
    exists o,
      stk (ms s) x t = Some o
      /\ obsv s o (Oiter t)
      /\ ~ undf s x t
      /\ (forall f v, N f = Some v -> FieldHolds s t o f v)
      /\ (forall rho1 rho2, rho1 ++ rho2 = rho ->
            exists o', hstar (hp (ms s)) (rt (ms s)) rho1 = Some o'
                    /\ obsv s o' (Oiter t))
      /\ hstar (hp (ms s)) (rt (ms s)) rho = Some o
      /\ lk (ms s) = Some t
      /\ flist s o = None.

  (** [rcuFresh N].  The last conjunct is the clause added in the revision:
      every RCU field *outside* the map is null, so [N] determines the fresh
      node's whole RCU footprint rather than only the written part.  Without it
      an untracked field could point anywhere. *)
  Definition D_rcuFresh (s : LState) (t : TID) (x : Var) (N : FieldMap) : Prop :=
    exists o,
      stk (ms s) x t = Some o
      /\ obsv s o (Ofresh t)
      /\ ~ undf s x t
      /\ flist s o = None
      /\ (forall f v, N f = Some v -> FieldHolds s t o f v)
      /\ (forall g, FType g = RCUField -> N g = None ->
            hp (ms s) o g = Some VNull).

  Definition D_unlinked (s : LState) (t : TID) (x : Var) : Prop :=
    exists o,
      stk (ms s) x t = Some o
      /\ obsv s o (Ounlk t)
      /\ lk (ms s) = Some t
      /\ ~ undf s x t.

  Definition D_freeable (s : LState) (t : TID) (x : Var) : Prop :=
    exists o,
      stk (ms s) x t = Some o
      /\ obsv s o (Ofree t)
      /\ lk (ms s) = Some t
      /\ ~ undf s x t
      /\ flist s o = Some (fun _ => False).

  Definition D_undef (s : LState) (t : TID) (x : Var) : Prop :=
    undf s x t /\ (forall o, stk (ms s) x t = Some o -> flist s o = None).

  Definition D_rcuRoot (s : LState) (t : TID) (x : Var) : Prop :=
    stk (ms s) x t = Some (rt (ms s)) /\ obsv s (rt (ms s)) Oroot.

  (** ** Consequences

      Two sanity properties first, then the two that matter. *)

  (** An iterator reference is not simultaneously unlinked.  This is WULK read
      through the denotations, and it is what stops a writer from holding the
      same object under two incompatible types. *)
  Lemma itr_not_unlinked s t x rho N :
    WULK s -> D_rcuItr s t x rho N -> ~ D_unlinked s t x.
  Proof.
    intros HW [o (Hstk & Hitr & _ & _ & _ & _ & Hlk & _)]
              [o' (Hstk' & Hunl & _ & _)].
    rewrite Hstk in Hstk'. injection Hstk' as <-.
    destruct (HW t o t Hlk Hitr) as [Hno _]. exact (Hno Hunl).
  Qed.

  (** A writer's iterator is reachable at its path.  This is the hypothesis the
      reachability corollaries of [HeapPaths.v] take. *)
  Lemma itr_reaches s t x rho N o :
    D_rcuItr s t x rho N -> stk (ms s) x t = Some o ->
    hstar (hp (ms s)) (rt (ms s)) rho = Some o.
  Proof.
    intros [o' (Hstk & _ & _ & _ & _ & Hreach & _)] Hstk'.
    rewrite Hstk in Hstk'. injection Hstk' as <-. exact Hreach.
  Qed.

  (** *** T-Insert's hypothesis is supplied by the denotation

      [PointsOnlyAt h n f4 o] says the fresh node's only outgoing RCU edge is
      [f4], pointing at [o].  [HeapPaths.v] took it as a hypothesis and argued
      in prose that the rule supplies it.  It does, but only with the added
      clause: the rule's own condition covers the tracked fields, and the
      denotation covers the rest.

      The [Heap] here is the raw heap, which carries RCU fields; the
      [FType g = RCUField] side condition is what restricts the quantification
      to those. *)
  Theorem fresh_denot_PointsOnlyAt s t x N n f4 y o :
    (forall g, FType g = RCUField) ->
    D_rcuFresh s t x N ->
    stk (ms s) x t = Some n ->
    N f4 = Some (FVar y) ->
    stk (ms s) y t = Some o ->
    (forall f, N f <> None -> f <> f4 -> N f = Some FNull) ->
    PointsOnlyAt (hp (ms s)) n f4 o.
  Proof.
    intros Hall [n' (Hstk & _ & _ & _ & Hfields & Hnull)] Hstkn Hf4 Hy Hother.
    rewrite Hstk in Hstkn. injection Hstkn as <-.
    split.
    - (* the f4 edge points at o *)
      destruct (Hfields f4 (FVar y) Hf4) as [oy (Hy' & Hedge & _ & _)].
      rewrite Hy in Hy'. injection Hy' as <-. exact Hedge.
    - (* every other field is null, tracked or not *)
      intros g z Hg Hedge.
      destruct (N g) as [v|] eqn:Hng.
      + (* tracked, and not f4, so null by the rule's premise *)
        assert (Hv : N g = Some FNull)
          by (apply Hother; [rewrite Hng; discriminate | exact Hg]).
        pose proof (Hfields g FNull Hv) as Hnullg. simpl in Hnullg.
        rewrite Hnullg in Hedge. discriminate.
      + (* untracked: null by the added clause of the denotation *)
        rewrite (Hnull g (Hall g) Hng) in Hedge. discriminate.
  Qed.

  (** *** T-Replace's hypothesis is supplied by the denotation plus the new
      side condition

      [Mirrors h n o] says the fresh node agrees with the replaced one on every
      field.  Equality of the two field maps is not enough on its own -- that is
      the gap the revision records -- but with the side condition that
      [dom(N)] covers every RCU field, the two denotations pin every field of
      both nodes and mirroring follows. *)
  Theorem replace_denot_Mirrors s t xn xo rho N n o :
    (forall g, FType g = RCUField) ->
    D_rcuFresh s t xn N ->
    D_rcuItr s t xo rho N ->
    stk (ms s) xn t = Some n ->
    stk (ms s) xo t = Some o ->
    (forall g, FType g = RCUField -> N g <> None) ->
    Mirrors (hp (ms s)) n o.
  Proof.
    intros Hall [n' (Hstkn & _ & _ & _ & Hfn & _)]
                [o' (Hstko & _ & _ & Hfo & _)] Hn Ho Hdom g.
    rewrite Hstkn in Hn. injection Hn as <-.
    rewrite Hstko in Ho. injection Ho as <-.
    (* every field is tracked, so both denotations fix it to the same thing *)
    destruct (N g) as [v|] eqn:Hng.
    - destruct v as [y|].
      + destruct (Hfn g (FVar y) Hng) as [oy1 (Hy1 & He1 & _ & _)].
        destruct (Hfo g (FVar y) Hng) as [oy2 (Hy2 & He2 & _ & _)].
        rewrite Hy1 in Hy2. injection Hy2 as <-.
        rewrite He1, He2. reflexivity.
      + pose proof (Hfn g FNull Hng) as He1. simpl in He1.
        pose proof (Hfo g FNull Hng) as He2. simpl in He2.
        rewrite He1, He2. reflexivity.
    - exfalso. exact (Hdom g (Hall g) Hng).
  Qed.


  (** ** Type environments

      The environment denotation is the *intersection* of the individual
      variables' denotations, not a separating conjunction.  That is faithful to
      the figure, and it is not an incidental choice: it is what allows two
      variables to denote overlapping structure, which is how a rcuFresh
      reference can come to point at the node T-Replace unlinks.  The
      counterexample is [FPI_not_preserved_by_replace] in WellFormed.v; here the
      definition simply records that nothing in the environment's shape rules it
      out. *)

  Inductive Ty :=
  | TItr   (rho : list FName) (N : FieldMap)
  | TFresh (N : FieldMap)
  | TUnlinked
  | TFreeable
  | TUndef
  | TRoot.

  Definition D_ty (s : LState) (t : TID) (x : Var) (T : Ty) : Prop :=
    match T with
    | TItr rho N => D_rcuItr s t x rho N
    | TFresh N   => D_rcuFresh s t x N
    | TUnlinked  => D_unlinked s t x
    | TFreeable  => D_freeable s t x
    | TUndef     => D_undef s t x
    | TRoot      => D_rcuRoot s t x
    end.

  Definition Env := list (Var * Ty).

  Definition D_env (s : LState) (t : TID) (G : Env) : Prop :=
    forall x T, In (x, T) G -> D_ty s t x T.

  (** ** From FR to the two unreachability facts UNQR_replace needs *)

  (** FR's first clause: nothing in the heap points at a fresh node. *)
  Lemma fresh_no_incoming s t x N n :
    FR s -> D_rcuFresh s t x N -> stk (ms s) x t = Some n ->
    forall o f, hp (ms s) o f <> Some (VLoc n).
  Proof.
    intros HFR [n' (Hstk & Hfresh & _)] Hstkn o f Hedge.
    rewrite Hstk in Hstkn. injection Hstkn as <-.
    destruct (HFR t x n' Hstk Hfresh) as [Hno _].
    exact (Hno o f Hedge).
  Qed.

  (** FR's second clause: no other variable aliases a fresh node.  The root is
      held by a rcuRoot reference, so a fresh node is never the root. *)
  Lemma fresh_not_root s t xr xn N n :
    FR s -> D_rcuRoot s t xr -> D_rcuFresh s t xn N ->
    stk (ms s) xn t = Some n -> xr <> xn -> rt (ms s) <> n.
  Proof.
    intros HFR [Hrstk _] [n' (Hstk & Hfresh & _)] Hstkn Hne Heq.
    rewrite Hstk in Hstkn. injection Hstkn as <-.
    destruct (HFR t xn n' Hstk Hfresh) as [_ Halias].
    apply (Halias xr t).
    - intros Hpair. apply Hne. congruence.
    - rewrite Hrstk, Heq. reflexivity.
  Qed.

  (** A fresh node is unreachable from the root. *)
  Lemma fresh_unreachable s t xr xn N n :
    FR s -> D_rcuRoot s t xr -> D_rcuFresh s t xn N ->
    stk (ms s) xn t = Some n -> xr <> xn ->
    forall sigma, hstar (hp (ms s)) (rt (ms s)) sigma <> Some n.
  Proof.
    intros HFR Hroot Hfresh Hstkn Hne.
    apply no_incoming_unreachable.
    - exact (fresh_no_incoming s t xn N n HFR Hfresh Hstkn).
    - exact (fresh_not_root s t xr xn N n HFR Hroot Hfresh Hstkn Hne).
  Qed.

  (** ** An atomic-action lemma

      T-Replace preserves the tree shape.  This is the UNQR case of the Replace
      lemma of the appendix, assembled from the pieces rather than argued: the
      denotations supply the mirroring and the two unreachability facts, and
      [UNQR_replace] does the path reasoning.

      Every hypothesis here is either an invariant of the pre-state or a premise
      of the rule.  Nothing is assumed about the heap directly. *)
  Theorem replace_preserves_UNQR s t xr xp xo xn f rho rho1 N Np op oo on :
    (forall g, FType g = RCUField) ->
    (* pre-state invariants *)
    UNQR_h (hp (ms s)) (rt (ms s)) ->
    FR s ->
    (* the environment *)
    D_rcuRoot  s t xr ->
    D_rcuItr   s t xp rho  Np ->
    D_rcuItr   s t xo rho1 N ->
    D_rcuFresh s t xn N ->
    stk (ms s) xp t = Some op ->
    stk (ms s) xo t = Some oo ->
    stk (ms s) xn t = Some on ->
    xr <> xn ->
    (* rule premises: p.f is o, and N covers every RCU field *)
    Np f = Some (FVar xo) ->
    (forall g, FType g = RCUField -> N g <> None) ->
    UNQR_h (upd (hp (ms s)) op f (VLoc on)) (rt (ms s)).
  Proof.
    intros Hall HU HFR Hroot Hp Ho Hn Hstkp Hstko Hstkn Hne Hpf Hdom.
    (* the written edge *)
    assert (Hedge : hp (ms s) op f = Some (VLoc oo)).
    { destruct Hp as [op' (Hstkp' & _ & _ & Hfields & _)].
      rewrite Hstkp in Hstkp'. injection Hstkp' as <-.
      destruct (Hfields f (FVar xo) Hpf) as [oy (Hy & He & _ & _)].
      rewrite Hstko in Hy. injection Hy as <-. exact He. }
    (* the fresh node is unreachable, hence distinct from p *)
    assert (Hfresh : forall sigma,
              hstar (hp (ms s)) (rt (ms s)) sigma <> Some on)
      by exact (fresh_unreachable s t xr xn N on HFR Hroot Hn Hstkn Hne).
    assert (Hnp : on <> op).
    { intros ->. apply (Hfresh rho).
      exact (itr_reaches s t xp rho Np op Hp Hstkp). }
    apply (UNQR_replace (hp (ms s)) (rt (ms s)) op f oo on HU).
    - exact (replace_denot_Mirrors s t xn xo rho1 N on oo
                                   Hall Hn Ho Hstkn Hstko Hdom).
    - exact Hnp.
    - exact Hedge.
    - (* no path from o back to p: the tree shape *)
      exact (UNQR_no_back_edge (hp (ms s)) (rt (ms s)) op f oo rho HU
               (itr_reaches s t xp rho Np op Hp Hstkp) Hedge).
    - exact Hfresh.
  Qed.

End Denotations.

(** ** Status

    The denotations are stated, and the two hypotheses that [HeapPaths.v] took
    on trust are now derived from them:

      - [fresh_denot_PointsOnlyAt] needs the clause added to the [rcuFresh]
        denotation.  Without it the untracked-field case has nothing to appeal
        to, which is exactly the hole the revision found.
      - [replace_denot_Mirrors] needs the side condition added to T-Replace.
        Without it the [N g = None] case is not contradictory and the two
        subtrees may differ.

    So both repairs are load-bearing here, not bookkeeping: each is the step
    that makes its proof close.

    What remains for milestone 4 is the environment denotation and the
    atomic-action lemmas as Hoare triples over [rcu_inv]. *)

Print Assumptions itr_not_unlinked.
Print Assumptions fresh_denot_PointsOnlyAt.
Print Assumptions replace_denot_Mirrors.
Print Assumptions fresh_unreachable.
Print Assumptions replace_preserves_UNQR.
