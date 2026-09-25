(** * Closed: the reader's read, and the enumerations

    Milestone 9.  Two things were named as open at the end of [Triples.v] and
    neither is a missing invariant; both are about what a rule can be *stated*
    to consume.

    The first is the reader's read.  [read_typed] is the step and the
    environment in one statement, but it takes the edge as a hypothesis, and
    the reason recorded there was that a reader cannot learn a cell's contents
    while the points-to assertion is exclusive.  That reason is wrong, and
    finding out why is the content of the first half of this file: the
    invariant *holds* the authoritative heap, so a reader that opens it learns
    the edge there, and the reader's own denotation mentions no cell at all --
    so no fragment, and no fraction, is needed on either side.

    What was actually in the way is one step further on.  [read_typed] moves
    the reader's stack fragment, and closing the invariant needs the *machine*
    stack to move with it; the general bind asks for the bound node to be
    neither detached nor awaiting reclamation, and a reader can have neither.
    Holding a reference to a node a writer has already unlinked is not an edge
    case of RCU, it is the whole of it.  So the bind a reader performs is a
    different lemma, and [reader_bind_preserves_WellFormed] is it.

    The second is the enumeration premises, and they come out by finiteness:
    every set that has to be enumerated is a set of keys of a [gmap] the
    invariant already carries.

    Checked with Rocq 9.2, axiom-free. *)

From iris.algebra Require Import auth gmap gset excl local_updates.
From iris.algebra.lib Require Import excl_auth.
From iris.base_logic.lib Require Import invariants own.
From iris.proofmode Require Import proofmode.
From stdpp Require Import gmap sets.
From RCU Require Import WellFormed HeapPaths IrisGhost Denotations Actions
                        Epochs Triples.

(** ** The reader's bind

    The read grants the observation and the bind moves the stack, and the two
    are separate because their premises are.  The observation is
    [reader_acquire_preserves_WellFormed] in [Actions.v] and it is where the
    bounding obligation is discharged; what is left here changes [stk] and the
    scope and nothing else.

    That makes the proof short in a way worth recording rather than hiding.
    Of the twenty conjuncts exactly four mention the stack --- RWOW, AWRT, FR
    and WFresh --- and only the first two mention the scope.  The other sixteen
    are identities, because the observation map, the free list, the heap, the
    lock and the root are all untouched.  So a reader's bind cannot break an
    invariant about detachment or reclamation, which is why it needs no premise
    about either, and why the general bind's two premises --- the node is not
    detached, and has no free-list entry --- are not weakened here but absent.

    They are absent because they were never the bind's business.  They belong
    to the *writer's* bind, whose post-type is \itr{} with a path and a field
    map, and whose denotation asks for both. *)

Section reader_bind.
  Variable FType : FName -> FieldKind.
  Variables (m : MState) (Og : ObsMap) (U U' : Var -> TID -> Prop)
            (T : gset TID) (F : gmap Loc (gset TID)).
  Variables (t : TID) (y : Var) (o : Loc).

  Let s  := to_LState_t m Og U T F.
  Let s' := to_LState_t (bind_ms m y t o) Og U' T F.

  (** What the read has already established. *)
  Hypothesis Hitr : obsv s o (Oiter t).
  Hypothesis Hnf  : forall t0, ~ obsv s o (Ofresh t0).

  (** And what the bind does to the scope: nothing, off the slot it writes.
      That [y] itself becomes *defined* is not needed here and is not assumed:
      it is what the reader's post-type asks for, not what the invariant does,
      and an invariant that needed it would be an invariant about a type. *)
  Hypothesis Hscope : forall z q, (z, q) <> (y, t) -> (U' z q <-> U z q).

  Lemma rb_stk_inv z q p :
    stk (ms s') z q = Some p ->
    (z = y /\ q = t /\ p = o)
    \/ (stk (ms s) z q = Some p /\ (z, q) <> (y, t)).
  Proof.
    simpl. destruct (decide ((z, q) = (y, t))) as [Heq | Hne].
    - injection Heq as -> ->. intros H. injection H as <-.
      left. by repeat split.
    - intros H. by right.
  Qed.

  Lemma rb_RWOW : RWOW s -> RWOW s'.
  Proof.
    intros H z q p Hstk Hnu.
    destruct (rb_stk_inv z q p Hstk) as [(-> & -> & ->) | [Hstk0 Hne]].
    - by left.
    - exact (H z q p Hstk0 (fun Hc => Hnu (proj2 (Hscope z q Hne) Hc))).
  Qed.

  Lemma rb_AWRT : AWRT s -> AWRT s'.
  Proof.
    intros H z q Hstk Hnu.
    destruct (rb_stk_inv z q (rt (ms s')) Hstk) as [(-> & -> & Hq) | [Hstk0 Hne]].
    - rewrite Hq. exact Hitr.
    - exact (H z q Hstk0 (fun Hc => Hnu (proj2 (Hscope z q Hne) Hc))).
  Qed.

  Lemma rb_FR : FR s -> FR s'.
  Proof.
    intros H q z p Hstk Hfr.
    destruct (rb_stk_inv z q p Hstk) as [(-> & -> & ->) | [Hstk0 Hne]].
    - by destruct (Hnf t Hfr).
    - destruct (H q z p Hstk0 Hfr) as [Hno Halias].
      split; [exact Hno |].
      intros w q' Hw Hbad.
      destruct (rb_stk_inv w q' p Hbad) as [(-> & -> & Hp) | [Hstk1 _]].
      + subst p. by destruct (Hnf q Hfr).
      + exact (Halias w q' Hw Hstk1).
  Qed.

  Lemma rb_WFresh : WFresh s -> WFresh s'.
  Proof.
    intros H q z p Hstk Hfr.
    destruct (rb_stk_inv z q p Hstk) as [(-> & -> & ->) | [Hstk0 Hne]].
    - by destruct (Hnf t Hfr).
    - exact (H q z p Hstk0 Hfr).
  Qed.

  Theorem reader_bind_preserves_WellFormed :
    WellFormed FType s -> WellFormed FType s'.
  Proof.
    intros (HOW & HRWOW & HAWRT & HIFL & HULKR & HFLR & HWULK & HFR & HWFresh
            & HFNR & HFPI & HWNR & HRITR & HRINFL & HHD & HUa & HUb & HWU & HWI
            & HUq).
    repeat apply conj.
    - exact HOW.
    - exact (rb_RWOW HRWOW).
    - exact (rb_AWRT HAWRT).
    - exact HIFL.
    - exact HULKR.
    - exact HFLR.
    - exact HWULK.
    - exact (rb_FR HFR).
    - exact (rb_WFresh HWFresh).
    - exact HFNR.
    - exact HFPI.
    - exact HWNR.
    - exact HRITR.
    - exact HRINFL.
    - exact HHD.
    - exact HUa.
    - exact HUb.
    - exact HWU.
    - exact HWI.
    - exact HUq.
  Qed.

End reader_bind.

Print Assumptions reader_bind_preserves_WellFormed.

(** ** Reading a field, closed against the invariant

    The statement the reader's read was short of.  A reader inside a critical
    section, holding its registration, its own observation entries, an iterator
    at [x] and the slot it is about to overwrite, performs [y := x.f] and gets
    back an iterator at [y] --- or, if the field held no reference, gets back
    exactly what it had.

    Nothing is assumed about the heap.  The edge is *read* from the invariant,
    which is where the earlier account went wrong: it asked how a reader could
    hold a points-to for a cell a writer may be about to overwrite, and the
    answer is that it does not have to.  The authoritative heap is in the
    invariant, the read is one access inside it, and the reader's post-type
    mentions no cell --- a reader's \itr{} is observations and a stack binding
    and nothing else.  A fraction would buy something only if the reader had to
    carry a cell out past the closing, and it does not.

    What the proof does need, and what [Triples.v] could not supply, is the
    bind: the machine's stack has to move with the ghost one, and the general
    bind's premises fail for a reader.  [reader_bind_preserves_WellFormed]
    above is the replacement, and the two facts it asks for are the two the
    read itself establishes. *)

(** Changing the *domain* a registration records leaves the epoch state alone,
    because the epoch state reads only the epoch.  That is what lets a read
    grow the reader's domain without disturbing anything the free list is
    derived from. *)
Lemma mkE_dom g Rg St t e D D' :
  Rg !! t = Some (Some (e, D)) ->
  mkE g (<[t := Some (e, D')]> Rg) St = mkE g Rg St.
Proof.
  intros H. unfold mkE. f_equal. apply map_eq. intros t'.
  rewrite !lookup_omap.
  destruct (decide (t' = t)) as [-> | Hne].
  - by rewrite (lookup_insert_eq Rg t) H.
  - by rewrite (lookup_insert_ne Rg t t');
      [| exact (fun Hc => Hne (eq_sym Hc))].
Qed.

Section atomic_read.
  Context `{!rcuG Σ, !physG Σ, !heapG Σ, !lockG Σ, !stackG Σ, !freshG Σ,
            !invGS_gen hlc Σ}.
  Context (FType : FName -> FieldKind).
  Context (root : Loc) (fs : list FName).

  Lemma read_atomic N γm γh γl γs γo γf γr γe γq E (t : TID) (e : nat)
        (Ob : gmap Loc (gset obs)) (x y : Var) (f : FName) (o o0 : Loc)
        (so : gset obs) :
    ↑N ⊆ E ->
    Ob !! o = Some so -> Oiter t ∈ so ->
    rcu_invT FType (phys γm γh γl γs root fs) N γo γf γr γe γq -∗
    reg_cell γe t (Some (e, dom Ob)) -∗ obs_own γo t Ob -∗
    sv γs x t o -∗ sv γs y t o0
    ={E}=∗ sv γs x t o
      ∗ ((∃ z sz, ⌜dom (<[z := sz ∪ {[Oiter t]}]> Ob) = dom Ob ∪ {[z]}⌝
                  ∗ ⌜forall sg, Ob !! z = Some sg -> sg = sz⌝
                  ∗ reg_cell γe t (Some (e, dom Ob ∪ {[z]}))
                  ∗ obs_own γo t (<[z := sz ∪ {[Oiter t]}]> Ob)
                  ∗ sv γs y t z)
         ∨ (reg_cell γe t (Some (e, dom Ob)) ∗ obs_own γo t Ob
            ∗ sv γs y t o0)).
  Proof.
    iIntros (HN Hoo Hito) "#Hinv Hcell Hob Hsvx Hsvy".
    iInv "Hinv" as (m Og U T F St Rg gg ww Fr)
      ">(Hp & Ho & Hf & Hreg & Hwm & Hfr & %HWF & %HFLD & %HWFW & %HRefs & %HFrc
         & %Hwf & %HWUW & %HFeq & %HEWF & %HRR & %HBnd & %HLk & %HWm & %Hdom
         & %HSS & %HFRW & %HNE)"
      "Hclose".
    iDestruct (reg_cell_agree with "Hreg Hcell") as %Hcell.
    iDestruct (obs_own_agree with "Ho Hob") as %Hag.
    assert (Hrd : rds m t) by (apply HRR; by exists e, (dom Ob)).
    (* the edge, read from the invariant's own heap *)
    destruct (hp m o f) as [[z | ] | ] eqn:Hedge; last first.
    - (* no cell: nothing happens *)
      iMod ("Hclose" with "[Hp Ho Hf Hreg Hwm Hfr]") as "_";
        [ iNext; iExists m, Og, U, T, F, St, Rg, gg, ww, Fr; by iFrame |].
      iModIntro. iFrame. iRight. iFrame.
    - (* null: nothing happens *)
      iMod ("Hclose" with "[Hp Ho Hf Hreg Hwm Hfr]") as "_";
        [ iNext; iExists m, Og, U, T, F, St, Rg, gg, ww, Fr; by iFrame |].
      iModIntro. iFrame. iRight. iFrame.
    - (* a reference: the reader acquires it and binds *)
      rewrite HFeq in Hwf, HFLD, HWFW, HFrc, HWUW, HFRW.
      iMod (read_update FType γo γe m Og U T gg Rg St t e Ob o f z
              HWF Hwf HFRW HRR Hdom HSS Hedge
              (ex_intro _ so (conj Hoo Hito))
              with "Hreg Ho Hcell Hob")
        as (sz) "(Ho & Hreg & Hcell & Hob & %Hdz & %Hold & %HWF' & %Hwf')".
      rewrite <- HFeq in Hwf, HFLD, HWFW, HFrc, HWUW, HFRW, Hwf'.
      set (Og' := <[(z, t) := sz ∪ {[Oiter t]}]> Og).
      set (Rg' := <[t := Some (e, dom Ob ∪ {[z]})]> Rg).
      set (U'  := fun (w : Var) (q : TID) => U w q /\ (w, q) <> (y, t)).
      (* the target is not fresh: nothing reachable by an edge is *)
      assert (Hnf : forall t0, ~ obsv (to_LState_t m Og U T F) z (Ofresh t0))
        by (intros t0 Hbad; exact (HFRW z t0 Hbad o f Hedge)).
      (* observations of other threads are untouched *)
      assert (Hback : forall q ob, obs_tid ob <> Some t ->
                obsv (to_LState_t m Og' U T F) q ob ->
                obsv (to_LState_t m Og U T F) q ob).
      { intros q ob Hne Hx. destruct ob as [t1 | t1 | t1 | t1 |];
          [.. | exact Hx];
          (destruct Hx as [q0 [sg [Hl Hin]]];
           destruct (decide (q0 = t)) as [-> | Hne0];
           [ exfalso; apply Hne; exact (HWF' q t sg _ Hl Hin)
           | exists q0, sg; split; [| exact Hin];
             rewrite (lookup_insert_ne Og (z, t) (q, q0)) in Hl;
             [exact Hl | intros Hc; injection Hc as _ Hc;
              exact (Hne0 (eq_sym Hc))]]). }
      (* and the reader's own entry gains no detaching observation, because a
         reader has none anywhere: that is RITR, at the state the read has
         already been shown to leave well formed *)
      assert (Hdet : forall q t0 (ob : obs),
                (ob = Ounlk t0 \/ ob = Ofree t0 \/ ob = Ofresh t0) ->
                obsv (to_LState_t m Og' U T F) q ob ->
                obsv (to_LState_t m Og U T F) q ob).
      { intros q t0 ob Hsh Hx.
        destruct (decide (t0 = t)) as [-> | Hne].
        - exfalso.
          destruct Hwf' as (_&_&_&_&_&_&_&_&_&_&_&_&HRITR&_).
          destruct (HRITR q t Hrd) as (Hu & Hf0 & Hs0).
          destruct Hsh as [-> | [-> | ->]];
            [exact (Hu Hx) | exact (Hf0 Hx) | exact (Hs0 Hx)].
        - apply (Hback q ob); [| exact Hx].
          destruct Hsh as [-> | [-> | ->]]; simpl;
            intros Hc; injection Hc as Hc; exact (Hne Hc). }
      assert (Hunl : forall q t0, obsv (to_LState_t m Og' U T F) q (Ounlk t0) ->
                obsv (to_LState_t m Og U T F) q (Ounlk t0))
        by (intros q t0; apply (Hdet q t0 (Ounlk t0)); by left).
      assert (Hfre : forall q t0, obsv (to_LState_t m Og' U T F) q (Ofree t0) ->
                obsv (to_LState_t m Og U T F) q (Ofree t0))
        by (intros q t0; apply (Hdet q t0 (Ofree t0)); right; by left).
      assert (Hfrs : forall q t0, obsv (to_LState_t m Og' U T F) q (Ofresh t0) ->
                obsv (to_LState_t m Og U T F) q (Ofresh t0))
        by (intros q t0; apply (Hdet q t0 (Ofresh t0)); right; by right).
      (* the entry only grows, so every old observation survives *)
      assert (Hgrow : forall q ob, obsv (to_LState_t m Og U T F) q ob ->
                obsv (to_LState_t m Og' U T F) q ob).
      { intros q ob Hx. destruct ob as [t1 | t1 | t1 | t1 |];
          [.. | exact Hx];
          (destruct Hx as [q0 [sg [Hl Hin]]];
           destruct (decide ((q, q0) = (z, t))) as [Heq | Hne];
           [ assert (Hqz : q = z) by exact (f_equal fst Heq);
             assert (Hq0 : q0 = t) by exact (f_equal snd Heq);
             subst q0; subst q;
             assert (Hin' : z ∈ dom Ob)
               by exact (Hdom t e (dom Ob) z sg Hcell Hl);
             apply elem_of_dom in Hin' as [sg' Hsg'];
             pose proof (Hag z sg' Hsg') as Hl';
             rewrite Hl in Hl'; injection Hl' as <-;
             exists t, (sz ∪ {[Oiter t]});
             split; [by rewrite (lookup_insert_eq Og (z, t)) |];
             apply elem_of_union_l; rewrite <- (Hold sg Hsg'); exact Hin
           | exists q0, sg; split; [| exact Hin];
             by rewrite (lookup_insert_ne Og (z, t) (q, q0)) ]). }
      (* and the bind's two facts *)
      assert (Hitr : obsv (to_LState_t m Og' U T F) z (Oiter t)).
      { exists t, (sz ∪ {[Oiter t]}). split;
          [by rewrite (lookup_insert_eq Og (z, t)) |].
        apply elem_of_union_r. by apply elem_of_singleton. }
      assert (Hnf' : forall t0, ~ obsv (to_LState_t m Og' U T F) z (Ofresh t0))
        by (intros t0 Hbad; exact (Hnf t0 (Hfrs z t0 Hbad))).
      (* the machine's stack moves with the ghost one *)
      iMod (phys_bind _ _ _ _ _ _ _ y t z o0 with "Hp Hsvy") as "[Hp Hsvy]".
      assert (Hwf'' : WellFormed FType
                (to_LState_t (bind_ms m y t z) Og' U' T F)).
      { apply (reader_bind_preserves_WellFormed FType m Og' U U' T F t y z).
        - exact Hitr.
        - exact Hnf'.
        - unfold U'. intros w q Hne. split;
            [by intros [Hc _] | intros Hc; by split].
        - exact Hwf'. }
      assert (HmkE : mkE gg Rg' St = mkE gg Rg St)
        by exact (mkE_dom gg Rg St t e (dom Ob) (dom Ob ∪ {[z]}) Hcell).
      (* the registration still names the reader, and only its domain grew *)
      assert (Hreg' : forall t' e0 D0,
                Rg' !! t' = Some (Some (e0, D0)) ->
                (t' = t /\ e0 = e /\ D0 = dom Ob ∪ {[z]})
                \/ (t' <> t /\ Rg !! t' = Some (Some (e0, D0)))).
      { intros t' e0 D0 Hl. destruct (decide (t' = t)) as [-> | Hne].
        - rewrite (lookup_insert_eq Rg t) in Hl. injection Hl as <- <-.
          by left.
        - rewrite (lookup_insert_ne Rg t t') in Hl;
            [| exact (fun Hc => Hne (eq_sym Hc))].
          by right. }
      iMod ("Hclose" with "[Hp Ho Hf Hreg Hwm Hfr]") as "_".
      { iNext.
        iExists (bind_ms m y t z), Og', U', T, F, St, Rg', gg, ww, Fr.
        iFrame. iPureIntro. split_and!.
        - exact HWF'.
        - intros q Tr Hfl. destruct (HFLD q Tr Hfl) as [t0 Hd].
          exists t0. destruct Hd as [Hd | Hd]; [left | right];
            exact (Hgrow q _ Hd).
        - intros q t0 Hq. exact (HWFW q t0 (Hfrs q t0 Hq)).
        - exact HRefs.
        - intros q t0 Hq. exact (HFrc q t0 (Hfrs q t0 Hq)).
        - exact Hwf''.
        - intros q t0 Hq. destruct Hq as [Hq | Hq];
            [ exact (HWUW q t0 (or_introl (Hunl q t0 Hq)))
            | exact (HWUW q t0 (or_intror (Hfre q t0 Hq))) ].
        - by rewrite HmkE.
        - by rewrite HmkE.
        - intros t'. simpl. rewrite HRR. split.
          + intros [e0 [D0 Hl]]. destruct (decide (t' = t)) as [-> | Hne].
            * exists e, (dom Ob ∪ {[z]}). by rewrite (lookup_insert_eq Rg t).
            * exists e0, D0. rewrite (lookup_insert_ne Rg t t');
                [exact Hl | exact (fun Hc => Hne (eq_sym Hc))].
          + intros [e0 [D0 Hl]].
            destruct (Hreg' t' e0 D0 Hl) as [(-> & _ & _) | [_ Hl']];
              [by exists e, (dom Ob) | by exists e0, D0].
        - intros t'. rewrite HmkE. exact (HBnd t').
        - intros t' Hlk. destruct (decide (t' = t)) as [-> | Hne].
          + exfalso. rewrite (HLk t Hlk) in Hcell. discriminate.
          + rewrite (lookup_insert_ne Rg t t');
              [exact (HLk t' Hlk) | exact (fun Hc => Hne (eq_sym Hc))].
        - exact (proj1 HWm).
        - intros t' e0 D0 Hl.
          destruct (Hreg' t' e0 D0 Hl) as [(-> & -> & _) | [_ Hl']];
            [exact (proj2 HWm t e (dom Ob) Hcell)
            | exact (proj2 HWm t' e0 D0 Hl')].
        - intros t' e0 D0 q sg Hl Hq.
          destruct (Hreg' t' e0 D0 Hl) as [(-> & -> & ->) | [Hne Hl']].
          + destruct (decide (q = z)) as [-> | Hqz];
              [by apply elem_of_union_r, elem_of_singleton |].
            rewrite (lookup_insert_ne Og (z, t) (q, t)) in Hq;
              [| intros Hc; injection Hc as Hc; exact (Hqz (eq_sym Hc))].
            apply elem_of_union_l. exact (Hdom t e (dom Ob) q sg Hcell Hq).
          + rewrite (lookup_insert_ne Og (z, t) (q, t')) in Hq;
              [| intros Hc; injection Hc as _ Hc; exact (Hne (eq_sym Hc))].
            exact (Hdom t' e0 D0 q sg Hl' Hq).
        - exact HSS.
        - apply (FRW_obs m (bind_ms m y t z) Og Og' U U' T T F F);
            [reflexivity | exact Hfrs | exact HFRW].
        - apply ne_ins; [| exact HNE].
          intros Hc. assert (Hin : Oiter t ∈ (∅ : gset obs)).
          { rewrite <- Hc. by apply elem_of_union_r, elem_of_singleton. }
          by apply not_elem_of_empty in Hin. }
      iModIntro. iFrame. iLeft. iExists z, sz. iFrame.
      iPureIntro. by split.
  Qed.

  (** ...and with the reader's environment on both sides, which is what "the
      rule is sound" means for T-ReadH.  The iterator at [x] is no longer a
      hypothesis about the observation map: it comes out of the environment,
      which is where a type rule's premise should come from. *)
  Lemma read_typed_closed N γm γh γl γs γo γf γr γe γq E (t : TID) (e : nat)
        (Ob : gmap Loc (gset obs)) Sm (G : list Var)
        (U : Var -> TID -> Prop) (x y : Var) (f : FName) (o o0 : Loc) :
    ↑N ⊆ E ->
    In x G -> Sm !! (x, t) = Some o -> REnvOK t U Sm Ob G ->
    rcu_invT FType (phys γm γh γl γs root fs) N γo γf γr γe γq -∗
    reg_cell γe t (Some (e, dom Ob)) -∗ obs_own γo t Ob -∗
    sv γs x t o -∗ sv γs y t o0
    ={E}=∗ sv γs x t o
      ∗ ((∃ z sz, ⌜REnvOK t (fun w t' => U w t' /\ (w, t') <> (y, t))
                       (<[(y, t) := z]> Sm) (<[z := sz ∪ {[Oiter t]}]> Ob)
                       (y :: List.filter (fun w => negb (Nat.eqb w y)) G)⌝
                  ∗ reg_cell γe t (Some (e, dom Ob ∪ {[z]}))
                  ∗ obs_own γo t (<[z := sz ∪ {[Oiter t]}]> Ob)
                  ∗ sv γs y t z)
         ∨ (reg_cell γe t (Some (e, dom Ob)) ∗ obs_own γo t Ob
            ∗ sv γs y t o0)).
  Proof.
    iIntros (HN Hin Hstk Hok) "#Hinv Hcell Hob Hsvx Hsvy".
    destruct (Hok x Hin) as (ox & so & Hstk' & Hoo & Hito & _).
    rewrite Hstk in Hstk'. injection Hstk' as <-.
    iMod (read_atomic N γm γh γl γs γo γf γr γe γq E t e Ob x y f o o0 so
            HN Hoo Hito with "Hinv Hcell Hob Hsvx Hsvy")
      as "[Hsvx [Hyes | Hno]]".
    - iDestruct "Hyes" as (z sz) "(%Hdz & %Hold & Hcell & Hob & Hsvy)".
      iModIntro. iFrame. iLeft. iExists z, sz. iFrame.
      iPureIntro. exact (REnvOK_read t U Sm Ob G y z sz Hold Hok).
    - iModIntro. iFrame.
  Qed.

End atomic_read.

Print Assumptions read_atomic.
Print Assumptions read_typed_closed.

(** * The enumeration premises

    Four rules are stated as a step plus an environment with an enumeration
    made explicit rather than as a Hoare triple, and the reason recorded in
    [Triples.v] is that they are bulk updates: \textsc{SyncStart} stamps every
    detached node, \textsc{WriteBegin} observes every reachable node,
    \textsc{SyncStop} and \textsc{WriteEnd} hand back every entry of the
    writer's column.  "Every" was said there to be a premise no resource
    carries.

    That is two claims, and only one of them is true.  Whether the thread
    *owns* the pieces is a resource question and stays one; that is what
    ownership is, and a bulk update that did not have to own what it updates
    would be unsound.  But whether the set is *enumerable* is a mathematical
    question, and the answer is yes, for the same reason in all four cases:
    every one of these sets is a set of keys of a finite map the invariant
    already carries.  The heap is a [gmap], the observation map is a [gmap],
    and a set carved out of a [gmap] by a decidable condition is finite.

    So the premises are not assumptions about the world.  This section
    constructs the three lists and proves they cover, which leaves the four
    rules asking for exactly what a bulk update should ask for and nothing
    else. *)

(** ** Reachable nodes are in the heap

    The first step, and it is the only one with any content: a node reached by
    a path is either the root or the target of an edge.  Induction on the path
    from the far end is the wrong way round --- [hstar] consumes the front ---
    so the induction is on the path with the *source* generalised. *)
Lemma hstar_target (h : Heap) (r : Loc) (p : list FName) (o : Loc) :
  hstar h r p = Some o ->
  (p = [] /\ o = r) \/ (exists q f, h q f = Some (VLoc o)).
Proof.
  revert r. induction p as [| f p IH]; intros r Hh.
  - simpl in Hh. injection Hh as <-. by left.
  - simpl in Hh. destruct (h r f) as [[o' |] |] eqn:Hf;
      [| discriminate | discriminate].
    destruct (IH o' Hh) as [[-> ->] | Hex]; [| by right].
    right. by exists r, f.
Qed.

Lemma reachable_is_in_the_heap (s : LState) (p : list FName) (o : Loc) :
  Reaches s p o ->
  o = rt (ms s) \/ (exists q f, hp (ms s) q f = Some (VLoc o)).
Proof.
  intros Hr. destruct (hstar_target (hp (ms s)) (rt (ms s)) p o Hr)
    as [[_ ->] | Hex]; [by left | by right].
Qed.

(** ...and therefore in a finite set, once the heap is one.  [heap_locs] is the
    root together with every location the heap points at, read off the finite
    map the invariant carries. *)
Definition heap_locs (H : gmap (Loc * FName) Val) (r : Loc) : gset Loc :=
  {[ r ]} ∪ list_to_set ((fun p => match p.2 with
                                   | VLoc q => q
                                   | VNull  => r
                                   end) <$> map_to_list H).

Lemma heap_locs_covers H r q f o :
  H !! (q, f) = Some (VLoc o) -> o ∈ heap_locs H r.
Proof.
  intros Hl. unfold heap_locs. apply elem_of_union_r.
  apply elem_of_list_to_set, list_elem_of_fmap_2'
    with (x := ((q, f), VLoc o)); [| reflexivity].
  by apply elem_of_map_to_list.
Qed.

Theorem reachable_is_finite (s : LState) H p o :
  Represents (hp (ms s)) H -> Reaches s p o -> o ∈ heap_locs H (rt (ms s)).
Proof.
  intros HR Hr. destruct (reachable_is_in_the_heap s p o Hr) as [-> | [q [f Hf]]].
  - unfold heap_locs. apply elem_of_union_l, elem_of_singleton. reflexivity.
  - rewrite HR in Hf. exact (heap_locs_covers H (rt (ms s)) q f o Hf).
Qed.

(** ** Detached nodes are entries of the observation map

    The second, and it is immediate once observations are tagged: a node
    observed unlinked or freeable is observed by *some* thread, and under
    [ObsWF] that thread's entry is where the observation lives. *)
Definition obs_locs (Og : ObsMap) : gset Loc :=
  list_to_set ((fun p => p.1.1) <$> map_to_list Og).

Lemma obs_locs_covers Og q t sg :
  Og !! (q, t) = Some sg -> q ∈ obs_locs Og.
Proof.
  intros Hl. unfold obs_locs.
  apply elem_of_list_to_set, list_elem_of_fmap_2' with (x := ((q, t), sg));
    [| reflexivity].
  by apply elem_of_map_to_list.
Qed.

Theorem detached_is_finite m Og U T F q :
  Detached (to_LState_t m Og U T F) q -> q ∈ obs_locs Og.
Proof.
  intros [t0 Hd].
  assert (Hx : exists t1 sg, Og !! (q, t1) = Some sg).
  { destruct Hd as [Hd | [Hd | Hd]]; destruct Hd as [t1 [sg [Hl _]]];
      by exists t1, sg. }
  destruct Hx as [t1 [sg Hl]]. exact (obs_locs_covers Og q t1 sg Hl).
Qed.

(** ** The writer's column

    The third.  A thread's own observations are one column of the map, and the
    column of a finite map is a finite map --- so "every entry of the writer's
    column" is a map that can be written down, and [column_lookup] says it is
    the right one. *)
Definition column (Og : ObsMap) (t : TID) : gmap Loc (gset obs) :=
  list_to_map ((fun p => (p.1.1, p.2))
                 <$> filter (fun p => p.1.2 = t) (map_to_list Og)).

Lemma column_nodup Og t :
  NoDup (((fun p : (Loc * TID) * gset obs => (p.1.1, p.2))
            <$> filter (fun p => p.1.2 = t) (map_to_list Og)).*1).
Proof.
  rewrite <- list_fmap_compose.
  apply NoDup_fmap_2_strong; [| apply NoDup_filter, NoDup_map_to_list].
  intros [[q1 t1] s1] [[q2 t2] s2] Hin1 Hin2 Hq.
  apply list_elem_of_filter in Hin1 as [Ht1 Hin1].
  apply list_elem_of_filter in Hin2 as [Ht2 Hin2].
  simpl in Ht1, Ht2, Hq. subst t1. subst t2. subst q2.
  apply elem_of_map_to_list in Hin1. apply elem_of_map_to_list in Hin2.
  rewrite Hin1 in Hin2. by injection Hin2 as ->.
Qed.

Lemma column_lookup Og t o : column Og t !! o = Og !! (o, t).
Proof.
  unfold column.
  destruct (Og !! (o, t)) as [sg |] eqn:Hl.
  - apply elem_of_list_to_map_1; [apply column_nodup |].
    apply list_elem_of_fmap_2' with (x := ((o, t), sg)); [| reflexivity].
    apply list_elem_of_filter. split; [reflexivity |].
    by apply elem_of_map_to_list.
  - apply not_elem_of_list_to_map_1. rewrite <- list_fmap_compose.
    intros Hin. apply list_elem_of_fmap_1 in Hin as [[[q1 t1] s1] [Hq Hin]].
    apply list_elem_of_filter in Hin as [Ht1 Hin]. simpl in Ht1, Hq. subst t1.
    apply elem_of_map_to_list in Hin. subst q1. by rewrite Hin in Hl.
Qed.

Print Assumptions reachable_is_finite.
Print Assumptions detached_is_finite.
Print Assumptions column_lookup.

(** ** The three lists

    With the finiteness in hand the lists are constructions rather than
    assumptions.  Each one is read off a map the invariant carries, and each
    comes with the two halves the rule asks for: that it covers the set, and
    that everything in it belongs. *)

Definition detaching (ob : obs) : bool :=
  match ob with Ounlk _ => true | Ofree _ => true | _ => false end.

Definition detaching_set (sg : gset obs) : bool :=
  List.existsb detaching (elements sg).

Definition detached_locs (Og : ObsMap) : gset Loc :=
  list_to_set ((fun p : (Loc * TID) * gset obs => p.1.1)
    <$> List.filter (fun p => detaching_set p.2) (map_to_list Og)).

Definition detached_list (Og : ObsMap) (g : nat) : list (Loc * nat) :=
  (fun o => (o, g)) <$> elements (detached_locs Og).

Lemma detaching_set_true sg ob :
  ob ∈ sg -> detaching ob = true -> detaching_set sg = true.
Proof.
  intros Hin Hd. unfold detaching_set. apply List.existsb_exists.
  exists ob. split; [| exact Hd].
  apply list_elem_of_In, elem_of_elements, Hin.
Qed.

Lemma detaching_set_elim sg :
  detaching_set sg = true -> exists ob, ob ∈ sg /\ detaching ob = true.
Proof.
  intros H. apply List.existsb_exists in H as [ob [Hin Hd]].
  exists ob. split; [| exact Hd].
  by apply elem_of_elements, list_elem_of_In.
Qed.

Lemma detached_locs_intro Og q t sg :
  Og !! (q, t) = Some sg -> detaching_set sg = true -> q ∈ detached_locs Og.
Proof.
  intros Hl Hd. unfold detached_locs. apply elem_of_list_to_set.
  apply list_elem_of_fmap_2' with (x := ((q, t), sg)); [| reflexivity].
  apply list_elem_of_In, List.filter_In. split; [| exact Hd].
  by apply list_elem_of_In, elem_of_map_to_list.
Qed.

Lemma detached_locs_elim Og q :
  q ∈ detached_locs Og ->
  exists t sg, Og !! (q, t) = Some sg /\ detaching_set sg = true.
Proof.
  unfold detached_locs. intros Hin.
  apply elem_of_list_to_set, list_elem_of_fmap_1 in Hin
    as [[[q1 t1] s1] [Hq Hin]].
  apply list_elem_of_In, List.filter_In in Hin as [Hin Hd].
  simpl in Hq. subst q1. exists t1, s1. split; [| exact Hd].
  by apply elem_of_map_to_list, list_elem_of_In.
Qed.

(** The four premises of \textsc{SyncStart}'s enumeration, proved. *)
Theorem detached_list_NoDup Og g : NoDup (detached_list Og g).*1.
Proof.
  unfold detached_list. rewrite <- list_fmap_compose.
  apply NoDup_fmap_2_strong; [| apply NoDup_elements].
  intros q1 q2 _ _ H. exact H.
Qed.

Theorem detached_list_epoch Og g p : p ∈ detached_list Og g -> p.2 = g.
Proof.
  unfold detached_list. intros Hin.
  apply list_elem_of_fmap_1 in Hin as [o [-> _]]. reflexivity.
Qed.

Theorem detached_list_covers m Og U T F g o t :
  ObsWF Og ->
  obsv (to_LState_t m Og U T F) o (Ounlk t)
  \/ obsv (to_LState_t m Og U T F) o (Ofree t) ->
  (o, g) ∈ detached_list Og g.
Proof.
  intros HWF Hd. unfold detached_list.
  apply list_elem_of_fmap_2' with (x := o); [| reflexivity].
  apply elem_of_elements.
  assert (Hx : exists t1 sg ob, Og !! (o, t1) = Some sg /\ ob ∈ sg
                                /\ detaching ob = true).
  { destruct Hd as [Hd | Hd]; destruct Hd as [t1 [sg [Hl Hin]]];
      [ by exists t1, sg, (Ounlk t) | by exists t1, sg, (Ofree t) ]. }
  destruct Hx as [t1 [sg [ob (Hl & Hin & Hdt)]]].
  exact (detached_locs_intro Og o t1 sg Hl
           (detaching_set_true sg ob Hin Hdt)).
Qed.

Theorem detached_list_sound m Og U T F g p :
  p ∈ detached_list Og g ->
  exists t, obsv (to_LState_t m Og U T F) p.1 (Ounlk t)
         \/ obsv (to_LState_t m Og U T F) p.1 (Ofree t).
Proof.
  unfold detached_list. intros Hin.
  apply list_elem_of_fmap_1 in Hin as [o [-> Hin]]. simpl.
  apply elem_of_elements, detached_locs_elim in Hin as [t1 [sg [Hl Hd]]].
  apply detaching_set_elim in Hd as [ob [Hob Hdt]].
  destruct ob as [t2 | t2 | t2 | t2 |]; simpl in Hdt; try discriminate.
  - exists t2. left. by exists t1, sg.
  - exists t2. right. by exists t1, sg.
Qed.

Print Assumptions detached_list_NoDup.
Print Assumptions detached_list_covers.
Print Assumptions detached_list_sound.

(** ** The rules, with the enumerations supplied

    What is left of each premise once the list is constructed.  The two column
    rules become premise-free in the enumeration: [column] *is* the writer's
    column, so the two clauses relating the thread's map to the shared one hold
    by [column_lookup] and nothing is asked of the caller but the ownership,
    which is what ownership is for. *)

Section enumerated.
  Context `{!rcuG Σ, !heapG Σ, !stackG Σ, !lockG Σ, !invGS_gen hlc Σ}.
  Context (FType : FName -> FieldKind).
  Context (phys : MState -> iProp Σ).

  Corollary write_end_enumerated γo γf m Og U T F St root fs Qc lw Sm C Fl G :
    WellFormed FType (to_LState_t m Og U T F) ->
    ObsWF Og ->
    lk m = Some lw ->
    (forall o, ~ Detached (to_LState_t m Og U T F) o) ->
    EnvOK root lw U Qc FType fs Sm (column Og lw) C Fl G ->
    obs_own γo lw (column Og lw) -∗
    phys m -∗ tobs_auth γo Og -∗ fl_auth γf St -∗
    (phys m ==∗ phys (write_end_ms m)) -∗
    |==> ∃ Og', phys (write_end_ms m)
         ∗ tobs_auth γo Og'
         ∗ fl_auth γf St
         ∗ ⌜ObsWF Og'⌝
         ∗ ⌜WellFormed FType
              (to_LState_t (write_end_ms m) Og'
                 (fun z t' => U z t' \/ t' = lw) T F)⌝
         ∗ ⌜EnvOK root lw (fun z t' => U z t' \/ t' = lw) Qc FType fs Sm ∅ C Fl
              []⌝.
  Proof.
    intros Hwf Hobs Hlk Hclean Hok.
    apply (write_end_typed FType phys γo γf m Og U T F St root fs Qc lw Sm
             (column Og lw) C Fl G Hwf Hobs Hlk Hclean);
      [| exact Hok].
    intros o sg Ho. by rewrite (column_lookup Og lw o).
  Qed.

  Corollary sync_stop_enumerated γo γf m Og U T F St root fs Qc lw Sm C Fl G :
    WellFormed FType (to_LState_t m Og U T F) ->
    ObsWF Og ->
    lk m = Some lw ->
    (forall t, ~ bnd m t) ->
    (forall x o, In (x, TUnlinked) G -> Sm !! (x, lw) = Some o ->
       exists e, Fl !! o = Some e /\ Qc e) ->
    EnvOK root lw U Qc FType fs Sm (column Og lw) C Fl G ->
    obs_own γo lw (column Og lw) -∗
    phys m -∗ tobs_auth γo Og -∗ fl_auth γf St -∗
    (phys m ==∗ phys (sync_stop_ms m)) -∗
    |==> ∃ Og', phys (sync_stop_ms m)
         ∗ tobs_auth γo Og'
         ∗ fl_auth γf St
         ∗ obs_own γo lw
             ((fun sg => set_map sync_obs sg : gset obs) <$> column Og lw)
         ∗ ⌜ObsWF Og'⌝
         ∗ ⌜WellFormed FType (to_LState_t (sync_stop_ms m) Og' U T F)⌝
         ∗ ⌜EnvOK root lw U Qc FType fs Sm
              ((fun sg => set_map sync_obs sg : gset obs) <$> column Og lw)
              C Fl (syncenv G)⌝.
  Proof.
    intros Hwf Hobs Hlk Hquiet Hcert Hok.
    apply (sync_stop_typed FType phys γo γf m Og U T F St root fs Qc lw Sm
             (column Og lw) C Fl G Hwf Hobs Hlk Hquiet);
      [| | exact Hcert | exact Hok].
    - intros o sg Ho. by rewrite (column_lookup Og lw o).
    - intros o sg Ho. by rewrite (column_lookup Og lw o) in Ho.
  Qed.

  (** \textsc{SyncStart}'s four enumeration premises are the four theorems
      above, so the rule at [detached_list] asks only for the thread's own
      free-list fragments and the two conditions relating them to the
      invariant's --- which are about what the thread holds, not about how much
      of the world it can see. *)
  Corollary sync_start_enumerated γo γf g Rg m Og U T St root fs Qc
        lw Sm Ob C Fl G :
    WellFormed FType (to_LState_t m Og U T (e_F (mkE g Rg St))) ->
    FLD (to_LState_t m Og U T (e_F (mkE g Rg St))) ->
    EWF (mkE g Rg St) ->
    RepresentsR (rds m) Rg ->
    ObsWF Og ->
    (forall o e, Fl !! o = Some e -> St !! o = Some e) ->
    (forall o e, Fl !! o = Some e -> o ∉ (detached_list Og g).*1) ->
    EnvOK root lw U Qc FType fs Sm Ob C Fl G ->
    ([∗ list] p ∈ detached_list Og g,
       (∃ s, fl_ctl γf p.1 s) ∨ ⌜St !! p.1 = None⌝) -∗
    phys m -∗ tobs_auth γo Og -∗ fl_auth γf St -∗
    (phys m ==∗ phys (sync_start_ms m)) -∗
    |==> phys (sync_start_ms m)
         ∗ tobs_auth γo Og
         ∗ fl_auth γf (ins_list St (detached_list Og g))
         ∗ ([∗ list] p ∈ detached_list Og g, fl_ctl γf p.1 p.2)
         ∗ ⌜WellFormed FType
              (to_LState_t (sync_start_ms m) Og U T
                 (e_F (mkE (S g) Rg (ins_list St (detached_list Og g)))))⌝
         ∗ ⌜EnvOK root lw U Qc FType fs Sm Ob C
              (ins_list St (detached_list Og g)) G⌝.
  Proof.
    intros Hwf HFLD HEWF HRR Hobs Hsub Hfresh Hok.
    apply (sync_start_typed FType phys γo γf g Rg m Og U T St root fs Qc
             lw Sm Ob C Fl G (detached_list Og g) Hwf HFLD HEWF HRR).
    - apply detached_list_NoDup.
    - apply detached_list_epoch.
    - intros o t Hd.
      exact (detached_list_covers m Og U T (e_F (mkE g Rg St)) g o t Hobs Hd).
    - intros p Hp.
      exact (detached_list_sound m Og U T (e_F (mkE g Rg St)) g p Hp).
    - exact Hsub.
    - exact Hfresh.
    - exact Hok.
  Qed.

End enumerated.

Print Assumptions write_end_enumerated.
Print Assumptions sync_stop_enumerated.
Print Assumptions sync_start_enumerated.

(** ** Reachability, decided

    \textsc{WriteBegin} is the one whose enumeration is not read off a map
    directly: its set is the *reachable* nodes, and reachability is a closure,
    not a lookup.  So it has to be computed, and the computation has to be
    shown to terminate at the right answer.

    The construction is the obvious one --- iterate "add the successors" from
    the root --- and the only real step is that iterating it [n] times is
    enough, where [n] is the size of the set of locations the heap mentions at
    all.  That is a pigeonhole: the iterates increase, they all live in that
    finite set, so one of the first [n+1] is a fixed point, and after a fixed
    point nothing changes.  [chain_stabilises] is that argument on its own,
    stated about any increasing chain in a finite set, because it has nothing
    to do with heaps. *)

Definition succ_of (o : Loc) (p : (Loc * FName) * Val) : option Loc :=
  if decide (p.1.1 = o)
  then match p.2 with VLoc q => Some q | VNull => None end
  else None.

Definition succs (H : gmap (Loc * FName) Val) (o : Loc) : gset Loc :=
  list_to_set (omap (succ_of o) (map_to_list H)).

Lemma succs_intro H o f q : H !! (o, f) = Some (VLoc q) -> q ∈ succs H o.
Proof.
  intros Hl. unfold succs. apply elem_of_list_to_set, list_elem_of_omap.
  exists ((o, f), VLoc q). split; [by apply elem_of_map_to_list |].
  unfold succ_of. simpl. by rewrite decide_True.
Qed.

Lemma succs_elim H o q : q ∈ succs H o -> exists f, H !! (o, f) = Some (VLoc q).
Proof.
  unfold succs. intros Hin.
  apply elem_of_list_to_set, list_elem_of_omap in Hin as [[[q1 f1] v] [Hin Hs]].
  unfold succ_of in Hs. simpl in Hs.
  destruct (decide (q1 = o)) as [-> | Hne]; [| discriminate].
  destruct v as [q2 |]; [| discriminate].
  injection Hs as <-. exists f1. by apply elem_of_map_to_list.
Qed.

Definition step_set (H : gmap (Loc * FName) Val) (S : gset Loc) : gset Loc :=
  S ∪ union_list ((fun o => succs H o) <$> elements S).

Lemma step_set_grows H S : S ⊆ step_set H S.
Proof. unfold step_set. set_solver. Qed.

Lemma step_set_succ H S o q : o ∈ S -> q ∈ succs H o -> q ∈ step_set H S.
Proof.
  intros Ho Hq. unfold step_set. apply elem_of_union_r.
  apply elem_of_union_list. exists (succs H o). split; [| exact Hq].
  apply list_elem_of_fmap_2' with (x := o); [| reflexivity].
  by apply elem_of_elements.
Qed.

Lemma step_set_elim H S q :
  q ∈ step_set H S -> q ∈ S \/ (exists o, o ∈ S /\ q ∈ succs H o).
Proof.
  unfold step_set. intros Hq. apply elem_of_union in Hq as [Hq | Hq];
    [by left | right].
  apply elem_of_union_list in Hq as [X [Hin Hq]].
  apply list_elem_of_fmap_1 in Hin as [o [-> Ho]].
  exists o. split; [by apply elem_of_elements | exact Hq].
Qed.

Lemma step_set_mono H S S' : S ⊆ S' -> step_set H S ⊆ step_set H S'.
Proof.
  intros Hsub q Hq. destruct (step_set_elim H S q Hq) as [Hq' | [o [Ho Hs]]].
  - apply step_set_grows. by apply Hsub.
  - exact (step_set_succ H S' o q (Hsub o Ho) Hs).
Qed.

Fixpoint reach_upto (H : gmap (Loc * FName) Val) (r : Loc) (k : nat) : gset Loc :=
  match k with
  | 0    => {[ r ]}
  | S k' => step_set H (reach_upto H r k')
  end.

Lemma reach_step H r k : reach_upto H r k ⊆ reach_upto H r (S k).
Proof. simpl. apply step_set_grows. Qed.

Lemma reach_mono H r k k' : k <= k' -> reach_upto H r k ⊆ reach_upto H r k'.
Proof.
  induction 1 as [| k'' Hle IH]; [reflexivity |].
  etrans; [exact IH | apply reach_step].
Qed.

(** Every iterate is sound: a member is reached by some path. *)
Lemma reach_upto_sound (h : Heap) H r k o :
  Represents h H -> o ∈ reach_upto H r k -> exists p, hstar h r p = Some o.
Proof.
  intros HR. revert o. induction k as [| k IH]; intros o Ho.
  - simpl in Ho. apply elem_of_singleton in Ho as ->. by exists [].
  - simpl in Ho. destruct (step_set_elim H _ o Ho) as [Ho' | [q [Hq Hs]]];
      [exact (IH o Ho') |].
    destruct (IH q Hq) as [p Hp].
    apply succs_elim in Hs as [f Hf]. rewrite <- HR in Hf.
    exists (p ++ [f]). clear -Hp Hf.
    revert r Hp. induction p as [| g p IHp]; intros r Hp; simpl in Hp |- *.
    + injection Hp as <-. by rewrite Hf.
    + destruct (h r g) as [[r' |] |]; [| discriminate | discriminate].
      exact (IHp r' Hp).
Qed.

(** And the shift: what is reachable from a successor in [k] steps is
    reachable from the node itself in [k+1]. *)
Lemma reach_shift H r o' k :
  o' ∈ succs H r -> reach_upto H o' k ⊆ reach_upto H r (S k).
Proof.
  intros Ho'. induction k as [| k IH].
  - intros q Hq. simpl in Hq. apply elem_of_singleton in Hq as ->.
    apply (step_set_succ H {[r]} r); [by apply elem_of_singleton | exact Ho'].
  - simpl. etrans; [apply (step_set_mono H _ _ IH) | reflexivity].
Qed.

Lemma reach_upto_complete (h : Heap) H r p o :
  Represents h H -> hstar h r p = Some o -> o ∈ reach_upto H r (length p).
Proof.
  intros HR. revert r. induction p as [| f p IH]; intros r Hp.
  - simpl in Hp. injection Hp as <-. simpl. by apply elem_of_singleton.
  - simpl in Hp. destruct (h r f) as [[r' |] |] eqn:Hf;
      [| discriminate | discriminate].
    assert (Hs : r' ∈ succs H r)
      by (apply (succs_intro H r f r'); by rewrite <- HR).
    exact (reach_shift H r r' (length p) Hs o (IH r' Hp)).
Qed.

(** The pigeonhole, on its own.  Nothing here is about heaps: an increasing
    chain of subsets of a finite set has a fixed point among its first
    [size Univ + 1] members, because otherwise its sizes would outrun the
    set's.  The search for the fixed point is bounded, so it is decidable, and
    the argument stays constructive. *)
Lemma bounded_search (P : nat -> Prop) `{forall j, Decision (P j)} (n : nat) :
  (exists j, j <= n /\ P j) \/ (forall j, j <= n -> ~ P j).
Proof.
  induction n as [| n IH].
  - destruct (decide (P 0)) as [Hy | Hn];
      [left; by exists 0 |].
    right. intros j Hj. assert (j = 0) by lia. by subst j.
  - destruct IH as [[j [Hj HP]] | Hn]; [left; exists j; split; [lia | exact HP] |].
    destruct (decide (P (S n))) as [Hy | Hn'];
      [left; by exists (S n) |].
    right. intros j Hj. destruct (decide (j = S n)) as [-> | Hne];
      [exact Hn' | apply Hn; lia].
Qed.

Lemma chain_stabilises (f : nat -> gset Loc) (Univ : gset Loc) :
  (forall k, f k ⊆ f (S k)) -> (forall k, f k ⊆ Univ) ->
  exists j, j <= size Univ /\ f (S j) = f j.
Proof.
  intros Hgrow Hin.
  destruct (bounded_search (fun j => f (S j) = f j) (size Univ))
    as [Hy | Hn]; [exact Hy |].
  exfalso.
  assert (Hstrict : forall j, j <= size Univ -> size (f j) < size (f (S j))).
  { intros j Hj. apply subset_size. split; [apply Hgrow |].
    intros Hc. apply (Hn j Hj).
    apply (anti_symm (⊆)); [exact Hc | apply Hgrow]. }
  assert (Hbig : forall k, k <= S (size Univ) -> k <= size (f k)).
  { induction k as [| k IH]; intros Hk; [apply Nat.le_0_l |].
    assert (Hk' : k <= size Univ) by lia.
    pose proof (Hstrict k Hk') as Hlt.
    pose proof (IH ltac:(lia)) as Hle. lia. }
  pose proof (Hbig (S (size Univ)) (Nat.le_refl _)) as Hle.
  pose proof (subseteq_size (f (S (size Univ))) Univ (Hin _)) as Hle'.
  lia.
Qed.

Print Assumptions reach_upto_sound.
Print Assumptions reach_upto_complete.
Print Assumptions chain_stabilises.

(** The universe the iterates live in: the root, and everything the heap points
    at.  [heap_locs] was already that, for the same reason. *)
Definition heap_universe (H : gmap (Loc * FName) Val) (r : Loc) : gset Loc :=
  {[ r ]} ∪ heap_locs H r.

Lemma reach_upto_in_universe H r k :
  reach_upto H r k ⊆ heap_universe H r.
Proof.
  induction k as [| k IH]; simpl.
  - unfold heap_universe. set_solver.
  - intros q Hq. destruct (step_set_elim H _ q Hq) as [Hq' | [o [Ho Hs]]];
      [exact (IH q Hq') |].
    apply succs_elim in Hs as [f Hf].
    unfold heap_universe. apply elem_of_union_r.
    exact (heap_locs_covers H r o f q Hf).
Qed.

Definition reach_set (H : gmap (Loc * FName) Val) (r : Loc) : gset Loc :=
  reach_upto H r (size (heap_universe H r)).

Lemma reach_saturates H r k : reach_upto H r k ⊆ reach_set H r.
Proof.
  unfold reach_set.
  set (N := size (heap_universe H r)).
  destruct (chain_stabilises (reach_upto H r) (heap_universe H r)
              (reach_step H r) (reach_upto_in_universe H r)) as [j [Hj Hfix]].
  assert (Hconst : forall i, reach_upto H r (j + i) = reach_upto H r j).
  { induction i as [| i IH]; [by rewrite Nat.add_0_r |].
    replace (j + S i) with (S (j + i)) by lia. simpl. rewrite IH.
    exact Hfix. }
  destruct (Nat.le_gt_cases k N) as [Hle | Hgt];
    [exact (reach_mono H r k N Hle) |].
  assert (Hjk : j <= k) by lia.
  replace k with (j + (k - j)) by lia. rewrite Hconst.
  exact (reach_mono H r j N Hj).
Qed.

Theorem reach_set_sound (h : Heap) H r o :
  Represents h H -> o ∈ reach_set H r -> exists p, hstar h r p = Some o.
Proof. intros HR Ho. exact (reach_upto_sound h H r _ o HR Ho). Qed.

Theorem reach_set_complete (h : Heap) H r p o :
  Represents h H -> hstar h r p = Some o -> o ∈ reach_set H r.
Proof.
  intros HR Hp.
  exact (reach_saturates H r (length p) o (reach_upto_complete h H r p o HR Hp)).
Qed.

Print Assumptions reach_set_sound.
Print Assumptions reach_set_complete.

(** ** \textsc{WriteBegin}'s list

    The writer takes an iterator on every reachable node, keeping whatever it
    already had there.  So the entry for a node is its old content --- empty if
    it had none --- together with the new observation, and that is the whole of
    the construction; the six conditions the rule asks of it are then readings
    of [reach_set_sound] and [reach_set_complete] and of the shape of the
    entry. *)
Definition wb_list (Og : ObsMap) (H : gmap (Loc * FName) Val) (r : Loc)
    (lw : TID) : list ((Loc * TID) * gset obs) :=
  (fun o => ((o, lw), default ∅ (Og !! (o, lw)) ∪ {[Oiter lw]}))
    <$> elements (reach_set H r).

Lemma wb_list_elem Og H r lw p :
  p ∈ wb_list Og H r lw ->
  exists o, o ∈ reach_set H r /\ p.1 = (o, lw)
         /\ p.2 = default ∅ (Og !! (o, lw)) ∪ {[Oiter lw]}.
Proof.
  unfold wb_list. intros Hin.
  apply list_elem_of_fmap_1 in Hin as [o [-> Ho]].
  exists o. by rewrite elem_of_elements in Ho.
Qed.

Theorem wb_list_NoDup Og H r lw : NoDup (wb_list Og H r lw).*1.
Proof.
  unfold wb_list. rewrite <- list_fmap_compose.
  apply NoDup_fmap_2_strong; [| apply NoDup_elements].
  intros q1 q2 _ _ Hq. exact (f_equal fst Hq).
Qed.

Theorem wb_list_key Og H r lw p : p ∈ wb_list Og H r lw -> p.1.2 = lw.
Proof.
  intros Hin. destruct (wb_list_elem Og H r lw p Hin) as [o (_ & Hp1 & _)].
  by rewrite Hp1.
Qed.

Theorem wb_list_iter Og H r lw p :
  p ∈ wb_list Og H r lw -> Oiter lw ∈ p.2.
Proof.
  intros Hin. destruct (wb_list_elem Og H r lw p Hin) as [o (_ & _ & Hp2)].
  rewrite Hp2. by apply elem_of_union_r, elem_of_singleton.
Qed.

Theorem wb_list_grow Og H r lw p ob :
  p ∈ wb_list Og H r lw ->
  (exists sg, Og !! p.1 = Some sg /\ ob ∈ sg) -> ob ∈ p.2.
Proof.
  intros Hin [sg [Hl Hob]].
  destruct (wb_list_elem Og H r lw p Hin) as [o (_ & Hp1 & Hp2)].
  rewrite Hp1 in Hl. rewrite Hp2. rewrite Hl. simpl.
  by apply elem_of_union_l.
Qed.

Theorem wb_list_content Og H r lw p ob :
  p ∈ wb_list Og H r lw -> ob ∈ p.2 ->
  ob = Oiter lw \/ (exists sg, Og !! p.1 = Some sg /\ ob ∈ sg).
Proof.
  intros Hin Hob.
  destruct (wb_list_elem Og H r lw p Hin) as [o (_ & Hp1 & Hp2)].
  rewrite Hp2 in Hob. apply elem_of_union in Hob as [Hob | Hob];
    [| left; by apply elem_of_singleton in Hob].
  destruct (Og !! (o, lw)) as [sg |] eqn:Hl; simpl in Hob;
    [| by apply not_elem_of_empty in Hob].
  right. exists sg. rewrite Hp1. by split.
Qed.

Theorem wb_list_reaches (s : LState) Og H lw p :
  Represents (hp (ms s)) H ->
  p ∈ wb_list Og H (rt (ms s)) lw -> exists q, Reaches s q p.1.1.
Proof.
  intros HR Hin.
  destruct (wb_list_elem Og H (rt (ms s)) lw p Hin) as [o (Ho & Hp1 & _)].
  destruct (reach_set_sound (hp (ms s)) H (rt (ms s)) o HR Ho) as [q Hq].
  exists q. unfold Reaches. by rewrite Hp1.
Qed.

Theorem wb_list_covers (s : LState) Og H lw q o :
  Represents (hp (ms s)) H -> Reaches s q o ->
  exists v, ((o, lw), v) ∈ wb_list Og H (rt (ms s)) lw.
Proof.
  intros HR Hr.
  pose proof (reach_set_complete (hp (ms s)) H (rt (ms s)) q o HR Hr) as Ho.
  exists (default ∅ (Og !! (o, lw)) ∪ {[Oiter lw]}).
  unfold wb_list.
  apply list_elem_of_fmap_2' with (x := o); [| reflexivity].
  by apply elem_of_elements.
Qed.

Print Assumptions wb_list_NoDup.
Print Assumptions wb_list_reaches.
Print Assumptions wb_list_covers.
Print Assumptions wb_list_content.

Section enumerated_wb.
  Context `{!rcuG Σ, !heapG Σ, !stackG Σ, !lockG Σ, !invGS_gen hlc Σ}.
  Context (FType : FName -> FieldKind).
  Context (phys : MState -> iProp Σ).

  (** \textsc{WriteBegin} at its own list.  Seven of the fourteen premises were
      the enumeration; what is left is the four the action carries, the root
      binding, and the resources. *)
  Corollary write_begin_enumerated γo γf m Og U T F St root fs Qc lw x Sm C Fl
        H :
    Represents (hp m) H ->
    WellFormed FType (to_LState_t m Og U T F) ->
    ObsWF Og ->
    lk m = None ->
    ~ rds m lw ->
    (forall o, ~ Detached (to_LState_t m Og U T F) o) ->
    (forall q o, Reaches (to_LState_t m Og U T F) q o ->
        flist (to_LState_t m Og U T F) o = None) ->
    Sm !! (x, lw) = Some root ->
    ([∗ list] p ∈ wb_list Og H (rt m) lw,
       (∃ s, tobs_ctl γo p.1.1 p.1.2 s) ∨ ⌜Og !! p.1 = None⌝) -∗
    phys m -∗ tobs_auth γo Og -∗ fl_auth γf St -∗
    (phys m ==∗ phys (write_begin_ms m lw)) -∗
    |==> phys (write_begin_ms m lw)
         ∗ tobs_auth γo (ins_list Og (wb_list Og H (rt m) lw))
         ∗ fl_auth γf St
         ∗ ([∗ list] p ∈ wb_list Og H (rt m) lw,
              tobs_ctl γo p.1.1 p.1.2 p.2)
         ∗ ⌜ObsWF (ins_list Og (wb_list Og H (rt m) lw))⌝
         ∗ ⌜WellFormed FType
              (to_LState_t (write_begin_ms m lw)
                 (ins_list Og (wb_list Og H (rt m) lw)) U T F)⌝
         ∗ ⌜forall Ob, EnvOK root lw U Qc FType fs Sm Ob C Fl [(x, TRoot)]⌝.
  Proof.
    intros HR Hwf Hobs Hlk Hnrd Hclean Hrfl Hroot.
    apply (write_begin_typed FType phys γo γf m Og U T F St root fs Qc lw x Sm
             C Fl (wb_list Og H (rt m) lw) Hwf Hobs Hlk Hnrd Hclean Hrfl).
    - apply wb_list_NoDup.
    - apply wb_list_key.
    - intros p Hp.
      exact (wb_list_reaches (to_LState_t m Og U T F) Og H lw p HR Hp).
    - intros q o Hq.
      exact (wb_list_covers (to_LState_t m Og U T F) Og H lw q o HR Hq).
    - apply wb_list_iter.
    - apply wb_list_grow.
    - apply wb_list_content.
    - exact Hroot.
  Qed.

End enumerated_wb.

Print Assumptions write_begin_enumerated.
