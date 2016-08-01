Require Coq.FSets.FMapFacts.
Require Coq.FSets.FMapInterface.
Require Import Coq.Lists.SetoidList.

Require Aniceto.List.

Lemma ina_to_in:
  forall {A:Type} (x:A) l,
  (InA eq x l <-> In x l).
Proof.
  intros.
  split.
  - intros.
    rewrite InA_altdef in H.
    rewrite Exists_exists in H.
    destruct H as (x', (Hin, Heq)).
    subst; assumption.
  - intros.
    rewrite InA_altdef.
    rewrite Exists_exists.
    exists x.
    intuition.
Qed.

Module MapUtil (Import M:FMapInterface.WS).
  Module F := FMapFacts.Facts M.
  Module P := FMapFacts.Properties M.
  Import F.
  Import P.
  Lemma mapsto_to_in:
    forall elt k e m,
    MapsTo (elt:=elt) k e m ->
    In k m.
  Proof.
    intros.
    unfold In.
    exists e.
    assumption.
  Qed.

  Lemma in_to_mapsto : forall (elt:Type) m x,
    In x m -> exists (e:elt), MapsTo x e m.
  Proof.
    intros.
    unfold In in H.
    assumption.
  Qed.

  Lemma add_neq_mapsto:
    forall {elt:Type} k k' e (e':elt) m,
    ~ E.eq k k' ->
    MapsTo k e (add k' e' m) ->
    MapsTo k e m.
  Proof.
    intros.
    rewrite add_mapsto_iff in H0.
    destruct H0 as [(Hr,Hn)|(_,Hr)].
    subst.
    contradiction H.
    auto.
    auto.
  Qed.

  Lemma add_in:
    forall {elt:Type} x y (e:elt) m,
    In x m ->
    In x (add y e m).
  Proof.
    intros.
    unfold In in *.
    destruct H as (e', H).
    destruct (eq_dec x y).
    - exists e.
      apply add_1.
      auto.
    - apply add_2 with (x:=y) (e':=e) in H.
      exists e'.
      auto.
      auto.
  Qed.

  Lemma remove_in:
    forall {elt:Type} x y m,
    In x (@remove elt y m) ->
    In x m.
  Proof.
    intros.
    unfold In in *.
    destruct H as (e, Hmt).
    eauto using remove_3.
  Qed.

  Let add_not_in:
    forall {elt:Type} k k' (e:elt) m,
    ~ In k (add k' e m) ->
    ~ In k m.
  Proof.
    intros.
    intuition.
    apply add_in with (y:=k') (e0:=e) in H0.
    apply H in H0.
    trivial.
  Qed.

  Lemma add_inv:
    forall {elt:Type} (x y:key) (e:elt) m1 m2,
    Add x e m1 m2 ->
    forall y,
    (exists e', MapsTo y e' m2 /\ MapsTo y e' (add x e m1)) \/
    (~ In y m2 /\ ~ In y (add x e m1)).
  Proof.
    intros.
    unfold Add in *.
    assert (Hr := H y0).
    remember (find y0 m2) as r.
    symmetry in Heqr.
    symmetry in Hr.
    destruct r.
    rewrite <- find_mapsto_iff in Heqr.
    rewrite <- find_mapsto_iff in Hr.
    left.
    exists e0. intuition.
    (* negative case *)
    rewrite <- not_find_in_iff in Hr.
    rewrite <- not_find_in_iff in Heqr.
    right.
    intuition.
  Qed.

  Lemma add_mapsto_neq:
    forall {elt:Type} k k' e (e':elt) m1 m2,
    MapsTo k e m1 ->
    Add k' e' m1 m2 ->
    ~ E.eq k k' ->
    MapsTo k e m2.
  Proof.
    intros.
    apply add_inv with (y0:=k) in H0.
    destruct H0 as [(e1, (H2, H3))|(H2,H3)].
    apply add_neq_mapsto in H3.
    apply MapsTo_fun with (e:=e) in H3.
    subst. trivial.
    assumption.
    assumption.
    (* absurd case *)
    assert (Hin: In k m1).
    unfold In.
    exists e.
    assumption.
    (* end of assert *)
    apply add_not_in in H3.
    contradiction H3.
    auto.
  Qed.

  Lemma add_mapsto_eq:
    forall {elt:Type} k k' (e':elt) m1 m2,
    Add k' e' m1 m2 ->
    E.eq k k' ->
    MapsTo k e' m2.
  Proof.
    intros.
    assert (Heq : E.eq k' k') by auto.
    apply add_eq_o with (elt:=elt) (m:=m1) (e:=e') in Heq.
    unfold Add in H.
    assert (Hf := H k'). clear H.
    remember (find k' m2) as f.
    destruct f.
    - symmetry in H0.
      rewrite Heq in Hf.
      inversion Hf.
      subst.
      symmetry in Heqf.
      rewrite <- find_mapsto_iff in Heqf.
      rewrite <- H0.
      assumption.
    - rewrite <- Hf in Heq.
      inversion Heq.
  Qed.


  Lemma in_elements_impl_maps_to:
    forall {elt:Type} k (e:elt) m,
    List.In (k, e) (elements (elt:=elt) m) ->
    MapsTo k e m.
  Proof.
    intros.
    apply elements_2.
    apply In_InA.
    + unfold eq_key_elt.
        intuition.
        * unfold Symmetric.
          intros.
          destruct x, y, H0.
          simpl in *.
          auto.
        * unfold Transitive.
          intros.
          destruct x, y, z, H0, H1.
          simpl in *.
          subst.
          intuition.
          apply E.eq_trans with (y:=k1); repeat assumption.
      + assumption.
  Qed.

  Lemma maps_to_impl_in_elements:
    forall {elt:Type} k (e:elt) m,
    MapsTo k e m ->
    exists k', E.eq k k' /\ List.In (k', e) (elements (elt:=elt) m).
  Proof.
    intros.
    apply elements_1 in H.
    apply InA_alt in H.
    destruct H as ((k', e'), (Heq, Hin)).
    inversion Heq.
    simpl in *.
    subst.
    exists k'.
    intuition.
  Qed.

  Lemma maps_to_iff_in_elements:
    forall {elt:Type} k (e:elt) m,
    (forall k k', E.eq k k' -> k = k') ->
    (MapsTo k e m <->
    List.In (k, e) (elements (elt:=elt) m)).
  Proof.
    intros.
    split.
    - intros. apply maps_to_impl_in_elements in H0.
      destruct H0 as (k', (Heq, Hin)).
      apply H in Heq.
      subst.
      assumption.
    - apply in_elements_impl_maps_to.
  Qed.

  Lemma in_to_ina_eq_key_elt (k_eq: forall k k', E.eq k k' <-> k = k'):
    forall {elt:Type} k v (l: list (key * elt)),
    List.In (k,v) l -> InA (eq_key_elt (elt:=elt)) (k,v) l.
  Proof.
    intros.
    rewrite InA_altdef.
    rewrite Exists_exists.
    exists (k, v).
    intuition.
    unfold eq_key_elt.
    simpl.
    rewrite k_eq.
    intuition.
  Qed.

  Lemma in_elements_to_in:
    forall {elt:Type} k e (m: t elt),
    List.In (k, e) (elements m) ->
    In k m.
  Proof.
    intros.
    rewrite elements_in_iff.
    exists e.
    apply InA_altdef.
    apply Exists_exists.
    exists (k,e).
    intuition.
    unfold eq_key_elt.
    intuition.
  Qed.

  Lemma of_list_in_iff
    {elt:Type}
    (k_eq: forall k k', E.eq k k' <-> k = k'):
    forall (k:E.t) (v:elt) (l:list (E.t * elt)),
    NoDupA (eq_key (elt:=elt)) l ->
    (MapsTo k v (of_list l) <-> List.In (k, v) l).
  Proof.
    intros.
    split.
    - intros.
      apply of_list_1 in H0.
      apply InA_alt in H0.
      destruct H0 as (kv, (Heq, Hin)).
      destruct kv.
      unfold eq_key_elt in Heq.
      destruct Heq.
      simpl in *.
      apply k_eq in H0.
      subst.
      assumption.
      assumption.
   - intros.
     apply of_list_1; auto.
     apply in_to_ina_eq_key_elt; repeat auto.
 Qed.


  Lemma to_list_of_list
    {elt:Type}
    (k_eq: forall k k', E.eq k k' <-> k = k'):
    forall (k:E.t) (v:elt) (l:list (E.t * elt)),
    NoDupA (eq_key (elt:=elt)) l ->
    List.In (k, v) l ->
    List.In (k, v) (to_list (of_list l)).
  Proof.
    intros.
    apply (in_to_ina_eq_key_elt k_eq) in H0.
    apply (of_list_1 (l:=l) k v H) in H0.
    unfold to_list.
    apply maps_to_impl_in_elements in H0.
    destruct H0 as (k', (Heq, Hin)).
    apply k_eq in Heq; subst.
    assumption.
  Qed.

  Lemma empty_to_mapsto:
    forall {elt:Type} k (e:elt) m,
    Empty m ->
    ~ MapsTo k e m.
  Proof.
    intros.
    unfold Empty in *.
    apply H.
  Qed.

  (* *** filter for map  **** *)
  Definition filter_elements {elt:Type} (f:(key * elt)%type -> bool) (m:t elt) := List.filter f (elements m).
  Lemma filter_elements_spec
      {elt:Type}
      (k_eq: forall k k', E.eq k k' <-> k = k'):
    forall (f:(key * elt)%type -> bool) (k:key) (e:elt) (m:t elt),
    List.In (k, e) (filter_elements f m) <-> MapsTo k e m /\  f (k, e) = true.
  Proof.
    intros.
    unfold filter_elements.
    rewrite filter_In.
    rewrite maps_to_iff_in_elements; repeat intuition.
    apply k_eq; assumption.
  Qed.

  Lemma filter_preserves_ina {elt:Type}:
    forall a f l,
    InA (eq_key (elt:=elt)) a (List.filter f l) ->
    InA (eq_key (elt:=elt)) a l.
  Proof.
    intros.
    induction l.
    - trivial.
    - simpl in *.
      remember (f a0).
      destruct b.
      + inversion H.
        * subst.
          apply InA_cons_hd; repeat auto.
        * subst.
          apply IHl in H1.
          apply InA_cons_tl.
          assumption.
      + apply IHl in H; clear IHl.
        apply InA_cons_tl.
        assumption.
  Qed.

  Lemma filter_preserves_nodupa {elt:Type}:
    forall l f,
    NoDupA (eq_key (elt:=elt)) l ->
    NoDupA (eq_key (elt:=elt)) (List.filter f l).
  Proof.
    intros.
    induction l.
    - trivial. (* base case *)
    - inversion H.
      subst.
      apply IHl in H3.
      simpl.
      remember (f a).
      destruct b.
      + apply NoDupA_cons; repeat auto.
        intuition.
        apply H2.
        apply filter_preserves_ina with (f0:=f).
        assumption.
      + assumption.
  Qed.

  Lemma filter_elements_nodupa:
    forall {elt:Type} (f:(key * elt)%type -> bool) (k:key) (e:elt) (m:t elt),
    NoDupA (eq_key (elt:=elt)) (filter_elements f m).
  Proof.
    intros.
    unfold filter_elements.
    apply filter_preserves_nodupa.
    apply elements_3w.
  Qed.

  Definition filter {elt:Type} (f: key -> elt -> bool) (m:t elt) : t elt :=
    of_list (filter_elements (fun p => let (k, e) := p in f k e) m).

  Lemma filter_spec
      {elt:Type}
      (k_eq: forall k k', E.eq k k' <-> k = k'):
    forall (f:key -> elt -> bool) (k:key) (e:elt) (m:t elt),
    MapsTo k e (filter f m) <-> MapsTo k e m /\ f k e = true.
  Proof.
    intros.
    unfold filter.
    rewrite of_list_in_iff.
    - rewrite filter_elements_spec.
      intuition.
      auto.
   - apply k_eq.
   - apply filter_elements_nodupa; repeat auto.
  Qed.

  Lemma in_choice:
    forall {elt:Type} (m:t elt),
    { exists k, In k m } + { ~ exists k, In k m }.
  Proof.
    intros elt.
    apply map_induction with (elt:=elt).
    - intuition.
      right.
      intros.
      destruct H0 as (k, (e, Hmt)).
      unfold Empty in *.
      apply H in Hmt.
      assumption.
    - intros.
      left.
      exists x.
      unfold In.
      exists e.
      apply add_mapsto_eq with (k:=x) in H1.
      assumption.
      auto.
  Qed.

  Lemma nonempty_in:
    forall {elt:Type} (m:t elt),
    ~ Empty m <->
    exists k, In k m.
  Proof.
    split.
    + intros.
      remember (elements m).
      destruct l.
      - symmetry in Heql.
        apply elements_Empty in Heql.
        tauto.
      - destruct p as (k, e).
        assert (List.In (k, e) (elements m)). {
          rewrite <- Heql.
          auto with *.
        }
        exists k.
        eauto using in_elements_to_in.
    + intros.
      unfold Empty.
      intuition.
      unfold In in *.
      destruct H as (k, (e, Hmt)).
      eauto using H0.
  Qed.

  (**
    Given a predicate, pick an element from the map, otherwise the predicate
    is not matched for all elements in the map.
    *)
  Lemma pred_choice:
    forall {elt:Type} (m:t elt) f,
    Proper (E.eq ==> eq ==> eq) f ->
    {exists k v, MapsTo k v m /\ f k v = true } +
    {forall k v, MapsTo k v m -> f k v = false}.
  Proof.
    intros.
    remember (fst (P.partition f m)) as y.
    destruct (in_choice y).
  - left.
    destruct e as (k, Hin).
    apply in_to_mapsto in Hin.
    destruct Hin as (e, Hin).
    exists k.
    exists e.
    apply P.partition_iff_1 with (k:=k) (e:=e) in Heqy; auto with *.
    intuition.
  - right.
    intros.
    remember (f k v) as b.
    destruct b; auto.
    symmetry in Heqb.
    assert (exists k, In k y). {
      exists k.
      unfold In.
      exists v.
      apply P.partition_iff_1 with (k:=k) (e:=v) in Heqy; auto.
      rewrite Heqy.
      intuition.
    }
    contradiction H1.
  Qed.


  Definition keys {elt:Type} (m:t elt) : list key :=  fst (split (elements m)).

  Lemma keys_spec_1:
    forall {elt:Type} (m:t elt) (k:key),
    List.In k (keys m) -> In k m.
  Proof.
    intros.
    unfold keys in *.
    apply List.in_fst_split in H.
    destruct H as (e, H).
    apply in_elements_to_in with (e0:=e).
    assumption.
  Qed.

  Lemma keys_spec_2:
    forall {elt:Type} (m:t elt) (k:key),
    In k m ->
    exists k', E.eq k k' /\ List.In k' (keys m).
  Proof.
    intros.
    unfold keys in *.
    destruct H as (e, H).
    apply maps_to_impl_in_elements in H.
    destruct H as (k', (Heq, Hin)).
    apply in_split_l in Hin.
    exists k'.
    intuition.
  Qed.

  Lemma keys_spec (k_eq: forall k k', E.eq k k' <-> k = k'):
    forall {elt:Type} (m:t elt) (k:key),
    In k m <-> List.In k (keys m).
  Proof.
    intros.
    split.
    - intros.
      apply keys_spec_2 in H.
      destruct H as (k', (Heq, H)).
      apply k_eq in Heq; subst.
      assumption.
    - apply keys_spec_1.
  Qed.

  Lemma ina_fst_split_alt:
    forall {elt:Type} (k:key) (e:elt) (l:list (key*elt)%type),
    InA E.eq k (fst (List.split_alt l)) ->
    InA (eq_key (elt:=elt)) (k, e) l.
  Proof.
    intros.
    induction l.
    - inversion H. (* absurd *)
    - inversion H.
      + subst.
        destruct a as (k', e').
        simpl in *.
        inversion H0.
        subst.
        clear H0.
        apply InA_cons_hd.
        unfold eq_key.
        auto.
      +
        destruct a as (k', e').
        simpl in *.
        inversion H0.
        subst.
        clear H0.
        apply IHl in H1; clear IHl.
        apply InA_cons_tl.
        assumption.
  Qed.

  Lemma fst_split_nodupa:
    forall {elt:Type} (l:list (key*elt)%type),
    NoDupA (eq_key (elt:=elt)) l ->
    NoDupA E.eq (fst (split l)).
  Proof.
    intros; induction l.
    - simpl. apply NoDupA_nil.
    - inversion H; clear H.
      subst.
      apply IHl in H3; clear IHl.
      destruct a as (k,e).
      rewrite List.split_alt_spec.
      simpl.
      apply NoDupA_cons.
      + intuition.
        apply ina_fst_split_alt with (e0:=e) in H.
        contradiction H.
      + rewrite List.split_alt_spec in H3.
        assumption.
  Qed.

  Lemma keys_nodupa:
    forall {elt:Type} (m:t elt),
    NoDupA E.eq (keys m).
  Proof.
    intros.
    unfold keys.
    apply fst_split_nodupa.
    apply elements_3w.
  Qed.

  Lemma keys_nodup (k_eq: forall k k', E.eq k k' <-> k = k'):
    forall {elt:Type} (m:t elt),
    NoDup (keys m).
  Proof.
    intros.
    assert (Hx := keys_nodupa m).
    apply List.nodupa_nodup_iff in Hx.
    assumption.
    apply k_eq.
  Qed.

  Lemma in_dec {elt:Type} (is_eq:forall k k' : E.t, E.eq k k' <-> k = k'):
    forall k (m:t elt),
    { In k m } + { ~ In k m  }.
  Proof.
    intros.
    assert (eq_dec  : forall x y:E.t, { x = y } + { x <> y }). {
      intros.
      destruct (E.eq_dec x y).
      - left.
        rewrite <- is_eq.
        assumption.
      - right.
        intuition.
        rewrite is_eq in *.
        tauto.
    }
    destruct (List.in_dec eq_dec k (keys m)).
    - left.
      auto using keys_spec_1.
    - right.
      intuition.
      assert (List.In  k (keys m)). {
        apply keys_spec; auto.
      }
      contradiction H0.
  Qed.

  Definition values {elt:Type} (m:t elt) : list elt :=  snd (split (elements m)).

  Lemma values_spec_1:
    forall {elt:Type} (m:t elt) (e:elt),
    List.In e (values m) ->
    exists k, MapsTo k e m.
  Proof.
    intros.
    unfold values in *.
    apply List.in_snd_split in H.
    destruct H as (k, Hin).
    apply in_elements_impl_maps_to in Hin.
    exists k.
    assumption.
  Qed.

  Lemma values_spec_2:
    forall {elt:Type} (m:t elt) (k:key) (e:elt),
    MapsTo k e m ->
    List.In e (values m).
  Proof.
    intros.
    unfold values.
    apply maps_to_impl_in_elements in H.
    destruct H as (k', (Heq, Hin)).
    apply in_split_r in Hin.
    simpl in *.
    assumption.
  Qed.

  Lemma values_spec:
    forall {elt:Type} (m:t elt) (e:elt),
    List.In e (values m) <-> exists k, MapsTo k e m.
  Proof.
    intros.
    split.
    apply values_spec_1.
    intros.
    destruct H as (k, H).
    apply values_spec_2 with (k0:=k).
    assumption.
  Qed.

  Lemma eq_key_unfold:
    forall {elt:Type} (k k':E.t) (e e':elt),
    eq_key (k, e) (k', e') <-> E.eq k k'.
  Proof.
    unfold eq_key.
    tauto.
  Qed.
  
  Lemma eq_key_in_to_ina:
    forall {elt:Type} (k k':E.t) (e e':elt) l,
    E.eq k' k -> 
    List.In (k, e) l ->
    InA (eq_key (elt:=elt)) (k', e') l.
  Proof.
    intros.
    apply InA_alt.
    exists (k, e).
    intuition.
  Qed.

  Lemma find_rw:
    forall {A:Type} k (m: t A),
    { find k m = None /\ ~ In k m }
    + { exists e, find k m = Some e /\ MapsTo k e m }.
  Proof.
    intros.
    remember (find _ _) as o.
    symmetry in Heqo.
    destruct o as [e|].
    - right.
      exists e.
      intuition.
    - left; intuition.
      apply not_find_in_iff in Heqo.
      contradiction.
  Qed.

Section OMap.
  Set Implicit Arguments.
  Variable A: Type.
  Variable B: Type.

  (** omap changes the element only if there is some return value. *)
  Variable f : E.t -> A -> option B.

  Variable m:t A.

  Let adapt_f (p:E.t * A) :=
    let (k, v) := p in
    match f k v with
    | Some v => Some (k,v)
    | None => None
    end.

  Definition omap := of_list (List.omap adapt_f (to_list m)).

  Let notina_inv_cons:
    forall x a l,
    ~ InA (eq_key (elt:=A)) x (a :: l) ->
    ~ InA (eq_key (elt:=A)) x l.
  Proof.
    intros.
    intuition.
  Qed.

  Let notina_cons:
    forall k k' e b l,
    ~ E.eq k k' ->
    ~ InA (eq_key (elt:=B)) (k, e) l ->
    ~ InA (eq_key (elt:=B)) (k, e) ((k', b) :: l).
  Proof.
    intros.
    intuition.
    inversion H1; subst.
    - compute in H3.
      contradiction.
    - contradiction.
  Qed.

  Let notina_omap:
    forall l k e e',
    ~ InA (eq_key (elt:=A)) (k, e') l ->
    ~ InA (eq_key (elt:=B)) (k, e) (List.omap adapt_f l).
  Proof.
    induction l.
    - intros.
      simpl.
      intuition.
      inversion H0.
    - intros.
      simpl.
      remember (adapt_f a).
      destruct o.
      + simpl.
        destruct a as (k', a).
        simpl in Heqo.
        destruct (f k' a).
        * inversion Heqo; subst; clear Heqo.
          destruct (E.eq_dec k k'). {
            contradiction H.
            eauto using InA_eqA.
          }
          assert (~ InA (eq_key (elt:=B)) (k, e) (List.omap adapt_f l)). {
            eauto.
          }
          eauto.
        * inversion Heqo.
      + eauto.
  Qed.

  Let nodupa_omap:
    NoDupA (eq_key (elt:=B)) (List.omap adapt_f (elements m)).
  Proof.
    intros.
    assert (NoDupA (eq_key (elt:=A)) (elements m))
    by eauto using elements_3w.
    induction H.
    - simpl.
      apply NoDupA_nil.
    - simpl.
      remember (adapt_f x).
      destruct o.
      + simpl.
        destruct x as (k', v).
        simpl in Heqo.
        destruct (f k' v). {
          inversion Heqo; subst.
          apply NoDupA_cons; auto.
          eauto.
        }
        inversion Heqo.
      + auto.
  Qed.

  Variable eq_rw:
    forall k k',
    E.eq k k' <-> k = k'.

  Lemma omap_1:
    forall k x y,
    MapsTo k x m ->
    f k x = Some y ->
    MapsTo k y omap.
  Proof.
    intros.
    unfold omap.
    remember (List.omap _ _) as l.
    apply elements_mapsto_iff in H.
    unfold to_list in *.
    rewrite InA_altdef in H.
    rewrite Exists_exists in H.
    destruct H as ((k',x'), (Hin, Heq)).
    compute in Heq.
    destruct Heq as (He, ?).
    subst x.
    subst.
    assert (adapt_f (k, x') = Some (k, y)). {
      simpl.
      rewrite H0.
      trivial.
    }
    apply List.in_omap_1 with (f:=adapt_f) (y:=(k,y)) in Hin; auto.
    - rewrite of_list_1; auto.
      rewrite InA_altdef.
      rewrite Exists_exists.
      exists (k, y).
      intuition.
      compute.
      intuition.
    - apply eq_rw in He.
      subst.
      trivial.
  Qed.

  Lemma omap_2:
    forall k x,
    MapsTo k x omap ->
    exists y, f k y = Some x /\ MapsTo k y m.
  Proof.
    intros.
    unfold omap in *.
    unfold to_list in *.
    rewrite of_list_1 in H; eauto.
    rewrite InA_altdef in H.
    rewrite Exists_exists in H.
    destruct H as ((k', e'), (Hin, Heq)).
    compute in Heq.
    destruct Heq.
    subst.
    apply List.in_omap_2 in Hin.
    destruct Hin as ((a,b), (Hin, Ha)).
    simpl in Ha.
    remember (f a b).
    destruct o.
    - inversion Ha; subst; clear Ha.
      assert (InA (eq_key_elt (elt:=A)) (k', b) (elements m)). {
        rewrite InA_altdef.
        rewrite Exists_exists.
        exists (k', b).
        intuition.
        compute.
        intuition.
      }
      apply elements_2 in H0.
      symmetry in Heqo.
      exists b.
      assert (k' = k). {
        apply eq_rw in H.
        auto.
      }
      subst.
      intuition.
    - inversion Ha.
  Qed.
End OMap.

Section Partition.
  Variable elt:Type.
  Variable f : key -> elt -> bool.
  Variable f_prop: Proper (E.eq ==> eq ==> eq) f.
  Lemma partition_in_1_to_all:
    forall k m,
    In k (fst (P.partition f m)) ->
    In k m.
  Proof.
    intros.
    unfold In in *.
    destruct H as (e, mt).
    remember (fst (partition f m)) as m1.
    rewrite partition_iff_1 with (f:=f) (m:=m) (m1:=m1) in mt; eauto.
    destruct mt.
    eauto.
  Qed.

  Lemma partition_in_2_to_all:
    forall k m,
    In k (snd (P.partition f m)) ->
    In k m.
  Proof.
    intros.
    unfold In in *.
    destruct H as (e, mt).
    remember (snd (partition f m)) as m1.
    rewrite partition_iff_2 with (f:=f) (m:=m) (m2:=m1) in mt; eauto.
    destruct mt.
    eauto.
  Qed.

  Lemma partition_in_fst:
    forall {elt:Type} m m1 m2 k,
    Partition (elt:=elt) m m1 m2 ->
    In k m1 ->
    In k m.
  Proof.
    intros.
    unfold Partition in *.
    destruct H as (H, Hx).
    apply in_to_mapsto in H0.
    destruct H0 as (?, Hm).
    apply mapsto_to_in with (x).
    rewrite Hx.
    auto.
  Qed.

  Lemma partition_in_snd:
    forall {elt:Type} m m1 m2 k,
    Partition (elt:=elt) m m1 m2 ->
    In k m2 ->
    In k m.
  Proof.
    intros.
    unfold Partition in *.
    destruct H as (H, Hx).
    apply in_to_mapsto in H0.
    destruct H0 as (?, Hm).
    apply mapsto_to_in with (x).
    rewrite Hx.
    auto.
  Qed.

End Partition.

Section NotIn.
  Require Import Coq.Structures.OrderedType.
  Variable elt:Type.
  Variable zero: E.t.
  Variable next: E.t -> E.t.
  Variable Lt: E.t -> E.t -> Prop.
  Variable lt_trans:
    forall x y z,
    Lt x y ->
    Lt y z ->
    Lt x z.
  Variable lt_irrefl:
    forall x,
    ~ Lt x x.

  Variable lt_comparable:
    forall x y, Compare Lt eq x y.

  Variable lt_zero:
    forall x, ~ Lt x zero.

  Variable lt_next:
    forall x,
    Lt x (next x).

  Variable eq_rw:
    forall k k',
    E.eq k k' -> k = k'.

  Definition supremum (m:t elt) := (List.supremum zero next lt_comparable (keys m)).

  Definition Supremum x (m:t elt) := forall y, In y m -> Lt y x.

  Lemma supremum_spec:
    forall (m:t elt),
    Supremum (supremum m) m.
  Proof.
    intros.
    assert (X:=List.supremum_spec zero next lt_trans lt_comparable lt_next (keys m)).
    unfold List.Supremum in *.
    rewrite Forall_forall in X.
    unfold Supremum.
    intros.
    apply keys_spec_2 in H.
    destruct H as (k', (E,Hi)).
    apply eq_rw in E; subst.
    auto.
  Qed.

  Lemma supremum_not_in:
    forall x m,
    Supremum x m ->
    ~ In x m.
  Proof.
    intros.
    unfold not; intros.
    apply H in H0.
    apply lt_irrefl in H0.
    contradiction.
  Qed.

  Theorem find_not_in:
    forall m,
    ~ In (supremum m) m.
  Proof.
    intros.
    assert (S: Supremum (supremum m) m) by auto using supremum_spec.
    apply supremum_not_in in S.
    assumption.
  Qed.

End NotIn.

End MapUtil.
