Require Import Coq.FSets.FMapFacts.
Require Import Coq.FSets.FSetProperties.
Require Import Aniceto.Set.
Require Import Aniceto.Map.
Require Import Aniceto.List.

Require Recdef. (* Required by Function *)
Require Coq.Arith.Wf_nat. (* Required implicitly by measure obligations *)

Set Implicit Arguments.

Section MATCH.

Variable K : Type.

Variable V : Type.

Variable key_eq_dec : forall x y : K, {x = y} + {x <> y}.

Variable value_eq_dec : forall x y : V, {x = y} + {x <> y}.

Definition match_key (k:K) (p:K*V) :=
  let (k', _) := p in
  if key_eq_dec k k' then true else false.

Let partition_in':
  forall k k' v l matched mismatched,
  partition (match_key k) l = (matched, mismatched) ->
  In (k', v) l ->
  {In (k',v) matched /\ k = k'} + {In (k',v) mismatched /\ k <> k'}.
Proof.
  intros.
  assert (Heq1 : matched = fst (partition (match_key k) l)).
  rewrite H; auto. (* eoa *)
  assert (Heq2 : mismatched = snd (partition (match_key k) l)).
  rewrite H; auto. (* eoa *)
  rewrite Heq1; rewrite Heq2.
  assert (Hdec: {In (k', v) (fst (partition (match_key k) l)) /\ match_key k (k',v) = true} +
{In (k', v) (snd (partition (match_key k) l)) /\ match_key k (k',v) = false}).
  apply partition_in.
  assumption.
  (* eoa *)
  destruct Hdec.
  - left.
    destruct a.
    simpl in *.
    destruct (key_eq_dec k k').
    subst.
    auto.
    inversion H2.
  - right.
    intuition.
    simpl in *.
    destruct (key_eq_dec k k').
    inversion H2.
    contradiction f.
Qed.

Let match_key_refl:
  forall k v,
  match_key k (k,v) = true.
Proof.
  intros.
  simpl.
  destruct (key_eq_dec k k).
  auto.
  contradiction n.
  trivial.
Qed.

Let partition_match_key_spec_1:
  forall v k l,
  In (k, v) l <-> In (k, v) (fst (partition (match_key k) l)).
Proof.
  intros.
  split.
  - intros.
    rewrite partition_iff_1.
    intuition.
  - intros.
    rewrite partition_iff_1 in H.
    intuition.
Qed.

Let match_key_subst:
  forall k k' v,
  match_key k (k', v) = true ->
  k = k'.
Proof.
  intros.
  simpl in *.
  destruct (key_eq_dec k k').
  assumption.
  inversion H.
Qed.

Let partition_match_key_spec_2:
  forall v k' k l,
  In (k', v) (fst (partition (match_key k) l)) ->
  k' = k.
Proof.
  intros.
  rewrite partition_iff_1 in H.
  destruct H as (_, H).
  apply match_key_subst in H.
  auto.
Qed.

Let partition_match_key_spec_3:
  forall v k l,
  In (k, v) l <-> In v (snd (split (fst (partition (match_key k) l)))).
Proof.
  intros.
  split.
  - intros.
    apply partition_match_key_spec_1 in H.
    apply in_split_r in H.
    auto.
  - intros.
    rewrite partition_match_key_spec_1.
    apply split_in_r in H.
    destruct H as (k', Hin).
    assert (H := Hin).
    apply partition_match_key_spec_2 in H.
    subst.
    assumption.
Qed.

Let in_split_r_2:
  forall {L R:Type}(lst:list (L * R)%type) (lst_l:list L) (lst_r:list R) (l:L) (r:R),
  split lst = (lst_l, lst_r) ->
  In (l, r) lst ->
  In r lst_r.
Proof.
  intros.
  assert (lst_r = snd (split lst)).
  rewrite H; auto. (* eoa *)
  rewrite H1.
  assert (r = snd (l, r)). auto. (* eoa *)
  rewrite H2.
  apply in_split_r.
  assumption.
Qed.

Let in_matched:
  forall k v ks vs l matched mismatched,
  In v vs ->
  split matched = (ks, vs) ->
  partition (match_key k) l = (matched, mismatched) ->
  In (k, v) (fst (partition (match_key k) l)).
Proof.
  intros.
  assert (In (k, v) (fst (partition (match_key k) l))).
  rewrite partition_iff_1.
  assert (In v (snd (split matched))).
  rewrite H0; auto. (* eoa *)
  clear H H0.
  intuition.
  rewrite partition_match_key_spec_3.
  rewrite H1.
  auto.
  assumption.
Qed.


Import Recdef. (* Required by Function *)
Import Coq.Arith.Wf_nat. (* Required implicitly by measure obligations *)

Function unproj (l:list (K*V)) {measure length l} : list (K * (list V)) :=
  match l with
    | e :: l' =>
      let (k, v) := e in
      let (matched, mismatched) := partition (match_key k) l' in
      let (_, vs) := split matched in
      (k, v :: vs)::(unproj mismatched)
    | nil => nil
  end.
Proof.
  intros.
  subst.
  assert (mismatched = (snd (partition (match_key k) l'))).
  rewrite teq1; auto.
  rewrite H.
  simpl.
  apply Lt.le_lt_n_Sm.
  apply partition_length.
Defined.

Theorem unproj_spec:
  forall k v l,
  (List.In (k, v) l <-> exists l', List.In (k, l') (unproj l) /\ In v l').
Proof.
  intros.
  functional induction (unproj l).
  - split.
    + intros.
      inversion H.
      * inversion H0; subst; clear H0 H.
        exists (v :: vs).
        intuition.
      * assert ({In (k,v) matched /\ k0 = k} + {In (k,v) mismatched /\ k0 <> k}).
        apply partition_in' with (k:=k0) (k':=k) (l:=l').
        auto.
        auto.
        (* eoa *)
        destruct H1 as [(H1, H2)|(H1, H2)].
        subst.
        exists (v0 :: vs).
        intuition.
        apply in_cons.
        apply in_split_r_2 with (lst:=matched) (lst_l:=_x) (l:=k); repeat auto.
        (* eoa *)
        apply IHl0 in H1.
        destruct H1 as (s, (Hin, Hin')).
        exists s.
        intuition.
     + intros.
       destruct H as (s, (Hin, Hin')).
       destruct Hin.
       * inversion H; subst; clear H.
         destruct (value_eq_dec v v0).
         subst; apply in_eq. (* end of eq *)
         apply in_cons.
         clear IHl0.
         apply in_cons_neq in Hin'.
         apply in_matched with (k:=k) (ks:=_x) (l:=l') (matched:=matched) (mismatched:=mismatched) in Hin'.
         apply partition_iff_1 in Hin'.
         intuition.
         auto.
         auto.
         auto.
       * assert (exists s', In (k, s') (unproj mismatched) /\ In v s').
         exists s; auto.
         apply IHl0 in H0. clear IHl0.
         apply in_cons.
         assert (In (k, v) (snd (partition (match_key k0) l'))).
         rewrite e2; auto. (* eoa *)
         apply partition_iff_2 in H1.
         intuition.
  - split.
    intros. inversion H.
    intros.
    destruct H as (s, (Hin, _)).
    inversion Hin.
Qed.

Let in_unproj_to_in:
  forall k v l l',
  List.In (k, l') (unproj l) ->
  In v l' ->
  List.In (k, v) l.
Proof.
  intros.
  assert (exists l', List.In (k, l') (unproj l) /\ In v l').
  exists l'.
  intuition.
  apply unproj_spec.
  assumption.
Qed.

Definition eq_key {A:Type} (p p':K*A) := (fst p) = (fst p').

Definition NotInA {A:Type} f (k:K) l := forall (v:A), ~ InA f (k, v) l.

Let ina_to_in:
  forall {A:Type} k (v:A) l,
  InA eq_key (k, v) l ->
  exists v', In (k, v') l.
Proof.
  intros.
  rewrite InA_altdef in H.
  rewrite Exists_exists in H.
  destruct H as ((k',v'), (Hin, Heq)).
  unfold eq_key in Heq.
  simpl in Heq; subst.
  exists v'.
  auto.
Qed.

Let in_to_ina:
  forall {A:Type} k (v:A) l,
  In (k, v) l ->
  InA eq_key (k, v) l.
Proof.
  intros.
  rewrite InA_altdef.
  rewrite Exists_exists.
  exists (k, v).
  intuition.
Qed.

Lemma unproj_absurd:
  forall k l,
  In (k, nil) (unproj l) -> False.
Proof.
  intros.
  functional induction (unproj l).
  - inversion H.
    + inversion H0.
    + apply IHl0.
      assumption.
  - inversion H.
Qed.

Let partition_match_key_spec_4:
  forall v k l,
  In (k, v) (snd (partition (match_key k) l)) -> False.
Proof.
  intros.
  rewrite partition_iff_2 in H.
  destruct H as (_, H).
  assert (Hm:= match_key_refl k v).
  rewrite Hm in H.
  inversion H.
Qed.

Let partition_match_key_spec_5:
  forall k l,
  NotInA eq_key k (snd (partition (match_key k) l)).
Proof.
  intros.
  unfold NotInA.
  intros.
  intuition.
  apply ina_to_in in H.
  destruct H as (v', Hin).
  apply partition_match_key_spec_4 in Hin.
  assumption.
Qed.

Theorem nodupa_unproj:
  forall l,
  NoDupA eq_key (unproj l).
Proof.
  intros.
  functional induction (unproj l).
  - apply NoDupA_cons.
    + intuition.
      apply ina_to_in in H.
      destruct H as (vs', Hin).
      assert (Hx := partition_match_key_spec_5 (k:=k) l').
      assert (Heq : mismatched = snd (partition (match_key k) l')).
      rewrite e2; simpl; auto.
      rewrite <- Heq in Hx.
      destruct vs'.
      * apply unproj_absurd in Hin. inversion Hin.
      * assert (Hinv : In v0 (v0 :: vs')).
        apply in_eq.
        apply in_unproj_to_in with (v:=v0) in Hin.
        unfold NotInA in Hx.
        apply in_to_ina in Hin.
        apply (Hx v0) in Hin.
        inversion Hin.
        assumption.
    + assumption.
  - auto.
Qed.

End MATCH.

Module Project (M:FMapInterface.WS) (S:FSetInterface.WS).
  (* XXX: Use ProjectList instead of doing everything from scratch *)

  Module S_Props := FSetProperties.Properties S.
  Module M_Props := FMapFacts.Properties M.
  Module M_Extra := MapUtil M.
  Module S_Extra := SetUtil S.

  Section Defs.

  Let proj_edges (e:(M.E.t * S.t)) :=
    let (k, s) := e in
    List.map (fun v=> (k, v)) (S.elements s).

  Definition project m : list (M.E.t * S.E.t) :=
  List.flat_map proj_edges (M.elements m).

  Variable key_eq_rw: forall k1 k2, M.E.eq k1 k2 -> k1 = k2.
  Variable elem_eq_rw: forall e1 e2, S.E.eq e1 e2 -> e1 = e2.

  Theorem project_spec:
    forall k e m,
    (List.In (k,e) (project m) <-> (exists (s:S.t), M.MapsTo k s m  /\ S.In e s)).
  Proof.
    unfold project in *.
    intros k e m.
    split; intros.
    - rewrite List.in_flat_map in *.
      unfold proj_edges in *.
      destruct H as ((r', ts), (H1, H2)).
      rewrite List.in_map_iff in H2.
      destruct H2 as (t'', (H2, H3)).
      inversion H2; subst; clear H2.
      apply M_Extra.in_elements_impl_maps_to in H1.
      apply S_Extra.in_iff_in_elements in H3; auto.
      eauto.
    - destruct H as (s, (Hmt, Hin)).
      rewrite in_flat_map.
      unfold proj_edges.
      exists (k, s).
      intuition.
      + rewrite <- M_Extra.maps_to_iff_in_elements; auto.
      + rewrite in_map_iff.
        exists e.
        intuition.
        rewrite <- S_Extra.in_iff_in_elements; auto.
  Qed.

  Notation edge := (M.E.t * S.E.t)%type.

  Let value_eq_dec:
    forall (e1 e2:S.E.t),
    {e1 = e2} + {e1 <> e2}.
  Proof.
    intros.
    destruct (S.E.eq_dec e1 e2).
    + left; auto.
   + right.
     intuition.
     contradiction n.
     subst.
     auto using S.E.eq_refl.
  Qed.

  Let key_eq_dec:
    forall (e1 e2:M.E.t),
    {e1 = e2} + {e1 <> e2}.
  Proof.
    intros.
    destruct (M.E.eq_dec e1 e2).
    + left; auto.
    + right.
      intuition.
      subst.
      contradiction n; auto using M.E.eq_refl.
  Qed.

  Let unproj_0 l := unproj (V:=S.E.t) key_eq_dec l.

  Let unproj_0_spec:
    forall k v l,
    (List.In (k, v) l <-> exists l', List.In (k, l') (unproj_0 l) /\ In v l').
  Proof.
    intros.
    split; intros;
    rewrite unproj_spec with (key_eq_dec:=key_eq_dec) in *; auto.
  Qed.

  Let nodupa_conv:
    forall {A:Type} l,
    NoDupA (eq_key (A:= A)) l ->
    NoDupA (M.eq_key (elt:=A)) l.
  Proof.
    induction l; intros; auto.
    inversion H.
    unfold M.eq_key in *.
    unfold eq_key in *.
    subst.
    apply NoDupA_cons; auto.
    intuition.
    rewrite InA_altdef in *.
    rewrite Exists_exists in *.
    destruct H0 as (?, (?, ?)).
    eauto.
  Qed.

  Let unproj_0_nodupa:
    forall l,
    NoDupA (M.eq_key (elt:=list S.E.t)) (unproj_0 l).
  Proof.
    eauto using nodupa_unproj.
  Qed.

  Let unproj_1 l := map (fun p => (fst p, S_Props.of_list (snd p))) (unproj_0 l).

  Let s_ina_to_in:
    forall v vs,
    (InA S.E.eq v vs <-> In v vs).
  Proof.
    intros.
    split; intros; rewrite InA_altdef in *; rewrite Exists_exists in *.
    - destruct H as (x, (Hin, Heq)).
      apply elem_eq_rw in Heq.
      subst; assumption.
    - eauto.
  Qed.

  Let unproj_1_spec:
    forall k v l,
    (List.In (k, v) l <-> exists s, List.In (k, s) (unproj_1 l) /\ S.In v s).
  Proof.
    intros.
    unfold unproj_1.
    split; intros.
    - rewrite unproj_0_spec in H.
      destruct H as (l', (Hkv, Hin)).
      assert (S.In v (S_Props.of_list l')). {
        apply S_Props.of_list_1.
        apply s_ina_to_in.
        assumption.
      }
      exists (S_Props.of_list l').
      split; auto.
      apply in_map_iff.
      exists (k, l').
      auto.
    - destruct H as (s, (Hkv, Hin)).
      apply in_map_iff in Hkv.
      destruct Hkv as ((k', l'), (Heq, Hin_l)).
      inversion Heq.
      simpl in *.
      subst.
      clear Heq.
      apply S_Props.of_list_1 in Hin.
      rewrite s_ina_to_in in Hin.
      rewrite unproj_0_spec.
      eauto.
  Qed.

  Let in_unproj_1_to_in:
    forall v s k l,
    S.In v s ->
    List.In (k, s) (unproj_1 l) ->
    List.In (k, v) l.
  Proof.
    intros.
    assert (exists s, List.In (k, s) (unproj_1 l) /\ S.In v s) by eauto.
    apply unproj_1_spec in H1; auto.
  Qed.

  Let unproj_1_nodupa:
    forall l,
    NoDupA (M.eq_key (elt:=S.t)) (unproj_1 l).
  Proof.
    intros.
    unfold unproj_1.
    assert (Hx:= unproj_0_nodupa l).
    remember (unproj_0 l).
    eapply List.nodupa_map; eauto.
    intros.
    destruct a1, a2.
    auto.
  Qed.

  Definition unproject l := M_Props.of_list (unproj_1 l).

  Let ina_to_in
    (k_eq_subst : forall e1 e2, M.E.eq e1 e2 <-> e1 = e2)
    :
    forall {elt:Type} k v l,
    InA (M.eq_key (elt:=elt)) (k, v) l ->
    exists v', In (k, v') l.
  Proof.
    intros.
    rewrite InA_altdef in *.
    rewrite Exists_exists in *.
    destruct H as ((k',v'), (Hin, Heq)).
    unfold eq_key,M.eq_key in *.
    simpl in Heq; subst.
    exists v'.
    apply k_eq_subst in Heq.
    subst.
    auto.
  Qed.

  Let in_to_ina:
    forall {elt:Type} k v l,
    In (k, v) l ->
    InA (M.eq_key (elt:=elt)) (k, v) l.
  Proof.
    unfold M.eq_key.
    intros.
    rewrite InA_altdef.
    rewrite Exists_exists.
    exists (k, v).
    intuition.
  Qed.

  Theorem unproject_spec:
    forall k v l,
    (List.In (k, v) l <-> exists s, M.MapsTo k s (unproject l) /\ S.In v s).
  Proof.
    unfold unproject.
    intros.
    split; intros.
    - rewrite unproj_1_spec in H.
      destruct H as (s, (Hkv, Hin)).
      exists s.
      intuition.
      apply M_Extra.in_elements_impl_maps_to.
      apply M_Extra.to_list_of_list; auto.
      intros.
      split; intros; subst; auto using M.E.eq_refl.
    - destruct H as (s, (Hmt, Hin)).
      apply M_Props.of_list_1 in Hmt; auto.
      apply in_unproj_1_to_in with (s:=s); repeat auto.
      rewrite InA_altdef in *.
      rewrite Exists_exists in *.
      destruct Hmt as ((k',s'), (Hin', Heq)).
      unfold M.eq_key_elt in Heq.
      destruct Heq as (Heq1, Heq2).
      simpl in *.
      apply key_eq_rw in Heq1.
      subst.
      intuition.
  Qed.
  End Defs.
End Project.


Module ProjectList (M:FMapInterface.WS).
  Module M_Props := FMapFacts.Properties M.
  Module M_Extra := MapUtil M.
  Section Defs.

  Variable A:Type.
  Let proj_edges  (e:(M.E.t * list A)) :=
  let (k, l) := e in List.map (fun v=> (k, v)) l.

  Definition project m : list (M.E.t * A) :=
    List.flat_map proj_edges (M.elements m).

  Variable k_eq_subst: forall e1 e2, M.E.eq e1 e2 <-> e1 = e2.

  Theorem project_spec:
    forall k e m,
    (forall k1 k2, M.E.eq k1 k2 -> k1 = k2) ->
    (List.In (k,e) (project m) <-> (exists (s:list A), M.MapsTo k s m  /\ List.In e s)).
  Proof.
    unfold project.
    intros k e m Heq2.
    split.
    - intros.
      rewrite List.in_flat_map in *.
      unfold proj_edges in *.
      destruct H as ((r', ts), (H1, H2)).
      rewrite List.in_map_iff in H2.
      destruct H2 as (t'', (H2, H3)).
      inversion H2; subst; clear H2.
      eauto using M_Extra.in_elements_impl_maps_to.
    - intros.
      destruct H as (s, (Hmt, Hin)).
      rewrite in_flat_map.
      unfold proj_edges.
      exists (k, s).
      intuition.
      + rewrite <- M_Extra.maps_to_iff_in_elements; auto.
      + rewrite in_map_iff; eauto.
  Qed.

  Notation edge := (M.E.t * A)%type.

  Variable value_eq_dec:
    forall (e1 e2:A),
    {e1 = e2} + {e1 <> e2}.

  Let key_eq_dec:
    forall (e1 e2:M.E.t),
    {e1 = e2} + {e1 <> e2}.
  Proof.
    intros.
    destruct (M.E.eq_dec e1 e2).
    + left.
      apply k_eq_subst; assumption.
    + right.
      intuition.
      apply k_eq_subst in H.
      contradiction n.
  Qed.

  Let unproj_0 (l:list edge) : list (M.E.t * (list A)) := unproj key_eq_dec l.

  Let unproj_0_spec :
    forall k v l,
    (List.In (k, v) l <-> exists l', List.In (k, l') (unproj_0 l) /\ In v l').
  Proof.
    intros.
    split.
    - intros.
      rewrite unproj_spec with (key_eq_dec:=key_eq_dec) in H; auto using value_eq_dec.
    - intros; rewrite unproj_spec with (key_eq_dec:=key_eq_dec); auto.
  Qed.

  Let nodupa_conv:
    forall {A:Type} l,
    NoDupA (eq_key (A:= A)) l ->
    NoDupA (M.eq_key (elt:=A)) l.
  Proof.
    intros.
    induction l.
    - auto.
    - inversion H.
      subst.
      apply NoDupA_cons; auto.
      intuition.
      rewrite InA_altdef in *.
      rewrite Exists_exists in *.
      destruct H0 as (s, (Hin, Heq)).
      apply H2.
      unfold M.eq_key in *.
      unfold eq_key.
      exists s.
      intuition.
      apply k_eq_subst.
      assumption.
  Qed.

  Let unproj_0_nodupa:
    forall l,
    NoDupA (M.eq_key (elt:=list A)) (unproj_0 l).
  Proof.
    unfold unproj_0.
    auto using nodupa_unproj, nodupa_conv.
  Qed.

  Let in_unproj_0_to_in:
    forall v s k l,
    List.In v s ->
    List.In (k, s) (unproj_0 l) ->
    List.In (k, v) l.
  Proof.
    intros.
    assert (exists s, List.In (k, s) (unproj_0 l) /\ List.In v s) by eauto.
    apply unproj_0_spec in H1.
    auto.
  Qed.

  Definition unproject l := M_Props.of_list (unproj_0 l).

  Theorem unproject_spec:
    forall k v l,
    (List.In (k, v) l <-> exists s, M.MapsTo k s (unproject l) /\ List.In v s).
  Proof.
    intros.
    unfold unproject.
    split.
    - intros.
      rewrite unproj_0_spec in H.
      destruct H as (s, (Hkv, Hin)).
      eauto using M_Extra.in_elements_impl_maps_to, M_Extra.to_list_of_list. 
    - intros.
      destruct H as (s, (Hmt, Hin)).
      apply M_Props.of_list_1 in Hmt; auto.
      apply in_unproj_0_to_in with (s:=s); repeat auto.
      rewrite InA_altdef in Hmt.
      rewrite Exists_exists in Hmt.
      destruct Hmt as ((k',s'), (Hin', Heq)).
      unfold M.eq_key_elt in Heq.
      destruct Heq as (Heq1, Heq2).
      simpl in *.
      apply k_eq_subst in Heq1.
      subst.
      assumption.
  Qed.
  End Defs.
End ProjectList.
