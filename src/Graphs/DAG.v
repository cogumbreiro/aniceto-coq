Set Implicit Arguments.

Require Import Aniceto.Graphs.Graph.

Section Defs.
  Variable A:Type.

  Variable Lt: A -> A -> Prop.

  Variable lt_trans:
    forall (x y z: A),
    Lt x y ->
    Lt y z ->
    Lt x z.

  Notation Edge := (fun e => let (x,y) := e in Lt x y).

  Lemma walk_to_lt:
    forall w x y,
    Walk2 Edge x y w ->
    Lt x y.
  Proof.
    induction w; intros. {
      apply walk2_nil_inv in H.
      inversion H.
    }
    destruct a as (x',z).
    destruct w. {
      apply walk2_inv_pair in H.
      destruct H.
      inversion H; subst; clear H.
      assumption.
    }
    apply walk2_inv in H.
    destruct H as (z', (He, (Hi, Hw))).
    inversion He; subst; clear He; rename z' into z.
    assert (Lt z y) by eauto.
    eauto.
  Qed.
End Defs.

Section Finite.
  Require Import Coq.Lists.List.
  Variable A:Type.

  Variable Lt: A -> A -> Prop.

  Definition LtEdge (e:A*A) := let (x,y) := e in Lt x y.

  Definition DAG := (Forall LtEdge).

  Lemma dag_in_to_lt:
    forall es,
    DAG es ->
    forall x y,
    List.In (x, y) es ->
    Lt x y.
  Proof.
    induction es; intros. {
      inversion H0.
    }
    inversion H; subst; clear H.
    destruct H0. {
      inversion H; subst; auto.
    }
    eauto.
  Qed.

  Lemma make_dag:
    forall es,
    (forall x y, List.In (x,y) es -> Lt x y) ->
    DAG es.
  Proof.
    intros.
    unfold DAG; rewrite Forall_forall.
    unfold LtEdge.
    intros; destruct x.
    auto.
  Qed.

  Notation Edge := (fun g e => @List.In (A*A) e g) %type.

  Require Import Aniceto.Graphs.Graph.

  Variable lt_trans:
    forall (x y z: A),
    Lt x y ->
    Lt y z ->
    Lt x z.

  Lemma dag_walk_to_lt:
    forall es,
    DAG es ->
    forall w x y,
    Walk2 (Edge es) x y w ->
    Lt x y.
  Proof.
    intros.
    apply walk_to_lt with (w:=w); eauto.
    apply walk2_impl with (E:=Edge es); auto.
    intros.
    destruct e as (a,b); simpl.
    eauto using dag_in_to_lt.
  Qed.

  Definition UpperBound max :=
  List.Forall (fun (e:A*A)=> let (x,y) := e in Lt x max /\ Lt y max).

  Lemma upper_bound:
    forall (max a b:A) l,
    UpperBound max l ->
    List.In (a,b) l ->
    Lt a max /\ Lt b max.
  Proof.
    unfold UpperBound.
    intros.
    rewrite Forall_forall in H.
    apply H in H0.
    auto.
  Qed.

  Variable lt_irrefl:
    forall x,
    ~ Lt x x.

  Let dag_cons_inv:
    forall a b es,
    DAG es ->
    UpperBound b es ->
    Lt a b ->
    forall w,
    Walk (Edge ((a,b)::es)) w ->
    End w (a,b) \/ ~ List.In (a,b) w.
  Proof.
    induction w; intros. {
      eauto.
    }
    inversion H2; subst.
    assert (W:=H5).
    apply IHw in H5; clear H2 IHw.
    destruct H5 as [?|?].
    - left; auto using end_cons.
    - destruct a0 as (x,y).
      destruct H6. {
        inversion H3; subst; clear H3.
        left.
        destruct w; auto using end_nil.
        (* absurd *)
        destruct p as (y',z).
        apply linked_inv in H7; subst.
        apply walk_to_forall in W.
        assert (i:List.In (y,z) ((y,z)::w)) by eauto using in_eq.
        rewrite Forall_forall in W.
        apply W in i.
        destruct i as [i|i].
        - inversion i; subst.
          apply lt_irrefl in H1.
          contradiction.
        - apply upper_bound with (max:=y) in i; auto.
          destruct i as (i,_).
          apply lt_irrefl in i.
          contradiction.
      }
      right.
      unfold not; intros.
      destruct H4.
      + inversion H4; subst; clear H4.
        apply upper_bound with (max:=b) in H3; auto.
        destruct H3 as (?,n).
        apply lt_irrefl in n.
        contradiction.
      + contradiction. 
  Qed.

  Let dag_cons_inv_2:
    forall a b es,
    DAG es ->
    UpperBound b es ->
    Lt a b ->
    forall w,
    Walk (Edge ((a,b)::es)) (w ++ ((a,b)::nil)) ->
    ~ List.In (a,b) w.
  Proof.
    induction w; intros. {
      (* absurd *)
      intuition.
    }
    inversion H2; subst.
    assert (W:=H5).
    apply IHw in H5; clear IHw.
    assert ((a,b) <> a0). {
      unfold not; intros; subst; clear H6.
      destruct w. {
        simpl in H7.
        apply linked_inv in H7.
        subst.
        apply lt_irrefl in H1.
        contradiction.
      }
      destruct p as (b',c).
      apply linked_inv in H7.
      subst.
      assert (List.In (b,c) ((a,b)::es)). {
        apply walk_to_edge with (e:=(b,c)) in W; simpl; auto using in_eq.
      }
      destruct H3. {
        inversion H3; subst.
        apply lt_irrefl in H1.
        contradiction.
      }
      apply upper_bound with (max:=b) in H3; auto.
      destruct H3 as (n, _).
      apply lt_irrefl in n.
      contradiction.
    }
    unfold not; intros.
    destruct H4. {
      subst.
      contradiction H3; trivial.
    }
    contradiction.
  Qed.

  Let dag_impl_simpl:
    forall a b es w,
    Walk (Edge ((a,b)::es)) w ->
    ~ List.In (a,b) w ->
    Walk (Edge es) w.
  Proof.
    intros.
    apply walk_impl_weak with (E:=Edge ((a, b) :: es)); auto; intros.
    destruct H2.
    - subst.
      contradiction.
    - auto.
  Qed.

  Lemma dag_walk2_inv_cons_edge:
    forall a b es,
    DAG es ->
    UpperBound b es ->
    Lt a b ->
    forall w x y,
    Walk2 (Edge ((a,b)::es)) x y w ->
    w = ((a,b) :: nil) \/ 
    (exists w', (w = w' ++ ((a,b)::nil)) /\ Walk2 (Edge es) x a w' /\ y = b) \/
    Walk2 (Edge es) x y w.
  Proof.
    intros.
    assert (W2:=H2).
    inversion H2; subst; clear H2.
    assert (X: End w (a,b) \/ ~ List.In (a,b) w) by eauto.
    destruct X. {
      apply end_to_append in H2.
      destruct H2 as (w', rw).
      subst.
      assert (W:=H5).
      apply dag_cons_inv_2 in H5; auto.
      apply walk_split in W.
      destruct W as [?|(?,(?,?))]. {
        subst.
        simpl in *.
        eauto.
      }
      apply dag_impl_simpl in H6; auto; clear H5.
      apply ends_with_inv_append in H4; subst.
      destruct w'. {
        simpl in *.
        eauto.
      }
      right; left.
      destruct p as (x',v).
      apply starts_with_eq in H3; subst.
      exists ((x,v)::w').
      intuition.
      auto using starts_with_def, walk2_def.
    }
    right; right.
    apply dag_impl_simpl in H5; auto.
    auto using walk2_def.
  Qed.
End Finite.
