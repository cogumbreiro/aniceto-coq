Set Implicit Arguments.

Require Import Aniceto.Graphs.Graph.

Require Import Coq.Lists.List.

Section Defs.
  Variable A:Type.

  Variable Lt: A -> A -> Prop.

  Variable lt_trans:
    forall (x y z: A),
    Lt x y ->
    Lt y z ->
    Lt x z.

  Notation Edge := (prod_curry Lt).

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

Require Import Aniceto.Graphs.FGraph.

Section Finite.
  Variable A:Type.

  Variable Lt: A -> A -> Prop.

  Definition LtEdge (e:A*A) := let (x,y) := e in Lt x y.

  Definition Edge es (e:A*A) := List.In e es.

  Definition DAG es := Forall LtEdge es.

  Lemma dag_to_forall_lt:
    forall es,
    DAG es ->
    Forall LtEdge es.
  Proof.
    intros.
    induction H.
    - apply Forall_nil.
    - auto using Forall_cons.
  Qed.

  Lemma dag_in_to_lt:
    forall es x y,
    DAG es ->
    List.In (x,y) es ->
    Lt x y.
  Proof.
    intros.
    apply dag_to_forall_lt in H.
    rewrite Forall_forall in H.
    apply H in H0.
    auto.
  Qed.

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

  Lemma dag_reaches_to_lt:
    forall es x y,
    DAG es ->
    Reaches (Edge es) x y ->
    Lt x y.
  Proof.
    intros.
    inversion H0; eauto using dag_walk_to_lt.
  Qed.

  Variable lt_irrefl:
    forall x,
    ~ Lt x x.

  Lemma dag_irrefl:
    forall es x,
    DAG es ->
    ~ Reaches (Edge es) x x.
  Proof.
    intros.
    intuition.
    inversion H0.
    eauto using dag_walk_to_lt.
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


  Lemma dag_asymm:
    forall es x y,
    DAG es ->
    Reaches (Edge es) x y ->
    ~ Reaches (Edge es) y x.
  Proof.
    intros.
    unfold not; intros.
    assert (C: ~ Reaches (Edge es) x x) by eauto using dag_irrefl.
    contradiction C.
    eauto using reaches_trans.
  Qed.

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

Section Props.
  Lemma dag_impl:
    forall {A:Type} (E F: A -> A -> Prop),
    (forall x y, E x y -> F x y ) ->
    forall es,
    DAG E es ->
    DAG F es.
  Proof.
    unfold DAG in *.
    intros.
    apply Forall_impl with (P:=LtEdge E); auto.
    intros.
    destruct a as (x,y).
    simpl in *; auto.
  Qed.

  Lemma dag_incl:
    forall {A:Type} (E:A->A->Prop) es es',
    DAG E es ->
    incl es' es ->
    DAG E es'.
  Proof.
    intros.
    unfold DAG in *.
    rewrite Forall_forall in *.
    unfold incl in *.
    eauto.
  Qed.

  Section find_o.
  Variable A:Type.
  Variable eq_dec: forall (x y:A), {x = y} + {x <> y}.
  Variable Lt : A -> A -> Prop.

  Let fst_eq x (e:A*A) := if eq_dec (fst e) x then true else false.

  Let fst_eq_true:
    forall x e,
    fst_eq x e = true ->
    fst e = x.
  Proof.
    intros.
    unfold fst_eq in *.
    destruct (eq_dec (fst e) x); auto.
    inversion H.
  Qed.

  Let fst_eq_false:
    forall x e,
    fst_eq x e = false ->
    fst e <> x.
  Proof.
    intros.
    unfold fst_eq in *.
    destruct (eq_dec (fst e) x); auto.
    inversion H.
  Qed.

  Require Import Coq.Lists.List.
  Require Import Aniceto.List.

  Let find_fst_eq_some:
    forall x es e,
    find (fst_eq x) es = Some e ->
    List.In e es /\ fst e = x.
  Proof.
    intros.
    apply List.find_some_spec in H.
    destruct H.
    apply fst_eq_true in H0.
    intuition.
  Qed.

  Require Import Aniceto.Pair.

  Let edge_eq_dec := pair_eq_dec eq_dec.

  Let find_outgoing x (es:list(A*A)) :=
  find (fst_eq x) es.

  Let find_outgoing_some:
    forall x x' y es,
    find_outgoing x es = Some (x',y) ->
    List.In (x,y) es /\ x' = x.
  Proof.
    intros.
    unfold find_outgoing in H.
    apply find_fst_eq_some in H.
    destruct H.
    intuition.
    simpl in *; subst; auto.
  Qed.

  Let find_outgoing_none:
    forall x es,
    find_outgoing x es = None ->
    forall y z, List.In (y,z) es -> y <> x.
  Proof.
    intros.
    unfold find_outgoing in *.
    remember (find _ _).
    destruct o.
    - inversion H.
    - clear H.
      symmetry in Heqo.
      unfold not; intros; subst.
      apply find_none_impl_existsb in Heqo.
      rewrite existsb_forallb in Heqo.
      rewrite Bool.negb_false_iff in Heqo.
      rewrite forallb_forall in Heqo.
      apply Heqo in H0.
      rewrite Bool.negb_true_iff in H0.
      apply fst_eq_false in H0; simpl in *.
      contradiction H0; trivial.
  Qed.

  Let rm_edge e es := remove edge_eq_dec e es.

  Let find_outgoing_some_lt:
    forall x es e,
    find_outgoing x es = Some e ->
    length (rm_edge e es) < length es.
  Proof.
    intros.
    unfold find_outgoing in *.
    apply find_some_spec in H.
    destruct H.
    unfold rm_edge.
    auto using remove_in_length_lt.
  Qed.

  Function find_path x es { measure length es } : list (A*A)  :=
  match find_outgoing x es with
  | Some (x',y) => (x',y) :: find_path y (rm_edge (x',y) es)
  | None => nil
  end.
  Proof.
    intros.
    eauto using find_outgoing_some_lt.
  Qed.

  Let find_path_starts_with:
    forall x es w,
    find_path x es = w ->
    w <> nil ->
    StartsWith w x.
  Proof.
    intros.
    destruct w; rewrite find_path_equation in H.
    - contradiction H0; trivial.
    - clear H0.
      remember (find_outgoing _ _).
      symmetry in Heqo.
      destruct o.
      + destruct p0 as (a,b).
        inversion H; subst; clear H.
        apply find_outgoing_some in Heqo.
        destruct Heqo.
        subst.
        auto using starts_with_def.
      + inversion H.
  Qed.

  Let find_path_nil:
    forall w x,
    find_path x w = nil ->
    forall y z, List.In (y,z) w -> y <> x.
  Proof.
    induction w; intros; subst.
    - inversion H0.
    - rewrite find_path_equation in H.
      remember (find_outgoing _ _).
      destruct o.
      + destruct p.
        inversion H.
      + clear H.
        symmetry in Heqo.
        assert (Hx := find_outgoing_none _ Heqo).
        eauto.
  Qed.

  Let find_path_rw_nil:
    forall x w,
    find_path x nil = w ->
    w = nil.
  Proof.
    intros.
    rewrite find_path_equation in *.
    remember (find_outgoing _ _).
    symmetry in Heqo.
    destruct o.
    - destruct p as (a,b).
      apply find_outgoing_some in Heqo.
      destruct Heqo.
      inversion H0.
    - auto.
  Qed.

  Let find_path_connected:
    forall l es x,
    find_path x es = l ->
    Connected l.
  Proof.
    induction l; intros; auto using connected_nil.
    rewrite find_path_equation in H.
    remember (find_outgoing _ _ ).
    symmetry in Heqo.
    destruct o.
    - destruct p as (v1,v2).
      apply find_outgoing_some in Heqo.
      destruct Heqo; subst.
      inversion H; subst; clear H.
      remember (find_path _ _).
      symmetry in Heql.
      destruct l. {
        auto using connected_cons, linked_nil, connected_nil.
      }
      assert (Connected (p::l)) by eauto.
      destruct p as (v2', v3).
      assert (S: StartsWith ((v2',v3)::l) v2). {
        assert ((v2',v3)::l <> nil) . {
          unfold not; intros.
          inversion H1.
        }
        eauto using find_path_starts_with.
      }
      apply starts_with_eq in S; subst.
      auto using connected_cons, linked_eq.
    - inversion H.
  Qed.

  Let find_path_incl:
    forall w es x,
    find_path x es = w ->
    incl w es.
  Proof.
    induction w; intros; remember (find_path _ _); symmetry in Heql. {
      subst.
      auto using incl_nil_any.
    }
    subst.
    rewrite find_path_equation in H.
    remember (find_outgoing _ _ ).
    symmetry in Heqo.
    destruct o.
    - destruct p as (v1,v2).
      inversion H; clear H.
      apply find_outgoing_some in Heqo; destruct Heqo.
      rewrite H0 in *; clear H0.
      clear H1.
      assert (incl w (rm_edge (x,v2) es)) by eauto.
      rewrite H2.
      apply incl_cons; auto.
      unfold rm_edge in *.
      assert (incl (remove edge_eq_dec (x, v2) es) es) by eauto using remove_incl.
      eauto using incl_tran.
    - inversion H.
  Qed.

  Let find_path_to_walk:
    forall l es x,
    find_path x es = l ->
    Walk (Edge es) l.
  Proof.
    intros.
    apply walk_def.
    - apply Forall_forall; intros.
      apply find_path_incl in H.
      unfold Edge.
      unfold incl in *; auto.
    - eauto using find_path_connected.
  Qed.

  Let find_path_to_walk2:
    forall x es w y,
    find_path x es = w ->
    EndsWith w y ->
    Walk2 (Edge es) x y w.
  Proof.
    intros.
    eauto using walk2_def, find_path_to_walk, find_path_starts_with, ends_with_non_nil.
  Qed.

  Let find_path_to_reaches:
    forall x es w y,
    find_path x es = w ->
    EndsWith w y ->
    Reaches (Edge es) x y.
  Proof.
    intros.
    eauto using reaches_def, find_path_to_walk2.
  Qed.

  Variable lt_irefl: forall x, ~ Lt x x.
  Variable lt_trans: forall x y z, Lt x y -> Lt y z -> Lt x z.

  Let dag_impl_rm_edge:
    forall E es,
    DAG E es ->
    forall e,
    DAG E (rm_edge e es).
  Proof.
    intros.
    unfold DAG in *.
    rewrite Forall_forall in *.
    intros.
    unfold rm_edge in *.
    eauto using remove_in.
  Qed.

  Let find_path_cons_nil:
    forall es x x' z,
    DAG Lt es ->
    find_path x es = (x', z) :: nil ->
    x' = x /\ forall e, List.In e es -> fst e <> z.
  Proof.
    intros.
    rewrite find_path_equation in *.
    remember (find_outgoing _ _).
    symmetry in Heqo.
    destruct o.
    - destruct p as (x'', z').
      apply find_outgoing_some in Heqo.
      destruct Heqo.
      inversion H0; repeat subst; clear H0.
      split; auto.
      intros (e1,e2); intros; simpl.
      destruct (pair_eq_dec eq_dec (e1,e2) (x',z)).
      + inversion e; subst; clear e.
        unfold not; intros; subst.
        assert (n: ~ Lt z z) by eauto.
        contradiction n.
        apply dag_in_to_lt with (Lt:=Lt) in H1; auto.
      + apply find_path_nil with (y:=e1) (z:=e2) in H6; auto.
        unfold rm_edge.
        auto using remove_in_neq.
    - inversion H0.
  Qed.

  Let find_path_some:
    forall w (x y:A) es,
    DAG Lt es ->
    find_path x es = w ->
    find_ends_with w = Some y ->
    forall e, List.In e es -> fst e <> y.
  Proof.
    induction w; intros. {
      unfold find_ends_with in *.
      rewrite find_end_rw_nil in H1.
      inversion H1.
    }
    destruct a as (v1,v2).
    destruct w. {
      apply find_ends_with_some in H1.
      apply ends_with_eq in H1.
      subst.
      apply find_path_cons_nil in H0; auto.
      destruct H0.
      subst.
      auto.
    }
    rewrite find_path_equation in *.
    remember (find_outgoing _ _).
    symmetry in Heqo.
    destruct o.
    - destruct p0 as (a,b).
      inversion H0; subst; clear H0.
      destruct (pair_eq_dec eq_dec e (v1,v2)).
      + subst.
        simpl.
        unfold not; intros; subst.
        apply find_outgoing_some in Heqo.
        destruct Heqo; subst.
        assert (n: ~ Lt x x) by eauto.
        contradiction n.
        assert (Reaches (Edge es) v2 x). {
          assert (Walk2 (Edge es) v2 x (p::w)). {
            assert (Walk2 (Edge (rm_edge (x,v2) es)) v2 x (p::w)) by
            eauto using find_path_to_walk2, find_ends_with_some, dag_impl_rm_edge, ends_with_inv.
            apply walk2_impl with (E:=Edge (rm_edge (x, v2) es)); auto.
            intros.
            unfold Edge in *; simpl in *.
            unfold rm_edge in *.
            eauto using remove_in.
          }
          eauto using reaches_def.
        }
        assert (Reaches (Edge es) x v2) by
        eauto using reaches_def, edge_to_walk2.
        assert (Reaches (Edge es) x x) by
        eauto using reaches_trans.
        apply dag_reaches_to_lt with (es:=es); auto.
      + eauto using find_ends_with_cons_cons_2, remove_in_neq.
    - inversion H0.
  Qed.

  Let find_path_cons:
    forall v1 v2 es w,
    find_path v1 ((v1,v2)::es) = w ->
    StartsWith w v1.
  Proof.
    intros.
    rewrite find_path_equation in *.
    remember (find_outgoing _ _).
    symmetry in Heqo.
    destruct o as [(?,?)|?]. {
      apply find_outgoing_some in Heqo.
      destruct Heqo.
      subst.
      auto using starts_with_def.
    }
    apply find_outgoing_none with (y:=v1) (z:=v2) in Heqo; auto using in_eq.
    contradiction Heqo; trivial.
  Qed.

  Let dag_find_path:
    forall w es x y,
    DAG Lt es ->
    find_path x es = w ->
    EndsWith w y ->
    forall z, ~ Reaches (Edge es) y z.
  Proof.
    intros.
    apply ends_with_to_find_ends_with in H1.
    assert (X: forall e, List.In e es -> fst e <> y) by eauto.
    unfold not; intros.
    assert (Y: exists (v:A), In (y,v) es). {
      inversion H2.
      inversion H3; subst.
      inversion H4.
      destruct H0 as (w', (?,?)); subst.
      destruct x0 as (v1,v2).
      simpl in *.
      exists v2.
      assert (Edge es (v1,v2)). {
        apply walk_to_edge with (w:=(v1,v2)::w'); auto.
        auto using in_eq.
      }
      unfold Edge in *.
      auto.
    }
    destruct Y.
    apply X in H3.
    simpl in H3; contradiction H3; trivial.
  Qed.

  Let find_outgoing_rw_cons:
    forall v1 v2 es,
    find_outgoing v1 ((v1, v2) :: es) = Some (v1, v2).
  Proof.
    intros.
    unfold find_outgoing.
    simpl.
    remember (fst_eq v1 (v1,v2)).
    symmetry in Heqb.
    destruct b; simpl in *; auto.
    apply fst_eq_false in Heqb.
    simpl in *; contradiction Heqb; auto.
  Qed.

  Let find_path_rw_cons:
    forall v1 v2 es p l,
    find_path v1 ((v1, v2) :: es) = p :: l ->
    p = (v1, v2).
  Proof.
    intros.
    rewrite find_path_equation in H.
    rewrite find_outgoing_rw_cons in *.
    inversion H; auto.
  Qed.

  Lemma dag_supremum:
    forall es,
    DAG Lt es ->
    es <> nil ->
    exists x, Graph.In (Edge es) x /\ forall y, ~ Reaches (Edge es) x y.
  Proof.
    intros.
    destruct es. {
      contradiction H0; trivial.
    }
    destruct p as (v1,v2).
    remember (find_path v1 ((v1,v2)::es)).
    symmetry in Heql.
    destruct l. {
      apply find_path_nil with (y:=v1) (z:=v2) in Heql; auto using in_eq.
      intros.
      contradiction Heql; trivial.
    }
    assert (X:=Heql).
    apply find_path_cons in Heql.
    assert (Y: exists (y:A), EndsWith (p::l) y). {
      assert (p :: l <> nil). {
        intuition;subst.
        inversion H1.
      }
      auto using ends_with_neq_nil.
    }
    destruct Y as (y, Y).
    exists y.
    split; eauto.
    inversion Y as ((e1,e2),(?,?)); subst; simpl in *.
    assert (p = (v1,v2)) by eauto; subst.
    apply in_def with (e:=(e1,e2)).
    - auto using pair_in_right.
    - unfold Edge.
      assert (I: incl ((v1, v2) :: l) ((v1, v2) :: es)) by eauto.
      unfold incl in *.
      apply end_in in H1.
      eauto.
  Qed.
  End find_o.

End Props.