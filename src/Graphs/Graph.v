Require Import Coq.Lists.List.

Require Import Aniceto.Tactics.
Require Import Aniceto.Pair.

Set Implicit Arguments.

Section Walk.
Variable Implicit A:Type.
Notation edge := (A*A)%type.
Notation walk := (list edge).

Definition head (e:edge) : A := fst e.
Definition tail (e:edge) : A := snd e.
Definition walk_head (default:A) (w:walk) : A := head (List.hd (default, default) w).

Definition Linked e w := tail e = walk_head (tail e) w.

Lemma linked_nil:
  forall e,
  Linked e nil.
Proof.
  compute; auto.
Qed.

Lemma linked_eq:
  forall v1 v2 v3 w,
  Linked (v1,v2) ((v2,v3)::w).
Proof.
  compute;auto.
Qed.

Inductive Connected : walk -> Prop :=
  | connected_cons:
    forall e w,
    Connected w ->
    Linked e w ->
    Connected (e :: w)
  | connected_nil:
    Connected nil.

Lemma connected_inv:
  forall e w,
  Connected (e :: w) ->
  Linked e w.
Proof.
  intros.
  inversion H.
  subst.
  assumption.
Qed.


Inductive End : walk -> edge -> Prop :=
  | end_nil:
    forall e,
    End (e :: nil) e
  | end_cons:
    forall e e' w,
    End w e ->
    End (e'::w) e.

Lemma end_inv:
  forall e1 e2,
  End (e1 :: nil) e2 ->
  e1 = e2.
Proof.
  intros.
  inversion H.
  - reflexivity.
  - subst.
    inversion H3.
Qed.

Lemma end_inv_cons:
  forall e1 e2 e3 w,
  End (e1 :: e2 :: w) e3 ->
  End (e2 :: w) e3.
Proof.
  intros.
  inversion H.
  subst.
  assumption.
Qed.

Lemma end_total:
  forall e w,
  exists e', End (e :: w) e'.
Proof.
  intros.
  induction w.
  - exists e.
    apply end_nil.
  - destruct IHw as (e', H).
    inversion H; subst.
    + exists a.
      auto using end_cons, end_nil.
    + exists e'.
      auto using end_cons.
Qed.

Lemma end_inv2:
  forall v1 v2 v1' v2',
  End ((v1,v2) :: nil) (v1', v2') ->
  v1 = v1' /\ v2 = v2'.
Proof.
  intros.
  apply end_inv in H.
  inversion H.
  intuition.
Qed.

Lemma end_det:
  forall w e e',
  End w e ->
  End w e' ->
  e = e'.
Proof.
  intros.
  induction w.
  - inversion H.
  - inversion H; inversion H0; subst; auto.
    + inversion H7. (* absurd *)
    + inversion H4. (* absurd *)
Qed.

Lemma end_cons_eq:
  forall w e e' e'',
  End w e ->
  End (e' :: w) e'' ->
  e = e''.
Proof.
  intros.
  assert (H1 := end_cons e' H).
  eauto using end_det.
Qed.

Lemma end_in:
  forall w e,
  End w e ->
  In e w.
Proof.
  intros.
  induction w.
  - inversion H.
  - destruct w.
    + apply end_inv in H.
      subst.
      apply in_eq.
    + apply end_inv_cons in H.
      apply IHw in H; clear IHw.
      auto using in_cons.
Qed.

Definition StartsWith (w:walk) (v:A) :=
  exists e' w', w = e' :: w' /\ fst e' = v.

Definition EndsWith w (v:A) :=
  exists e, End w e /\ snd e = v.

Lemma ends_with_cons:
  forall w v e,
  EndsWith w v ->
  EndsWith (e :: w) v.
Proof.
  intros.
  unfold EndsWith in *.
  destruct H as (e', (H,H1)).
  exists e'.
  intuition.
  auto using end_cons.
Qed.

Lemma ends_with_nil_inv:
  forall v,
  EndsWith nil v ->
  False.
Proof.
  intros.
  unfold EndsWith in H.
  destruct H as (e, (H, ?)).
  inversion H.
Qed.

Lemma starts_with_def:
  forall v v' w,
  StartsWith ((v, v')::w) v.
Proof.
  intros.
  unfold StartsWith.
  exists (v, v').
  exists w.
  intuition.
Qed.

Lemma starts_with_inv_nil:
  forall (x:A),
  StartsWith nil x -> False.
Proof.
  intros.
  intuition.
  inversion H.
  destruct H0 as (w', Hx).
  destruct Hx.
  inversion H0.
Qed.

Lemma ends_with_def:
  forall v v' w,
  End w (v', v) ->
  EndsWith w v.
Proof.
  intros.
  unfold EndsWith.
  exists (v', v).
  intuition.
Qed.


Lemma starts_with_eq:
  forall v1 v1' v2 w,
  StartsWith ((v1', v2) :: w) v1 ->
  v1' = v1.
Proof.
  intros.
  inversion H.
  destruct H0 as (?, (?, ?)).
  destruct x.
  inversion H0.
  auto.
Qed.

Lemma ends_with_eq:
  forall (v1 v2 v2':A),
  EndsWith ((v1, v2') :: nil) v2 ->
  v2' = v2.
Proof.
  intros.
  unfold EndsWith in *.
  destruct H as ((v1', v2''), (?, ?)).
  apply end_inv2 in H; repeat auto.
  destruct H.
  simpl in *.
  subst.
  trivial.
Qed.

Lemma ends_with_inv:
  forall e1 e2 w (v:A),
  EndsWith (e1 :: e2 :: w) v ->
  EndsWith (e2 :: w) v.
Proof.
  intros.
  unfold EndsWith in *.
  destruct H as (e, (?, ?)).
  exists e.
  intuition.
  inversion H.
  auto.
Qed.


  Lemma ends_with_fun:
    forall w (x y:A),
    EndsWith w x ->
    EndsWith w y ->
    x = y.
  Proof.
    intros.
    induction w. {
      apply ends_with_nil_inv in H0.
      inversion H0.
    }
    destruct w. {
      destruct a as (a, b).
      apply ends_with_eq in H.
      apply ends_with_eq in H0.
      subst.
      trivial.
    }
    eauto using ends_with_inv.
  Qed.

  Lemma ends_with_inv_cons_nil:
    forall (x y z:A),
    EndsWith ((x, y) :: nil) z ->
    y = z.
  Proof.
    intros.
    inversion H.
    destruct H0.
    apply end_inv in H0.
    subst.
    eauto.
  Qed.
  
  Lemma ends_with_edge:
    forall (x y:A),
    EndsWith ((x, y) :: nil) y.
  Proof.
    intros.
    eauto using ends_with_def, end_nil.
  Qed.

Lemma starts_with_to_linked:
  forall w v,
  StartsWith w v ->
  forall v',
  Linked (v', v) w.
Proof.
  intros.
  unfold Linked.
  unfold walk_head.
  simpl.
  destruct w.
  + auto.
  + destruct p.
    apply starts_with_eq in H.
    subst.
    auto.
Qed.

(* * * * * * * * * * * * * * * *)
Section EDGE.

Variable Edge : edge -> Prop.

Inductive Walk : walk -> Prop :=
  | walk_cons:
    forall e w,
    Walk w ->
    Edge e ->
    Linked e w ->
    Walk (e :: w)
  | walk_nil:
    Walk nil.

Lemma walk_to_connected:
  forall w,
  Walk w ->
  Connected w.
Proof.
  intros.
  induction w.
  - apply connected_nil.
  - inversion H.
    subst.
    apply IHw in H2.
    apply_auto connected_cons.
Qed.

Lemma walk_def:
  forall w,
  Forall Edge w ->
  Connected w ->
  Walk w.
Proof.
  intros.
  induction w.
  - apply walk_nil.
  - inversion H.
    subst.
    apply IHw in H4.
    + auto using walk_cons, connected_inv.
    + inversion H0; assumption.
Qed.

Lemma walk_to_forall:
  forall w,
  Walk w ->
  Forall Edge w.
Proof.
  intros.
  induction w.
  - auto.
  - apply Forall_cons; inversion H; subst; auto.
Qed.

Lemma walk_inv:
  forall w,
  Walk w ->
  Forall Edge w /\
  Connected w.
Proof.
  intros.
  split; 
  auto using walk_to_forall, walk_to_connected.
Qed.

Lemma walk_cons2:
  forall v1 v2 v3 w,
  Edge (v1, v2) ->
  Walk ((v2, v3) :: w) ->
  Walk ((v1, v2) :: (v2, v3) :: w).
Proof.
  intros.
  auto using walk_cons, linked_eq.
Qed.

Lemma edge_to_walk:
  forall e,
  Edge e ->
  Walk (e::nil).
Proof.
  intros.
  auto using walk_cons, walk_nil, linked_nil.
Qed.

Lemma edge_to_walk_cons_cons_nil:
  forall v1 v2 v3,
  Edge (v1, v2) ->
  Edge (v2, v3) ->
  Walk ((v1,v2)::(v2,v3)::nil).
Proof.
  auto using walk_cons, edge_to_walk, linked_eq.
Qed.

Lemma in_edge:
  forall e w,
  Walk w ->
  List.In e w ->
  Edge e.
Proof.
  intros.
  induction w.
  inversion H0.
  apply List.in_inv in H0.
  destruct H0; (
    subst;
    inversion H;
    auto).
Qed.


Lemma end_to_edge:
  forall w e,
  Walk w ->
  End w e ->
  Edge e.
Proof.
  intros.
  induction w.
  - inversion H0.
  - inversion H.
    subst.
    destruct w.
    + apply end_inv in H0.
      subst.
      assumption.
    + apply IHw; try inversion H0; auto.
Qed.

Inductive Walk2: A -> A -> list edge -> Prop :=
  walk2_def:
    forall v1 v2 w,
    StartsWith w v1 ->
    EndsWith w v2 ->
    Walk w ->
    Walk2 v1 v2 w.

Lemma walk2_nil_inv:
  forall v1 v2,
  Walk2 v1 v2 nil ->
  False.
Proof.
  intros.
  inversion H; subst; clear H.
  eauto using ends_with_nil_inv.
Qed.

Inductive Cycle: walk -> Prop :=
  cycle_def:
    forall v1 v2 vn w,
    End ((v1,v2) :: w) (vn, v1) ->
    Walk ((v1,v2) :: w) ->
    Cycle ((v1,v2) :: w).

Lemma cycle_inv:
  forall w,
  Cycle w ->
  exists v,
  StartsWith w v /\ EndsWith w v /\ Walk w.
Proof.
  intros.
  inversion H.
  exists v1.
  unfold StartsWith.
  unfold EndsWith.
  simpl.
  intuition.
  - exists (v1, v2).
    exists w0.
    auto.
  - exists (vn, v1).
    auto.
Qed.

Lemma cycle_def2:
  forall w v,
  StartsWith w v ->
  EndsWith w v ->
  Walk w ->
  Cycle w.
Proof.
  intros.
  destruct H as (e, (w', (x, y))).
  destruct e.
  destruct H0 as (e', (e_end, H0)).
  destruct e'.
  simpl in *.
  subst.
  eauto using cycle_def.
Qed.

Lemma walk_to_cycle_cons_nil:
  forall v,
  Walk ((v,v)::nil) ->
  Cycle ((v,v)::nil).
Proof.
  intros.
  eauto using cycle_def, end_nil.
Qed.

Lemma edge_to_cycle:
  forall v,
  Edge (v,v) ->
  Cycle ((v,v)::nil).
Proof.
  intros.
  apply edge_to_walk in H.
  auto using walk_to_cycle_cons_nil.
Qed.

Lemma walk_to_cycle_cons_cons_nil:
  forall v1 v2,
  Walk ((v1, v2) :: (v2, v1)::nil)%list ->
  Cycle ((v1, v2) :: (v2, v1)::nil)%list.
Proof.
  eauto using cycle_def, end_cons, end_nil.
Qed.

Lemma edge_to_cycle_cons_cons_nil:
  forall v1 v2,
  Edge (v1, v2) ->
  Edge (v2, v1) ->
  Cycle ((v1, v2) :: (v2, v1)::nil)%list.
Proof.
  auto using edge_to_walk_cons_cons_nil, walk_to_cycle_cons_cons_nil.
Qed.

Let list_inv:
  forall A x y,
  @In A x (y :: nil) ->
  x = y.
Proof.
  intros.
  inversion H.
  - subst. auto.
  - inversion H0.
Qed.

Lemma pred_in_walk:
  forall w v1 v2,
  Walk w ->
  List.In (v1, v2) w ->
  ((exists w', w = (v1,v2):: w') \/
  exists v3, List.In (v3, v1) w).
Proof.
  intros.
  induction H.
  - assert (Hin := H0).
    apply in_inv in H0.
    destruct H0 as [H0|H0].
    + subst.
      left.
      exists w.
      auto.
    + apply IHWalk in H0; clear IHWalk.
      destruct H0 as [(w',H0)|H0].
      * subst.
        destruct e as (v3, v1').
        compute in H2.
        subst.
        right.
        exists v3.
        apply in_eq.
      * destruct H0 as (v3, H0).
        right.
        exists v3.
        auto using in_cons.
  - inversion H0.
Qed.

Lemma succ_in_walk:
  forall w v1 v2,
  Walk w ->
  List.In (v1, v2) w ->
  (End w (v1, v2) \/ exists v3, List.In (v2, v3) w).
Proof.
  intros.
  induction H.
  - assert (Hin := H0).
    apply in_inv in H0.
    destruct H0.
    + subst.
      destruct w.
      * left; auto.
        apply end_nil.
      * right.
        compute in H2.
        destruct p as (v2', v3).
        rewrite <- H2 in *.
        exists v3.
        auto using in_cons, in_eq.
    + apply IHWalk in H0; clear IHWalk.
      destruct H0.
      * left; auto using end_cons.
      * destruct H0 as (v3, Hx).
        right.
        exists v3.
        auto using in_cons.
  - inversion H0.
Qed.

Lemma in_inv_nil:
  forall A e e',
  @In A e (e' :: nil) ->
  e = e'.
Proof.
  intros.
  inversion H.
  auto.
  inversion H0.
Qed.

Lemma pred_in_cycle:
  forall w v1 v2,
  Cycle w ->
  List.In (v1, v2) w ->
  exists v3, List.In (v3, v1) w.
Proof.
  intros.
  inversion H.
  subst.
  destruct w0.
  - apply end_inv in H1.
    inversion H1; subst; clear H1.
    apply in_inv_nil in H0.
    inversion H0; subst; clear H0.
    eauto using in_eq.
  - apply pred_in_walk with (v1:=v1) (v2:=v2) in H2; auto.
    destruct H2 as [(w,H2)|H2]; auto.
    * inversion H2; subst; clear H2.
      apply end_in in H1.
      eauto.
Qed.


Lemma succ_in_cycle:
  forall w v1 v2,
  Cycle w ->
  List.In (v1, v2) w ->
  exists v3, List.In (v2, v3) w.
Proof.
  intros.
  inversion H.
  subst.
  destruct w0.
  - apply end_inv in H1.
    inversion H1; subst; clear H1.
    apply in_inv_nil in H0.
    inversion H0; subst; clear H0.
    eauto using in_eq.
  - apply succ_in_walk with (v1:=v1) (v2:=v2) in H2; auto.
    destruct H2 as [H2|(v4, H2)]; eauto.
    apply end_det with (e:=(v1,v2)) in H1; auto.
    inversion H1; subst; clear H1.
    eauto using in_eq.
Qed.

Definition In (v:A) :=
  exists e, Edge e /\ pair_In v e.

Lemma in_def:
  forall v e,
  pair_In v e ->
  Edge e ->
  In v.
Proof.
  intros.
  unfold In.
  eauto.
Qed.

Lemma in_left:
  forall v v',
  Edge (v, v') ->
  In v.
Proof.
  intros.
  eauto using in_def, pair_in_left.
Qed.

Lemma in_right:
  forall v v',
  Edge (v', v) ->
  In v.
Proof.
  intros.
  eauto using in_def, pair_in_right.
Qed.

Lemma walk2_nil:
  forall v1 v2,
  Edge (v1, v2) ->
  Walk2 v1 v2 ((v1, v2)::nil).
Proof.
  intros.
  apply walk2_def;
  eauto using starts_with_def, ends_with_def, end_nil, edge_to_walk.
Qed.

Lemma edge_to_walk2:
  forall x y,
  Edge (x, y) ->
  Walk2 x y ((x, y) :: nil).
Proof.
  intros.
  apply walk2_def.
  + auto using starts_with_def.
  + auto using ends_with_edge.
  + auto using edge_to_walk.
Qed.

Lemma walk2_inv_cons:
  forall (v1 vn:A) e w,
  Walk2 v1 vn (e :: w) ->
  exists v2, e = (v1, v2) /\ Edge (v1, v2).
Proof.
  intros.
  destruct e as (v1', v2).
  inversion H.
  subst.
  exists v2.
  apply starts_with_eq in H0.
  inversion H2.
  subst.
  intuition.
Qed.

Lemma linked_inv:
  forall (v1 v2 v2' v3:A) w,
  Linked (v1, v2) ((v2', v3) :: w) ->
  v2' = v2.
Proof.
  intros.
  unfold Linked in *.
  unfold walk_head in *.
  auto.
Qed.

Lemma walk2_inv:
  forall (v1 vn:A) e e' w,
  Walk2 v1 vn (e :: e' :: w) ->
  exists v2, e = (v1, v2) /\ Edge (v1, v2) /\ Walk2 v2 vn (e' :: w).
Proof.
  intros.
  assert (Hx : exists v2 : A, e = (v1, v2) /\ Edge (v1, v2)). {
    eauto using walk2_inv_cons.
  }
  destruct Hx as (v2', (?, ?)).
  exists v2'; intuition.
  destruct e' as (v2, v3).
  inversion H; subst; clear H.
  inversion H4.
  apply linked_inv in H7.
  subst.
  eauto using walk2_def, starts_with_def, ends_with_inv.
Qed.

Lemma walk2_inv_pair:
  forall (v1 v2:A) e,
  Walk2 v1 v2 (e :: nil) ->
  e = (v1, v2) /\ Edge (v1, v2).
Proof.
  intros.
  inversion H; subst.
  destruct e as (v1', v2').
  apply starts_with_eq in H0.
  apply ends_with_eq in H1.
  subst.
  apply walk2_inv_cons in H.
  destruct H as (v, (?, ?)).
  inversion H; subst.
  intuition.
Qed.


Lemma walk2_cons:
  forall x y z w,
  Walk2 y z w ->
  Edge (x, y) ->
  Walk2 x z ((x, y) :: w).
Proof.
  intros.
  inversion H; subst.
  auto using walk2_def, starts_with_def, ends_with_cons, walk_cons, starts_with_to_linked.
Qed.

Lemma walk2_concat:
  forall w1 x y z w2,
  Walk2 x y w1 ->
  Walk2 y z w2 ->
  Walk2 x z (w1 ++ w2).
Proof.
  intros w1.
  induction w1.
  - intros.
    apply walk2_nil_inv in H.
    inversion H.
  - intros.
    simpl.
    destruct a.
    assert (a = x). {
      apply walk2_inv_cons in H.
      destruct H as (?, (?, ?)).
      inversion H.
      trivial.
    }
    subst.
    destruct w1.
    + apply walk2_inv_pair in H.
      destruct H.
      inversion H.
      subst.
      simpl.
      auto using walk2_cons.
    + apply walk2_inv in H.
      destruct H as (v, (Heq, (He, Hw))).
      inversion Heq; subst; clear Heq.
      eauto using walk2_cons.
Qed.

Lemma walk2_to_forall:
  forall x y w,
  Walk2 x y w ->
  List.Forall Edge w.
Proof.
  intros.
  inversion H.
  auto using walk_to_forall.
Qed.

Lemma walk2_to_edge:
  forall v1 v2 x y w,
  Walk2 x y w ->
  List.In (v1,v2) w ->
  Edge (v1, v2).
Proof.
  intros.
  apply walk2_to_forall in H.
  rewrite Forall_forall in H.
  eauto.
Qed.

End EDGE.

End Walk.

Lemma walk_impl_weak:
  forall {A:Type} (E: (A * A) %type -> Prop) (F: (A * A) %type -> Prop),
  forall w,
  (forall e, List.In e w -> E e -> F e) ->
  Walk E w ->
  Walk F w.
Proof.
  intros.
  apply walk_inv in H0.
  destruct H0.
  apply walk_def; repeat auto.
  rewrite Forall_forall in *.
  auto.
Qed.

Lemma walk_impl:
  forall {A:Type} (E: (A * A) %type -> Prop) (F: (A * A) %type -> Prop),
  (forall e, E e -> F e) ->
  forall w,
  Walk E w ->
  Walk F w.
Proof.
  intros.
  eauto using walk_impl_weak.
Qed.

Lemma walk_map_impl:
  forall {A:Type} (E F: (A*A)->Prop) f,
  (forall a, E a -> F (f a)) ->
  (forall a w, Linked a w -> Linked (f a) (map f w)) ->
  forall w,
  Walk E w ->
  Walk F (map f w).
Proof.
  intros.
  induction w. {
    eauto using walk_nil.
  }
  inversion H1.
  subst.
  apply IHw in H4.
  clear IHw.
  simpl.
  apply walk_cons; auto.
Qed.

Lemma walk_eq:
  forall {A:Type} (E: (A * A) %type -> Prop) (F: (A * A) %type -> Prop),
  (forall e, E e <-> F e) ->
  forall w,
  Walk E w <-> Walk F w.
Proof.
  split; repeat (apply walk_impl; apply H).
Qed.

Lemma walk2_impl_weak:
  forall {A:Type} (E: (A * A) %type -> Prop) (F: (A * A) %type -> Prop),
  forall w,
  (forall e, List.In e w -> E e -> F e) ->
  forall x y,
  Walk2 E x y w ->
  Walk2 F x y w.
Proof.
  intros.
  inversion H0; subst; clear H0.
  eauto using walk2_def, walk_impl_weak.
Qed.

Lemma walk2_impl:
  forall {A:Type} (E: (A * A) %type -> Prop) (F: (A * A) %type -> Prop),
  (forall e, E e -> F e) ->
  forall x y w,
  Walk2 E x y w ->
  Walk2 F x y w.
Proof.
  intros.
  inversion H0; subst; clear H0.
  eauto using walk2_def, walk_impl.
Qed.

Lemma walk2_eq:
  forall {A:Type} (E: (A * A) %type -> Prop) (F: (A * A) %type -> Prop),
  (forall e, E e <-> F e) ->
  forall x y w,
  Walk2 E x y w <-> Walk2 F x y w.
Proof.
  intros.
  split; repeat (apply walk2_impl; apply H).
Qed.

  Lemma walk2_inv_2 {A:Type}:
    forall E (t1 t2 t3 tn:A) w,
    Walk2 E t1 tn ((t1, t2) :: (t2, t3) :: w) ->
    Walk2 E t2 tn ((t2, t3) :: w).
  Proof.
    intros.
    inversion H.
    subst.
    apply walk2_def.
    - auto using starts_with_def.
    - eauto using ends_with_inv.
    - inversion H2; subst; auto.
  Qed.


Lemma cycle_impl_weak:
  forall {A:Type} (E: (A * A) %type -> Prop) (F: (A * A) %type -> Prop),
  forall w,
  (forall e, List.In e w -> E e -> F e) ->
  Cycle E w ->
  Cycle F w.
Proof.
  intros.
  inversion H0.
  subst.
  eauto using walk_impl_weak, cycle_def.
Qed.

Lemma cycle_impl:
  forall {A:Type} (E: (A * A) %type -> Prop) (F: (A * A) %type -> Prop),
  (forall e, E e -> F e) ->
  forall w,
  Cycle E w ->
  Cycle F w.
Proof.
  intros.
  inversion H0.
  eauto using walk_impl, cycle_def.
Qed.

Lemma cycle_eq:
  forall {A:Type} (E: (A * A) %type -> Prop) (F: (A * A) %type -> Prop),
  (forall e, E e <-> F e) ->
  forall w,
  Cycle E w <-> Cycle F w.
Proof.
  intros.
  split; repeat (apply cycle_impl; apply H).
Qed.

Implicit Arguments Cycle.
Implicit Arguments Walk.
Implicit Arguments Linked.
Implicit Arguments Connected.
Implicit Arguments End.
Implicit Arguments In.
Implicit Arguments cycle_def.
Implicit Arguments StartsWith.
Implicit Arguments EndsWith.
Implicit Arguments ends_with_cons.

(** Subgraph relation *)

Section SUBGRAPH.

Variable A:Type.
Notation edge := (A*A)%type.

Definition subgraph (E E':edge -> Prop) :=
  forall e,
  E e ->
  E' e.

Lemma subgraph_edge:
  forall (E E':edge -> Prop) e,
  subgraph E E' ->
  E e ->
  E' e.
Proof.
  intros.
  unfold subgraph in *.
  apply H.
  assumption.
Qed.

Lemma subgraph_in:
  forall E E' (v:A),
  subgraph E E' ->
  In E v ->
  In E' v.
Proof.
  intros.
  inversion H0.
  destruct H1.
  apply subgraph_edge with (e:=x) (E':=E') in H1;
  eauto using in_def.
Qed.

Lemma subgraph_walk:
  forall (E E':edge -> Prop) w,
  subgraph E E' ->
  Walk E w ->
  Walk E' w.
Proof.
  intros.
  eauto using walk_impl.
Qed.

Lemma subgraph_cycle:
  forall (E E':edge -> Prop) w,
  subgraph E E' ->
  Cycle E w ->
  Cycle E' w.
Proof.
  intros.
  eauto using cycle_impl.
Qed.

Lemma walk_is_subgraph:
  forall E w,
  Walk E w ->
  subgraph (fun x => List.In x w) E.
Proof.
  intros.
  unfold subgraph.
  intros.
  eauto using (in_edge (Edge:=E)).
Qed.

Lemma cycle_is_subgraph:
  forall E w,
  Cycle E w ->
  subgraph (fun x => List.In x w) E.
Proof.
  intros.
  inversion H.
  subst.
  eauto using walk_is_subgraph.
Qed.

Definition Forall (E:edge -> Prop) (P: A -> Prop) :=
  forall (v:A), In E v -> P v.

Lemma subgraph_forall:
  forall E E' P,
  subgraph E E' ->
  Forall E' P ->
  Forall E P.
Proof.
  intros.
  unfold Forall in *.
  intros.
  auto using (subgraph_in (E:=E)).
Qed.

Lemma forall_incl:
  forall E (P P': A -> Prop),
  (forall x, P x -> P' x) ->
  Forall E P ->
  Forall E P'.
Proof.
  intros.
  unfold Forall in *.
  intros.
  auto.
Qed.

End SUBGRAPH.
Implicit Arguments Forall.
Implicit Arguments subgraph.

Section CLOS_TRANS.

Require Import Coq.Relations.Relations.

Variable A:Type.
Variable Edge: (A * A) % type -> Prop.
Variable R: A -> A -> Prop.
Variable R_to_Edge:
  forall x y,
  R x y <-> Edge (x, y).

Lemma walk2_to_clos_trans:
  forall w v1 vn,
  Walk2 Edge v1 vn w ->
  clos_trans A R v1 vn.
Proof.
  intros w.
  induction w.
  - intros.
    apply walk2_nil_inv in H.
    inversion H.
  - intros.
    destruct w.
    + apply walk2_inv_pair in H.
      destruct H.
      rewrite <- R_to_Edge in *.
      apply t_step; auto.
    + apply walk2_inv in H.
      destruct H as (v2, (Heq, (He,Hw))).
      rewrite <- R_to_Edge in *.
      apply t_trans with (y:=v2); auto using t_step.
Qed.

Lemma clos_trans_to_walk2:
  forall v1 vn,
  clos_trans A R v1 vn ->
  exists w, Walk2 Edge v1 vn w.
Proof.
  intros.
  induction H.
  - exists ((x, y) :: nil).
    rewrite R_to_Edge in *.
    auto using walk2_nil.
  - destruct IHclos_trans1 as (w1, Hw1).
    destruct IHclos_trans2 as (w2, Hw2).
    eauto using walk2_concat.
Qed.

Lemma clos_trans_iff_walk2:
  forall v1 vn,
  clos_trans A R v1 vn <-> exists w, Walk2 Edge v1 vn w.
Proof.
  intros.
  split.
  - apply clos_trans_to_walk2.
  - intros; destruct H.
    eauto using walk2_to_clos_trans.
Qed.
End CLOS_TRANS.

Section PROPS.
  Lemma clos_trans_impl:
    forall {A:Type} (P Q: relation A),
    (forall x y, P x y -> Q x y) ->
    forall x y,
    clos_trans A P x y ->
    clos_trans A Q x y.
  Proof.
    intros.
    induction H0.
    - auto using t_step.
    - eauto using t_trans.
  Qed.

  Lemma walk2_impl_cycle:
    forall {A:Type} (E:A*A -> Prop) x w,
    Walk2 E x x w ->
    Cycle E w.
  Proof.
    intros.
    inversion H; subst.
    inversion H0; subst.
    destruct H3 as (w', (?, ?)).
    destruct x0 as (a,b).
    simpl in *.
    subst.
    eauto using cycle_def2.
  Qed.

  Lemma cycle_to_walk:
    forall {A:Type} (Edge:A*A -> Prop) w,
    Cycle Edge w ->
    Walk Edge w.
  Proof.
    intros.
    inversion H; eauto.
  Qed.

  Lemma walk2_from_walk:
    forall {A:Type} E F (x y: A) w,
    Walk2 E x y w ->
    Walk F w ->
    Walk2 F x y w.
  Proof.
    intros.
    destruct H.
    eauto using walk2_def.
  Qed.

  Lemma clos_trans_cycle_impl:
    forall {A:Type} (P Q: relation A),
    (forall x y z w, P z x -> P y w -> P x y -> Q x y) ->
    forall x,
    clos_trans A P x x ->
    clos_trans A Q x x.
  Proof.
    intros.
    pose (E:= (fun e => P (fst e) (snd e))).
    assert (W : exists w, Walk2 E x x w). {
      apply clos_trans_to_walk2 with (R:=P); eauto.
      intros.
      simpl.
      tauto.
    }
    destruct W as (w, W).
    assert (Cycle E w) by eauto using walk2_impl_cycle.
    apply clos_trans_t1n in H0.
    pose (F:= (fun e => Q (fst e) (snd e))).
    assert (Cycle F w). {
      apply cycle_impl_weak with (E0:=E); intros; auto.
      destruct e as (a, b).
      unfold E, F in *.
      simpl in *.
      assert (Hc: exists c, P c a). {
        apply pred_in_cycle with (Edge := E) in H2; auto.
        destruct H2 as (c, H2).
        exists c.
        eapply walk2_to_edge in H2; eauto.
        auto.
      }
      assert (Hd: exists d, P b d). {
        apply succ_in_cycle with (Edge := E) in H2; auto.
        destruct H2 as (d, H2).
        exists d.
        eapply walk2_to_edge in H2; eauto.
        auto.
      }
      destruct Hc as (c, Hc).
      destruct Hd as (d, Hd).
      eauto.
    }
    apply cycle_to_walk in H2.
    assert (Walk2 F x x w) by eauto using walk2_from_walk.
    apply walk2_to_clos_trans with (Edge:=F) (w:=w); auto.
    intros.
    unfold F; simpl; tauto.
  Qed.

  Lemma clos_trans_cycle_pred_impl:
    forall {A:Type} (P Q: relation A),
    (forall x y z, P x y -> P y z -> Q y z) ->
    forall x,
    clos_trans A P x x ->
    clos_trans A Q x x.
  Proof.
    intros.
    apply clos_trans_cycle_impl with (P0:=P); auto.
    intros.
    eauto.
  Qed.

  Lemma clos_trans_cycle_succ_impl:
    forall {A:Type} (P Q: relation A),
    (forall x y z, P y z -> P x y -> Q x y) ->
    forall x,
    clos_trans A P x x ->
    clos_trans A Q x x.
  Proof.
    intros.
    apply clos_trans_cycle_impl with (P0:=P); auto.
    intros.
    eauto.
  Qed.

  Lemma clos_trans_impl_ex:
    forall {A B:Type} f (P: relation A) (Q: relation B),
    (forall x y, P x y -> Q (f x) (f y)) ->
    forall x y,
    clos_trans A P x y ->
    clos_trans B Q (f x) (f y).
  Proof.
    intros.
    induction H0.
    - auto using t_step.
    - eauto using t_trans.
  Qed.


  Inductive Reaches {A:Type} E (x y:A) : Prop :=
  | reaches_def:
    forall w,
    Walk2 E x y w ->
    Reaches E x y.

  Lemma reaches_trans:
    forall {A:Type} (x y z:A) E,
    Reaches E x y ->
    Reaches E y z ->
    Reaches E x z.
  Proof.
    intros.
    inversion H.
    inversion H0.
    eauto using walk2_concat, reaches_def.
  Qed.

  Require Import Coq.Relations.Relation_Operators.

  (** Reflexive closure of continue. *)

  Definition ClosTransRefl {A:Type} E (x y:A) := Reaches E x y \/ x = y.

  Lemma walk_to_edge:
    forall {A:Type} (E:A*A->Prop) w e,
    Walk E w ->
    List.In e w ->
    E e.
  Proof.
    intros.
    apply walk_to_forall in H.
    rewrite Forall_forall in H.
    auto.
  Qed.

  Lemma end_to_append:
    forall {A:Type} w (x y:A),
    End w (x,y) ->
    exists w', w = w' ++ ((x,y)::nil).
  Proof.
    intros.
    induction w. {
      inversion H.
    }
    inversion H; subst. {
      exists nil.
      simpl.
      auto.
    }
    apply IHw in H3; clear IHw.
    destruct H3 as (w', rw).
    subst.
    simpl.
    exists (a::w').
    auto.
  Qed.

  Lemma ends_with_alt:
    forall {A} (x y:A),
    EndsWith ((x, y) :: nil) y.
  Proof.
    intros.
    apply ends_with_def with (v':=x).
    auto using end_nil.
  Qed.

  Lemma ends_with_inv_append:
    forall {A:Type} w (x y z:A),
    EndsWith (w ++ (x, y) :: nil) z ->
    y = z.
  Proof.
    intros.
    induction w. {
      simpl in *.
      eauto using ends_with_eq.
    }
    simpl in H.
    apply IHw.
    inversion H; subst.
    destruct x0  as (v1,v2).
    destruct H0; subst.
    inversion H0; subst. {
      destruct w; inversion H3.
    }
    eauto using ends_with_def.
  Qed.

  Lemma walk_split:
    forall {A:Type} (a b: A) w w' E,
    Walk E (w ++ (a, b) :: w') ->
    w = nil \/ (EndsWith w a /\ Walk E w /\ Walk E ((a,b)::w')).
  Proof.
    intros.
    induction w. {
      simpl in *.
      eauto.
    }
    right.
    simpl in H.
    inversion H; subst; clear H.
    assert (W:=H2).
    apply IHw in H2; clear IHw.
    destruct a0 as (x,y).
    destruct H2 as [?|(?,(?,?))]. {
      subst; simpl in *.
      apply linked_inv in H4; subst.
      repeat split; auto using ends_with_alt.
      eauto using edge_to_walk.
    }
    split; auto using ends_with_cons.
    destruct w. {
      simpl in *.
      apply linked_inv in H4; subst.
      eauto using edge_to_walk.
    }
    auto using walk_cons.
  Qed.

End PROPS.

Section EndsWith.
  Require Import Coq.Arith.Wf_nat.
  Require Import Coq.funind.Recdef.

  Function find_end {A:Type} (l:list A) { measure length l} : option A :=
  match l with
  | x :: l =>
    match l with
    | y :: l => find_end (y::l)
    | nil => Some x
    end
  | nil => None
  end.
  Proof.
    intros.
    subst.
    simpl.
    intuition.
  Qed.

  Lemma find_end_some:
    forall {A:Type} (x:A*A) l,
    find_end l = Some x ->
    End l x.
  Proof.
    induction l; intros; rewrite find_end_equation in H. {
      inversion H.
    }
    destruct l.
    - inversion H; subst; eauto using end_nil.
    - eauto using end_cons.
  Qed.

  Lemma find_end_none:
    forall {A:Type} l,
    find_end l = None ->
    l = @nil (A*A).
  Proof.
    intros.
    induction l. {
      auto.
    }
    rewrite find_end_equation in H.
    destruct l.
    - inversion H.
    - apply IHl in H; clear IHl.
      inversion H.
  Qed.

  Lemma find_end_rw_nil:
    forall {A:Type},
    find_end nil = @None A.
  Proof.
    intros.
    rewrite find_end_equation.
    trivial.
  Qed.

  Definition find_ends_with {A:Type} (l:list (A*A)) :=
  match find_end l with
  | Some (x, y) => Some y
  | _ => None
  end.

  Lemma find_ends_with_some:
    forall {A:Type} (x:A) w,
    find_ends_with w = Some x ->
    EndsWith w x.
  Proof.
    intros.
    unfold find_ends_with in *.
    remember (find_end _).
    symmetry in Heqo.
    destruct o.
    - destruct p as (a,b).
      inversion H; subst.
      apply find_end_some in Heqo.
      eauto using ends_with_def.
    - inversion H.
  Qed.

  Lemma find_ends_with_none:
    forall {A:Type} (w:list(A*A)),
    find_ends_with w = None ->
    w = nil.
  Proof.
    intros.
    destruct w.
    - auto.
    - unfold find_ends_with in *.
      remember (find_end _).
      symmetry in Heqo.
      destruct o.
      + destruct p0 as (a,b).
        inversion H.
      + apply find_end_none in Heqo.
        inversion Heqo.
  Qed.

  Lemma find_ends_with_cons_cons_1:
    forall {A:Type} e1 e2 w (x:A),
    find_ends_with (e2 :: w) = Some x ->
    find_ends_with (e1 :: e2 :: w) = Some x.
  Proof.
    intros.
    unfold find_ends_with in *.
    rewrite find_end_equation.
    auto.
  Qed.

  Lemma find_ends_with_cons_cons_2:
    forall {A:Type} e1 e2 w (x:A),
    find_ends_with (e1 :: e2 :: w) = Some x ->
    find_ends_with (e2 :: w) = Some x.
  Proof.
    intros.
    unfold find_ends_with in *.
    rewrite find_end_equation in H.
    auto.
  Qed.

  Lemma ends_with_dec {A:Type} w:
    { exists (x:A), EndsWith w x } + { w = nil}.
  Proof.
    remember (find_ends_with w).
    symmetry in Heqo.
    destruct o.
    - eauto using find_ends_with_some.
    - eauto using find_ends_with_none.
  Qed.

  Lemma ends_with_neq_nil:
    forall {A:Type} w,
    w <> nil ->
    exists (x:A), EndsWith w x.
  Proof.
    intros.
    destruct (ends_with_dec w).
    - auto.
    - contradiction.
  Qed.

  Lemma ends_with_to_find_ends_with:
    forall {A:Type} w (x:A),
    EndsWith w x ->
    find_ends_with w = Some x.
  Proof.
    induction w; intros. {
      apply ends_with_nil_inv in H; inversion H.
    }
    destruct w. {
      destruct a as (a1, a2).
      apply ends_with_eq in H; subst.
      unfold find_ends_with.
      rewrite find_end_equation.
      trivial.
    }
    apply ends_with_inv in H.
    eapply find_ends_with_cons_cons_1; eauto.
  Qed.

  Lemma ends_with_non_nil:
    forall {A:Type} w (y:A),
    EndsWith w y ->
    w <> nil.
  Proof.
    intuition.
    subst.
    eauto using ends_with_nil_inv.
  Qed.


End EndsWith.

Section EqDec.
  Variable A:Type.

  Variable eq_dec: forall (x y:A), { x = y } + { x <> y }.

  (** Checks if an edge equals another edge. *)

  Definition edge_eq_dec := pair_eq_dec eq_dec.

End EqDec.


Section Walk2.
  Require Import Aniceto.List.

  Lemma walk2_inv_eq_fst:
    forall {A:Type} E (x y x' z:A) w,
    Walk2 E x y ((x', z) :: w) ->
    x' = x.
  Proof.
    intros.
    inversion H; subst.
    eauto using starts_with_eq.
  Qed.

  Lemma walk2_inv_eq_snd:
    forall {A:Type} E (x x' y y':A),
    Walk2 E x y ((x', y') :: nil) ->
    y' = y.
  Proof.
    intros.
    inversion H; subst.
    eauto using ends_with_eq.
  Qed.

  Lemma starts_with_app:
    forall {A:Type} e w w' (x:A),
    StartsWith ((e :: w) ++ w') x ->
    StartsWith ((e :: w)) x.
  Proof.
    intros.
    inversion H.
    unfold StartsWith.
    destruct H0 as (?,(?,?)).
    simpl in *.
    inversion H0; subst; clear H0.
    eauto.
  Qed.

  Lemma ends_with_app:
    forall {A:Type} w' e w (x:A),
    EndsWith (w' ++ e :: w) x ->
    EndsWith (e :: w) x.
  Proof.
    induction w'; intros; auto.
    simpl in *.
    destruct w'; simpl in *;
      eauto using ends_with_inv.
  Qed.

  Section SplitWalk.
    Variable A:Type.
    Variable eq_dec: forall (x y:A), {x = y} + {x <> y}.

    (** The edge [e] is an outgoing edge of [x]. *)

    Definition Outgoing (x:A) (e:A*A) := x = fst e.

    Definition outgoing (x:A) (e:A*A) : bool :=
    if eq_dec x (fst e) then true else false.

    Definition Incoming (x:A) (e:A*A) := x = snd e.

    Definition incoming (x:A) (e:A*A) : bool :=
    if eq_dec x (snd e) then true else false.

    (** A path [w] has at least one outgoing edge of [x]. *)

    Definition HasOutgoing (x:A) (w:list (A*A)) := List.Exists (Outgoing x) w.

    Definition has_outgoing x := existsb (outgoing x).

    Definition HasIncoming (x:A) (w:list (A*A)) := List.Exists (Incoming x) w.

    Definition has_incoming x := existsb (incoming x).

    Definition edge_eqb e x := if pair_eq_dec eq_dec e x then true else false.

    Lemma edge_eqb_rw:
      forall e,
      edge_eqb e e = true.
    Proof.
      intros.
      unfold edge_eqb.
      destruct (pair_eq_dec eq_dec e e). {
        trivial.
      }
      contradiction n; trivial.
    Qed.

    Lemma edge_eqb_true:
      forall x y,
      edge_eqb x y = true ->
      x = y.
    Proof.
      intros.
      unfold edge_eqb in *.
      destruct (pair_eq_dec eq_dec x y). {
        trivial.
      }
      inversion H.
    Qed.

    Lemma edge_eqb_false:
      forall x y,
      edge_eqb x y = false ->
      x <> y.
    Proof.
      intros.
      unfold edge_eqb in *.
      destruct (pair_eq_dec eq_dec x y). {
        inversion H.
      }
      trivial.
    Qed.

    Lemma walk_split_fst:
      forall E w (e:A*A),
      List.In e w ->
      Walk E w ->
      (exists w1 w2, w = w1 ++ e :: w2 /\ ~ List.In e w1).
    Proof.
      intros.
      assert (He: Exists (fun x=> edge_eqb e x = true) w). {
        rewrite Exists_exists.
        eauto using edge_eqb_rw.
     }
     apply partition_fst in He.
     destruct He as (w1, (w2, (x, (?,(Hx,Hy))))).
     apply edge_eqb_true in Hx.
     subst.
     assert (~ List.In x w1). {
       unfold not; intros.
       rewrite Forall_forall in Hy.
       apply Hy in H1.
       apply edge_eqb_false in H1; contradiction H1; trivial.
     }
     eauto.
   Qed.

  Lemma walk_split_snd:
    forall E w (e:A*A),
    List.In e w ->
    Walk E w ->
    (exists w1 w2, w = w1 ++ e :: w2 /\ ~ List.In e w2).
  Proof.
      intros.
      assert (He: Exists (fun x=> edge_eqb e x = true) w). {
        rewrite Exists_exists.
        eauto using edge_eqb_rw.
     }
     apply partition_snd in He.
     destruct He as (w1, (w2, (x, (?,(Hx,Hy))))).
     apply edge_eqb_true in Hx.
     subst.
     assert (~ List.In x w2). {
       unfold not; intros.
       rewrite Forall_forall in Hy.
       apply Hy in H1.
       apply edge_eqb_false in H1; contradiction H1; trivial.
     }
     eauto.
  Qed.

  Let outgoing_to_true:
    forall x e,
    Outgoing x e ->
    outgoing x e = true.
  Proof.
    intros.
    unfold outgoing, Outgoing in *.
    destruct (eq_dec x (fst e)). {
      trivial.
    }
    subst.
    contradiction n; trivial.
  Qed.

  Let outgoing_true_rw:
    forall x y z,
    outgoing x (y, z) = true ->
    y = x.
  Proof.
    intros.
    unfold outgoing in *.
    simpl in *.
    destruct (eq_dec x y). {
      auto.
    }
    inversion H.
  Qed.

    Lemma walk_split_outgoing_snd:
      forall E w (x:A),
      HasOutgoing x w ->
      Walk E w ->
      (exists w1 w2 y, w = w1 ++ (x,y) :: w2 /\ ~ HasOutgoing x w2).
    Proof.
      intros.
      unfold HasOutgoing in *.
      assert (He: Exists (fun e=> outgoing x e = true) w). {
        rewrite Exists_exists in *.
        destruct H as (e, (Hw, Ho)).
        exists e; split; auto.
      }
      clear H.
      apply partition_snd in He.
      destruct He as (w1, (w2, (e, (?,(Hx,Hy))))).
      subst.
      destruct e as (x', y).
      apply outgoing_true_rw in Hx.
      subst.
      exists w1.
      exists w2.
      exists y.
      split; auto.
      unfold not; intros Hx.
      rewrite Forall_forall in Hy.
      rewrite Exists_exists in *.
      destruct Hx as (e, (Hi, Ho)).
      apply Hy in Hi.
      apply outgoing_to_true in Ho.
      rewrite Hi in *.
      inversion Ho.
    Qed.


  Let incoming_to_true:
    forall x e,
    Incoming x e ->
    incoming x e = true.
  Proof.
    intros.
    intros.
    unfold incoming, Incoming in *.
    destruct (eq_dec x (snd e)). {
      trivial.
    }
    subst.
    contradiction n; trivial.
  Qed.

  Let incoming_true_rw:
    forall x y z,
    incoming x (y, z) = true ->
    z = x.
  Proof.
    intros.
    unfold incoming in *.
    simpl in *.
    destruct (eq_dec x z). {
      auto.
    }
    inversion H.
  Qed.

    Lemma walk_split_incoming_fst:
      forall E w (x:A),
      HasIncoming x w ->
      Walk E w ->
      (exists w1 w2 y, w = w1 ++ (y,x) :: w2 /\ ~ HasIncoming x w1).
    Proof.
      intros.
      unfold HasIncoming in *.
      assert (He: Exists (fun e=> incoming x e = true) w). {
        rewrite Exists_exists in *.
        destruct H as (e, (Hw, Ho)).
        exists e; split; auto.
      }
      clear H.
      apply partition_fst in He.
      destruct He as (w1, (w2, (e, (?,(Hx,Hy))))).
      subst.
      destruct e as (y, x').
      apply incoming_true_rw in Hx.
      subst.
      exists w1.
      exists w2.
      exists y.
      split; auto.
      unfold not; intros Hx.
      rewrite Forall_forall in Hy.
      rewrite Exists_exists in *.
      destruct Hx as (e, (Hi, Ho)).
      apply Hy in Hi.
      apply incoming_to_true in Ho.
      rewrite Hi in *.
      inversion Ho.
    Qed.

  End SplitWalk.

  Lemma walk2_split:
    forall {A:Type} E w (x:A) y a b,
    Walk2 E x y w ->
    List.In (a,b) w ->
    (a = x) \/
    (b = y) \/
    (exists wa wb,
      w = wa ++ (a,b) :: wb /\ (Walk2 E x a wa /\ Walk2 E b y wb)
    ).
  Proof.
    intros.
    inversion H; subst.
    assert (X:= H0); apply in_split in X.
    destruct X as (wa,(wb,R)).
    subst.
    destruct wa. {
      left.
      simpl in *.
      apply starts_with_eq in H1.
      intuition.
    }
    right.
    destruct wb. {
      left.
      apply ends_with_inv_append in H2; subst.
      auto.
    }
    right.
    exists (p::wa); exists (p0::wb); split; auto.
    assert (X:=H3).
    apply walk_split in X.
    destruct X as [X|(?,(?,?))]. {
      inversion X.
    }
    split. {
      eauto using starts_with_app, ends_with_app, walk2_def.
    }
    inversion H6; subst.
    destruct p0 as (b',c).
    assert (b' = b) by eauto using linked_inv; subst.
    eauto using walk2_def, starts_with_def, ends_with_inv, ends_with_app.
  Qed.

  Let walk2_split_neq:
    forall {A:Type} E w (x:A) y a b,
    Walk2 E x y w ->
    List.In (a,b) w ->
    x <> a ->
    y <> b ->
    exists wa wb, w = wa ++ (a,b) :: wb /\ Walk2 E x a wa /\ Walk2 E b y wb.
  Proof.
    intros.
    eapply walk2_split in H; eauto.
    destruct H as [?|[?|(wa,(wb,(?,X)))]].
    - contradiction H1; auto.
    - contradiction H2; auto.
    - eauto.
  Qed.

  Let ends_with_app_fst:
    forall {A:Type} E w1 e a (b:A) w2,
    Walk E ((e :: w1) ++ (a, b) :: w2) ->
    EndsWith (e :: w1) a.
  Proof.
    induction w1; intros; destruct e as (x,y); simpl in *. {
      inversion H; subst.
      apply linked_inv in H4.
      subst.
      auto using ends_with_edge.
    }
    inversion H; subst.
    eauto using ends_with_cons.
  Qed.

  Let walk2_inv_app_snd:
    forall {A:Type} E w1 x (y:A) w2 a b,
    Walk2 E x y (w1 ++ (a, b) :: w2) ->
    Walk2 E a y ((a,b)::w2).
  Proof.
    induction w1; intros; simpl in *.
    - assert (X:=H).
      apply walk2_inv_eq_fst in X.
      subst.
      auto.
    - destruct w1. {
        simpl in *.
        apply walk2_inv in H.
        destruct H as (?,(?,(?,?))).
        subst.
        assert (X:=H1).
        apply walk2_inv_eq_fst in X.
        subst.
        auto.
      }
      simpl in *.
      apply walk2_inv in H.
      destruct H as (?,(?,(?,?))).
      subst.
      eauto.
  Qed.

  Let walk2_split_neq_neq:
    forall {A:Type} (eq_dec: forall (x y:A), {x = y} + {x <> y}) E w (x:A) y a b,
    Walk2 E x y w ->
    List.In (a,b) w ->
    x <> a ->
    y <> b ->
    (exists wa, Walk2 E x a wa /\ ~ List.In (a,b) wa) /\
    (exists wb, Walk2 E b y wb /\ ~ List.In (a,b) wb).
  Proof.
    intros.
    inversion H; subst.
    split.
    - apply walk_split_fst with (e:=(a,b)) in H5; auto.
      destruct H5 as (w1,(w2,(R,ni))).
      subst.
      destruct w1. {
        simpl in *.
        apply starts_with_eq in H3.
        contradiction H1; auto.
      }
      exists (p::w1).
      split; auto.
      apply walk2_def.
      + eauto using starts_with_app.
      + inversion H; eauto using ends_with_app_fst.
      + inversion H; subst.
        apply walk_split in H7.
        destruct H7 as [?|(?,(?,?))]. {
          inversion H7.
        }
        auto.
    - apply walk_split_snd with (e:=(a,b)) in H5; auto.
      destruct H5 as (w1,(w2,(R,ni))).
      subst.
      exists w2.
      split; auto.
      apply walk2_inv_app_snd in H.
      destruct w2. {
        apply ends_with_inv_append in H4.
        contradiction H2; auto.
      }
      apply walk2_inv in H.
      destruct H as (?,(R,(?,?))).
      inversion R; subst; clear R.
      auto.
  Qed.

  Lemma walk2_split_not_in:
    forall {A:Type} (eq_dec: forall (x y:A), {x = y} + {x <> y}) E w (x:A) y a b,
    Walk2 E x y w ->
    List.In (a,b) w ->
    (a = x /\ b = y) \/
    (a = x /\ exists wb, Walk2 E b y wb /\ ~ List.In (a,b) wb) \/
    (b = y /\ exists wa, Walk2 E x a wa /\ ~ List.In (a,b) wa) \/
    (
      (exists wa, Walk2 E x a wa /\ ~ List.In (a,b) wa) /\
      (exists wb, Walk2 E b y wb /\ ~ List.In (a,b) wb)
    ).
  Proof.
    intros.
    inversion H; subst.
    destruct (eq_dec a x), (eq_dec b y); subst.
    - auto.
    - apply walk_split_snd with (e:=(x,b)) in H3; auto.
      destruct H3 as (w1,(w2,(?,Hni))); subst.
      destruct w2. {
        apply ends_with_inv_append in H2.
        subst.
        auto.
      }
      right; left.
      split; auto.
      exists (p::w2).
      split; auto.
      apply walk2_inv_app_snd in H.
      apply walk2_inv in H.
      destruct H as (?,(R,(?,?))).
      inversion R; subst.
      auto.
    - apply walk_split_fst with (e:=(a,y)) in H3; auto.
      destruct H3 as (w1,(w2,(?,Hni))); subst.
      destruct w1. {
        simpl in *.
        apply starts_with_eq in H1; subst.
        contradiction n; auto.
      }
      right; right; left.
      split; auto.
      exists (p::w1).
      split; auto.
      apply walk2_def.
      + eauto using starts_with_app.
      + inversion H; eauto using ends_with_app_fst.
      + inversion H; subst.
        apply walk_split in H5.
        destruct H5 as [?|(?,(?,?))]. {
          inversion H5.
        }
        auto.
    - eauto using walk2_split_neq_neq.
  Qed.


  Lemma walk2_split_app:
    forall {A:Type} E w1 x (y:A) e w2 a b,
    Walk2 E x y ((e :: w1) ++ (a, b) :: w2) ->
    Walk2 E x a ((e :: w1)) /\ Walk2 E a y ((a, b) :: w2).
  Proof.
    induction w1; intros. {
      simpl in *.
      destruct e as (v1,v).
      inversion H; subst.
      apply starts_with_eq in H0; subst.
      inversion H2; subst.
      apply linked_inv in H6; subst.
      split.
      - apply walk2_def; auto using starts_with_def, ends_with_edge, edge_to_walk.
      - apply walk2_def; eauto using starts_with_def, ends_with_inv.
    }
    simpl in *.
    apply walk2_inv in H.
    destruct H as (v2, (?,(?,?))); subst.
    apply IHw1 in H1.
    destruct H1; split; auto using walk2_cons.
  Qed.

  Lemma walk2_to_in_fst:
    forall {A:Type} E x (y:A) w,
    Walk2 E x y w ->
    In E x.
  Proof.
    intros.
    destruct H.
    inversion H.
    destruct x as (x,y).
    destruct H2 as (?,(?,?)).
    simpl in *.
    subst.
    assert (List.In (v1,y) ((v1,y) :: x0)) by auto using in_eq.
    assert (E (v1,y)) by (eapply walk_to_edge; eauto).
    eauto using in_left.
  Qed.

  Lemma walk2_to_in_snd:
    forall {A:Type} E x (y:A) w,
    Walk2 E x y w ->
    In E y.
  Proof.
    intros.
    inversion H; subst; clear H.
    destruct H1 as ((v1,v2),(?,?)); simpl in *;subst.
    assert (E (v1,y)) by (eapply walk_to_edge; eauto using end_in).
    eauto using in_right.
  Qed.

End Walk2.

Section In.
  Lemma in_impl:
    forall {A:Type} (E F:A*A -> Prop) (X:forall e, E e -> F e) (x:A),
    In E x ->
    In F x.
  Proof.
    intros.
    destruct H as (e, (?,?)).
    eauto using in_def.
  Qed.
End In.

Section Reaches.

  Lemma reaches_impl:
    forall {A:Type} (x y:A) (E F:(A*A)->Prop),
    (forall e, E e -> F e) ->
    Reaches E x y ->
    Reaches F x y.
  Proof.
    intros.
    inversion H0.
    eauto using walk2_impl, reaches_def.
  Qed.

  Lemma edge_to_reaches:
    forall {A:Type} (x y:A) (E:A*A->Prop),
    E (x,y) ->
    Reaches E x y.
  Proof.
    intros.
    eauto using reaches_def, edge_to_walk2.
  Qed.

  Lemma reaches_to_in_fst:
    forall {A:Type} E x (y:A),
    Reaches E x y ->
    In E x.
  Proof.
    intros.
    inversion H.
    eauto using walk2_to_in_fst.
  Qed.

  Lemma reaches_to_in_snd:
    forall {A:Type} E x (y:A),
    Reaches E x y ->
    In E y.
  Proof.
    intros.
    inversion H.
    eauto using walk2_to_in_snd.
  Qed.


End Reaches.

Section Flip.

  Lemma walk2_flip:
    forall {A:Type} (E F:A*A->Prop) (Impl:forall x y, E (x,y) -> F (y,x)) w (x y:A),
    Walk2 E x y w ->
    Walk2 F y x (rev (map flip w)).
  Proof.
    induction w; intros. {
      apply walk2_nil_inv in H; contradiction.
    }
    simpl.
    destruct a as (x',z).
    assert (x'=x) by eauto using walk2_inv_eq_fst; subst.
    assert (rw: flip (x,z) = (z,x)) by auto; rewrite rw.
    destruct w. {
      simpl.
      assert (z = y) by eauto using walk2_inv_eq_snd; subst.
      apply walk2_to_edge with (v1:=x) (v2:=y) in H; auto using in_eq.
      auto using edge_to_walk2.
    }
    apply walk2_inv in H.
    destruct H as (v2, (He,(HE,Hw))).
    inversion He; subst; clear He; rename v2 into z.
    eauto using walk2_concat, edge_to_walk2.
  Qed.

  Lemma reaches_flip:
    forall {A:Type} (E F:A*A->Prop) (Impl:forall x y, E (x,y) -> F (y,x)) (x y:A),
    Reaches E x y ->
    Reaches F y x.
  Proof.
    intros.
    inversion H.
    eauto using reaches_def, walk2_flip.
  Qed.
End Flip.