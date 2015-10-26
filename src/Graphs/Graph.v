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

Lemma edge2_to_walk:
  forall v1 v2 v3,
  Edge (v1, v2) ->
  Edge (v2, v3) ->
  Walk ((v1,v2)::(v2,v3)::nil).
Proof.
  intros.
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

Lemma walk1_to_cycle:
  forall v,
  Walk ((v,v)::nil) ->
  Cycle ((v,v)::nil).
Proof.
  intros.
  eauto using cycle_def, end_nil.
Qed.

Lemma edge1_to_cycle:
  forall v,
  Edge (v,v) ->
  Cycle ((v,v)::nil).
Proof.
  intros.
  apply edge_to_walk in H.
  auto using walk1_to_cycle.
Qed.

Lemma walk2_to_cycle:
  forall v1 v2,
  Walk ((v1, v2) :: (v2, v1)::nil)%list ->
  Cycle ((v1, v2) :: (v2, v1)::nil)%list.
Proof.
  intros.
  eauto using cycle_def, end_cons, end_nil.
Qed.

Lemma edge2_to_cycle:
  forall v1 v2,
  Edge (v1, v2) ->
  Edge (v2, v1) ->
  Cycle ((v1, v2) :: (v2, v1)::nil)%list.
Proof.
  intros.
  assert (H': Walk ((v1, v2) :: (v2, v1)::nil)%list). {
    auto using edge2_to_walk.
  }
  auto using walk2_to_cycle.
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

Lemma walk_eq:
  forall {A:Type} (E: (A * A) %type -> Prop) (F: (A * A) %type -> Prop),
  (forall e, E e <-> F e) ->
  forall w,
  Walk E w <-> Walk F w.
Proof.
  split; repeat (apply walk_impl; apply H).
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
