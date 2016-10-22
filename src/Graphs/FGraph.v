Require Import Coq.Lists.List.
Require Import Coq.Lists.ListSet.
Require Import Coq.Bool.Bool.

Require Import Aniceto.Graphs.Graph.
Require Import Aniceto.Pair.
Require Import Aniceto.List.
Require Import Aniceto.Sig.
Require Import Aniceto.ListSet.

Set Implicit Arguments.

Section FGRAPHS.

Variable V:Type.

Variable eq_dec : forall (v1 v2:V), {v1 = v2} + {v1 <> v2}.

Let edge := (V*V)%type.
Let fgraph := list edge.

Definition Edge := (fun g e => @List.In edge e g).

Let in_nil:
  forall v,
  Graph.In (Edge nil) v -> False.
Proof.
  intros.
  repeat (try inversion H; destruct H).
Qed.

Notation In v g := (Graph.In (Edge g) v).

Lemma edge_spec:
  forall g e,
  Edge g e <-> List.In e g.
Proof.
  intros.
  simpl.
  tauto.
Qed.

Let in_cons:
  forall v e g,
  Graph.In (Edge g) v ->
  Graph.In (Edge (e :: g)) v.
Proof.
  unfold Edge.
  intros.
  inversion H.
  destruct H0.
  eauto using List.in_cons, in_def.
Qed.

Lemma pred_in_cycle:
  forall v w E,
  Cycle E w ->
  In v w ->
  exists v', E (v', v) /\ Edge w (v', v).
Proof.
  intros.
  destruct H0 as ((v1, v2), (Hin, Hpin)).
  assert (Hw : Walk E w).
  inversion H; auto.
  inversion Hpin.
  - subst; simpl in *.
    apply Graph.pred_in_cycle with (v1:=v1) (v2:=v2) in H.
    destruct H as (v3, H).
    exists v3.
    intuition.
    + apply in_edge with (w:=w); repeat auto.
    + auto.
  - subst; simpl in *.
    exists v1.
    intuition.
    apply in_edge with (w:=w); repeat auto.
Qed.

Lemma succ_in_cycle:
  forall v w E,
  Cycle E w ->
  In v w ->
  exists v', E (v, v') /\ Edge w (v, v').
Proof.
  intros.
  destruct H0 as ((v1, v2), (Hin, Hpin)).
  assert (Hw : Walk E w).
  inversion H; auto.
  inversion Hpin.
  - subst; simpl in *.
    exists v2.
    intuition.
    apply in_edge with (w:=w); repeat auto.
  - subst; simpl in *.
    apply Graph.succ_in_cycle with (v1:=v1) (v2:=v2) in H.
    destruct H as (v3, H).
    exists v3.
    intuition.
    + apply in_edge with (w:=w); repeat auto.
    + auto.
Qed.


Definition mem (v:V) (g:fgraph) : bool :=
  existsb (fun e => pair_mem eq_dec v e) g.

Lemma mem_prop:
  forall v g,
  mem v g = true ->
  In v g.
Proof.
  intros.
  unfold mem in *.
  apply existsb_exists in H.
  destruct H as (x, (x_in_g, mem_in_x)).
  apply pair_mem_prop in mem_in_x.
  eauto using in_def.
Qed.

Lemma mem_from_prop:
  forall v g,
  In v g ->
  mem v g = true.
Proof.
  intros.
  destruct H as (e, (e_in_g, v_in_e)).
  unfold mem.
  rewrite existsb_exists.
  exists e.
  eauto using pair_mem_from_prop.
Qed.

Lemma incl_to_subgraph:
  forall g g',
  incl g g' -> subgraph (Edge g) (Edge g').
Proof.
  unfold Edge, Graph.subgraph.
  eauto.
Qed.

Lemma subgraph_to_incl:
  forall g g',
  subgraph (Edge g) (Edge g') ->  incl g g'.
Proof.
  intros.
  unfold Graph.subgraph in *.
  unfold incl.
  assumption.
Qed.

Lemma subgraph_incl:
  forall g g',
  incl g g' <-> subgraph (Edge g) (Edge g').
Proof.
  split; auto using incl_to_subgraph, subgraph_to_incl.
Qed.

Lemma subgraph_filter:
  forall g f,
  subgraph (Edge (filter f g)) (Edge g).
Proof.
  intros.
  assert (Hx := filter_incl f g).
  auto using subgraph_incl.
Qed.

Lemma walk_is_subgraph:
  forall g w,
  Walk (Edge g) w ->
  subgraph (Edge w) (Edge g).
Proof.
  intros.
  unfold Graph.subgraph.
  intros.
  eauto using (in_edge _ H).
Qed.

Lemma subgraph_cons:
  forall (g:fgraph) e,
  subgraph (Edge g) (Edge (cons e g)).
Proof.
  unfold Graph.subgraph, Edge.
  eauto using List.in_cons.
Qed.

Lemma cycle_add:
  forall (g:fgraph) e w,
  Cycle (Edge g) w ->
  Cycle (Edge (cons e g)) w.
Proof.
  intros.
  eauto using subgraph_cycle, subgraph_cons.
Qed.

Inductive HasIncoming : fgraph -> V -> Prop :=
  has_incoming_def:
    forall v v' g,
    Edge g (v', v) ->
    HasIncoming g v.

Lemma has_incoming_cons:
  forall e g v,
  HasIncoming g v ->
  HasIncoming (e :: g) v.
Proof.
  intros.
  inversion H. subst.
  unfold Edge in *.
  apply List.in_cons with (a:=e) in H0.
  eauto using has_incoming_def.
Qed.

Inductive HasOutgoing : fgraph -> V -> Prop :=
  has_outgoing_def:
    forall v v' g,
    Edge g (v, v') ->
    HasOutgoing g v.

Lemma has_outgoing_cons:
  forall e g v,
  HasOutgoing g v ->
  HasOutgoing (e :: g) v.
Proof.
  intros.
  inversion H. subst.
  unfold Edge in *.
  apply List.in_cons with (a:=e) in H0.
  eauto using has_outgoing_def.
Qed.

Definition has_incoming (g:fgraph) (v:V) : bool :=
  existsb (fun e => if eq_dec v (snd e) then true else false) g.

Lemma has_incoming_prop:
  forall g v,
  has_incoming g v = true ->
  HasIncoming g v.
Proof.
  intros.
  unfold has_incoming in H.
  apply existsb_exists in H.
  destruct H as (x, (x_in_g, v_in_x)).
  destruct x as (v1, v2).
  simpl in *.
  destruct (eq_dec v v2).
  - subst.
    eauto using has_incoming_def.
  - inversion v_in_x.
Qed.

Lemma has_incoming_from_prop:
  forall g v,
  HasIncoming g v ->
  has_incoming g v = true.
Proof.
  intros.
  unfold has_incoming.
  apply existsb_exists.
  inversion H.
  subst.
  exists (v', v).
  split.
  assumption.
  - simpl.
    destruct (eq_dec v v).
    auto.
    contradiction n.
    trivial.
Qed.

Lemma has_incoming_in_snd:
  forall e w,
  List.In e w ->
  HasIncoming w (snd e).
Proof.
  intros.
  destruct e.
  simpl.
  eauto using has_incoming_def.
Qed.

(** Checks if an edge is in the graph. *)

Lemma is_edge_dec : forall e es, {Edge e es} + {~ Edge e es}.
Proof.
  intros.
  destruct (in_dec (@edge_eq_dec V eq_dec) es e); auto.
Defined.

Lemma in_edge_dec: forall (v:V) es, {Graph.In (Edge es) v } + {~ Graph.In (Edge es) v }.
Proof.
  intros.
  remember (existsb (fun (e:V*V)=>
    if (eq_dec (fst e) v) then true else
    if (eq_dec (snd e) v) then true else false
  ) es).
  symmetry in Heqb.
  destruct b.
  - rewrite existsb_exists in Heqb.
    left.
    destruct Heqb as ((v1,v2), (Hi, He)); simpl in *.
    destruct (eq_dec v1 v). {
      subst.
      eauto using in_left.
    }
    destruct (eq_dec v2 v). {
      subst.
      eauto using in_right.
    }
    inversion He.
  - right; unfold not; intros.
    apply existsb_Forall in Heqb.
    rewrite Forall_forall in *.
    destruct H as (e, (He,Hi)).
    apply Heqb in He.
    destruct e as (v1,v2); simpl in *.
    destruct Hi; simpl in *; subst.
    + destruct (eq_dec v1 v1);
      inversion He;
      contradiction n; trivial.
    + destruct (eq_dec v1 v2). {
        inversion He.
      }
      destruct (eq_dec v2 v2). {
        inversion He.
      }
      contradiction n0; trivial.
Defined.

Definition rm_sources (g:fgraph) :=
  feedback_filter (edge_eq_dec eq_dec) (fun g' e => has_incoming g' (fst e)) g.

Lemma rm_sources_incl:
  forall g,
  incl (rm_sources g) g.
Proof.
  intros.
  unfold rm_sources.
  apply feedback_filter_incl.
Qed.

Lemma rm_sources_subgraph:
  forall g,
  subgraph (Edge (rm_sources g)) (Edge g).
Proof.
  intros.
  apply subgraph_incl.
  apply rm_sources_incl.
Qed.

Lemma rm_sources_in:
  forall v g,
  In v (rm_sources g) ->
  In v g.
Proof.
  intros.
  eauto using subgraph_in, rm_sources_subgraph.
Qed.

Lemma rm_sources_has_incoming:
  forall g v,
  In v (rm_sources g) ->
  HasIncoming (rm_sources g) v.
Proof.
  intros.
  unfold Edge, rm_sources in *.
  destruct H as (e, (e_in_g, v_in_e)).
  assert (Hx := e_in_g).
  apply feedback_filter_in_f in e_in_g.
  apply has_incoming_prop in e_in_g.
  inversion v_in_e.
  - rewrite <- H in e_in_g.
    assumption.
  - remember (feedback_filter (edge_eq_dec eq_dec) _) as rm_g.
    destruct e as (v1, v2).
    simpl in *.
    rewrite <- H in *.
    eauto using has_incoming_def.
Qed.

Lemma filter_edge_in:
  forall e f g,
  Edge g e ->
  f e = true ->
  Edge (filter f g) e.
Proof.
  intros.
  apply filter_In.
  intuition.
Qed.

Lemma filter_vertex_in:
  forall v e f g,
  pair_In v e ->
  Edge g e ->
  f e = true ->
  In v (filter f g).
Proof.
  intros.
  unfold Graph.In.
  exists e.
  intuition.
  auto using filter_edge_in.
Qed.

Let edge_incl:
  forall g g' e,
  Edge g' e ->
  incl g' g ->
  Edge g e.
Proof.
  intros.
  unfold Edge in *.
  auto.
Qed.

Lemma has_outgoing_filter:
  forall g v,
  let fg := (fun e : V * V => has_incoming g (fst e)) in
  In v (filter fg g) ->
  HasOutgoing g v ->
  HasOutgoing (filter fg g) v.
Proof.
  intros.
  inversion H.
  subst.
  destruct H1.
  destruct x.
  inversion H2.
  - simpl in H3.
    rewrite H3 in *.
    eauto using has_outgoing_def.
  - simpl in H3. subst.
    (* let's check the edge in the original graph *)
    inversion H0; subst; clear H0.
    remember (fg (v1, v')) as b.
    symmetry in Heqb.
    destruct b.
    + eauto using has_outgoing_def, filter_edge_in.
    + (* absurd case *)
      unfold fg in Heqb.
      simpl in Heqb.
      assert (Hx: has_incoming g v1 = true). {
        assert (Hi: incl (filter fg g) g) by auto using filter_incl.
        eauto using has_incoming_from_prop, has_incoming_def.
      }
      rewrite Hx in Heqb.
      inversion Heqb.
Qed.

Lemma has_outgoing_rm_incl:
  forall v g,
  HasOutgoing g v ->
  In v (rm_sources g) ->
  HasOutgoing (rm_sources g) v.
Proof.
  intros.
  unfold rm_sources in *.
  remember (fun (g' : list (V * V)) e => has_incoming g' (fst e)) as f.
  functional induction (feedback_filter (edge_eq_dec eq_dec) f g).
  - assumption.
  - rename l into g.
    remember (fun (g' : list (V * V)) (e0 : V * V) => _) as f.
    remember (fun e : V * V => _ ) as ff.
    apply IHl; auto.
    rewrite Heqff.
    apply has_outgoing_filter; auto.
    inversion H0.
    destruct H1.
    exists x.
    intuition.
    unfold Edge in *.
    apply feedback_filter_in in H1.
    subst.
    assumption.
Qed.

Lemma forall_inv:
  forall (v:V) g (e:edge) P,
  Forall (Edge (e :: g)) P  ->
  Forall (Edge g) P.
Proof.
  intros.
  apply subgraph_forall with (E':= Edge (e :: g));
  auto using incl_to_subgraph, incl_tl, incl_refl.
Qed.

Definition AllOutgoing g : Prop := Forall (Edge g) (fun v => HasOutgoing g v).

Lemma all_outgoing_in:
  forall v g,
  In v g ->
  AllOutgoing g ->
  HasOutgoing g v.
Proof.
  intros.
  unfold AllOutgoing in *.
  unfold Forall in *.
  auto.
Qed.

Lemma all_outgoing_rm_incl:
  forall g,
  AllOutgoing g ->
  AllOutgoing (rm_sources g).
Proof.
  intros.
  unfold AllOutgoing in *.
  unfold Forall in *.
  unfold Graph.Forall in *.
  intros.
  apply has_outgoing_rm_incl; auto.
  apply rm_sources_in in H0; auto.
Qed.

Definition AllIncoming g : Prop := Forall (Edge g) (fun v => HasIncoming g v).

(* Returns all incoming edges *)
Fixpoint get_incoming (g:fgraph) v : list edge :=
  match g with
    | e :: g' =>
      let res := get_incoming g' v in
      if eq_dec (snd e) v
      then e :: res
      else res
    | nil => nil
  end.

Lemma get_incoming_inv:
  forall v1 v2 v g,
  List.In (v1, v2) (get_incoming g v) ->
  v2 = v.
Proof.
  intros.
  induction g.
  - simpl in H. inversion H.
  - destruct a.
    simpl in H.
    destruct (eq_dec v3 v); auto.
    subst.
    inversion H; auto.
    inversion H0.
    trivial.
Qed.

Lemma all_incoming_prop:
  forall v v' g,
  Edge g (v', v) ->
  List.In (v', v) (get_incoming g v).
Proof.
  intros.
  induction g.
  - inversion H. (* absurd *)
  - destruct a.
    simpl.
    destruct (eq_dec v1 v).
    + subst.
      destruct H.
      * inversion H.
        subst.
        apply in_eq.
      * apply IHg in H; clear IHg.
        auto using List.in_cons.
    + apply IHg.
      inversion H; trivial.
      inversion H0.
      subst.
      contradiction n; trivial.
Qed.

Lemma all_incoming_from_prop:
  forall e g v,
  List.In e (get_incoming g v) ->
  Edge g e.
Proof.
  intros.
  induction g.
  - simpl in H. inversion H.
  - simpl in H.
    destruct a.
    simpl in H.
    destruct (eq_dec v1 v).
    + inversion H.
      * inversion H0; subst.
        apply List.in_eq.
      * apply IHg in H0.
        unfold Edge in *.
        auto using List.in_cons.
    + apply IHg in H.
      unfold Edge in *.
      auto using List.in_cons.
Qed.

Lemma subgraph_get_incoming:
  forall g v,
  subgraph (Edge (get_incoming g v)) (Edge g).
Proof.
  intros.
  unfold subgraph.
  unfold Graph.subgraph.
  intros.
  eauto using all_incoming_from_prop.
Qed.

Lemma has_incoming_neq_nil:
  forall g v,
  HasIncoming g v <->
  get_incoming g v <> nil.
Proof.
  intros.
  split.
  + intros.
    inversion H.
    subst.
    apply all_incoming_prop in H0.
    remember (get_incoming g v).
    destruct l.
    - inversion H0.
    - intuition.
      inversion H1.
  + intros.
    remember (get_incoming g v) as g'.
    destruct g'.
    - contradiction H; trivial.
    - assert (List.In e (get_incoming g v)). {
        rewrite <- Heqg';
        apply in_eq.
      }
      assert (Hx := H0).
      destruct e.
      apply get_incoming_inv in H0.
      subst.
      eauto using has_incoming_def, all_incoming_from_prop.
Qed.

Lemma all_incoming_in:
  forall v g,
  In v g ->
  AllIncoming g ->
  HasIncoming g v.
Proof.
  intros.
  unfold AllIncoming in *.
  unfold Forall in *.
  auto.
Qed.

Lemma all_incoming_rm_incl:
  forall g,
  AllOutgoing g ->
  AllIncoming (rm_sources g).
Proof.
  intros.
  unfold AllOutgoing in *.
  unfold AllIncoming.
  unfold Forall in *.
  unfold Graph.Forall in *.
  auto using rm_sources_has_incoming.
Qed.

Lemma rm_filter_nonempty:
  forall g,
  AllOutgoing g ->
  let fg := fun (e:edge) => has_incoming g (fst e) in
  (exists v, In v g) ->
  exists v, In v (filter fg g).
Proof.
  intros.
  destruct H0 as (v, H0).
  inversion H0.
  destruct H1.
  destruct x as (vi, vo).
  assert (vo_out: HasOutgoing g vo) by eauto using all_outgoing_in, in_right.
  inversion vo_out.
  subst.
  exists v'.
  apply filter_vertex_in with (e:=(vo, v')); repeat auto.
  apply pair_in_right.
  unfold fg.
  simpl.
  eauto using has_incoming_from_prop, has_incoming_def.
Qed.

Let subgraph_forall_filter:
  forall P f g,
  Forall (Edge g) P ->
  Forall (Edge (filter f g)) P.
Proof.
  intros.
  eauto using subgraph_forall, subgraph_filter.
Qed.

Let rm_sources_nonempty':
  forall g,
  let g' := (rm_sources g) in
  AllOutgoing g ->
  (exists v, In v g) ->
  AllOutgoing g' ->
  AllIncoming g' ->
  exists v', In v' g'.
Proof.
  intros.
  unfold rm_sources in *.
  remember (fun (g' : list (V * V)) (e : V * V) => _) as fg.
  functional induction (feedback_filter (edge_eq_dec eq_dec) fg g); auto.
  unfold g' in *.
  rename l into g.
  remember (feedback_filter _ _)  as  gf.
  apply IHl; auto.
  - unfold AllOutgoing.
    unfold Forall.
    unfold Graph.Forall.
    intros.
    (* -- *)
    unfold AllOutgoing in H.
    unfold Forall in H.
    inversion H3.
    destruct H4.
    unfold Edge in *.
    apply filter_in in H4.
    apply has_outgoing_filter; auto.
    apply H.
    exists x.
    auto.
  - subst.
    auto using rm_filter_nonempty.
Qed.

Lemma nonempty_exists_vertex:
  forall g,
  g <> nil <->
  exists v, In v g.
Proof.
  intros.
  split.
  + intros; destruct g.
    - contradiction H.
      trivial.
    - destruct e.
      exists v.
      unfold Edge in *.
      eauto using in_left, List.in_eq.
  + intros.
    intuition.
    destruct H.
    inversion H.
    destruct H1.
    subst.
    inversion H1.
Qed.

Lemma rm_sources_nonempty:
  forall g,
  AllOutgoing g ->
  g <> nil ->
  AllOutgoing (rm_sources g) ->
  AllIncoming (rm_sources g) ->
  rm_sources g <> nil.
Proof.
  intros.
  apply nonempty_exists_vertex in H0.
  apply nonempty_exists_vertex.
  auto using rm_sources_nonempty'.
Qed.

Theorem exists_has_incoming:
  forall g,
  AllOutgoing g ->
  g <> nil ->
  exists (g':fgraph),
  subgraph (Edge g') (Edge g) /\
  AllOutgoing g' /\
  AllIncoming g' /\
  g' <> nil.
Proof.
  intros.
  exists (rm_sources g).
  assert (Ha : AllOutgoing (rm_sources g)).
  apply all_outgoing_rm_incl; assumption.
  assert (Hb : AllIncoming (rm_sources g)).
  apply all_incoming_rm_incl; assumption.
  split.
  - unfold rm_sources.
    unfold subgraph.
    apply feedback_filter_incl.
  - repeat split; auto using rm_sources_nonempty.
Qed.

Definition prepend (w:list edge) (g:fgraph) : option edge :=
  match w with
    | e :: _ =>
      match (get_incoming g (fst e)) with
        | e :: _ => Some e
        | nil => None
      end
    | nil => None
  end.

Lemma prepend_walk:
  forall g w e,
  Walk (Edge g) w ->
  prepend w g = Some e ->
  Linked e w.
Proof.
  intros.
  destruct w.
  - unfold Linked. auto.
  - simpl in H0.
    destruct p.
    simpl in *.
    remember (get_incoming g v).
    destruct l.
    inversion H0.
    destruct e0.
    assert (List.In (v1, v2) (get_incoming g v)).
    rewrite <- Heql. apply in_eq.
    apply get_incoming_inv in H1.
    destruct e.
    inversion H0.
    subst.
    unfold Linked.
    auto.
Qed.

Lemma prepend_edge:
  forall g w e,
  prepend w g = Some e ->
  Edge g e \/ Edge w e.
Proof.
  intros.
  destruct w.
  - simpl in *.
    destruct g.
    * inversion H.
    * inversion H; intuition; apply List.in_eq.
  - simpl in *.
    destruct e0.
    simpl in *.
    remember (get_incoming g v).
    destruct l.
    + inversion H.
    + inversion H; subst; clear H.
      assert (List.In e (get_incoming g v)). {
        rewrite <- Heql.
        apply in_eq.
      }
      left.
      assert (Hs: subgraph (Edge (get_incoming g v)) (Edge g))
      by auto using subgraph_get_incoming.
      auto using (subgraph_edge _ Hs).
Qed.

Fixpoint cut (v:V) (w:list edge) :=
  match w with
    | nil => nil
    | e :: w' =>
      if eq_dec v (snd e)
      then e :: nil
      else e :: (cut v w')
  end.

Lemma starts_with_cons_inv:
  forall e w (v:V),
  StartsWith (e :: w) v ->
  fst e = v.
Proof.
  intros.
  destruct H.
  destruct H as (w', (H1, H2)).
  inversion H1.
  auto.
Qed.

Lemma starts_with_cons:
  forall e w (v:V),
  fst e = v ->
  StartsWith (e :: w) v.
Proof.
  intros.
  unfold StartsWith.
  exists e.
  exists w.
  intuition.
Qed.

Lemma cut_starts_with:
  forall v v' w,
  StartsWith w v ->
  StartsWith (cut v' w) v.
Proof.
  intros.
  destruct w.
  - repeat (destruct H; try inversion H).
  - simpl.
    destruct (eq_dec v' (snd p));
    (apply starts_with_cons_inv in H;
      auto using starts_with_cons).
Qed.

Lemma cut_ends_with:
  forall v w,
  HasIncoming w v ->
  EndsWith (cut v w) v.
Proof.
  intros.
  induction w.
  - inversion H. inversion H0.
  - inversion H.
    subst.
    apply in_inv in H0.
    destruct H0.
    + destruct a.
      inversion H0; subst; clear H0.
      exists (v', v).
      intuition.
      simpl.
      destruct (eq_dec v v).
      * apply end_nil.
      * assert (v = v); auto.
        apply f in H0; inversion H0.
    + apply has_incoming_def in H0.
      apply IHw in H0.
      destruct H0.
      destruct H0.
      simpl.
      destruct (eq_dec v (snd a)).
      * destruct x; destruct a.
        simpl in *; subst.
        exists (v2, v3).
        simpl.
        intuition.
        apply end_nil.
      * exists x.
        intuition.
        apply end_cons; auto.
Qed.

Lemma cut_is_linked:
  forall a v w,
  Linked a w ->
  Linked a (cut v w).
Proof.
  intros.
  induction w.
  - auto.
  - simpl.
    destruct (eq_dec v (snd a0)).
    + inversion H.
      auto.
    + auto.
Qed.

Lemma cut_is_walk:
  forall g w v,
  Walk (Edge g) w ->
  Walk (Edge g) (cut v w).
Proof.
  intros.
  induction w.
  - simpl. assumption.
  - inversion H.
    subst.
    apply IHw in H2.
    simpl.
    destruct (eq_dec v (snd a)).
    + apply edge_to_walk; auto.
    + apply walk_cons; auto using cut_is_linked.
Qed.

Definition sublen (p:(list edge * fgraph)) :=
  let (w, g) := p in
  length w - length g.

Section FIND_CYCLE.

Variable g:fgraph.

Definition IsWalkOf w := Walk (Edge g) w /\ NoDup w.

Definition WalkOf := { w : list edge | Walk (Edge g) w /\ NoDup w /\ w <> nil}.

Lemma prepend_edge2:
  forall w g e,
  prepend w g = Some e ->
  Walk (Edge g) w ->
  Edge g e.
Proof.
  intros.
  apply prepend_edge in H.
  destruct H; auto.
  simpl in *.
  assert (Hs: subgraph (Edge w) (Edge g0)) by auto using walk_is_subgraph.
  auto using (subgraph_edge _ Hs).
Qed.

Lemma prepend_edge3:
  forall w g e,
  prepend w g = Some e ->
  subgraph (Edge w) (Edge g) ->
  List.In e g.
Proof.
  intros.
  apply prepend_edge in H.
  unfold  Edge in *.
  intuition.
Qed.

Definition ConsOf (w:list edge) := {e: edge | Walk (Edge g) (e :: w) }.

Definition CycleOf := { c:list edge | Cycle (Edge g) c}.

Definition BuildCycle w := { v: V | HasIncoming w v /\ StartsWith w v }.

Lemma choose_option:
  forall {A} (o:option A),
  sum {x | o = Some x} {_:option A | o = None} .
Proof.
  intros.
  destruct o.
  - refine (inl (Sig_yes a)).
    auto.
  - refine (inr (Sig_yes None)).
    auto.
Defined.

Lemma choose_prepend:
  forall w,
  option {e | prepend w g = Some e}.
Proof.
  intros.
  remember (prepend w g).
  destruct o.
  - refine (Some (Sig_yes e)).
    auto.
  - refine None.
Defined.


Lemma next_edge_ok:
  forall (w:WalkOf) (e:{e | prepend (Sig_take w) g = Some e}),
  ConsOf (Sig_take w).
Proof.
  intros.
  destruct e as (e, H).
  destruct w as (w, (H1, (H2, H3))).
  refine (Sig_yes e).
  apply walk_cons.
  auto.
  intuition.
  apply prepend_edge2 with (w:=w).
  auto.
  intuition.
  apply prepend_walk with (g:=g).
  intuition.
  auto.
Defined.

Definition next_edge (w:WalkOf) : option (ConsOf (Sig_take w)) :=
  match choose_option (prepend (Sig_take w) g) with
    | inl e => Some (next_edge_ok w e)
    | inr _ => None
  end.

Lemma next_edge_nil_inv:
  forall w,
  next_edge w = None ->
  prepend (Sig_take w) g = None.
Proof.
  intros.
  destruct w.
  unfold next_edge in H.
  remember (choose_option (prepend x g)).
  destruct s.
  + inversion H.
  + destruct s.
    assumption.
Qed.

Lemma starts_with_linked:
  forall (e:edge) w,
  w <> nil ->
  Linked e w ->
  StartsWith w (snd e).
Proof.
  intros.
  destruct e.
  compute in H.
  destruct w.
  destruct H. trivial.
  destruct p.
  compute in H0.
  simpl.
  subst.
  apply starts_with_cons.
  auto.
Qed.

Definition try_prepend: forall (w:WalkOf) (e:ConsOf (Sig_take w)),
 sum WalkOf (BuildCycle (Sig_take w)).
Proof.
  intros.
  destruct e as (e, H).
  destruct w as (w, (H1, (H2,H3))).
  destruct (in_dec (edge_eq_dec eq_dec) e w).
  - refine (inr (Sig_yes (snd e))).
    split.
    + apply has_incoming_in_snd.
      assumption.
    + inversion H; subst.
      destruct e.
      destruct w.
      inversion i.
      apply starts_with_linked.
      * intuition.
      * assumption.
  - refine (inl (Sig_yes (e :: w))).
    intuition.
    apply NoDup_cons; repeat auto.
    inversion H0.
Defined.

Definition lendiff (w:WalkOf) :=
  set_length (edge_eq_dec eq_dec) g - set_length (edge_eq_dec eq_dec) (Sig_take w).

Definition build_cycle: forall (w:WalkOf) (v:BuildCycle (Sig_take w)), CycleOf.
Proof.
  intros.
  destruct w as (w, (?, ?)).
  destruct v as (v, (?, ?)).
  refine (Sig_yes (cut v w)).
  apply cycle_def2 with (v:=v);
  auto using cut_starts_with, cut_ends_with, cut_is_walk.
Defined.

Function find_cycle (w:WalkOf)
  { measure lendiff } : option CycleOf :=
  match next_edge w with
    | Some e =>
      match try_prepend w e with
        | inr v => Some (build_cycle w v)
        | inl w' => find_cycle w'
      end
    | None => None
  end.
Proof.
  intros.
  simpl in *.
  destruct e as ((?,?), ?).
  destruct w as (?, (?, (?,?))).
  simpl in *.
  destruct (in_dec (edge_eq_dec eq_dec) (v, v0)); inversion teq0.
  destruct w' as (?, (?,(?,?))).
  inversion H0.
  unfold lendiff.
  auto using (set_length_minus _ _ (walk_is_subgraph w0)).
Defined.

Lemma find_cycle_total:
  forall (w:WalkOf),
  AllIncoming g ->
  g <> nil ->
  exists w', find_cycle w = Some w'.
Proof.
  intros.
  functional induction (find_cycle w).
  - destruct w as (?, (?, (?, ?))).
    destruct v as (?, (?, ?)).
    eauto.
  - auto.
  - apply next_edge_nil_inv in e.
    destruct w as (w, (Hw1, (?, Hw3))).
    destruct w.
    { contradiction Hw3; trivial. (* absurd *) }
    simpl in e.
    remember (get_incoming g (fst e0)).
    destruct l; inversion e;  clear e.
    apply all_incoming_in with (v:=fst e0) in H.
    rewrite has_incoming_neq_nil in H.
    contradiction H; auto.
    unfold Graph.In.
    exists e0.
    destruct e0.
    split; try (inversion Hw1; subst); auto using pair_in_left.
Qed.

End FIND_CYCLE.

Theorem all_pos_idegree_impl_cycle:
  forall g (w:list edge),
  AllIncoming g ->
  g <> nil ->
  exists w, Cycle (Edge g) w.
Proof.
  intros.
  destruct g.
  contradiction H0; trivial.
  assert (Walk (Edge (e::g)) (e::nil)).
  assert (Edge (e::g) e).
  apply in_eq.
  apply edge_to_walk.
  assumption.
  assert (w':WalkOf (e::g)). {
    refine (Sig_yes (e::nil)).
    intuition.
    apply NoDup_cons.
    auto.
    apply NoDup_nil.
    inversion H2.
  }
  assert (Hg : exists c, find_cycle w' = Some c) by (
    apply find_cycle_total; repeat auto).
  destruct Hg as ((x,?), Hg).
  eauto.
Qed.

Theorem all_pos_odegree_impl_cycle:
  forall g,
  g <> nil ->
  AllOutgoing g ->
  exists w, Cycle (Edge g) w.
Proof.
  intros.
  destruct (exists_has_incoming H0 H) as
  (g', (H1, (H2, (H3, H4)))).
  apply all_pos_idegree_impl_cycle in H3; repeat auto.
  destruct H3.
  exists x.
  eauto using subgraph_cycle.
Qed.
End FGRAPHS.

Implicit Arguments subgraph.
Implicit Arguments HasIncoming.
Implicit Arguments HasOutgoing.

Section Edge.

  Lemma in_incl:
    forall {A:Type} (x:A) es es',
    Graph.In (Edge es) x ->
    incl es es' ->
    Graph.In (Edge es') x.
  Proof.
    intros.
    apply in_impl with (E:=Edge es); auto.
  Qed.
End Edge.

Section Restriction.
  Variable A:Type.
  Variable eq_dec:
    forall (x y:A), { x = y } + { x <> y }.

  Let vertex_mem (vs:list A) (x:A) := ListSet.set_mem eq_dec x vs.

  Let edge_mem vs (e:A*A) := let (x,y) := e in andb (vertex_mem vs x) (vertex_mem vs y).

  Definition restriction vs es := filter (edge_mem vs) es.

  Lemma restriction_incl:
    forall vs es,
    incl (restriction vs es) es.
  Proof.
    intros.
    unfold restriction.
    auto using List.filter_incl.
  Qed.

  Let vertex_mem_true_to_prop:
    forall x l,
    vertex_mem l x = true ->
    List.In x l.
  Proof.
    unfold vertex_mem.
    intros.
    apply ListSet.set_mem_correct1 in H.
    auto.
  Qed.

  Let vertex_mem_false_to_prop:
    forall x l,
    vertex_mem l x = false ->
    ~ List.In x l.
  Proof.
    unfold vertex_mem.
    intros.
    apply ListSet.set_mem_complete1 in H.
    auto.
  Qed.

  Let edge_mem_true_to_prop:
    forall rs x1 x2,
    edge_mem rs (x1, x2) = true ->
    List.In x1 rs /\ List.In x2 rs.
  Proof.
    unfold edge_mem.
    intros.
    remember (vertex_mem _ x1) as b1.
    remember (vertex_mem _ x2) as b2.
    symmetry in Heqb1; symmetry in Heqb2.
    destruct b1, b2; subst; try inversion H.
    auto using vertex_mem_true_to_prop.
  Qed.

  Let edge_mem_false_to_prop:
    forall rs x1 x2,
    edge_mem rs (x1, x2) = false ->
    ~ List.In x1 rs \/ ~ List.In x2 rs.
  Proof.
    unfold edge_mem.
    intros.
    rewrite Bool.andb_false_iff in H.
    destruct H;
    eauto using vertex_mem_false_to_prop.
  Qed.

  Let edge_mem_true_from_prop:
    forall rs x1 x2,
    List.In x1 rs ->
    List.In x2 rs ->
    edge_mem rs (x1, x2) = true.
  Proof.
    intros.
    remember (edge_mem _ _).
    symmetry in Heqb.
    destruct b; auto.
    apply edge_mem_false_to_prop in Heqb.
    destruct Heqb; contradiction.
  Qed.

  Let restriction_inv_edge:
    forall x1 x2 rs es,
    List.In (x1, x2) (restriction rs es) ->
    List.In x1 rs /\ List.In x2 rs.
  Proof.
    unfold restriction.
    intros.
    apply filter_In in H.
    destruct H.
    auto.
  Qed.

  Lemma restriction_in_1:
    forall rs es x,
    Graph.In (Edge (restriction rs es)) x ->
    List.In x rs.
  Proof.
    unfold Edge.
    intros.
    destruct H as ((x1,x2),(He,inP)).
    apply restriction_inv_edge in He.
    destruct He.
    destruct inP; simpl in *; subst; auto.
  Qed.

  Lemma restriction_in_2:
    forall x1 x2 rs es,
    List.In (x1, x2) es ->
    List.In x1 rs ->
    List.In x2 rs ->
    List.In (x1, x2) (restriction rs es).
  Proof.
    unfold restriction.
    intros.
    apply List.filter_true_to_in; auto.
  Qed.

End Restriction.


Section ConsEdge.
  Variable A:Type.

  Let edge_inv_neq:
    forall (e' e:A*A) es,
    Edge (e' :: es) e ->
    e' <> e ->
    Edge es e.
  Proof.
    unfold Edge.
    intros.
    apply in_cons_neq in H; auto.
  Qed.

  Lemma walk_inv_not_in_walk:
    forall w (e:A*A) es,
    ~ List.In e w ->
    Walk (Edge (e :: es)) w ->
    Walk (Edge es) w.
  Proof.
    induction w; intros. {
      auto using walk_nil.
    }
    inversion H0; subst; clear H0.
    destruct H4. {
      subst.
      contradiction H; auto using in_eq.
    }
    assert (~ List.In e w) by intuition.
    apply walk_cons; eauto.
  Qed.

  Lemma walk2_inv_not_in_walk:
    forall e es (x:A) y w,
    ~ List.In e w ->
    Walk2 (Edge (e :: es)) x y w ->
    Walk2 (Edge es) x y w.
  Proof.
    intros.
    inversion H0; subst.
    eauto using walk2_def, walk_inv_not_in_walk.
  Qed.

  Lemma walk_inv_in_edges:
    forall w (e:A*A) es,
    List.In e es ->
    Walk (Edge (e :: es)) w ->
    Walk (Edge es) w.
  Proof.
    induction w; intros. {
      auto using walk_nil.
    }
    inversion H0; subst; clear H0.
    apply IHw in H3; auto.
    destruct H4; subst; auto using walk_cons.
  Qed.

  Lemma edge_cons:
    forall es (e:A*A) e',
    Edge es e ->
    Edge (e' :: es) e.
  Proof.
    unfold Edge in *.
    auto using in_cons.
  Qed.

  Lemma reaches_cons:
    forall (x:A) y e es,
    Reaches (Edge es) x y ->
    Reaches (Edge (e :: es)) x y.
  Proof.
    eauto using reaches_impl, edge_cons.
  Qed.

  Let walk2_inv_cons:
    forall w (x:A) y z es,
    Walk2 (Edge ((z,y) :: es)) x y w ->
    z = x \/ exists w', Walk2 (Edge es) x y w' \/ Walk2 (Edge es) x z w'.
  Proof.
    induction w; intros. {
      apply walk2_nil_inv in H; contradiction.
    }
    destruct w. {
      destruct a as (x', y').
      assert (x'=x) by eauto using walk2_inv_eq_fst; subst.
      assert (y'=y) by eauto using walk2_inv_eq_snd; subst.
      apply walk2_inv_cons in H.
      destruct H as (v2, (Heq, He)).
      symmetry in Heq; inversion Heq; subst; clear Heq.
      inversion He; subst; clear He. {
        inversion H; subst.
        intuition.
      }
      eauto using edge_to_walk2.
    }
    apply walk2_inv in H.
    destruct H as (v, (Heq, (He, Hw))).
    subst.
    destruct He. {
      inversion H; subst; clear H.
      intuition.
    }
    apply IHw in Hw;auto.
    destruct Hw as [?|(w',Hx)]. {
      subst.
      eauto using edge_to_walk2.
    }
    destruct Hx. {
      eauto using walk2_cons.
    }
    eauto using walk2_cons.
  Qed.

  Lemma reaches_inv_cons_2:
    forall (x:A) y z es,
    Reaches (Edge ((z,y) :: es)) x y ->
    z = x \/ Reaches (Edge es) x y \/ Reaches (Edge es) x z.
  Proof.
    intros.
    destruct H.
    apply walk2_inv_cons in H.
    destruct H as [?|(w',[?|?])]; eauto using reaches_def.
  Qed.

  Lemma reaches_impl_cons:
    forall es e (x:A) y,
    Reaches (Edge es) x y ->
    Reaches (Edge (e :: es)) x y.
  Proof.
    intros.
    apply reaches_impl with (E:=Edge es); auto; intros.
    unfold Edge in *.
    auto using in_cons.
  Qed.

End ConsEdge.

Section RmEdge.
  Require Import Aniceto.Pair.
  Require Import Aniceto.List.

  Variable A:Type.
  Variable eq_dec: forall (x y:A), {x = y} + {x <> y}.

  Definition rm_edge e es := remove (edge_eq_dec eq_dec) e es.

  Lemma rm_edge_in_neq:
    forall e es e',
    List.In e' es ->
    e' <> e ->
    List.In e' (rm_edge e es).
  Proof.
    intros.
    unfold rm_edge.
    auto using remove_in_neq.
  Qed.

  Lemma edge_rm_edge_to_edge:
    forall e e' es,
    Edge (rm_edge e es) e' ->
    Edge es e'.
  Proof.
    unfold Edge in *; simpl in *.
    unfold rm_edge in *.
    eauto using remove_in.
  Qed.

End RmEdge.
