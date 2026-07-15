From DAGs Require Import Basics Descendants CycleDetection TopologicalSort PathFinding.
From Stdlib Require Import Lia Bool.
From CausalDiagrams Require Import Assignments Interventions DSeparation.
From Semantics Require Import FunctionRepresentation FindValue EquateValues.
From Utils Require Import Lists Logic.
From Experiment Require Import Main.
Import ListNotations.

(* =====================================================================
   "randomize n r" correctness
   ===================================================================== *)

Lemma do_remove_incoming : forall (n : node) (G : graph),
  do n G = remove_incoming n G.
Proof. intros n [V E]. reflexivity. Qed.

Lemma count_edge_cons_self : forall (e : edge) (E0 : edges),
  count_edge e (e :: E0) = S (count_edge e E0).
Proof.
  intros [u v] E0. simpl. rewrite !Nat.eqb_refl. reflexivity.
Qed.

Lemma count_edge_cons_other : forall (eu ev hu hv : node) (E0 : edges),
  (hu =? eu) && (hv =? ev) = false ->
  count_edge (eu, ev) ((hu, hv) :: E0) = count_edge (eu, ev) E0.
Proof.
  intros eu ev hu hv E0 H. simpl. rewrite H. reflexivity.
Qed.

Lemma In_remove_edges_into : forall (n : node) (E : edges) (e : edge),
  In e (remove_edges_into n E) -> In e E /\ snd e <> n.
Proof.
  intros n E [u w] H. unfold remove_edges_into in H. apply filter_In in H.
  destruct H as [H1 H2]. simpl in H2. simpl. split.
  - exact H1.
  - intros F. subst w. rewrite Nat.eqb_refl in H2. discriminate H2.
Qed.

Lemma member_edge_remove_edges_into : forall (n : node) (E : edges) (e : edge),
  member_edge e (remove_edges_into n E) = true -> member_edge e E = true.
Proof.
  intros n E e H. apply member_edge_In_equiv. apply member_edge_In_equiv in H.
  apply In_remove_edges_into in H. destruct H as [H _]. exact H.
Qed.

Lemma count_edge_remove_edges_into_same : forall (n : node) (E : edges) (eu : node),
  count_edge (eu, n) (remove_edges_into n E) = 0.
Proof.
  intros n E eu. induction E as [| [hu hv] t IH].
  - reflexivity.
  - unfold remove_edges_into in *. simpl.
    destruct (hv =? n) eqn:Hhv.
    + simpl. exact IH.
    + simpl. rewrite Hhv. rewrite andb_false_r. exact IH.
Qed.

Lemma count_edge_remove_edges_into_other : forall (n : node) (E : edges) (eu ev : node),
  (ev =? n) = false ->
  count_edge (eu, ev) (remove_edges_into n E) = count_edge (eu, ev) E.
Proof.
  intros n E eu ev Hev. induction E as [| [hu hv] t IH].
  - reflexivity.
  - unfold remove_edges_into in *. simpl.
    destruct (hv =? n) eqn:Hhv.
    + apply Nat.eqb_eq in Hhv. subst hv. simpl.
      assert (Hnev: (n =? ev) = false).
      { rewrite Nat.eqb_sym. exact Hev. }
      rewrite Hnev. rewrite andb_false_r. exact IH.
    + simpl. destruct ((hu =? eu) && (hv =? ev)) eqn:He.
      * rewrite IH. reflexivity.
      * exact IH.
Qed.

(* endpoints of a well-formed graph's edges are nodes of the graph *)
Lemma wf_edge_endpoints : forall (V : nodes) (E : edges) (u w : node),
  G_well_formed (V, E) = true -> In (u, w) E ->
  member u V = true /\ member w V = true.
Proof.
  intros V E u w Hwf Hin. unfold G_well_formed in Hwf.
  apply split_and_true in Hwf. destruct Hwf as [Hwf _].
  apply split_and_true in Hwf. destruct Hwf as [HA _].
  pose proof (forallb_true _ _ (u, w) E Hin HA) as H0. simpl in H0.
  apply split_and_true in H0. exact H0.
Qed.

Lemma G_well_formed_do : forall (n : node) (G : graph),
  G_well_formed G = true -> G_well_formed (do n G) = true.
Proof.
  intros n [V E] Hwf.
  pose proof Hwf as Hwf0.
  unfold G_well_formed in Hwf.
  apply split_and_true in Hwf. destruct Hwf as [Hwf HC].
  apply split_and_true in Hwf. destruct Hwf as [HA HB].
  unfold do, G_well_formed.
  apply split_and_true. split. apply split_and_true. split.
  - apply <- forallb_forall. intros e He.
    apply In_remove_edges_into in He. destruct He as [HeE _].
    exact (forallb_true _ _ e E HeE HA).
  - exact HB.
  - apply <- forallb_forall. intros [a b] He.
    apply In_remove_edges_into in He. destruct He as [HeE Hbn].
    simpl in Hbn.
    assert (Hbn': (b =? n) = false) by (apply Nat.eqb_neq; exact Hbn).
    cbv beta. rewrite (count_edge_remove_edges_into_other n E a b Hbn').
    exact (forallb_true _ _ (a, b) E HeE HC).
Qed.

Lemma G_well_formed_randomize : forall (n r : node) (V : nodes) (E : edges),
  G_well_formed (V, E) = true ->
  member n V = true ->
  member r V = false ->
  G_well_formed (add_fresh_source r n (remove_incoming n (V, E))) = true.
Proof.
  intros n r V E Hwf Hn Hr.
  pose proof Hwf as Hwf0.
  unfold G_well_formed in Hwf.
  apply split_and_true in Hwf. destruct Hwf as [Hwf HC].
  apply split_and_true in Hwf. destruct Hwf as [HA HB].
  unfold add_fresh_source, remove_incoming, G_well_formed.
  simpl fst. simpl snd.
  apply split_and_true. split. apply split_and_true. split.
  - (* edge endpoints are nodes *)
    apply <- forallb_forall. intros [a b] He.
    cbv beta iota.
    simpl in He. destruct He as [He | He].
    + (* the fresh edge (r, n) *)
      inversion He. subst a b.
      simpl. rewrite Nat.eqb_refl. simpl.
      destruct (r =? n); [reflexivity | rewrite Hn; reflexivity].
    + apply In_remove_edges_into in He. destruct He as [HeE _].
      destruct (wf_edge_endpoints V E a b Hwf0 HeE) as [Ha Hb].
      simpl. destruct (r =? a); destruct (r =? b); simpl;
        try rewrite Ha; try rewrite Hb; reflexivity.
  - (* each node appears once *)
    simpl forallb. apply split_and_true. split.
    + (* the fresh node r *)
      simpl. rewrite Nat.eqb_refl.
      rewrite (not_member_count_0 V r Hr). reflexivity.
    + apply <- forallb_forall. intros x Hx.
      assert (Hrx: (r =? x) = false).
      { apply Nat.eqb_neq. intros F. subst x.
        apply member_In_equiv in Hx. rewrite Hx in Hr. discriminate Hr. }
      simpl. rewrite Hrx.
      exact (forallb_true _ _ x V Hx HB).
  - (* each edge appears once *)
    apply <- forallb_forall. intros [a b] He.
    cbv beta.
    simpl in He. destruct He as [He | He].
    + (* the fresh edge (r, n) *)
      inversion He. subst a b.
      rewrite count_edge_cons_self.
      rewrite (count_edge_remove_edges_into_same n E r). reflexivity.
    + apply In_remove_edges_into in He. destruct He as [HeE Hbn].
      simpl in Hbn.
      assert (Hbn': (b =? n) = false) by (apply Nat.eqb_neq; exact Hbn).
      assert (Hne: (r =? a) && (n =? b) = false).
      { destruct (r =? a) eqn:Hra; simpl; [| reflexivity].
        rewrite Nat.eqb_sym. exact Hbn'. }
      rewrite (count_edge_cons_other a b r n _ Hne).
      rewrite (count_edge_remove_edges_into_other n E a b Hbn').
      exact (forallb_true _ _ (a, b) E HeE HC).
Qed.

Lemma dir_path_helper_impl : forall (L : nodes) (G1 G2 : graph),
  (forall a b, In a L -> is_edge (a, b) G1 = true -> is_edge (a, b) G2 = true) ->
  is_dir_path_in_graph_helper L G1 = true ->
  is_dir_path_in_graph_helper L G2 = true.
Proof.
  intros L G1 G2 Himpl H. induction L as [| h t IH].
  - reflexivity.
  - destruct t as [| h' t'].
    + reflexivity.
    + simpl in H. apply split_and_true in H. destruct H as [He Hrest].
      simpl. apply split_and_true. split.
      * apply Himpl. { left. reflexivity. } exact He.
      * apply IH.
        -- intros a b Ha Hab. apply Himpl. { right. exact Ha. } exact Hab.
        -- exact Hrest.
Qed.

Lemma is_edge_do : forall (a b n : node) (G : graph),
  is_edge (a, b) (do n G) = true -> is_edge (a, b) G = true.
Proof.
  intros a b n [V E] H. simpl in H. simpl.
  apply split_and_true in H. destruct H as [H Hme].
  apply split_and_true in H. destruct H as [Ha Hb].
  apply member_edge_remove_edges_into in Hme.
  rewrite Ha. rewrite Hb. rewrite Hme. reflexivity.
Qed.

Lemma contains_cycle_do : forall (n : node) (G : graph),
  G_well_formed G = true ->
  contains_cycle G = false ->
  contains_cycle (do n G) = false.
Proof.
  intros n G Hwf Hcyc.
  apply contains_cycle_false_complete.
  - apply G_well_formed_do. exact Hwf.
  - intros p Hp.
    apply (contains_cycle_false_correct G p Hwf Hcyc).
    destruct p as [[a b] int].
    apply dir_path_helper_impl with (G1 := do n G).
    + intros x y _ Hxy. apply is_edge_do with (n := n). exact Hxy.
    + exact Hp.
Qed.

Lemma is_edge_randomize_orig : forall (V : nodes) (E : edges) (n r a b : node),
  G_well_formed (V, E) = true ->
  member r V = false ->
  a <> r ->
  is_edge (a, b) (add_fresh_source r n (remove_incoming n (V, E))) = true ->
  is_edge (a, b) (V, E) = true.
Proof.
  intros V E n r a b Hwf Hr Har H.
  unfold add_fresh_source, remove_incoming in H. simpl in H.
  apply split_and_true in H. destruct H as [_ Hme].
  assert (Hra: (r =? a) = false).
  { apply Nat.eqb_neq. intros F. apply Har. symmetry. exact F. }
  rewrite Hra in Hme. simpl in Hme.
  apply member_edge_remove_edges_into in Hme.
  apply member_edge_In_equiv in Hme as HinE.
  destruct (wf_edge_endpoints V E a b Hwf HinE) as [Ha Hb].
  simpl. rewrite Ha. rewrite Hb. rewrite Hme. reflexivity.
Qed.

Lemma dir_path_helper_randomize : forall (L V : nodes) (E : edges) (n r : node),
  G_well_formed (V, E) = true ->
  member r V = false ->
  ~ In r L ->
  is_dir_path_in_graph_helper L (add_fresh_source r n (remove_incoming n (V, E))) = true ->
  is_dir_path_in_graph_helper L (V, E) = true.
Proof.
  intros L V E n r Hwf Hr HrL H.
  apply dir_path_helper_impl
    with (G1 := add_fresh_source r n (remove_incoming n (V, E))).
  - intros a b Ha Hab.
    apply is_edge_randomize_orig with (n := n) (r := r); auto.
    intros F. subst a. contradiction.
  - exact H.
Qed.

(* the fresh source r has no incoming edge in the randomized graph *)
Lemma no_edge_into_fresh : forall (V : nodes) (E : edges) (n r y : node),
  G_well_formed (V, E) = true ->
  member n V = true ->
  member r V = false ->
  is_edge (y, r) (add_fresh_source r n (remove_incoming n (V, E))) = false.
Proof.
  intros V E n r y Hwf Hn Hr.
  assert (Hnr: (n =? r) = false).
  { apply Nat.eqb_neq. intros F. subst n. rewrite Hn in Hr. discriminate Hr. }
  unfold add_fresh_source, remove_incoming. simpl.
  rewrite Hnr. rewrite andb_false_r. simpl.
  destruct (member_edge (y, r) (remove_edges_into n E)) eqn:Hin.
  - apply member_edge_remove_edges_into in Hin.
    apply member_edge_In_equiv in Hin.
    destruct (wf_edge_endpoints V E y r Hwf Hin) as [_ Hrr].
    rewrite Hrr in Hr. discriminate Hr.
  - rewrite andb_false_r. reflexivity.
Qed.

(* any non-initial node of a directed path has an incoming edge *)
Lemma dir_path_helper_pred : forall (L1 L2 : nodes) (x : node) (G : graph),
  is_dir_path_in_graph_helper (L1 ++ x :: L2) G = true ->
  L1 <> [] ->
  exists y, is_edge (y, x) G = true.
Proof.
  intros L1. induction L1 as [| h t IH]; intros L2 x G H Hne.
  - contradiction.
  - destruct t as [| h' t'].
    + simpl in H. apply split_and_true in H. destruct H as [He _].
      exists h. exact He.
    + simpl in H. apply split_and_true in H. destruct H as [_ Hrest].
      apply IH with (L2 := L2).
      * exact Hrest.
      * discriminate.
Qed.

Lemma contains_cycle_randomize : forall (V : nodes) (E : edges) (n r : node),
  G_well_formed (V, E) = true ->
  contains_cycle (V, E) = false ->
  member n V = true ->
  member r V = false ->
  contains_cycle (add_fresh_source r n (remove_incoming n (V, E))) = false.
Proof.
  intros V E n r Hwf Hcyc Hn Hr.
  apply contains_cycle_false_complete.
  - apply G_well_formed_randomize; auto.
  - intros [[a b] int] Hp.
    unfold is_directed_path_in_graph in Hp.
    (* b is not the fresh node: it has an incoming edge *)
    assert (Hbr: b <> r).
    { intros F. subst b.
      destruct (dir_path_helper_pred (a :: int) [] r
                  (add_fresh_source r n (remove_incoming n (V, E))) Hp)
        as [y Hy]; [discriminate |].
      rewrite no_edge_into_fresh in Hy; auto. discriminate Hy. }
    (* no intermediate node is the fresh node either *)
    assert (Hrint: ~ In r int).
    { intros F. apply in_split in F. destruct F as [l1 [l2 Hint]]. subst int.
      assert (Heq: (a :: (l1 ++ r :: l2)) ++ [b] = (a :: l1) ++ r :: (l2 ++ [b])).
      { simpl. rewrite <- app_assoc. reflexivity. }
      rewrite Heq in Hp.
      destruct (dir_path_helper_pred (a :: l1) (l2 ++ [b]) r
                  (add_fresh_source r n (remove_incoming n (V, E))) Hp)
        as [y Hy]; [discriminate |].
      rewrite no_edge_into_fresh in Hy; auto. discriminate Hy. }
    destruct (Nat.eq_dec a r) as [Har | Har].
    + (* the path starts at the fresh source *)
      subst a.
      destruct int as [| h t].
      * (* p = (r, b, []) *)
        simpl. repeat split; auto.
      * (* p = (r, b, h :: t): the tail is a path in the original graph *)
        simpl in Hp. apply split_and_true in Hp. destruct Hp as [_ Htail].
        assert (HtailG: is_dir_path_in_graph_helper ((h :: t) ++ [b]) (V, E) = true).
        { apply dir_path_helper_randomize with (n := n) (r := r); auto.
          intros F. apply in_app_or in F. destruct F as [F | F].
          - apply Hrint. exact F.
          - simpl in F. destruct F as [F | F]; [| contradiction].
            apply Hbr. exact F. }
        assert (Hq: acyclic_path_2 (h, b, t)).
        { apply (contains_cycle_false_correct (V, E) (h, b, t) Hwf Hcyc).
          exact HtailG. }
        simpl in Hq. destruct Hq as [Hhb [Hht [Hbt Hacyc]]].
        simpl. repeat split.
        -- intros F. apply Hbr. symmetry. exact F.
        -- exact Hrint.
        -- intros F. simpl in F. destruct F as [F | F].
           ++ apply Hhb. exact F.
           ++ apply Hbt. exact F.
        -- simpl. apply split_and_true. split.
           ++ destruct (member h t) eqn:Hmht; [| reflexivity].
              apply member_In_equiv in Hmht. contradiction.
           ++ destruct t as [| h' t'].
              ** reflexivity.
              ** exact Hacyc.
    + (* the fresh node is not on the path at all *)
      assert (HrL: ~ In r ((a :: int) ++ [b])).
      { intros F. apply in_app_or in F. destruct F as [F | F].
        - simpl in F. destruct F as [F | F].
          + apply Har. exact F.
          + apply Hrint. exact F.
        - simpl in F. destruct F as [F | F]; [| contradiction].
          apply Hbr. exact F. }
      apply (contains_cycle_false_correct (V, E) (a, b, int) Hwf Hcyc).
      unfold is_directed_path_in_graph.
      apply dir_path_helper_randomize with (n := n) (r := r); auto.
Qed.

Lemma find_parents_from_edges_none : forall (E0 : edges) (r : node),
  (forall u w, In (u, w) E0 -> w <> r) ->
  find_parents_from_edges r E0 = [].
Proof.
  intros E0. induction E0 as [| [u w] t IH]; intros r H.
  - reflexivity.
  - simpl. destruct (w =? r) eqn:Hwr.
    + apply Nat.eqb_eq in Hwr. exfalso. apply (H u w).
      * left. reflexivity.
      * exact Hwr.
    + apply IH. intros u' w' Hin. apply (H u' w'). right. exact Hin.
Qed.

Lemma find_parents_fresh : forall (n r : node) (V : nodes) (E : edges),
  G_well_formed (V, E) = true ->
  member n V = true ->
  member r V = false ->
  find_parents r (add_fresh_source r n (remove_incoming n (V, E))) = [].
Proof.
  intros n r V E Hwf Hn Hr.
  assert (Hnr: (n =? r) = false).
  { apply Nat.eqb_neq. intros F. subst n. rewrite Hn in Hr. discriminate Hr. }
  unfold add_fresh_source, remove_incoming, find_parents. simpl.
  rewrite Hnr.
  apply find_parents_from_edges_none.
  intros u w Hin. apply In_remove_edges_into in Hin.
  destruct Hin as [HinE _].
  intros F. subst w.
  destruct (wf_edge_endpoints V E u r Hwf HinE) as [_ Hrr].
  rewrite Hrr in Hr. discriminate Hr.
Qed.

Lemma is_assignment_for_cons_fresh : forall (X : Type) (U : assignments X)
    (r : node) (v : X) (V : nodes),
  is_assignment_for U V = true ->
  is_assignment_for ((r, v) :: U) (r :: V) = true.
Proof.
  intros X U r v V H. simpl.
  apply split_and_true. split.
  - rewrite Nat.eqb_refl. reflexivity.
  - exact (is_assignment_for_cat X U r v V H).
Qed.


Lemma randomize_value_at_n : forall (V : nodes) (E : edges) (g : @graphfun nat)
    (n : node) (v : nat) (U : assignments nat),
  G_well_formed (V, E) = true ->
  contains_cycle (V, E) = false ->
  member n V = true ->
  is_assignment_for U V = true ->
  find_value (V, E) (randomize_graphfun n g) n ((n, v) :: U) [] = Some v.
Proof.
  intros V E g n v U Hwf Hcyc Hn HU.
  assert (HUn: is_assignment_for ((n, v) :: U) (nodes_in_graph (V, E)) = true).
  { simpl. apply is_assignment_for_cat. exact HU. }
  assert (HnG: node_in_graph n (V, E) = true) by (simpl; exact Hn).
  destruct (find_value_evaluates_to_g (V, E) (randomize_graphfun n g) ((n, v) :: U) n
              (conj (conj Hwf Hcyc) (conj HUn HnG)))
    as [P [HP [pa [Hpa [unobs [Hunobs Hval]]]]]].
  simpl in Hunobs. rewrite Nat.eqb_refl in Hunobs. inversion Hunobs. subst unobs.
  rewrite Hval. unfold randomize_graphfun. rewrite Nat.eqb_refl. unfold f_unobs. reflexivity.
Qed.

Lemma do_value_at_n : forall (V : nodes) (E : edges) (g : @graphfun nat)
    (n : node) (v : nat) (U : assignments nat),
  G_well_formed (V, E) = true ->
  contains_cycle (V, E) = false ->
  member n V = true ->
  is_assignment_for U V = true ->
  find_value (do n (V, E)) (do_graphfun n v g) n U [] = Some v.
Proof.
  intros V E g n v U Hwf Hcyc Hn HU.
  assert (HGdwf: G_well_formed (do n (V, E)) = true) by (apply G_well_formed_do; auto).
  assert (HGdcyc: contains_cycle (do n (V, E)) = false) by (apply contains_cycle_do; auto).
  assert (HUd: is_assignment_for U (nodes_in_graph (do n (V, E))) = true) by (simpl; exact HU).
  assert (HnGd: node_in_graph n (do n (V, E)) = true) by (simpl; exact Hn).
  destruct (find_value_evaluates_to_g (do n (V, E)) (do_graphfun n v g) U n
              (conj (conj HGdwf HGdcyc) (conj HUd HnGd)))
    as [P [HP [pa [Hpa [unobs [Hunobs Hval]]]]]].
  assert (Hps: find_parents n (do n (V, E)) = []).
  { rewrite do_remove_incoming. apply find_parents_remove_incoming_self. }
  rewrite Hps in HP, Hpa.
  simpl in HP. inversion HP. subst P.
  simpl in Hpa. inversion Hpa. subst pa.
  rewrite Hval. unfold do_graphfun. rewrite Nat.eqb_refl. reflexivity.
Qed.

Lemma find_values_cross : forall (X : Type) (ps : nodes) (G1 G2 : graph)
    (g1 g2 : @graphfun X) (U1 U2 : assignments X),
  (forall p, In p ps -> find_value G1 g1 p U1 [] = find_value G2 g2 p U2 []) ->
  find_values G1 g1 ps U1 [] = find_values G2 g2 ps U2 [].
Proof.
  intros X ps G1 G2 g1 g2 U1 U2 H. induction ps as [| h t IH].
  - reflexivity.
  - simpl. rewrite (H h (or_introl eq_refl)).
    destruct (find_value G2 g2 h U2 []) eqn:Hh.
    + rewrite IH.
      * reflexivity.
      * intros p Hp. apply H. right. exact Hp.
    + reflexivity.
Qed.

Lemma randomize_do_step : forall (V : nodes) (E : edges) (g : @graphfun nat)
    (n w : node) (v : nat) (U : assignments nat),
  G_well_formed (V, E) = true ->
  contains_cycle (V, E) = false ->
  member n V = true ->
  is_assignment_for U V = true ->
  member w V = true ->
  w <> n ->
  (forall p, In p (find_parents w (V, E)) ->
     find_value (V, E) (randomize_graphfun n g) p ((n, v) :: U) []
     = find_value (do n (V, E)) (do_graphfun n v g) p U []) ->
  find_value (V, E) (randomize_graphfun n g) w ((n, v) :: U) []
  = find_value (do n (V, E)) (do_graphfun n v g) w U [].
Proof.
  intros V E g n w v U Hwf Hcyc Hn HU Hw Hwn Hpar.
  (* well-formedness bundles: the concrete side stays on the fixed graph (V,E),
     the spec side is do n (V,E) *)
  assert (HUn: is_assignment_for ((n, v) :: U) (nodes_in_graph (V, E)) = true).
  { simpl. apply is_assignment_for_cat. exact HU. }
  assert (HwG: node_in_graph w (V, E) = true) by (simpl; exact Hw).
  assert (HGdwf: G_well_formed (do n (V, E)) = true) by (apply G_well_formed_do; auto).
  assert (HGdcyc: contains_cycle (do n (V, E)) = false) by (apply contains_cycle_do; auto).
  assert (HUd: is_assignment_for U (nodes_in_graph (do n (V, E))) = true) by (simpl; exact HU).
  assert (HwGd: node_in_graph w (do n (V, E)) = true) by (simpl; exact Hw).
  (* unfold one evaluation step on each side *)
  destruct (find_value_evaluates_to_g (V, E) (randomize_graphfun n g) ((n, v) :: U) w
              (conj (conj Hwf Hcyc) (conj HUn HwG)))
    as [P1 [HP1 [pa1 [Hpa1 [u1 [Hu1 Hval1]]]]]].
  destruct (find_value_evaluates_to_g (do n (V, E)) (do_graphfun n v g) U w
              (conj (conj HGdwf HGdcyc) (conj HUd HwGd)))
    as [P2 [HP2 [pa2 [Hpa2 [u2 [Hu2 Hval2]]]]]].
  (* the spec side's parent set is the original one *)
  assert (Hps2: find_parents w (do n (V, E)) = find_parents w (V, E)).
  { rewrite do_remove_incoming. apply find_parents_remove_incoming_neq. exact Hwn. }
  rewrite Hps2 in HP2, Hpa2.
  (* parents evaluate identically *)
  assert (HPP: Some P1 = Some P2).
  { rewrite <- HP1. rewrite <- HP2. apply find_values_cross. exact Hpar. }
  inversion HPP. subst P2.
  assert (Hpapa: Some pa1 = Some pa2) by (rewrite Hpa1; symmetry; exact Hpa2).
  inversion Hpapa. subst pa2.
  (* the unobserved terms agree: the shadowing (n,v) is invisible to w <> n *)
  assert (Hnw: (n =? w) = false) by (apply Nat.eqb_neq; intros F; apply Hwn; symmetry; exact F).
  simpl in Hu1. rewrite Hnw in Hu1.
  rewrite Hu1 in Hu2. inversion Hu2. subst u2.
  (* the node functions agree *)
  assert (Hwn': (w =? n) = false) by (apply Nat.eqb_neq; exact Hwn).
  rewrite Hval1. rewrite Hval2.
  unfold randomize_graphfun, do_graphfun. rewrite Hwn'.
  reflexivity.
Qed.

(* Main theorem *)

Theorem randomize_semantic_do : forall (G : graph) (g : @graphfun nat)
    (n w : node) (v : nat) (U : assignments nat),
  G_well_formed G = true ->
  contains_cycle G = false ->
  node_in_graph n G = true ->
  is_assignment_for U (nodes_in_graph G) = true ->
  node_in_graph w G = true ->
  find_value G (randomize_graphfun n g) w ((n, v) :: U) [] = semantic_do n v G g w U.
Proof.
  intros [V E] g n w v U Hwf Hcyc Hn HU Hw.
  simpl in Hn, Hw. simpl in HU. unfold semantic_do.
  destruct (topo_sort_exists_for_acyclic (V, E) (conj Hwf Hcyc)) as [ts Hts].
  assert (Hmain: forall (i : nat) (w' : node),
    member w' V = true ->
    (exists j, index ts w' = Some j /\ j <= i) ->
    find_value (V, E) (randomize_graphfun n g) w' ((n, v) :: U) []
    = find_value (do n (V, E)) (do_graphfun n v g) w' U []).
  { induction i as [| i' IH]; intros w' Hw' [j [Hj Hji]].
    - (* w' is the first node in topological order: no parents *)
      assert (Hj0: j = 0) by lia. subst j.
      assert (Hps: find_parents w' (V, E) = []).
      { destruct ts as [| h t]; [discriminate Hj |].
        simpl in Hj. destruct (h =? w') eqn:Hhw.
        - apply Nat.eqb_eq in Hhw. subst h.
          apply topo_sort_first_node_no_parents with (ts := t).
          repeat split; assumption.
        - destruct (index t w'); discriminate Hj. }
      destruct (Nat.eq_dec w' n) as [-> | Hwn].
      + rewrite (randomize_value_at_n V E g n v U); auto.
        rewrite (do_value_at_n V E g n v U); auto.
      + apply randomize_do_step; auto.
        intros p Hp. rewrite Hps in Hp. destruct Hp.
    - destruct (Nat.eq_dec w' n) as [-> | Hwn].
      + rewrite (randomize_value_at_n V E g n v U); auto.
        rewrite (do_value_at_n V E g n v U); auto.
      + apply randomize_do_step; auto.
        intros p Hp.
        assert (HpV: member p V = true).
        { apply edge_from_parent_to_child in Hp as Hedge.
          destruct (edge_corresponds_to_nodes_in_well_formed (V, E) p w'
                      (conj Hwf Hedge)) as [Hp1 _].
          simpl in Hp1. exact Hp1. }
        destruct (topo_sort_parents (V, E) w' p ts
                    (conj Hwf (conj Hcyc Hts)) Hp) as [ip [jw [Hip [Hjw Hlt]]]].
        rewrite Hj in Hjw. inversion Hjw. subst jw.
        apply IH; auto.
        exists ip. split.
        * symmetry. exact Hip.
        * lia. }
  assert (HIn: In w ts).
  { apply (topo_sort_contains_nodes (V, E) ts Hts w). simpl. exact Hw. }
  destruct (proj1 (index_exists ts w) HIn) as [j Hj].
  apply (Hmain j w Hw).
  exists j. split.
  - symmetry. exact Hj.
  - lia.
Qed.

Corollary randomize_then_measure : forall (G0 : graph) (U : assignments nat)
    (st st' : unit_state) (n r w : node) (v : nat),
  G_well_formed G0 = true ->
  contains_cycle G0 = false ->
  node_in_graph n G0 = true ->
  is_assignment_for U (nodes_in_graph G0) = true ->
  node_in_graph w G0 = true ->
  apply_op G0 ((n, v) :: U) st (Randomize n r) = Some st' ->
  find_value G0 (cur_fun st') w ((n, v) :: U) [] = semantic_do n v G0 (cur_fun st) w U.
Proof.
  intros G0 U st st' n r w v Hwf Hcyc Hn HU Hw Hop.
  simpl in Hop. inversion Hop. subst st'. simpl.
  apply randomize_semantic_do; auto.
Qed.

(* three-node example *)

(* Randomize x (node 1) in G_3, injecting the randomizer draw (1, 1) that
   shadows x's natural noise, on the individual with U_z = 1: y evaluates to
   1 + 1 = 2 on both the concrete (no surgery) and the do(x = 1) sides. *)
Example rct_G_3_stratum_1 :
  find_value (dag G_3)
             (randomize_graphfun 1 g_3) 2 ((1, 1) :: [(1, 0); (2, 0); (3, 1)]) []
  = semantic_do 1 1 (dag G_3) g_3 2 [(1, 0); (2, 0); (3, 1)].
Proof. reflexivity. Qed.

Example rct_G_3_stratum_1_value :
  semantic_do 1 1 (dag G_3) g_3 2 [(1, 0); (2, 0); (3, 1)] = Some 2.
Proof. reflexivity. Qed.

(* =====================================================================
   Syntactic correctness of a simplified RCT

   A [simple_rct] over T (treatment) and R (response) is SYNTACTICALLY CORRECT
   when its post-experiment DAG satisfies the backdoor criterion over T and R.
   Randomizing T severs every backdoor path, so the empty set Z = [] is already
   admissible: [syntactic_backdoor <post-dag> T R []] holds.
   ===================================================================== *)

(* ---- Edge structure of the T-outgoing-mutilated post-RCT graph ---- *)
(* The randomized, then [remove_outgoing T]-mutilated graph on which the
   backdoor check runs is [(rand :: V, EH)] with
     EH = remove_edges_out_of T ((rand, T) :: remove_edges_into T E).
   Its only edge touching T is [rand -> T], and [rand]'s only edge is [rand -> T]:
   T is joined to the rest of the graph solely through the fresh source. *)

Lemma is_edge_In_edges : forall (e : edge) (V : nodes) (E : edges),
  is_edge e (V, E) = true -> In e E.
Proof.
  intros [u w] V E H. simpl in H.
  apply andb_prop in H. destruct H as [_ Hme].
  apply member_edge_In_equiv. exact Hme.
Qed.

Lemma not_In_is_edge_false : forall (e : edge) (V : nodes) (E : edges),
  ~ In e E -> is_edge e (V, E) = false.
Proof.
  intros [u w] V E Hni. simpl.
  apply member_edge_In_equiv_false in Hni. rewrite Hni. apply andb_false_r.
Qed.

(* Every edge of EH is either the fresh [rand -> T] edge, or an original edge of
   G that neither leaves nor enters T. *)
Lemma In_edge_remove_out_randomize : forall (T rand : node) (E : edges) (e : edge),
  In e (remove_edges_out_of T ((rand, T) :: remove_edges_into T E)) ->
  e = (rand, T) \/ (In e E /\ fst e <> T /\ snd e <> T).
Proof.
  intros T rand E e Hin.
  unfold remove_edges_out_of in Hin.
  apply filter_In in Hin. destruct Hin as [Hin HfT].
  apply negb_true_iff in HfT. apply Nat.eqb_neq in HfT.
  destruct Hin as [He | He].
  - left. symmetry. exact He.
  - right. unfold remove_edges_into in He.
    apply filter_In in He. destruct He as [HeE HsT].
    apply negb_true_iff in HsT. apply Nat.eqb_neq in HsT.
    repeat split; assumption.
Qed.

Lemma no_edge_from_fresh : forall (V : nodes) (E : edges) (a b : node),
  G_well_formed (V, E) = true -> member a V = false -> In (a, b) E -> False.
Proof.
  intros V E a b Hwf Ha Hin.
  destruct (wf_edge_endpoints V E a b Hwf Hin) as [Hma _].
  rewrite Hma in Ha. discriminate.
Qed.

Lemma no_edge_to_fresh : forall (V : nodes) (E : edges) (a b : node),
  G_well_formed (V, E) = true -> member b V = false -> In (a, b) E -> False.
Proof.
  intros V E a b Hwf Hb Hin.
  destruct (wf_edge_endpoints V E a b Hwf Hin) as [_ Hmb].
  rewrite Hmb in Hb. discriminate.
Qed.

(* The four adjacency facts about the mutilated graph [(rand :: V, EH)]. *)

Lemma rct_no_edge_from_T : forall (T rand : node) (V : nodes) (E : edges) (w : node),
  rand <> T ->
  is_edge (T, w)
    (rand :: V, remove_edges_out_of T ((rand, T) :: remove_edges_into T E)) = false.
Proof.
  intros T rand V E w HrandT.
  apply not_In_is_edge_false. intro Hin.
  apply In_edge_remove_out_randomize in Hin.
  destruct Hin as [Heq | [_ [Hfst _]]].
  - inversion Heq. congruence.
  - simpl in Hfst. congruence.
Qed.

Lemma rct_edge_into_T : forall (T rand : node) (V : nodes) (E : edges) (a : node),
  is_edge (a, T)
    (rand :: V, remove_edges_out_of T ((rand, T) :: remove_edges_into T E)) = true ->
  a = rand.
Proof.
  intros T rand V E a Hie.
  apply is_edge_In_edges in Hie.
  apply In_edge_remove_out_randomize in Hie.
  destruct Hie as [Heq | [_ [_ Hsnd]]].
  - inversion Heq. congruence.
  - simpl in Hsnd. congruence.
Qed.

Lemma rct_edge_from_rand : forall (T rand : node) (V : nodes) (E : edges) (w : node),
  G_well_formed (V, E) = true -> member rand V = false ->
  is_edge (rand, w)
    (rand :: V, remove_edges_out_of T ((rand, T) :: remove_edges_into T E)) = true ->
  w = T.
Proof.
  intros T rand V E w Hwf Hrand Hie.
  apply is_edge_In_edges in Hie.
  apply In_edge_remove_out_randomize in Hie.
  destruct Hie as [Heq | [HinE [_ _]]].
  - inversion Heq. congruence.
  - exfalso. eapply no_edge_from_fresh; eauto.
Qed.

Lemma rct_no_edge_into_rand : forall (T rand : node) (V : nodes) (E : edges) (w : node),
  G_well_formed (V, E) = true -> member rand V = false -> rand <> T ->
  is_edge (w, rand)
    (rand :: V, remove_edges_out_of T ((rand, T) :: remove_edges_into T E)) = false.
Proof.
  intros T rand V E w Hwf Hrand HrandT.
  apply not_In_is_edge_false. intro Hin.
  apply In_edge_remove_out_randomize in Hin.
  destruct Hin as [Heq | [HinE [_ _]]].
  - inversion Heq. congruence.
  - eapply no_edge_to_fresh; eauto.
Qed.

(* No (undirected, acyclic) path joins T and R in the mutilated graph: any such
   path must leave T via [rand -> T], but then can only return to T, never
   reaching R. *)
Lemma rct_no_TR_path : forall (T R rand : node) (V : nodes) (E : edges) (l : nodes),
  G_well_formed (V, E) = true ->
  member rand V = false ->
  rand <> T -> T <> R -> R <> rand ->
  is_path_in_graph (T, R, l)
    (rand :: V, remove_edges_out_of T ((rand, T) :: remove_edges_into T E)) = true ->
  acyclic_path_2 (T, R, l) -> False.
Proof.
  intros T R rand V E l Hwf Hrand HrandT HTR HRrand Hpath Hacyc.
  unfold is_path_in_graph in Hpath.
  destruct l as [| a l'].
  - (* l = [] : path list [T; R] *)
    cbn [app is_path_in_graph_helper] in Hpath.
    rewrite andb_true_r in Hpath.
    rewrite (rct_no_edge_from_T T rand V E R HrandT) in Hpath.
    cbn [orb] in Hpath.
    apply rct_edge_into_T in Hpath. congruence.
  - destruct l' as [| b l''].
    + (* l = [a] : path list [T; a; R] *)
      cbn [app is_path_in_graph_helper] in Hpath.
      rewrite andb_true_r in Hpath.
      apply andb_prop in Hpath. destruct Hpath as [H1 H2].
      rewrite (rct_no_edge_from_T T rand V E a HrandT) in H1.
      cbn [orb] in H1. apply rct_edge_into_T in H1. subst a.
      rewrite (rct_no_edge_into_rand T rand V E R Hwf Hrand HrandT) in H2.
      rewrite orb_false_r in H2.
      apply (rct_edge_from_rand T rand V E R Hwf Hrand) in H2. congruence.
    + (* l = a :: b :: l'' : first two edges are T ~ a and a ~ b *)
      cbn [app is_path_in_graph_helper] in Hpath.
      apply andb_prop in Hpath. destruct Hpath as [H1 Hrest].
      rewrite (rct_no_edge_from_T T rand V E a HrandT) in H1.
      cbn [orb] in H1. apply rct_edge_into_T in H1. subst a.
      apply andb_prop in Hrest. destruct Hrest as [H2 _].
      rewrite (rct_no_edge_into_rand T rand V E b Hwf Hrand HrandT) in H2.
      rewrite orb_false_r in H2.
      apply (rct_edge_from_rand T rand V E b Hwf Hrand) in H2. subst b.
      (* l = rand :: T :: l'', so T occurs in l, contradicting acyclicity *)
      destruct Hacyc as [_ [HnT _]]. apply HnT. right. left. reflexivity.
Qed.

(* If no acyclic undirected path joins u and v, they are d-separated given any Z:
   [d_separated_bool] quantifies over exactly those paths. *)
Lemma dsep_bool_of_no_acyclic_path : forall (u v : node) (G : graph) (Z : nodes),
  G_well_formed G = true ->
  no_one_cycles (snd G) = true ->
  (forall l, is_path_in_graph (u, v, l) G = true -> acyclic_path_2 (u, v, l) -> False) ->
  d_separated_bool u v G Z = true.
Proof.
  intros u v G Z Hwf Hloop Hno.
  unfold d_separated_bool. apply forallb_forall. intros p Hp.
  destruct p as [[u' v'] l].
  assert (Hv : v' = v).
  { destruct G as [V E]. unfold find_all_paths_from_start_to_end in Hp.
    apply filter_In in Hp. destruct Hp as [_ Hend].
    apply Nat.eqb_eq in Hend. simpl in Hend. congruence. }
  assert (Hu : u' = u).
  { destruct G as [V E]. unfold find_all_paths_from_start_to_end in Hp.
    apply filter_In in Hp. destruct Hp as [Hp _].
    assert (Hbase : forall q, In q (edges_as_paths_from_start u E) -> path_start q = u).
    { intros [[qa qb] qc] Hq.
      pose proof (edges_as_paths_from_start_helper u qa qb qc E Hq) as HH.
      simpl. exact HH. }
    pose proof (extend_paths_from_start_iter_start u
                  (edges_as_paths_from_start u E) E (length V) Hbase (u', v', l) Hp) as Hs.
    simpl in Hs. congruence. }
  subst u' v'.
  exfalso. apply (Hno l).
  - apply paths_start_to_end_valid; assumption.
  - apply (paths_start_to_end_acyclic u v l G); assumption.
Qed.

(* MAIN THEOREM.  A simplified RCT is syntactically correct: its post-experiment
   DAG satisfies the backdoor criterion over the treatment T and response R with
   the empty adjustment set.  T and R are the treatment / response nodes of G,
   and [rand] is any node not already present in G. *)
Theorem simple_rct_syntactically_correct :
  forall (G : aug_graph) (F : @graphfun nat) (S : list individual) (T R rand : node),
    wf_aug_graph G ->
    In T (treatment_nodes G) ->             (* T is the treatment node *)
    In R (response_nodes G) ->              (* R is the response node *)
    node_in_graph rand (dag G) = false ->   (* rand is a fresh randomizer *)
    syntactic_backdoor (post_experiment_dag (simple_rct G F S T R rand)) T R [] = true.
Proof.
  intros G F S T R rand Hwf HT HR Hrandfresh.
  (* extract graph-membership and labels of T and R *)
  apply In_nodes_with_label_inv in HT. destruct HT as [HTin HTlab].
  apply In_nodes_with_label_inv in HR. destruct HR as [HRin HRlab].
  destruct Hwf as [HGwf [HGcyc _]].
  (* reduce the post-experiment DAG and expose (V, E) *)
  rewrite post_dag_simple_rct.
  destruct (dag G) as [V E] eqn:Hdag.
  simpl in HTin, HRin, Hrandfresh.
  (* the syntactic backdoor check with Z = [] reduces to a single d-separation *)
  unfold syntactic_backdoor.
  cbn [dedup nodup no_descendant_of_b forallb andb].
  (* derive the disequalities the RCT graph needs *)
  assert (HrandT : rand <> T).
  { intro Heq. rewrite Heq, HTin in Hrandfresh. discriminate. }
  assert (HTR : T <> R).
  { intro Heq. rewrite Heq, HRlab in HTlab. discriminate. }
  assert (HRrand : R <> rand).
  { intro Heq. rewrite Heq, Hrandfresh in HRin. discriminate. }
  apply dsep_bool_of_no_acyclic_path.
  - (* well-formedness of the mutilated post-RCT graph *)
    apply G_well_formed_remove_outgoing.
    apply G_well_formed_randomize; assumption.
  - (* no self loops (from acyclicity) *)
    apply contains_cycle_no_self_loop.
    + apply G_well_formed_remove_outgoing.
      apply G_well_formed_randomize; assumption.
    + apply contains_cycle_remove_outgoing.
      * apply G_well_formed_randomize; assumption.
      * apply contains_cycle_randomize; assumption.
  - (* no undirected path joins T and R after randomizing T *)
    intros l Hpath Hacyc.
    apply (rct_no_TR_path T R rand V E l); assumption.
Qed.
