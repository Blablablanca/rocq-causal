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
    (st st' : unit_state) (n w : node) (v : nat),
  G_well_formed G0 = true ->
  contains_cycle G0 = false ->
  node_in_graph n G0 = true ->
  is_assignment_for U (nodes_in_graph G0) = true ->
  node_in_graph w G0 = true ->
  apply_op G0 ((n, v) :: U) st (Randomize n) = Some st' ->
  find_value G0 (cur_fun st') w ((n, v) :: U) [] = semantic_do n v G0 (cur_fun st) w U.
Proof.
  intros G0 U st st' n w v Hwf Hcyc Hn HU Hw Hop.
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
   [Randomize T] performs the same structural surgery as an intervention --
   it removes T's incoming edges (the randomizer is the experimenter's coin,
   not a node of the model) -- so the backdoor check with Z = [] runs on
   [remove_outgoing T (remove_incoming T G)], in which T is completely
   ISOLATED: no edge enters it (severed by randomization) and none leaves it
   (severed by the backdoor mutilation).  No undirected path joins T to
   anything, so d-separation is immediate.
   ===================================================================== *)

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

(* Every edge of the doubly mutilated graph avoids T on both endpoints. *)
Lemma In_edge_isolate : forall (T : node) (E : edges) (u w : node),
  In (u, w) (remove_edges_out_of T (remove_edges_into T E)) ->
  u <> T /\ w <> T.
Proof.
  intros T E u w Hin.
  unfold remove_edges_out_of in Hin.
  apply filter_In in Hin. destruct Hin as [Hin HfT].
  simpl in HfT. apply negb_true_iff in HfT. apply Nat.eqb_neq in HfT.
  apply In_remove_edges_into in Hin. destruct Hin as [_ HsT].
  simpl in HsT.
  split; assumption.
Qed.

(* T is an isolated vertex of the doubly mutilated graph: no edge touches it. *)
Lemma no_edge_touching_isolated : forall (T a b : node) (G : graph),
  a = T \/ b = T ->
  is_edge (a, b) (remove_outgoing T (remove_incoming T G)) = false.
Proof.
  intros T a b [V E] Hab.
  unfold remove_outgoing, remove_incoming. cbn [fst snd].
  apply not_In_is_edge_false. intro Hin.
  apply In_edge_isolate in Hin. destruct Hin as [HaT HbT].
  destruct Hab as [Ha | Hb]; congruence.
Qed.

(* Hence NO undirected path leaves T at all: its first hop would need an edge
   touching T in one direction or the other. *)
Lemma isolated_no_TR_path : forall (T R : node) (G : graph) (l : nodes),
  is_path_in_graph (T, R, l) (remove_outgoing T (remove_incoming T G)) = true ->
  False.
Proof.
  intros T R G l Hpath.
  unfold is_path_in_graph in Hpath.
  destruct l as [| a l'].
  - (* l = [] : path list [T; R] *)
    cbn [app is_path_in_graph_helper] in Hpath.
    rewrite andb_true_r in Hpath.
    rewrite (no_edge_touching_isolated T T R G (or_introl eq_refl)) in Hpath.
    cbn [orb] in Hpath.
    rewrite (no_edge_touching_isolated T R T G (or_intror eq_refl)) in Hpath.
    discriminate Hpath.
  - (* l = a :: l' : first hop is T ~ a *)
    cbn [app is_path_in_graph_helper] in Hpath.
    apply andb_prop in Hpath. destruct Hpath as [H1 _].
    rewrite (no_edge_touching_isolated T T a G (or_introl eq_refl)) in H1.
    cbn [orb] in H1.
    rewrite (no_edge_touching_isolated T a T G (or_intror eq_refl)) in H1.
    discriminate H1.
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
   the empty adjustment set.  The label hypotheses document the design reading
   (T is the treatment, R the response); the isolation argument itself does not
   need them -- randomizing T d-separates it from EVERYTHING. *)
Theorem simple_rct_syntactically_correct :
  forall (G : aug_graph) (F : @graphfun nat) (S : list individual) (T R : node),
    wf_aug_graph G ->
    In T (treatment_nodes G) ->             (* T is the treatment node *)
    In R (response_nodes G) ->              (* R is the response node *)
    syntactic_backdoor (post_experiment_dag (simple_rct G F S T R)) T R [] = true.
Proof.
  intros G F S T R Hwf HT HR.
  destruct Hwf as [HGwf [HGcyc _]].
  (* the post-experiment DAG is the intervention surgery on T *)
  rewrite post_dag_simple_rct.
  (* the syntactic backdoor check with Z = [] reduces to a single d-separation *)
  unfold syntactic_backdoor.
  cbn [dedup nodup no_descendant_of_b forallb andb].
  apply dsep_bool_of_no_acyclic_path.
  - (* well-formedness of the doubly mutilated graph *)
    apply G_well_formed_remove_outgoing.
    rewrite <- do_remove_incoming.
    apply G_well_formed_do. exact HGwf.
  - (* no self loops (from acyclicity) *)
    apply contains_cycle_no_self_loop.
    + apply G_well_formed_remove_outgoing.
      rewrite <- do_remove_incoming.
      apply G_well_formed_do. exact HGwf.
    + apply contains_cycle_remove_outgoing.
      * rewrite <- do_remove_incoming.
        apply G_well_formed_do. exact HGwf.
      * rewrite <- do_remove_incoming.
        apply contains_cycle_do; assumption.
  - (* T is isolated: no path joins it to R at all *)
    intros l Hpath _.
    exact (isolated_no_TR_path T R (dag G) l Hpath).
Qed.
