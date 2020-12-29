Require Import Coq.Init.Datatypes.
Require Import Coq.Structures.Orders.
Require Import Coq.Lists.List. Import ListNotations.
Require Import Coq.Lists.ListSet.
Require Import Coq.Lists.ListDec.
Require Import Coq.Init.Nat.
Require Import Coq.Arith.Peano_dec.
Require Import Coq.Arith.Le.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Classes.RelationClasses.
Require Coq.Program.Tactics.
Require Coq.Program.Wf.
Require Recdef.
From Coq Require Export Permutation.
From Coq Require Export Bool.Bool.
From Coq Require Export Arith.Arith.
From Coq Require Export Omega.

Require Export Setoid.
Require Export Relation_Definitions.

Require Export VerifShortestPathAlg.Graph. Import DirectedWeightedGraph.
Require Export VerifShortestPathAlg.Dijkstra. Import Dijkstra.

From Coq Require Import Lia.

Open Scope bool_scope.

Definition FILL_IN_HERE {T: Type} : T.  Admitted.

Lemma cons_neq : forall (A : Type) (a : A) (l : list A), a :: l <> l.
Proof.
  intros.
  induction l.
  - intro. symmetry in H. apply nil_cons in H. assumption.
  - intro. inversion H. subst. clear H.
    absurd (a0 :: l = l) ; try (assumption).
Qed.

Definition path : Type := list (nat * nat).

Inductive valid_path : DWGraph -> nat -> nat -> path -> Prop :=
| path_self (G : DWGraph) (s : nat) (DS : DijkstraStruct) : 
  eq (C DS s) (value 0) -> valid_path G s s []
| path_adj (G : DWGraph) (u v : nat) : E G u v -> valid_path G u v [(u, v)]
| path_long (G : DWGraph) 
            (u v' v : nat) 
            (p' : path) 
            (H : valid_path G v' v p') : 
            E G u v' -> valid_path G u v ((u, v') :: p').
     
Definition acc_dist (G : DWGraph) (c : cost) (uv : nat * nat) : cost :=
  match c with
  | value dval => value (dval + W G (fst uv) (snd uv))
  | INF => INF 
  end.

Definition path_cost (G : DWGraph) (p : path) : cost :=
  fold_left (acc_dist G) p (value 0).
 
Definition uv_pred_correct (DS : DijkstraStruct) (uv : nat * nat) : Prop :=
  P DS (snd uv) = id (fst uv).

Definition path_correct
  (G : DWGraph) 
  (DS : DijkstraStruct)
  (src dst : nat)
  (p : path) : Prop :=
  valid_path G src dst p /\
  ~ eq (path_cost G p) INF /\
  eq (path_cost G p) (C DS dst) /\
  Forall (uv_pred_correct DS) p.

Definition path_globally_optimal
  (G : DWGraph)
  (src dst : nat)
  (p : path) : Prop :=
  forall p', 
  valid_path G src dst p' -> le (path_cost G p) (path_cost G p').

Definition pair_in_list (S : set nat) (uv : nat * nat) : Prop :=
  In (fst uv) S /\ In (snd uv) S.

Definition all_hops_in_popped (p : path) (S : set nat) : Prop :=
  Forall (pair_in_list S) p.

Check (set_diff).

Definition inv_popped
  (G : DWGraph)
  (src : nat)
  (DS : DijkstraStruct)
  (q : priqueue)
  (dst : nat) : Prop := 
  exists p : path, 
    path_correct G DS src dst p /\
    all_hops_in_popped p (set_diff eq_nat_dec (all_nodes G) q) /\
    path_globally_optimal G src dst p.

Definition inv_popped_for_nodes_in_popped
  (G : DWGraph)
  (src : nat)
  (DS : DijkstraStruct)
  (q : priqueue)
  (S : set nat) : Prop :=
  Forall (inv_popped G src DS q) S.

Definition sp_outside_popped
  (G : DWGraph)
  (src dst : nat)
  (q : priqueue)
  (p : path) : Prop :=
  ~ all_hops_in_popped p (set_diff eq_nat_dec (all_nodes G) q) /\
  path_globally_optimal G src dst p.

Lemma and_snd_imply : forall P Q R : Prop,
  (Q -> R) -> P /\ Q -> P /\ R.
Proof.
  intros.
  split.
  - inversion H0. exact H1.
  - inversion H0. apply H in H2. exact H2.
Qed.

Lemma and_not_and_or : forall P Q R : Prop,
  P /\ ~ (Q /\ R) -> P /\ (~ Q \/ ~ R).
Proof.
  intros.
  split.
  - inversion H. exact H0.
  - inversion H. apply not_and_or in H1. exact H1.
Qed.

Lemma if_not_all_hops_in_popped_exists_x_y :
  forall
    (p : path)
    (S : set nat),
  ~ all_hops_in_popped p S ->
  exists xy : nat * nat,
    In xy p /\
    (~ In (fst xy) S \/ ~In (snd xy) S).
Proof.
  intros.
  unfold all_hops_in_popped in H.
  apply Exists_Forall_neg in H.
  - apply Exists_exists in H.
    unfold pair_in_list in H.
    destruct H.
    apply and_not_and_or in H.
    exists x.
    exact H.
  - intros.
    tauto.
Qed.

Lemma if_sp_outside_popped_exist_x_y :
  forall
    (G : DWGraph)
    (src dst x y: nat)
    (DS : DijkstraStruct)
    (q : priqueue)
    (p : path)
    (S : set nat),
  In x S ->
  S = set_diff eq_nat_dec (all_nodes G) q ->
  inv_popped_for_nodes_in_popped G src DS q S ->
  sp_outside_popped G src dst q p ->
  exists xy : nat * nat,
    In xy p /\ In (fst xy) S /\ ~ In (snd xy) S.
Proof.
  intros.
  inversion H2. 
  apply if_not_all_hops_in_popped_exists_x_y in H3.
Admitted. 

(**
  1. u = extract_min q (C DS)  
  2. exists p from s to u (valid_path G s u p)
  3. (C DS u) <> sp s u
  4. (x, y) in p s.t. In x S /\ ~ In y S
  5. (C DS y) = sp s y, 
        because loop_invar_holds -> (In x S) -> (C DS x) = sp s x -> (x, y) relaxed
          -> convergence property
  6. path s y u -> non-negative weights -> sp s y <= sp s u = (C DS u)
        because of the upper-bound property
  7. (C DS u) <= (C DS y) (because u = extract_min q (C DS))
  8. Thus (C DS u) = sp s u
        CONTRADICTION HERE.
*)

(**
  Some (u, q') = extract_min q (C DS) ->
  exists p : path, 
    path_is_shortest G s u p /\
    ~ eq (C DS u) (path_cost G p) ->
  ##### TODO : Prove link between above and below #####
  exists xy : nat * nat,
    In xy p /\
    In x S /\ ~ In y S ->
  exists p' : path,
    path_is_shortest G s y p' ->
  ##### TODO : Prove link between above and below #####
  eq (C DS y) (path_cost G p')
  DERIVE le (path_cost G p') (path_cost G p)
  DERIVE le (path_cost G p) (C DS u)
  DERIVE le (C DS u) (C DS y)
  DERIVE eq (path_cost G p) (C DS u)
  CONTRADICTION
  THUS ~ exist p
  DERIVE 
    inv_popped u holds ->
    S' = set_union S [u] ->
    dijkstra_loop_invar S' holds.
*)

Definition path_is_shortest (G : DWGraph) (src dst : nat) (p : path) : Prop :=
  valid_path G src dst p /\ path_globally_optimal G src dst p.
  
Definition sp_exists (G : DWGraph) (src dst : nat) : Prop :=
  exists p : path, path_is_shortest G src dst p.

Definition dijkstra_loop_invar 
  (G : DWGraph)
  (src : nat)
  (DS : DijkstraStruct)
  (q : priqueue) : Prop :=
  subset q (all_nodes G) /\
  Forall (inv_popped G src DS q) (set_diff eq_nat_dec (all_nodes G) q).

Definition dijkstra_incorrect_for_path
  (G : DWGraph)
  (DS : DijkstraStruct)
  (src u : nat)
  (p : path) : Prop :=
  path_is_shortest G src u p /\
  (C DS u) <> (path_cost G p).

Definition exists_p_su_neq_sp_cost_cost_map
  (G : DWGraph)
  (DS : DijkstraStruct)
  (q q' : priqueue) 
  (src u : nat) : Prop :=
  extract_min q (C DS) = Some (u, q') ->
  exists p : path, dijkstra_incorrect_for_path G DS src u p.

Lemma exists_p_su_implies_exists_x_y :
  forall
    (G : DWGraph)
    (DS : DijkstraStruct)
    (src y u : nat)
    (q q' : priqueue)
    (p : path),
  dijkstra_loop_invar G src DS q ->
  extract_min q (C DS) = Some (u, q') ->
  exists_p_su_neq_sp_cost_cost_map G DS q q' src u ->
  (* dijkstra_incorrect_for_path G DS src u p -> *)
  exists x : nat,
    In (x, y) p /\
    In x (set_diff eq_nat_dec (all_nodes G) q) /\ 
    ~ In y (set_diff eq_nat_dec (all_nodes G) q).
Proof. 
  intros.
  unfold exists_p_su_neq_sp_cost_cost_map in H1.
  apply H1 in H0.
  destruct H0.
  unfold dijkstra_incorrect_for_path in H0. 
  inversion H0.
  unfold path_is_shortest in H2.
  inversion H2.
  unfold dijkstra_loop_invar in H.
  inversion H.
  rewrite Forall_forall in H7.
  exact FILL_IN_HERE.
Qed.

Lemma exists_x_y_implies_exists_p_sy :
  forall
    (G : DWGraph)
    (DS : DijkstraStruct)
    (src u : nat)
    (q q' : priqueue)
    (p : path)
    (xy : nat * nat),
  dijkstra_loop_invar G src DS q ->
  (* exists_p_su_neq_sp_cost_cost_map G DS src u q q' -> *)
  (* dijkstra_incorrect_for_path G DS src u p -> *)
  In xy p ->
  In (fst xy) (set_diff eq_nat_dec (all_nodes G) q) ->
  ~ In (snd xy) (set_diff eq_nat_dec (all_nodes G) q) ->
  exists p' : path,
    path_is_shortest G src (snd xy) p' /\
    eq (C DS (snd xy)) (path_cost G p') /\
    p = p' ++ [(snd xy, u)].
Proof. Admitted.

(* Lemma eq_p_sy_cost_map_actual_cost :
  forall
    (G : DWGraph)
    (DS : DijkstraStruct)
    (src u : nat)
    (q q' : priqueue)
    (p' : path)
    (xy : nat * nat),
  dijkstra_loop_invar G src DS q ->
  (* exists_p_su_neq_sp_cost_cost_map G DS src u q q' -> *)
  (* dijkstra_incorrect_for_path G DS src u p -> *)
  (* In xy p /\ *)
  (* In (fst xy) (set_diff eq_nat_dec (all_nodes G) q) /\  *)
  (* ~ In (snd xy) (set_diff eq_nat_dec (all_nodes G) q) -> *)
  path_is_shortest G src (snd xy) p' ->
  eq (C DS (snd xy)) (path_cost G p').
Proof. Admitted. *)

Lemma if_shortest_path_cost_increases :
  forall
    (G: DWGraph)
    (src y u : nat)
    (p p' : path),
  path_is_shortest G src u p ->
  path_is_shortest G src y p' ->
  p = p' ++ [(y, u)] ->
  le (path_cost G p') (path_cost G p).
Proof. Admitted.

(* Lemma subset_implies_diff_union : forall (s s' : set nat),
  subset s s' -> set_union eq_nat_dec s (set_diff eq_nat_dec s' s) = s'.
Proof.
  intros.
  unfold subset in H.
  rewrite Forall_forall in H.
  rewrite set_In in H.
Qed. *)

(* Lemma neg_neg : forall P : Prop,
  ~ ~ P -> P.
Proof.
  intros.
  
  Search (_ -> False -> _).
Qed. *)

Lemma imply_contrapositive : forall (P Q : Prop),
  (P -> Q) -> (~ Q -> ~ P).
Proof. intros. intro. apply H0. apply H. exact H1. Qed.

Lemma imply_contrapositive2 : forall (P Q : Prop),
  (P -> Q) -> ~ Q -> ~ P.
Proof. intros. intro. apply H0. apply H in H1. exact H1. Qed.

Lemma imply_contrapositive3 : forall (P Q : Prop),
  (P -> Q) -> ~ Q -> P -> ~ P.
Proof.
  intros P Q P_implies_Q not_Q P_holds.
  intro Prop_acc.
  apply not_Q.
  apply P_implies_Q in Prop_acc.
  exact Prop_acc.
Qed.

Lemma not_in_S_implies_in_q :
  forall
    (G : DWGraph)
    (v : nat)
    (q : priqueue),
  subset q (all_nodes G) ->
  ~ set_In v (set_diff eq_nat_dec (all_nodes G) q) ->
  set_In v q.
Proof.
  intros.
  rewrite set_diff_iff in H0.
  apply not_and_or in H0. 
  unfold subset in H.
  rewrite Forall_forall in H.
  specialize (H v).
  unfold set_In in *.
  inversion H0. 
  - rewrite <- Decidable.contrapositive in H.
    + exact FILL_IN_HERE.
    + exact (In_decidable (PeanoNat.Nat.eq_decidable) v (all_nodes G)).
    
  - unfold set_In.
    apply Decidable.not_not.
    + exact (In_decidable (PeanoNat.Nat.eq_decidable) v q).
    + exact H1.
Qed.

Lemma extract_in_q : 
  forall (DS : DijkstraStruct) (u : nat) (q q': priqueue),
  Some (u, q') = extract_min q (C DS) ->
  set_In u q.
Proof.
  intros.
  induction q as [|hq tq].
  - unfold extract_min in H.
    absurd (Some (u, q') = None).
    + discriminate.
    + exact H.
  - unfold extract_min in H.
    exact FILL_IN_HERE.
Qed.

Lemma extract_min_correct :
  forall
    (DS : DijkstraStruct)
    (q q' : priqueue)
    (u : nat),
  extract_min q (C DS) = Some (u, q')  ->
  Forall (fun v => le (C DS u) (C DS v)) q'.
Proof.
  intros.
  unfold extract_min in H.
  destruct q.
  - absurd (None = Some (u, q')).
    + inversion H.
    + exact H.
  - destruct (select_min_in_cost_map n q (C DS)) eqn:Eq_let in H.
    Check (select_min_correct).
    apply (select_min_correct n q n0 l (C DS)) in Eq_let.
    apply option_equal_implies_boxed_equal in H.
    apply pair_equal_spec in H.
    inversion H. subst.
    exact Eq_let.
Qed.

Lemma neq_cost_neq_id : forall u v (cost: cost_map),
  ~ eq (cost u) (cost v) -> u <> v.
Proof.
  intros.
  unfold not in *.
  intros.
  rewrite H0 in H.
  assert (eq (cost0 v) (cost0 v)).
  { apply eq_refl. }
  apply H in H1.
  contradiction.
Qed.

Lemma le_cost_map_u_y :
  forall
    (DS : DijkstraStruct)
    (q q' : priqueue)
    (u y : nat),
  set_In y q ->
  extract_min q (C DS) = Some (u, q') ->
  le (C DS u) (C DS y).
Proof.
  intros. bdestruct (Dijkstra.eqb (C DS u) (C DS y)).
  - Check (eq_implies_le). apply eq_implies_le. assumption.
  - apply neq_cost_neq_id in H1.
    unfold set_In in H.
    assert (Hsp := extract_perm u q' q (C DS) H0).
    apply Permutation_in with (x := y) in Hsp.
    simpl in Hsp.
    destruct Hsp.
    + unfold not in H1. apply H1 in H2.
      contradiction.
    + apply extract_min_correct in H0.
      rewrite Forall_forall in H0.
      specialize (H0 y).
      apply H0 in H2.
      assumption.
    + assumption.
Qed.

Lemma eq_0_Sn_false : forall n, 0 = S n -> False.
Proof. intros. induction n ; try (discriminate). Qed.

Lemma value_equal_implies_eq : forall (n m : nat),
  value n = value m -> n = m.
Proof. intros. inversion H. reflexivity. Qed.

Lemma le_nat_both_ways_implies_eq : forall n m,
  n <= m -> m <= n -> n = m.
Proof. intros. nia. Qed.

Lemma le_both_ways_implies_eq : forall (c c' : cost),
  le c c' -> le c' c -> c = c'.
Proof.
  intros.
  unfold le in *.
  destruct c, c'.
  - apply (le_nat_both_ways_implies_eq v v0 H) in H0.
    rewrite H0.
    reflexivity.
  - contradiction.
  - contradiction.
  - reflexivity.
Qed.

Lemma no_non_dijkstra_optimal_path_to_u_exists :
  forall
    (G : DWGraph)
    (DS : DijkstraStruct)
    (src y u : nat)
    (q q' : priqueue)
    (p : path),
  dijkstra_loop_invar G src DS q ->
  path_is_shortest G src u p ->
  extract_min q (C DS) = Some (u, q') ->
  ~ In y (set_diff eq_nat_dec (all_nodes G) q) ->
  ~ exists_p_su_neq_sp_cost_cost_map G DS q q' src u.
Proof.
  unfold not.
  intros.
  unfold exists_p_su_neq_sp_cost_cost_map in H3.
  apply (exists_p_su_implies_exists_x_y G DS src y u q q' p H) in H3. 
  - destruct H3.
    destruct H3.
    destruct H4.
    apply (exists_x_y_implies_exists_p_sy G DS src u q q' p (x, y) H H3  H4) in H5.
    destruct H5.
    destruct H5.
    destruct H6.
    simpl in H5, H6, H7.
    assert (le_sp_y_sp_u : le (path_cost G x0) (path_cost G p)).
    { apply (if_shortest_path_cost_increases G src y u p x0 H0 H5 H7). }
    assert (le_sp_u_cost_map_u : le (path_cost G p) (C DS u)).
    {
      exact FILL_IN_HERE.
    }
    assert (le_cost_map_y_cost_map_u : le (C DS y) (C DS u)).
    { apply cost_in_le_fst_replaceable with (c := C DS y) in le_sp_y_sp_u.
      apply (
        Dijkstra.le_trans (C DS y) (path_cost G p) (C DS u) le_sp_y_sp_u le_sp_u_cost_map_u
      ). assumption. }
    unfold dijkstra_loop_invar in H.
    inversion H.
    (* y is member of set q *)
    apply (not_in_S_implies_in_q G y q H8) in H2.
    apply (le_cost_map_u_y DS q q' u y H2) in H1.
    apply (le_both_ways_implies_eq) in le_cost_map_y_cost_map_u.
    + exact FILL_IN_HERE.
    + assumption.
  - assumption.
Qed.

Lemma props_flattenable : forall P Q R : Prop,
  ((P -> Q) -> R) -> (P -> Q -> R).
Proof.
  intros.
  assert (P_implies_Q_holds : P0 -> Q).
  { intros. assumption. }
  apply H in P_implies_Q_holds.
  assumption.
Qed.

Lemma no_non_dijkstra_opt_implies_invar : 
  forall
    (G : DWGraph)
    (DS DS': DijkstraStruct)
    (src y u : nat)
    (q q' : priqueue)
    (p : path),
  (* current loop invariant *)
  dijkstra_loop_invar G src DS q ->
  (* properties on the next argument *)
  extract_min q (C DS) = Some (u, q') ->
  DS' = relax_adjacents G DS u ->
  (* no no dijkstra optimal path exists *)
  ~ exists_p_su_neq_sp_cost_cost_map G DS q q' src u ->
  (* next loop invariant *)
  dijkstra_loop_invar G src DS' q'.
Proof. 
  intros.
  unfold dijkstra_loop_invar in *.
  inversion H. subst. clear H.
  split.
  - apply (extract_min_res_subset u q q') in H0.
    apply (subset_trans q' q (all_nodes G) H0 H3).
  (* - rewrite Forall_forall in *. *)
  - intros. 
    unfold inv_popped in *.
    unfold exists_p_su_neq_sp_cost_cost_map in H2.
    unfold dijkstra_incorrect_for_path in H2.
    unfold path_is_shortest in H2.
    unfold path_correct in *.
    unfold not in H2.
    exact FILL_IN_HERE.
Qed.

Check (dijkstra_loop_equation).

Lemma dijkstra_loop_correct :
  forall
    (G G' : DWGraph)
    (DS DS': DijkstraStruct)
    (src y u : nat)
    (q q' : priqueue)
    (p : path),
  dijkstra_loop_invar G src DS q ->
  (q', DS') = dijkstra_loop G q DS ->
  dijkstra_loop_invar G src DS' q'.
Proof.
  intros.
  rewrite dijkstra_loop_equation in H0.
  destruct (extract_min q (C DS)) eqn:Eq_ext_res in H0.
  - destruct p0 eqn:Eq_let in H0.
    rewrite Eq_let in Eq_ext_res.
    remember (relax_adjacents G DS n) as DS_next.
    Check (no_non_dijkstra_optimal_path_to_u_exists).
    assert (Hnndop := no_non_dijkstra_optimal_path_to_u_exists G DS src y u q q' p).
    assert (
      Hnndop_applied := 
        no_non_dijkstra_opt_implies_invar G DS DS_next src y n q p1 p H Eq_ext_res).
    exact FILL_IN_HERE.
    (* apply Hnndop in H. *)
    (* Check (no_non_dijkstra_opt_implies_invar). *)
    (* exact FILL_IN_HERE. *)
    (* apply (no_non_dijkstra_opt_implies_invar G DS DS_next src y n q pq p) in H.
    + assumption.
    + assumption. *)
    (* exact FILL_IN_HERE. *)
  (* Proof below this line is complete *)
  - apply pair_equal_spec in H0.
    inversion H0. subst.
    assumption.
Qed.

Lemma convergence_prop :
  forall
    (G : DWGraph)
    (DS DS' : DijkstraStruct)
    (s u v : nat) 
    (p_su : path),
  valid_path G s u p_su ->
  path_is_shortest G s v (p_su ++ [(u, v)]) ->
  eq (C DS u) (path_cost G p_su) ->
  DS' = relax G u DS v ->
  eq (C DS' v) (path_cost G (p_su ++ [(u, v)])).
Proof. Admitted.
