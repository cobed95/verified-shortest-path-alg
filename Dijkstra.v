Require Import Coq.Init.Datatypes.
Require Import Coq.Init.Nat.
Require Import Coq.Lists.List. Import ListNotations.
Require Import Coq.Lists.ListSet.
Require Import Coq.Lists.ListDec.
Require Import Coq.Classes.RelationClasses.
Require Export Setoid.
Require Export Relation_Definitions.

From Coq Require Export Permutation.
From Coq Require Import Lia.
From Coq Require Export Arith.Arith.
From Coq Require Export Bool.Bool.

Require Recdef.

Require Export VerifShortestPathAlg.Graph. Import DirectedWeightedGraph.

Module Dijkstra.

Inductive cost :=
| value (v : nat)
| INF.

Definition eq (c c' : cost) :=
  match c, c' with
  | value cv, value cv' => cv = cv'
  | INF, INF => True
  | _, _ => False
  end.

Definition eqb (c c' : cost) :=
  match c, c' with
  | value cv, value cv' => cv =? cv'
  | INF, INF => true
  | _, _ => false
  end.

Definition lt (c c' : cost) :=
  match c, c' with
  | value cv, value cv' => cv < cv'
  | value _, INF => True
  | INF, value _ => False
  | INF, INF => False
  end.

Definition ltb (c c' : cost) :=
  match c, c' with
  | value cv, value cv' => cv <? cv'
  | value _, INF => true
  | INF, value _ => false
  | INF, INF => false
  end.

Definition le (c c' : cost) :=
  match c, c' with
  | value cv, value cv' => cv <= cv'
  | value _, INF => True
  | INF, value _ => False
  | INF, INF => True
  end.

Lemma eq_refl : Reflexive eq.
Proof.
  unfold Reflexive.
  intros. destruct x ; reflexivity.
Qed.

Check (Symmetric).

Lemma eq_sym : Symmetric eq.
Proof.
  unfold Symmetric. unfold eq.
  intros. destruct x, y ; try (contradiction).
  - rewrite H. reflexivity.
  - tauto.
Qed.

Lemma eq_trans : Transitive eq.
Proof.
  unfold Transitive. unfold eq.
  intros. destruct x, y, z ; try (contradiction).
  - rewrite H, <- H0. reflexivity.
  - tauto.
Qed.

Axiom eq_cost_refl : reflexive _ (eq).
Axiom eq_cost_sym : symmetric _ (eq).
Axiom eq_cost_trans : transitive _ (eq).

Add Parametric Relation : (cost) (@eq)
  reflexivity proved by (eq_cost_refl)
  symmetry proved by (eq_cost_sym)
  transitivity proved by (eq_cost_trans)
  as eq_cost_rel.

Goal eq (value 0) (value 0).
Proof. intros. reflexivity. Qed.

Lemma cost_in_le_fst_replaceable : forall c c' c'',
  eq c c' -> le c' c'' -> le c c''.
Proof.
  unfold eq, le. intros.
  destruct c, c', c''.
  - rewrite H. assumption.
  - tauto.
  - contradiction.
  - tauto.
  - contradiction.
  - tauto.
  - contradiction.
  - tauto.
Qed.

Lemma cost_in_le_snd_replaceable : forall c c' c'',
  eq c c'' -> le c' c'' -> le c' c.
Proof.
  unfold eq, le. intros.
  destruct c, c', c''.
  - rewrite H. assumption.
  - tauto.
  - contradiction.
  - tauto.
  - contradiction.
  - tauto.
  - contradiction.
  - tauto.
Qed.

Lemma le_c : forall (c : cost), le c c.
Proof.
  intros.
  destruct c.
  - unfold le. reflexivity.
  - unfold le. tauto.
Qed.

Lemma le_refl : Reflexive le.
Proof.
  unfold Reflexive.
  intros. apply le_c.
Qed.

Lemma eq_implies_le : forall (c c' : cost),
  eq c c' -> le c c'.
Proof.
  unfold eq, le.
  intros.
  destruct c, c'. 
  - rewrite H. reflexivity.
  - contradiction.
  - contradiction.
  - assumption.
Qed.

Lemma le_trans : forall (c c' c'' : cost),
  le c c' -> le c' c'' -> le c c''.
Proof.
  unfold le.
  intros.
  destruct c, c', c''; try (assumption).
  - apply (PeanoNat.Nat.le_trans v v0 v1 H H0).
  - contradiction.
Qed.

Definition leb (c c' : cost) :=
  match c, c' with
  | value cv, value cv' => cv <=? cv'
  | value _, INF => true
  | INF, value _ => false 
  | INF, INF => true 
  end.

Definition add (c c' : cost) : cost :=
  match c, c' with 
  | value cv, value cv' => value (cv + cv')
  | _, _ => INF
  end.

Lemma eqb_eq : forall (c c' : cost), eqb c c' = true <-> eq c c'.
Proof.
  intros.
  split ; intros ; unfold eqb, eq in * ; destruct c, c'.
  - apply Nat.eqb_eq in H. assumption.
  - absurd (false = true).
    + discriminate.
    + assumption.
  - absurd (false = true).
    + discriminate.
    + assumption.
  - tauto.
  - apply Nat.eqb_eq. assumption.
  - contradiction.
  - contradiction.
  - reflexivity.
Qed.

Lemma ltb_lt : forall (c c' : cost), ltb c c' = true <-> lt c c'.
Proof.
  intros.
  split ; intros; unfold ltb, lt in * ; destruct c, c'.
  - apply Nat.ltb_lt. assumption.
  - tauto.
  - absurd (false = true).
    * discriminate.
    * assumption.
  - absurd (false = true).
    * discriminate.
    * assumption.
  - apply Nat.ltb_lt. assumption.
  - reflexivity.
  - contradiction.
  - contradiction.
Qed.

Lemma leb_le : forall (c c' : cost), leb c c' = true <-> le c c'.
Proof.
  intros.
  split ; intros; unfold leb, le in * ; destruct c, c'.
  - apply Nat.leb_le. assumption.
  - tauto.
  - absurd (false = true).
    * discriminate.
    * assumption.
  - tauto.
  - apply Nat.leb_le. assumption.
  - reflexivity.
  - contradiction.
  - reflexivity.
Qed.

Lemma eqb_reflect : forall (x y : cost), reflect (eq x y) (eqb x y).
Proof.
  intros x y. apply iff_reflect. symmetry.
  apply eqb_eq.
Qed.

Lemma ltb_reflect : forall x y, reflect (lt x y) (ltb x y).
Proof.
  intros x y. apply iff_reflect. symmetry.
  apply ltb_lt.
Qed.

Lemma leb_reflect : forall x y, reflect (le x y) (leb x y).
Proof.
  intros x y. apply iff_reflect. symmetry.
  apply leb_le.
Qed.

Hint Resolve ltb_reflect leb_reflect eqb_reflect : bdestruct.

Ltac bdestruct X :=
  let H := fresh in let e := fresh "e" in
   evar (e: Prop);
   assert (H: reflect e X); subst e;
    [eauto with bdestruct
    | destruct H as [H|H];
       [ | try first [apply not_lt in H | apply not_le in H]]].

Inductive prev :=
| id (v : nat)
| UNDEF.

Definition total_map (A : Type) := nat -> A.
Definition empty_map {A : Type} (v : A) : total_map A := fun _ => v.
Definition update_map {A : Type} (map : total_map A) (k : nat) (v : A) : total_map A :=
  fun id => if id =? k then v else map id.

Definition cost_map : Type := total_map cost.
Definition prev_map : Type := total_map prev.

Lemma le_gt_le : forall (c c' c'' : cost), le c c' -> ~ le c'' c' -> le c c''.
Proof.
  intros. unfold le, leb in *.
  destruct c, c', c'' ; try (tauto ; contradiction). lia.
Qed.

Fixpoint select_min_in_cost_map
  (x : nat) (l : list nat) (cost : cost_map) : nat * list nat :=
  match l with
  | [] => (x, [])
  | hd :: tl =>
    if leb (cost x) (cost hd)
    then
      let (y, l') := select_min_in_cost_map x tl cost in
      (y, hd :: l')
    else
      let (y, l') := select_min_in_cost_map hd tl cost in
      (y, x :: l')
  end.

Lemma select_perm: forall x l cost,
  let (y, r) := select_min_in_cost_map x l cost in
  Permutation (x :: l) (y :: r).
Proof.
intros x l. generalize dependent x.
induction l; intros; simpl in *.
- apply Permutation_refl.
- bdestruct (leb (cost0 x) (cost0 a)).
  + specialize (IHl x cost0). destruct (select_min_in_cost_map x l cost0).
    Search (Permutation (_ :: _ :: _) (_ :: _ :: _)).
    rewrite perm_swap. apply Permutation_sym. rewrite perm_swap.
    apply perm_skip. apply Permutation_sym. apply IHl.
  + specialize (IHl a cost0). destruct (select_min_in_cost_map a l cost0).
    apply Permutation_sym. rewrite perm_swap.
    apply perm_skip. apply Permutation_sym. apply IHl.
Qed.

Lemma select_smallest_aux: forall x al y bl cost,
  Forall (fun z => le (cost y) (cost z)) bl ->
  select_min_in_cost_map x al cost = (y, bl) ->
  le (cost y) (cost x).
Proof.
intros x al y bl cost HF Hs. assert (Hsp := select_perm x al cost).
destruct (select_min_in_cost_map x al cost). inversion Hs. subst.
Search (Permutation _ _ -> In _ _ -> In _ _).
apply Permutation_in with (x := x) in Hsp.
- destruct Hsp.
  + rewrite H. apply le_refl.
  + Check Forall_forall. rewrite Forall_forall in HF.
    apply HF. apply H.
- unfold In. left. reflexivity.
Qed.

Lemma select_min_correct:
  forall x l y l' cost,
  select_min_in_cost_map x l cost = (y, l') ->
  Forall (fun v => le (cost y) (cost v)) l'.
Proof.
  intros x al. generalize dependent x.
  induction al; intros; simpl in *.
  - inversion H. subst. Search (Forall _ []). apply Forall_nil.
  - bdestruct (leb (cost0 x) (cost0 a)).
    + destruct (select_min_in_cost_map x al cost0) eqn:?H. inversion H. subst. clear H.
      Search (Forall _ (_ :: _)). apply Forall_cons. 
      * Check le_trans. apply le_trans with (c' := cost0 x).
        { apply (select_smallest_aux x al y l cost0).
          - apply IHal with (x := x). apply H1.
          - apply H1. }
        { apply H0. }
      * apply IHal with (x := x). apply H1.
    + destruct (select_min_in_cost_map a al cost0) eqn:?H. inversion H. subst.
      apply Forall_cons.
      * assert (Hs: le (cost0 y) (cost0 a)).
        { apply (select_smallest_aux _ al _ l).
          - apply IHal with (x := a). apply H1.
          - apply H1. }
        { apply le_gt_le with (c' := cost0 a); assumption. }
      * apply IHal with (x := a). apply H1.
Qed.
 
Lemma select_min_length_constant: 
  forall
    (x y : nat) (l l' : list nat) (cost : cost_map),
  select_min_in_cost_map x l cost = (y, l') ->
  length l = length l'.
Proof.
  intros. 
  assert (Hsp := select_perm x l cost0).
  destruct (select_min_in_cost_map x l cost0) eqn:Eq_let in Hsp.
  apply Permutation_length in Hsp.
  rewrite H in Eq_let.
  apply pair_equal_spec in Eq_let.
  inversion Eq_let. simpl in Hsp.
  Search (S _ = S _ -> _ = _).
  rewrite <- H1 in Hsp.
  rewrite Nat.succ_inj_wd in Hsp.
  assumption.
Qed.

Definition subset (s s' : set nat) : Prop :=
  Forall (fun x => set_In x s') s.
Definition eq_set (s s' : set nat) : Prop :=
  subset s s' /\ subset s' s.

Lemma subset_trans : forall (s s' s'' : set nat),
  subset s s' -> subset s' s'' -> subset s s''.
Proof.
  intros.
  unfold subset in *.
  rewrite Forall_forall in *.
  unfold set_In in *.
  intro.
  specialize (H x).
  specialize (H0 x).
  Search ((_ -> _) /\ (_ -> _) -> (_ -> _)).
  intro.
  apply H in H1.
  apply H0 in H1.
  assumption.
Qed.

Lemma Permutation_tail_subset : forall u s s',
  Permutation s' (u :: s) -> subset s s'.
Proof.
  intros.
  unfold subset. rewrite Forall_forall. unfold set_In.
  intros.
  apply Permutation_sym in H.
  apply Permutation_in with (x := x) in H.
  - assumption.
  - simpl. right. assumption.
Qed.

Definition priqueue : Type := set nat.
Definition extract_min 
  (q : priqueue) (cost : cost_map) : option (nat * priqueue) :=
  match q with
  | [] => None
  | hd :: tl =>
    let (v', q') := select_min_in_cost_map hd tl cost in
    Some (pair v' q')
  end.

Lemma option_equal_implies_boxed_equal : forall (A : Type) (v v' : A),
  Some v = Some v' -> v = v'.
Proof. intros. inversion H. reflexivity. Qed.

Lemma extract_perm : forall u q' q cost,
  extract_min q cost = Some (u, q') ->
  Permutation q (u :: q').
Proof.
  intros.
  unfold extract_min in H.
  destruct q.
  - absurd (None = Some (u, q')).
    + discriminate.
    + assumption.
  - assert (Hsp := select_perm n q cost0).
    destruct (select_min_in_cost_map n q cost0) eqn:Eq_let.
    apply option_equal_implies_boxed_equal in H.
    apply pair_equal_spec in H.
    inversion H. rewrite <- H0, <- H1. assumption.
Qed.

Lemma extract_min_res_subset : forall (u : nat) (q q' : priqueue) (cost : cost_map),
  extract_min q cost = Some (u, q') ->
  subset q' q.
Proof.
  intros.
  unfold extract_min in H.
  destruct q eqn:Eqq.
  - absurd (None = Some (u, q')).
    + discriminate.
    + assumption.
  - assert (Hsp := select_perm n p cost0).
    destruct (select_min_in_cost_map n p cost0) eqn:Eq_let.
    apply option_equal_implies_boxed_equal in H.
    apply pair_equal_spec in H.
    inversion H. subst. clear H.
    apply Permutation_tail_subset in Hsp.
    assumption.
Qed.

Lemma extract_min_non_empty_not_none: 
  forall (q : priqueue) (cost : cost_map) (res : option (nat * priqueue)),
  q <> [] -> res = extract_min q cost -> res <> None.
Proof.
  unfold extract_min.
  intros.
  inversion H0. subst.
  destruct q eqn:Eqq.
  - contradiction.
  - now destruct (select_min_in_cost_map n p cost0).
Qed.

Lemma extract_min_decreases_len_q : forall q q' u cost,
  Some (u, q') = extract_min q cost ->
  length q' < length q.
Proof. 
  intros.
  unfold extract_min in H.
  destruct q eqn:Eqq.
  - absurd (Some (u, q') = None).
    + discriminate.
    + assumption.
  - destruct (select_min_in_cost_map n p cost0) eqn:Eq_let.
    apply select_min_length_constant in Eq_let.
    apply option_equal_implies_boxed_equal in H.
    apply pair_equal_spec in H.
    inversion H. subst.
    simpl. rewrite Eq_let.
    nia.
Qed.

Record DijkstraStruct : Type := mkDS
  {
    C : cost_map ;
    P : prev_map
  }.

Definition empty := mkDS (empty_map INF) (empty_map UNDEF).

Definition initialize_single_source (G : DWGraph) (s : nat) : DijkstraStruct :=
  mkDS (update_map (empty_map INF) s (value 0)) (empty_map UNDEF).

Definition relax 
  (G : DWGraph) 
  (u : nat)
  (DS : DijkstraStruct) 
  (v : nat) : DijkstraStruct :=
  match C DS u with
  | value cu =>
    let sum_u_w := value (cu + (W G u v)) in
    if ltb sum_u_w (C DS v)
    then
      let C' := update_map (C DS) v sum_u_w in
      let P' := update_map (P DS) v (id u) in
      mkDS C' P'
    else DS
  | INF => DS
  end.

Definition relax_adjacents 
  (G : DWGraph) 
  (DS : DijkstraStruct)
  (u : nat) : DijkstraStruct :=
  let adj_v_ids := adjacent_v_ids G u in
  fold_left (relax G u) adj_v_ids DS.

Function dijkstra_loop 
  (* (fuel : nat) *) (G : DWGraph) 
  (q : priqueue) 
  (DS : DijkstraStruct) {measure length q}: priqueue * DijkstraStruct := 
  match extract_min q (C DS) with
  | Some (u, q') =>
    let DS' := relax_adjacents G DS u in
    dijkstra_loop G q' DS'
  | _ => (q, DS)
  end.
Proof.
  intros.
  symmetry in teq.
  apply (extract_min_decreases_len_q q q' u (C DS)) in teq.
  assumption.
Defined.

Definition dijkstra (G : DWGraph) (s : nat) : DijkstraStruct :=
  let DS := initialize_single_source G s in
  let q := all_nodes G in
  let (q', DS') := dijkstra_loop G q DS in
  DS'.

End Dijkstra.
