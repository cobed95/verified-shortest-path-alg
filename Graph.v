Require Import Coq.Init.Datatypes.
Require Import Coq.Lists.List. Import ListNotations.
Require Import Coq.Init.Nat.
Require Import Coq.Arith.EqNat.

Module Graph.

Definition vertex_id : Type := nat.

Definition weight : Type := nat.

Definition vertex : Type := vertex_id.
Definition edge : Type := vertex_id * vertex_id * weight.

Definition graph : Type := (list vertex) * (list edge).

Definition vertices_valid (v_id_list : list vertex_id) : Prop :=
  NoDup v_id_list.

Definition eq (e e' : edge) : Prop :=
  match e, e' with (s, d, _), (s', d', _) => s = s' /\ d = d' end.
  
Definition edges_valid (e_list : list edge) : Prop :=
  NoDup e_list. 

Definition vertices_edge_rel_valid (v_id_list : list vertex_id) (e : edge) : Prop :=
  match e with
  | (s, d, _) => In s v_id_list /\ In d v_id_list
  end.

Definition vertices_edges_rel_valid (g : graph) : Prop :=
  match g with (v_list, e_list) => Forall (vertices_edge_rel_valid v_list) e_list end.

Definition graph_valid (g : graph) : Prop :=
  match g with (v_list, e_list) =>
    vertices_valid v_list /\
    edges_valid e_list /\
    vertices_edges_rel_valid g
  end.

Definition src_valid (s : vertex_id) (g : graph) : Prop :=
  match g with (v_list, _) => In s v_list end.

Definition dest_valid (d : vertex_id) (g : graph) : Prop :=
  src_valid d g.

Definition src (e : edge) : vertex_id :=
  match e with (s, _, _) => s end.

Definition dest (e : edge) : vertex_id :=
  match e with (_, d, _) => d end.

Definition edge_src_eq (u : nat) (e : edge) : Prop := src e = u.

Definition edge_src_eq_bool (u : nat) (e : edge) : bool := src e =? u.

Definition edge_src_dest_eq (u v : nat) (e : edge) : Prop :=
  edge_src_eq u e /\ dest e = v.

Inductive path : (list edge) -> nat -> nat -> Prop :=
| path_single_edge (e_list : list edge) (u v : nat) : 
  Exists (edge_src_dest_eq u v) e_list -> path e_list u v
| path_multi_edge (e_list : list edge) (u v' v: nat) (H : path e_list u v'):
  Exists (edge_src_dest_eq v' v) e_list -> path e_list u v.
  
End Graph.
