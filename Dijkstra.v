Require Import Coq.Init.Datatypes.
Require Import Coq.Init.Nat.
Require Import Coq.Lists.List. Import ListNotations.
Require Export VerifShortestPathAlg.Graph. Import Graph.

Module Dijkstra.

Inductive distance :=
| reachable (d : weight)
| unreachable.

Inductive predecessor :=
| pred_id (v : vertex_id)
| undefined.

Definition total_map (A : Type) := vertex_id -> option A.
Definition empty_map {A : Type} : total_map A := fun _ => None.
Definition update_map {A : Type} 
  (prev_map : total_map A) (key : vertex_id) (val : A): total_map A :=
  fun id => if id =? key then Some val else prev_map id.

Definition total_map_pair (A : Type) := vertex_id * vertex_id -> option A.
Definition empty_map_pair {A : Type} : total_map_pair A := fun _ => None.
Definition update_map_pair {A : Type} 
  (prev_map : total_map_pair A) 
  (key : vertex_id * vertex_id) 
  (val : A): total_map_pair A :=
  fun pair => 
    match pair with (u, v) =>
      match key with (ku, kv) => 
        if andb (ku =? u) (kv =? v) then Some val 
        else prev_map pair
      end
    end.

Definition dist_map := total_map distance.
Definition pred_map := total_map predecessor.

Definition weight_map := total_map_pair weight.

Definition init_dist_map_iter
  (s: vertex_id) (dist : dist_map) (v : vertex_id) : dist_map := 
  if (v =? s) then update_map dist v (reachable 0)
  else update_map dist v unreachable.
Definition init_dist_map
  (v_list : list vertex_id) (s : vertex_id) : dist_map :=
  fold_left (init_dist_map_iter s) v_list empty_map.

Definition init_pred_map_iter
  (pred : pred_map) (v : vertex_id) : pred_map :=
  update_map pred v undefined.
Definition init_pred_map
  (v_list : list vertex_id) : pred_map :=
  fold_left init_pred_map_iter v_list empty_map.

Definition init_single_source 
  (v_list : list vertex_id) (s : vertex_id) : dist_map * pred_map :=
  (init_dist_map v_list s, init_pred_map v_list).

Definition init_weight_map_iter
  (wm : weight_map) (e : edge) : weight_map :=
  match e with (s, d, w) => update_map_pair wm (s, d) w end.
Definition init_weight_map
  (e_list : list edge) : weight_map :=
  fold_left init_weight_map_iter e_list empty_map_pair.

Definition init_weight_map_from_graph
  (g : graph) : weight_map :=
  match g with (_, e_list) => init_weight_map e_list end.

Definition relax 
  (wm : weight_map)
  (u : vertex_id)
  (dist_pred : dist_map * pred_map) 
  (v : vertex_id) : dist_map * pred_map :=
  match dist_pred with (dist, pred) =>
    match dist u, dist v, wm (u, v) with
    | Some (reachable du), Some unreachable, Some w =>
      let dv' := du + w in
      let dist' := update_map dist v (reachable dv') in
      let pred' := update_map pred v (pred_id u) in
      (dist', pred')
    | Some (reachable du), Some (reachable dv), Some w =>
      let sum_du_w := du + w in
      if (sum_du_w <=? dv)
      then
        let dist' := update_map dist v (reachable sum_du_w) in
        let pred' := update_map pred v (pred_id u) in
        (dist', pred')
      else
        (dist, pred)
    | _, _, _ => (dist, pred)
    end
  end.

Fixpoint select_priority {A : Type} 
  (x : A) (l : list A) (has_priority_over : A -> A -> bool) : A * list A :=
  match l with
  | [] => (x, [])
  | hd :: tl =>
    if has_priority_over x hd
    then
      let (y, l') := select_priority x tl has_priority_over in
      (y, hd :: l')
    else
      let (y, l') := select_priority hd tl has_priority_over in
      (y, x :: l')
  end.

Definition dist_smaller (dist: dist_map) (v v' : vertex_id) : bool :=
  match dist v, dist v' with
  | Some (reachable dv), Some (reachable dv') => dv <=? dv'
  | Some (unreachable), Some (reachable _) => false
  | _, _ => true
  end.

Definition priqueue : Type := list vertex_id.
Definition insert (v : vertex_id) (q : priqueue) : priqueue := v :: q.
Definition extract_min 
  (dist: dist_map) (q: priqueue) : (option vertex_id) * priqueue :=
  match q with
  | [] => (None, q)
  | hd :: tl =>
    let (extracted_v, extracted_q) := select_priority hd tl (dist_smaller dist) in
    (Some extracted_v, extracted_q)
  end.

Definition adjacent_v_ids
  (e_list : list edge) (u : vertex_id) : list vertex_id :=
  map dest (filter (edge_src_eq_bool u) e_list).

Fixpoint dijkstra_loop
  (n : nat)
  (s : list vertex_id)
  (q : priqueue)
  (e_list : list edge)
  (wm : weight_map)
  (dist : dist_map)
  (pred : pred_map) : list vertex_id * priqueue * dist_map * pred_map :=
  match n with
  | O => (s, q, dist, pred)
  | S n' =>
    match extract_min dist q with
    | (Some u, q') =>
      let s' := u :: s in
      let adj_v_ids := adjacent_v_ids e_list u in
      let (dist', pred') := fold_left (relax wm u) adj_v_ids (dist, pred) in
      dijkstra_loop n' s' q' e_list wm dist' pred'
    | _ => (s, q, dist, pred)
    end
  end.

Definition dijkstra_aux (g : graph) (wm : weight_map) (s: vertex_id) : dist_map * pred_map :=
  match g with (v_list, e_list) =>
    let (init_dist, init_pred) := init_single_source v_list s in
    let s := [] in
    let q := v_list in
    let '(s', q', dist', pred') := dijkstra_loop (length q) s q e_list wm init_dist init_pred in
    (dist', pred')
  end.

Definition dijkstra (g : graph) (s : vertex_id) : dist_map * pred_map :=
  let wm := init_weight_map_from_graph g in
  dijkstra_aux g wm s.

End Dijkstra.
