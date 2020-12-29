Require Import Coq.Init.Datatypes.
Require Import Coq.Lists.List. Import ListNotations.
Require Import Coq.Lists.ListSet.
Require Import Coq.Init.Nat.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.Peano_dec.
From Coq Require Import Lia.
Require Coq.Classes.RelationClasses.
Require Import Coq.Logic.Classical_Prop.

Open Scope bool_scope.

Set Implicit Arguments.

Module DirectedWeightedGraph.

Definition prop_on_unfolded_pair {A : Type}
  (pair : A * A) (P : A -> A -> Prop): Prop :=
  match pair with (fst, snd) => P fst snd end.

Notation "'Sig_no'" := (False_rec _ _) (at level 42).
Notation "'Sig_yes' e" := (exist _ e _) (at level 42).
Notation "'Sig_take' e" :=
  (match e with Sig_yes ex => ex end) (at level 42).

Fixpoint list_from_n'_to_0 (n : nat) : list nat :=
  match n with
  | S n' => n' :: list_from_n'_to_0 n'
  | O => []
  end.
(* Definition W : forall (u v : nat), { p : nat * nat | E u v /\ p = (u, v) }.
  refine (fun u v => if u =? v then Sig_no else Sig_yes (u, v)).



Check ({ p : nat * nat | E u v /\ p = (u, v) }). *)
Structure DWGraph := {
  num_v :> nat ;
  E :> nat -> nat -> Prop ;
  W : nat -> nat -> nat ;
  E_decidable : forall u v : nat, ({E u v} + {~ E u v}) ;
  adjacent (u v : nat) : bool := if E_decidable u v then true else false ;
  adjacent_v_ids (u : nat) : list nat := filter (adjacent u) (seq 0 num_v) ;
  all_nodes : set nat := seq 0 num_v
}.

Definition Empty (n : nat) : DWGraph.
Proof.
  refine {| num_v := n ;
            E := (fun x y => False)
         |}.
  auto.
  auto.
Defined.

Definition empty3 := Empty 3.
Compute (W empty3).
Compute (adjacent empty3).

End DirectedWeightedGraph.
