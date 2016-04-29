Require Import Coq.Bool.Bool.
Require Import Markov.Random.
Require Import Markov.RandomM.
(* Axiomatization of probability *)

(** [P T] is a probability distribution on [T] *)
Parameter P : Type -> Type.


(** Markov Decision Process *)
Record MDP : Type :=
{ S : Type
; A : Type
; Trans : S * A -> P S
; O : Type
; Obs   : S -> P O
}.

Require Import ExtLib.Data.Bool.
Require Import ExtLib.Data.Pair.
Require Import QArith.

Eval vm_compute
  in let n := 95 in
     let comp :=
         bind fair_coin (fun x =>
         bind fair_coin (fun y => ret (x, y)))
     in
     sample_discrete n comp.