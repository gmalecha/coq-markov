Require Import Coq.Bool.Bool.
Require Import ExtLib.Structures.Monoid.
Require Import ExtLib.Structures.Monad.
Require Import ExtLib.Data.List.
Require Import ExtLib.Data.Bool.
Require Import Markov.Random.
Require Import Markov.RandomM.

Import MonadNotation.
Local Open Scope monad_scope.

(** [P T] is a computable probability distribution on [T] *)
Definition P (T : Type) : Type := PD T.

(** Markov Decision Process *)
Record MDP : Type :=
{ State  : Type
; Action : Type
; Trans  : State -> Action -> P State
; Obs    : Type
; Look   : State -> P Obs
}.

(** The meaning of an MDP as a program
 **)
Section mdp.
  Variable m : MDP.

  Definition step (s : m.(State)) (a : m.(Action)) : PD (m.(State) * m.(Obs)) :=
    s' <- m.(Trans) s a ;;
    o <- m.(Look) s' ;;
    ret (s', o).

  Fixpoint mfold (n : nat) {S O} (M : Monoid O) (m : S -> PD (S * O)) (s : S) (o : O) : PD (S * O) :=
    match n with
    | O => ret (s, o)
    | S n => x <- m s ;;
             let (s',o') := x in
             mfold n M m s' (monoid_plus M o o')
    end.

End mdp.

Section on_off.

  Definition on_off : MDP :=
  {| State  := bool
   ; Action := unit
   ; Trans  := fun s _ =>
                 x <- fair_coin ;;
                 if x then ret s
                 else ret (negb s)
   ; Obs    := bool
   ; Look   := fun s =>
                 x <- fair_coin (* flip {| QArith_base.Qnum := 3 ; QArith_base.Qden := 4 |} *) ;;
                 if x then ret s
                 else ret (negb s)
   |}.

End on_off.

Definition tracer (n : nat) (m : MDP) (s : m.(State)) (z : m.(Action)) : PD (list m.(Obs)) :=
  x <- mfold n (@Monoid_list_app m.(Obs))
               (fun s =>
                  x <- step m s z ;;
                  ret (fst x, snd x :: nil)) s nil ;;
  ret (snd x).


Eval vm_compute
  in let samples := 100 in
     let length := 3 in
     sample_discrete samples (x <- fair_coin ;;
                              tracer length on_off x tt)%monad.