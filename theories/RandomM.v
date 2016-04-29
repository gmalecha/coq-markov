Require Import ExtLib.Data.Stream.
Require Import ExtLib.Structures.MonadState.
Require Import QArith.Qcanon.
Require Import QArith_base.
Require Import Coq.Lists.List.
Require Import ExtLib.Data.Vector.
Require Import ExtLib.Structures.Functor.

Require Import BinNums.
Require Import ExtLib.Structures.Monad.
Require Import ExtLib.Data.Monads.IdentityMonad.
Require Import ExtLib.Data.Monads.StateMonad.

Require Import Markov.Random.

(** Following the semantics of Huang and Morrisett:
 **  [An application of computable distributions to the semantics of probabilistic programming languages]
 **)
Definition PD (T : Type) : Type := state Bits T.
Global Instance Monad_PD : Monad PD := Monad_state _.

(**
 ** A sampler for biased coin flips
 **)
Local Fixpoint get_precision (n : positive) : positive :=
  match n with
  | q~1 => Psucc (get_precision q)
  | q~0 => Psucc (get_precision q)
  | 1 => 1
  end%positive.

Local Fixpoint Q_to_precision' (n : positive) (b : Bits) (acc : N) {T} (k : N -> Bits -> T) : T :=
  match n with
  | xH => match b with
          | Bit Int32.D1 b' => k (2 * acc + 1)%N b'
          | Bit Int32.D0 b' => k (2 * acc)%N b'
          end
  | xO n => Q_to_precision' n b acc (fun acc b => Q_to_precision' n b acc k)
  | xI n => match b with
            | Bit c b' =>
              let acc' := (if c then 2 * acc + 1 else 2 * acc)%N in
              Q_to_precision' n b' acc' (fun acc b => Q_to_precision' n b acc k)
            end
  end.

Local Definition Q_to_precision (prec : positive) (b : Bits) : Q * Bits :=
  Q_to_precision' prec b 0%N
                  (fun n b => ({| Qnum := Z_of_N n
                                ; Qden := pow_pos Pmult 2%positive prec |} , b)).

Definition flip (q : Q) : PD bool :=
  {| runState := fun b =>
                   match Qcompare q 0 with
                   | Lt => (true, b)
                   | _ => match Qcompare 1 q with
                          | Lt => (false, b)
                          | _ =>
                            let prec := get_precision q.(Qden) in
                            let (q', b') := Q_to_precision prec b in
                            (match Qcompare q' q with
                             | Lt | Eq => true
                             | Gt => false
                             end, b')
                          end
                   end |}.

(**
 ** A fair coin flip
 **)
Definition fair_coin : PD bool :=
  flip {| Qnum := 1 ; Qden := 2 |}.

(**
 ** Random from Range
 **)
Fixpoint from_range (low count : nat) : PD nat :=
  match count with
  | 0 => ret low
  | S n =>
    bind (flip {| Qnum := 1%Z ; Qden := Pos.of_succ_nat n |})
         (fun x => if x then ret low
                   else from_range (S low) n)
  end%nat.

(*
Definition digits (n : nat) : PD (vector Int32.digits n) :=
{| runState := fun b => takeBits n b (fun a b => (b, a)) |}.
*)

Section sample.
  Context {T : Type} (c : PD T).
  Local Instance MonadState_state : MonadState Bits PD := MonadState_state _.

  Let comp : PD T :=
    bind (mkState take_int32) (fun z1 =>
    bind (mkState take_int32) (fun z2 =>
    bind (mkState take_int32) (fun z3 =>
    bind (mkState take_int32) (fun z4 =>
    bind (MonadState.put (lfsr113_gen z1 z2 z3 z4))
         (fun _ => c))))).

  CoFixpoint sample (s : Bits)
  : stream T :=
    scons (evalState comp s)
          (sample (@takeBits 17 s _ (fun x _ => x))).
End sample.

(** TODO(gmalecha): To ExtLib **)
Section stream_take.
  Context {T : Type}.

  Fixpoint take (n : nat) (s : stream T) : list T :=
    match n with
    | Datatypes.O => nil
    | Datatypes.S n => match s with
                       | scons v s => v :: take n s
                       | snil => nil
                       end
    end.
End stream_take.

Require Import ExtLib.Core.RelDec.

Section sample_discrete.
  Context {T : Type} {r : RelDec (@eq T)}.

  Require Import ExtLib.Data.Map.FMapAList.

  Definition increment (k : T) (ls : alist T positive) : alist T positive :=
    match alist_find _ k ls with
    | None => alist_add _ k 1%positive ls
    | Some x => alist_add _ k (Pos.succ x) ls
    end.

  Definition sample_discrete (n : nat) (c : PD T) : alist T Q :=
    fmap (fun x => this (Q2Qc {| Qnum := Zpos x ; Qden := Pos.of_nat n |}))
         (List.fold_left (fun d r => increment r d) (take n (sample c lfsr113)) nil).
End sample_discrete.


Require Export ExtLib.Structures.Monad.
