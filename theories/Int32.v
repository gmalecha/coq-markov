(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)
(*            Benjamin Gregoire, Laurent Thery, INRIA, 2007             *)
(************************************************************************)

Require Import NaryFunctions.
Require Import Wf_nat.
Require Export ZArith.
Require Export DoubleType.

(** * 31-bit integers *)

(** This file contains basic definitions of a 31-bit integer
  arithmetic. In fact it is more general than that. The only reason
  for this use of 31 is the underlying mecanism for hardware-efficient
  computations by A. Spiwack. Apart from this, a switch to, say,
  63-bit integers is now just a matter of replacing every occurrences
  of 31 by 63. This is actually made possible by the use of
  dependently-typed n-ary constructions for the inductive type
  [int31], its constructor [I31] and any pattern matching on it.
  If you modify this file, please preserve this genericity.  *)

(** GMALECHA: Replaced 31 -> 32 *)
Definition size := 32%nat.

(** Digits *)

Inductive digits : Type := D0 | D1.

(** The type of 32-bit integers *)

(** The type [int32] has a unique constructor [I32] that expects
   32 arguments of type [digits]. *)

Definition digits32 t := Eval compute in nfun digits size t.

Inductive int32 : Type := I32 : digits32 int32.

(*
(* spiwack: Registration of the type of integers, so that the matchs in
   the functions below perform dynamic decompilation (otherwise some segfault
   occur when they are applied to one non-closed term and one closed term). *)
Register digits as int32 bits in "coq_int32" by True.
Register int32 as int32 type in "coq_int32" by True.
*)

Delimit Scope int32_scope with int32.
Bind Scope int32_scope with int32.
Local Open Scope int32_scope.

(** * Constants *)

(** Zero is [I32 D0 ... D0] *)
Definition On : int32 := Eval compute in napply_cst _ _ D0 size I32.

(** One is [I32 D0 ... D0 D1] *)
Definition In : int32 := Eval compute in (napply_cst _ _ D0 (size-1) I32) D1.

(** The biggest integer is [I32 D1 ... D1], corresponding to [(2^size)-1] *)
Definition Tn : int32 := Eval compute in napply_cst _ _ D1 size I32.

(** Two is [I32 D0 ... D0 D1 D0] *)
Definition Twon : int32 := Eval compute in (napply_cst _ _ D0 (size-2) I32) D1 D0.

(** * Bits manipulation *)


(** [sneakr b x] shifts [x] to the right by one bit.
   Rightmost digit is lost while leftmost digit becomes [b].
   Pseudo-code is
    [ match x with (I32 d0 ... dN) => I32 b d0 ... d(N-1) end ]
*)

Fixpoint fmap_nfun {V T U : Type} n (f : T -> U) : nfun V n T -> nfun V n U :=
  match n as n return nfun V n T -> nfun V n U with
  | 0 => f
  | S n => fun v x => fmap_nfun n f (v x)
  end.

Definition sneakr : digits -> int32 -> int32 := Eval compute in
 fun b => int32_rect _ (napply_except_last _ _ (size-1) (I32 b)).
Definition sneakr_cps {T} (k : int32 -> T) : digits -> int32 -> T := Eval compute in
 fun b => int32_rect (fun _ => T) (napply_except_last _ _ (size-1) (fmap_nfun 31 k (I32 b))).


(** [sneakl b x] shifts [x] to the left by one bit.
   Leftmost digit is lost while rightmost digit becomes [b].
   Pseudo-code is
    [ match x with (I32 d0 ... dN) => I32 d1 ... dN b end ]
*)

Definition sneakl : digits -> int32 -> int32 := Eval compute in
 fun b => int32_rect _ (fun _ => napply_then_last _ _ b (size-1) I32).
Definition sneakl_cps {T} (k : int32 -> T) : digits -> int32 -> T := Eval compute in
 fun b => int32_rect (fun _ => T) (fun _ => fmap_nfun 31 k (napply_then_last _ _ b (size-1) I32)).


(** [shiftl], [shiftr], [twice] and [twice_plus_one] are direct
    consequences of [sneakl] and [sneakr]. *)

Definition shiftl := sneakl D0.
Definition shiftr := sneakr D0.

Fixpoint shiftln (n : nat) : int32 -> int32 :=
  match n with
  | 0 => fun x => x
  | S n => sneakl_cps (shiftln n) D0
  end.

Fixpoint shiftrn (n : nat) : int32 -> int32 :=
  match n with
  | 0 => fun x => x
  | S n => sneakr_cps (shiftrn n) D0
  end.

Definition twice := sneakl D0.
Definition twice_plus_one := sneakl D1.

(** [firstl x] returns the leftmost digit of number [x].
    Pseudo-code is [ match x with (I32 d0 ... dN) => d0 end ] *)

Definition firstl : int32 -> digits := Eval compute in
 int32_rect _ (fun d => napply_discard _ _ d (size-1)).

(** [firstr x] returns the rightmost digit of number [x].
    Pseudo-code is [ match x with (I32 d0 ... dN) => dN end ] *)

Definition firstr : int32 -> digits := Eval compute in
 int32_rect _ (napply_discard _ _ (fun d=>d) (size-1)).

(** [iszero x] is true iff [x = I32 D0 ... D0]. Pseudo-code is
    [ match x with (I32 D0 ... D0) => true | _ => false end ] *)

Definition iszero : int32 -> bool := Eval compute in
 let f d b := match d with D0 => b | D1 => false end
 in int32_rect _ (nfold_bis _ _ f true size).

(* NB: DO NOT transform the above match in a nicer (if then else).
   It seems to work, but later "unfold iszero" takes forever. *)


(** [base] is [2^32], obtained via iterations of [Z.double].
   It can also be seen as the smallest b > 0 s.t. phi_inv b = 0
   (see below) *)

Definition base := Eval compute in
 iter_nat size Z Z.double 1%Z.

(** * Recursors *)

Fixpoint recl_aux (n:nat)(A:Type)(case0:A)(caserec:digits->int32->A->A)
 (i:int32) : A :=
  match n with
  | O => case0
  | S next =>
          if iszero i then
             case0
          else
             let si := shiftl i in
             caserec (firstl i) si (recl_aux next A case0 caserec si)
  end.

Fixpoint recr_aux (n:nat)(A:Type)(case0:A)(caserec:digits->int32->A->A)
 (i:int32) : A :=
  match n with
  | O => case0
  | S next =>
          if iszero i then
             case0
          else
             let si := shiftr i in
             caserec (firstr i) si (recr_aux next A case0 caserec si)
  end.

Definition recl := recl_aux size.
Definition recr := recr_aux size.

(** * Conversions *)

(** From int32 to Z, we simply iterates [Z.double] or [Z.succ_double]. *)

Definition phi : int32 -> Z :=
 recr Z (0%Z)
  (fun b _ => match b with D0 => Z.double | D1 => Z.succ_double end).

(** From positive to int32. An abstract definition could be :
      [ phi_inv (2n) = 2*(phi_inv n) /\
        phi_inv 2n+1 = 2*(phi_inv n) + 1 ] *)

Fixpoint phi_inv_positive p :=
  match p with
    | xI q => twice_plus_one (phi_inv_positive q)
    | xO q => twice (phi_inv_positive q)
    | xH => In
  end.

(** The negative part : 2-complement  *)

Fixpoint complement_negative p :=
  match p with
    | xI q => twice (complement_negative q)
    | xO q => twice_plus_one (complement_negative q)
    | xH => twice Tn
  end.

(** A simple incrementation function *)

Definition incr : int32 -> int32 :=
 recr int32 In
   (fun b si rec => match b with
     | D0 => sneakl D1 si
     | D1 => sneakl D0 rec end).

(** We can now define the conversion from Z to int32. *)

Definition phi_inv : Z -> int32 := fun n =>
 match n with
 | Z0 => On
 | Zpos p => phi_inv_positive p
 | Zneg p => incr (complement_negative p)
 end.

(** [phi_inv2] is similar to [phi_inv] but returns a double word
    [zn2z int32] *)

Definition phi_inv2 n :=
  match n with
  | Z0 => W0
  | _ => WW (phi_inv (n/base)%Z) (phi_inv n)
  end.

(** [phi2] is similar to [phi] but takes a double word (two args) *)

Definition phi2 nh nl :=
  ((phi nh)*base+(phi nl))%Z.

(** * Addition *)

(** Addition modulo [2^32] *)

Definition add32 (n m : int32) := phi_inv ((phi n)+(phi m)).
Notation "n + m" := (add32 n m) : int32_scope.

(** Addition with carry (the result is thus exact) *)

(* spiwack : when executed in non-compiled*)
(* mode, (phi n)+(phi m) is computed twice*)
(* it may be considered to optimize it *)

Definition add32c (n m : int32) :=
  let npm := n+m in
  match (phi npm ?= (phi n)+(phi m))%Z with
  | Eq => C0 npm
  | _ => C1 npm
  end.
Notation "n '+c' m" := (add32c n m) (at level 50, no associativity) : int32_scope.

(**  Addition plus one with carry (the result is thus exact) *)

Definition add32carryc (n m : int32) :=
  let npmpone_exact := ((phi n)+(phi m)+1)%Z in
  let npmpone := phi_inv npmpone_exact in
  match (phi npmpone ?= npmpone_exact)%Z with
  | Eq => C0 npmpone
  | _ => C1 npmpone
  end.

(** * Substraction *)

(** Subtraction modulo [2^32] *)

Definition sub32 (n m : int32) := phi_inv ((phi n)-(phi m)).
Notation "n - m" := (sub32 n m) : int32_scope.

(** Subtraction with carry (thus exact) *)

Definition sub32c (n m : int32) :=
  let nmm := n-m in
  match (phi nmm ?= (phi n)-(phi m))%Z with
  | Eq => C0 nmm
  | _ => C1 nmm
  end.
Notation "n '-c' m" := (sub32c n m) (at level 50, no associativity) : int32_scope.

(** subtraction minus one with carry (thus exact) *)

Definition sub32carryc (n m : int32) :=
  let nmmmone_exact := ((phi n)-(phi m)-1)%Z in
  let nmmmone := phi_inv nmmmone_exact in
  match (phi nmmmone ?= nmmmone_exact)%Z with
  | Eq => C0 nmmmone
  | _ => C1 nmmmone
  end.

(** Opposite *)

Definition opp32 x := On - x.
Notation "- x" := (opp32 x) : int32_scope.

(** Multiplication *)

(** multiplication modulo [2^32] *)

Definition mul32 (n m : int32) := phi_inv ((phi n)*(phi m)).
Notation "n * m" := (mul32 n m) : int32_scope.

(** multiplication with double word result (thus exact) *)

Definition mul32c (n m : int32) := phi_inv2 ((phi n)*(phi m)).
Notation "n '*c' m" := (mul32c n m) (at level 40, no associativity) : int32_scope.


(** * Division *)

(** Division of a double size word modulo [2^32] *)

Definition div3221 (nh nl m : int32) :=
  let (q,r) := Z.div_eucl (phi2 nh nl) (phi m) in
  (phi_inv q, phi_inv r).

(** Division modulo [2^32] *)

Definition div32 (n m : int32) :=
  let (q,r) := Z.div_eucl (phi n) (phi m) in
  (phi_inv q, phi_inv r).
Notation "n / m" := (div32 n m) : int32_scope.


(** * Unsigned comparison *)

Definition compare32 (n m : int32) := ((phi n)?=(phi m))%Z.
Notation "n ?= m" := (compare32 n m) (at level 70, no associativity) : int32_scope.

Definition eqb32 (n m : int32) :=
 match n ?= m with Eq => true | _ => false end.


(** Computing the [i]-th iterate of a function:
    [iter_int32 i A f = f^i] *)

Definition iter_int32 i A f :=
  recr (A->A) (fun x => x)
   (fun b si rec => match b with
      | D0 => fun x => rec (rec x)
      | D1 => fun x => f (rec (rec x))
    end)
    i.

(** Combining the [(32-p)] low bits of [i] above the [p] high bits of [j]:
    [addmuldiv32 p i j = i*2^p+j/2^(32-p)]  (modulo [2^32]) *)

Definition addmuldiv32 p i j :=
 let (res, _ ) :=
 iter_int32 p (int32*int32)
  (fun ij => let (i,j) := ij in (sneakl (firstl j) i, shiftl j))
  (i,j)
 in
 res.

(** Bitwise operations *)

Definition lor32 n m := phi_inv (Z.lor (phi n) (phi m)).
Definition land32 n m := phi_inv (Z.land (phi n) (phi m)).
Definition lxor32 n m := phi_inv (Z.lxor (phi n) (phi m)).

(*
Register add32 as int32 plus in "coq_int32" by True.
Register add32c as int32 plusc in "coq_int32" by True.
Register add32carryc as int32 pluscarryc in "coq_int32" by True.
Register sub32 as int32 minus in "coq_int32" by True.
Register sub32c as int32 minusc in "coq_int32" by True.
Register sub32carryc as int32 minuscarryc in "coq_int32" by True.
Register mul32 as int32 times in "coq_int32" by True.
Register mul32c as int32 timesc in "coq_int32" by True.
Register div3221 as int32 div21 in "coq_int32" by True.
Register div32 as int32 diveucl in "coq_int32" by True.
Register compare32 as int32 compare in "coq_int32" by True.
Register addmuldiv32 as int32 addmuldiv in "coq_int32" by True.
Register lor32 as int32 lor in "coq_int32" by True.
Register land32 as int32 land in "coq_int32" by True.
Register lxor32 as int32 lxor in "coq_int32" by True.
*)

Definition lnot32 n := lxor32 Tn n.
Definition ldiff32 n m := land32 n (lnot32 m).

Fixpoint euler (guard:nat) (i j:int32) {struct guard} :=
  match guard with
    | O => In
    | S p => match j ?= On with
               | Eq => i
               | _ => euler p j (let (_, r ) := i/j in r)
             end
  end.

Definition gcd32 (i j:int32) := euler (2*size)%nat i j.

(** Square root functions using newton iteration
    we use a very naive upper-bound on the iteration
    2^32 instead of the usual 32.
**)



Definition sqrt32_step (rec: int32 -> int32 -> int32) (i j: int32)  :=
Eval lazy delta [Twon] in
  let (quo,_) := i/j in
  match quo ?= j with
    Lt => rec i (fst ((j + quo)/Twon))
  | _ =>  j
  end.

Fixpoint iter32_sqrt (n: nat) (rec: int32 -> int32 -> int32)
          (i j: int32) {struct n} : int32 :=
  sqrt32_step
   (match n with
      O =>  rec
   | S n => (iter32_sqrt n (iter32_sqrt n rec))
   end) i j.

Definition sqrt32 i :=
Eval lazy delta [On In Twon] in
  match compare32 In i with
    Gt => On
  | Eq => In
  | Lt => iter32_sqrt 32 (fun i j => j) i (fst (i/Twon))
  end.

Definition v30 := Eval compute in (addmuldiv32 (phi_inv (Z.of_nat size - 1)) In On).

Definition sqrt322_step (rec: int32 -> int32 -> int32 -> int32)
   (ih il j: int32)  :=
Eval lazy delta [Twon v30] in
  match ih ?= j with Eq => j | Gt => j | _ =>
  let (quo,_) := div3221 ih il j in
  match quo ?= j with
    Lt => let m := match j +c quo with
                    C0 m1 => fst (m1/Twon)
                  | C1 m1 => fst (m1/Twon) + v30
                  end in rec ih il m
  | _ =>  j
  end end.

Fixpoint iter322_sqrt (n: nat)
          (rec: int32  -> int32 -> int32 -> int32)
          (ih il j: int32) {struct n} : int32 :=
  sqrt322_step
   (match n with
      O =>  rec
   | S n => (iter322_sqrt n (iter322_sqrt n rec))
   end) ih il j.

Definition sqrt322 ih il :=
Eval lazy delta [On In] in
  let s := iter322_sqrt 32 (fun ih il j => j) ih il Tn in
           match s *c s with
            W0 => (On, C0 On) (* impossible *)
          | WW ih1 il1 =>
             match il -c il1 with
                C0 il2 =>
                  match ih ?= ih1 with
                    Gt => (s, C1 il2)
                  | _  => (s, C0 il2)
                  end
              | C1 il2 =>
                  match (ih - In) ?= ih1 with (* we could parametrize ih - 1 *)
                    Gt => (s, C1 il2)
                  | _  => (s, C0 il2)
                  end
              end
          end.


Fixpoint p2i n p : (N*int32)%type :=
  match n with
    | O => (Npos p, On)
    | S n => match p with
               | xO p => let (r,i) := p2i n p in (r, Twon*i)
               | xI p => let (r,i) := p2i n p in (r, Twon*i+In)
               | xH => (N0, In)
             end
  end.

Definition positive_to_int32 (p:positive) := p2i size p.

(** Constant 32 converted into type int32.
    It is used as default answer for numbers of zeros
    in [head0] and [tail0] *)

Definition T32 : int32 := Eval compute in phi_inv (Z.of_nat size).

Definition head032 (i:int32) :=
  recl _ (fun _ => T32)
   (fun b si rec n => match b with
     | D0 => rec (add32 n In)
     | D1 => n
    end)
   i On.

Definition tail032 (i:int32) :=
  recr _ (fun _ => T32)
   (fun b si rec n => match b with
     | D0 => rec (add32 n In)
     | D1 => n
    end)
   i On.

(*
Register head032 as int32 head0 in "coq_int32" by True.
Register tail032 as int32 tail0 in "coq_int32" by True.
*)