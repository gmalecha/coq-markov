Require Import ExtLib.Data.Vector.
Require Import Markov.Int32.

(** Stream of random bits *)
CoInductive Bits : Type :=
| Bit : digits -> Bits -> Bits.

Section stream32.
  Local Notation "x >> y" := (Bit x y) (at level 5, right associativity).

  Definition stream_int32 (bs : int32) (rest : Bits) : Bits :=
    match bs with
    | I32 a b c d e f g h i j k l m n o p q r s t u v w x y z aa bb cc dd ee ff =>
      a >> b >> c >> d >> e >> f >> g >> h >> i >> j >> k >> l >> m >> n >> o >>
      p >> q >> r >> s >> t >> u >> v >> w >> x >> y >> z >> aa >> bb >> cc >>
      dd >> ee >> ff >> rest
    end.
End stream32.

Fixpoint takeBits (n : nat) (b : Bits) {T} {struct n}
: (Bits -> vector digits n -> T) -> T :=
  match n as n return (Bits -> vector digits n -> T) -> T with
  | Datatypes.O => fun k => k b (Vnil _)
  | Datatypes.S n => fun k =>
                       match b with
                       | Bit c b =>
                         takeBits n b (fun rest bs => k rest (Vcons c bs))
                       end
  end.

Fixpoint takeT (n : nat) (b : Bits) {T} {struct n}
: (Bits -> NaryFunctions.nfun digits n T) -> T :=
  match n as n return (Bits -> NaryFunctions.nfun digits n T) -> T with
  | Datatypes.O => fun k => k b
  | Datatypes.S n => fun k =>
                       match b with
                       | Bit c b =>
                         takeT n b (fun bs => k bs c)
                       end
  end.

Definition take_int32 (b : Bits) : int32 * Bits := Eval simpl in
  takeT 32 b (fun b => @NaryFunctions.nfun_to_nfun _ _ _ (fun i => (i,b)) 32 I32).


CoFixpoint proj1 (b : Bits) : Bits :=
  match b with
  | Bit x b => Bit x match b with
                     | Bit _ b => proj1 b
                     end
  end.
Definition proj2 (b : Bits) : Bits :=
  match b with
  | Bit _ b => proj1 b
  end.

Section lfsr113.
(* Taken from Stack Overflow:
 *   http://stackoverflow.com/questions/1167253/implementation-of-rand
 *
unsigned int lfsr113_Bits (void)
{
   static unsigned int z1 = 12345, z2 = 12345, z3 = 12345, z4 = 12345;
   unsigned int b;
   b  = ((z1 << 6) ^ z1) >> 13;
   z1 = ((z1 & 4294967294U) << 18) ^ b;
   b  = ((z2 << 2) ^ z2) >> 27;
   z2 = ((z2 & 4294967288U) << 2) ^ b;
   b  = ((z3 << 13) ^ z3) >> 21;
   z3 = ((z3 & 4294967280U) << 7) ^ b;
   b  = ((z4 << 3) ^ z4) >> 12;
   z4 = ((z4 & 4294967168U) << 13) ^ b;
   return (z1 ^ z2 ^ z3 ^ z4);
}
*)

  Local Notation "x >> y" := (Int32.shiftrn y%nat x) (at level 30, right associativity).
  Local Notation "x << y" := (Int32.shiftln y%nat x) (at level 30, right associativity).
  Local Notation "x ^ y" := (Int32.lxor32 x y) (at level 30, right associativity).
  Local Notation "x & y" := (Int32.land32 x y) (at level 30, right associativity).

  Definition n2int32 (n : N) : int32 :=
    match n with
    | N0 => On
    | Npos p => phi_inv_positive p
    end.
  Local Coercion n2int32 : N >-> int32.

  CoFixpoint lfsr113_gen (z1 z2 z3 z4 : int32) : Bits :=
    let b  := ((z1 << 6) ^ z1) >> 13 in
    let z1 := ((z1 & 4294967294%N) << 18) ^ b in
    let b  := ((z2 << 2) ^ z2) >> 27 in
    let z2 := ((z2 & 4294967288%N) << 2) ^ b in
    let b  := ((z3 << 13) ^ z3) >> 21 in
    let z3 := ((z3 & 4294967280%N) << 7) ^ b in
    let b  := ((z4 << 3) ^ z4) >> 12 in
    let z4 := ((z4 & 4294967168%N) << 13) ^ b in
    stream_int32 (z1 ^ z2 ^ z3 ^ z4) (lfsr113_gen z1 z2 z3 z4).

  Definition lfsr113 :=
    Eval cbv beta iota delta [n2int32 phi_inv_positive twice twice_plus_one sneakl In] in
    let x := (12345%N : int32) in
    lfsr113_gen x x x x.
End lfsr113.

(** My naive random number generator
Section seeded_random.
  Variable stepper : positive.

  Definition stream (p : positive) (b : Bits) : Bits :=
    Bit
      match p with
      | xI p' => true
      | xO p' => false
      | xH => false (* DEAD *)
      end b.

  Require Import PArith.BinPos.

  Fixpoint drop (n : nat) (p : positive) : positive :=
    match n with
    | Datatypes.O => p
    | Datatypes.S n =>
      match p with
      | xI p | xO p => drop n p
      | xH => xH
      end
    end.

  CoFixpoint random (seed : positive) : Bits :=
    let res := (seed * stepper)%positive in
    stream res (random (drop 3 res + 1)).
End seeded_random.
*)