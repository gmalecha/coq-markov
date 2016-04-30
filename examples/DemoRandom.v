Require Import ExtLib.Data.Bool.
Require Import ExtLib.Data.Pair.
Require Import ExtLib.Structures.Monad.
Import MonadNotation.
Require Import Markov.RandomM.

Local Open Scope monad_scope.

Eval vm_compute
  in let n := 95 in
     let comp :=
         x <- fair_coin ;;
         y <- fair_coin ;;
         ret (x,y)
     in
     sample_discrete n comp.
