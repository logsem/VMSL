From Coq Require Import ssreflect ZArith.
From HypVeri Require Import machine monad.
From stdpp Require Import fin_maps list countable fin vector.

Ltac solveWordSize :=
  pose proof word_size;
  unfold word_size;
  lia.

Ltac solveRegCount :=
  pose proof reg_count;
  unfold reg_count;
  lia.

Program Definition W0 : Word := (finz.FinZ 0 _ _).
Solve Obligations with solveWordSize.

Program Definition W1 : Word := (finz.FinZ 1 _ _).
Solve Obligations with solveWordSize.

Program Definition W2 : Word := (finz.FinZ 2 _ _).
Solve Obligations with solveWordSize.

Program Definition R0 :reg_name := (R 0 _).
Solve Obligations with solveRegCount.

Program Definition R1 :reg_name := (R 1 _).
Solve Obligations with solveRegCount.

Program Definition R2 :reg_name := (R 2 _).
Solve Obligations with solveRegCount.
