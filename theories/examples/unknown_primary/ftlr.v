From iris.proofmode Require Import tactics.
From machine_program_logic.program_logic Require Import weakestpre.
(* From HypVeri.lang Require Import lang. *)
From HypVeri.algebra Require Import base base_extra.
From HypVeri Require Import proofmode.
From HypVeri.examples Require Import unknown_primary.proof.
Import uPred.

Section up_ftlr.
  Context `{hypparams: (@HypervisorParameters up_vmconfig)}.
  Context `{!(@gen_VMG up_vmconfig) Σ}.


End up_ftlr.
