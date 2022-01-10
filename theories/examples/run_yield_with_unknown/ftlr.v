From iris.proofmode Require Import tactics.
From machine_program_logic.program_logic Require Import weakestpre.
From HypVeri.lang Require Import lang.
From HypVeri.algebra Require Import base base_extra.
(* From HypVeri.rules Require Import rules_base (* nop mov ldr str halt fail add sub mult cmp *). *)
From HypVeri.logrel Require Import logrel logrel_extra.
From HypVeri Require Import proofmode.
From HypVeri.examples Require Import run_yield_with_unknown.proof.
Import uPred.

Section rywu_ftlr.
  Context `{hypparams:!HypervisorParameters}.
  Context `{vmG: !gen_VMG Σ}.

  Definition rywu_interp_access (p_prog3 p_tx p_rx :PID):= interp_access V2 {[p_prog3]} p_tx p_rx ∅.

  Lemma rywu_ftlr (p_prog3 p_tx p_rx :PID):
   rywu_interp_access p_prog3 p_tx p_rx ⊢ interp_execute V2.
  Proof.
  Admitted.

End rywu_ftlr.
