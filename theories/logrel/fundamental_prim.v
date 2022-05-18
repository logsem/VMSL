From iris.proofmode Require Import tactics.
From machine_program_logic.program_logic Require Import weakestpre.
From HypVeri.lang Require Import lang trans_extra.
From HypVeri.algebra Require Import base pagetable mem trans.
From HypVeri.rules Require Import rules_base mov yield ldr halt fail add sub mult cmp br bne str run.
From HypVeri.logrel Require Import logrel_prim.
(* From HypVeri.logrel Require Import ftlr_nop ftlr_run ftlr_yield ftlr_share ftlr_retrieve ftlr_relinquish ftlr_reclaim ftlr_donate ftlr_lend *)
(*   ftlr_msg_send ftlr_msg_wait ftlr_msg_poll ftlr_invalid_hvc. *)
From HypVeri Require Import proofmode.
Import uPred.

Section fundamental_prim.
  Context `{hypconst:HypervisorConstants}.
  Context `{hypparams:!HypervisorParameters}.
  Context `{vmG: !gen_VMG Σ}.

  Lemma ftlr_p:
  ∀ p_tx p_rx ps_acc trans, interp_access_prim p_tx p_rx ps_acc trans ⊢ interp_execute V0.
  Proof.
    rewrite /interp_access_prim /=.
  Admitted.

End fundamental_prim.
