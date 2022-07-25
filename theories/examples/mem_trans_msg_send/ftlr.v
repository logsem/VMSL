From iris.proofmode Require Import tactics.
From machine_program_logic.program_logic Require Import weakestpre.
From HypVeri.lang Require Import lang.
From HypVeri.algebra Require Import base base_extra.
From HypVeri.logrel Require Import logrel logrel_extra fundamental.
From HypVeri Require Import proofmode.
From HypVeri.examples Require Import mem_trans_msg_send.proof.
Import uPred.

Section mtms_ftlr.
  Context `{hypparams: !@HypervisorParameters rywu_vmconfig}.
  Context `{vmG: !@gen_VMG rywu_vmconfig Σ}.

  Definition mtms_interp_access (p_prog3 p_tx p_rx :PID):= interp_access (V2 : leibnizO VMID) p_tx p_rx {[p_prog3; p_tx; p_rx]} ∅.

  Lemma mtms_ftlr (p_prog3 p_tx p_rx :PID):
   mtms_interp_access p_prog3 p_tx p_rx ⊢ interp_execute V2.
  Proof. iApply ftlr. Qed.

End mtms_ftlr.
