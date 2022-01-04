From iris.proofmode Require Import tactics.
From machine_program_logic.program_logic Require Import weakestpre.
From HypVeri.lang Require Import lang.
From HypVeri.algebra Require Import base base_extra.
(* From HypVeri.rules Require Import rules_base (* nop mov ldr str halt fail add sub mult cmp *). *)
From HypVeri.logrel Require Import logrel logrel_extra.
From HypVeri Require Import proofmode.
(* From HypVeri.examples Require Import run_yield_with_unknown.proof. *)
Import uPred.

Section rywu_logrel.
  Context `{hypparams:HypervisorParameters}.
  Context `{vmG: !gen_VMG Σ}.

  Notation V := ((leibnizO VMID) -n> iPropO Σ).

  Program Definition rywu_interp_access: V :=
    λne (i:leibnizO VMID),
    (∃ regs ps_acc,
      (* registers *)
      (⌜is_total_gmap regs⌝ ∗ [∗ map] r ↦ w ∈ regs, r @@ i ->r w) ∗
      (* mailbox *)
      (∃ p, RX@i := p) ∗ (∃ p, TX@i := p) ∗
      (RX@ i :=() ∨ ∃ w s, RX@ i :=(w, s)) ∗
      i -@A> [ps_acc] ∗
      (* VMProp *)
      VMProp i
      ( (∃ mem ps_na trans hpool,
            let ps_trans := ps_trans (trans) in
            let ps_oea := ps_acc ∖ ps_trans in
        (* lower bound *)
        LB@ i := [ps_na] ∗ ⌜ps_na ## ps_acc⌝ ∗
        (* resources *)
        hp [hpool] ∗ tran_entries trans ∗
        pgt_entries_own_excl ps_oea i true ∗
        tran_carried_pgt_entries i trans ∗
        accessible_memory_cells ps_acc mem ∗
        R0 @@ V0 ->r encode_hvc_func(Run) ∗ R1 @@ V0 ->r encode_vmid(i)) ∗
        (* if i yielding, we give following resources back to pvm *)
        VMProp V0 (
          ∃ mem ps_na trans hpool,
            let ps_trans := ps_trans (trans) in
            let ps_oea := ps_acc ∖ ps_trans in
          (* lower bound *)
          LB@ i := [ps_na] ∗ ⌜ps_na ## ps_acc⌝ ∗
          (* resources *)
          hp [hpool] ∗ tran_entries trans ∗
          pgt_entries_own_excl ps_oea i true ∗
          tran_carried_pgt_entries i trans ∗
          accessible_memory_cells ps_acc mem ∗
          (* R0 and R1 of pvm *)
          (R0 @@ V0 ->r encode_hvc_func(Yield) ∗ R1 @@ V0 ->r encode_vmid(i))
          (* no scheduling, we finish the proof *)
          ∨ False) (1/2)%Qp
        )
      (1/2)%Qp
    )%I.

End rywu_logrel.

Section rywu_ftlr.

  Context `{hypparams:HypervisorParameters}.
  Context `{vmG: !gen_VMG Σ}.
  (* TODO *)

  Lemma rywu_ftlr (i:VMID)  :
   rywu_interp_access i ⊢ interp_execute i.
  Proof.
  Admitted.

End rywu_ftlr.
