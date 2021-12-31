From iris.proofmode Require Import tactics.
From machine_program_logic.program_logic Require Import weakestpre.
From HypVeri.lang Require Import lang.
From HypVeri.algebra Require Import base.
From HypVeri.rules Require Import rules_base (* nop mov ldr str halt fail add sub mult cmp *).
From HypVeri.logrel Require Import logrel logrel_extra.
From HypVeri Require Import proofmode.
From HypVeri.examples Require Import run_yield_with_unknown.proof.
Import uPred.

Section rywu_logrel.
  Context `{hypparams:!HypervisorParameters}.
  Context `{vmG: !gen_VMG Σ}.

  Notation V := ((leibnizO VMID) -n> (leibnizO page_table) -n> iPropO Σ).

  Program Definition rywu_interp_access: V :=
    λne (i:leibnizO VMID) (pgt: page_table),
    (∃ regs mem ,
      (* registers *)
      (⌜total_gmap regs⌝ ∗ [∗ map] r ↦ w ∈ regs, r @@ i ->r w) ∗
      (* mailbox *)
      (∃ p, RX@i := p) ∗ (∃ p, TX@i := p) ∗
        (* status of RX *)
        (RX@ i :=() ∨ ∃ w s, RX@ i :=(w, s)) ∗
        (* memory is total *)
        ⌜total_gmap mem⌝ ∗
        (* pagetable is total *)
        ⌜total_gmap pgt⌝ ∗
        (* accessible memory *)
        (accessible_memory_cells i pgt mem) ∗
      (* VMProp *)
      VMProp i (
        (
        (* in case of yielding, we need the following to apply yield rule*)
        (* R0 & R1 of pvm *)
        (R0 @@ V0 ->r encode_hvc_func(Run) ∗ R1 @@ V0 ->r encode_vmid(i) ∗
        (* VMProp of pvm *)
        (* if 1 yielding, we give following resources back to pvm *)
        VMProp V0 (
          (* R0 and R1 of pvm *)
          (R0 @@ V0 ->r encode_hvc_func(Yield) ∗ R1 @@ V0 ->r encode_vmid(i) ∗
           (* pagetable entries *)
           (pagetable_entries pgt))
              (* no scheduling, we finish the proof *)
          ∨ False
               ) (1/2)%Qp ∗
        (* pagetable entries *)
        (pagetable_entries pgt)))
      ) (1/2)%Qp
    )%I.

End rywu_logrel.

Section rywu_ftlr.

  Context `{hypparams:!HypervisorParameters}.
  Context `{vmG: !gen_VMG Σ}.
  (* TODO *)

  Lemma rywu_ftlr (i:VMID)  :
   ∀ pgt, rywu_interp_access V2 pgt ⊢ interp_execute V2.
  Proof.
  Admitted.

End rywu_ftlr.
