From iris.proofmode Require Import tactics.
From machine_program_logic.program_logic Require Import weakestpre.
From HypVeri.lang Require Import lang.
From HypVeri.algebra Require Import base.
From HypVeri.rules Require Import rules_base.
Import uPred.


(**  unary logical relation *)
Section logrel.
  Context `{hypconst:HypervisorConstants}.
  Context `{hypparams:!HypervisorParameters}.
  Context `{vmG: !gen_VMG Σ}.

  Notation V := ((leibnizO VMID) -n> (leibnizO page_table) -n> (leibnizO reg_file) -n> iPropO Σ).
  Notation E := ((leibnizO VMID) -n> iPropO Σ).
  Implicit Types i : (leibnizO VMID).
  Implicit Types interp_expr : (E).

  Program Definition V0 : VMID := (@nat_to_fin 0 _ _).
  Next Obligation.
  destruct hypconst. simpl. lia.
  Defined.

  Definition unknown_mem_page (p: PID):=
   ([∗ list] a ∈ (finz.seq (of_pid p) (Z.to_nat page_size)), ∃ w, (a ->a w))%I.


  (** definition **)
  Program Definition interp_execute: E :=
   λne (i: leibnizO VMID), (⌜ fin_to_nat i ≠ 0 ⌝ -∗ (VMProp_holds i (1/2)%Qp -∗ WP ExecI @ i {{(λ _, True )}}))%I.


  Definition shared_or_noaccess_pages (i:VMID) (pgt: page_table) : iProp Σ:=
    (
      [∗ map] p ↦ perm ∈ pgt, let sacc := perm.2 in
                              ∃ (j: VMID), ⌜j ≠ i ∧ j ∈ sacc⌝ -∗
                                p -@{1}A> [sacc] ∗
                                  (⌜i ∈ sacc⌝ -∗ unknown_mem_page p)
    )%I.

  Definition exclusive_access_pages (i:VMID) (pgt: page_table) : iProp Σ:=
    (
      [∗ map] p ↦ perm ∈ pgt, let sacc := perm.2 in
                               ⌜{[i]} = sacc⌝ -∗
                                p -@EA> i ∗ unknown_mem_page p
    )%I.

  Definition full_reg_map (reg : reg_file) : iProp Σ := (∀ (r :reg_name), ⌜is_Some (reg !! r)⌝)%I.

  (*TODO: full_mem_map*)
  (*XXX: partial pgt_map? *)

  Program Definition interp_access: V :=
    λne (i:leibnizO VMID) (pgt: page_table) (regs: reg_file),
      ( (* registers *)
        ( full_reg_map regs ∗ [∗ map] r ↦ w ∈ regs, r @@i ->r w) ∗
        (* VMProp  *)
        VMProp i (
          (* in case of yielding, we need the following to apply yield rule*)
          (* R0 & R1 of pvm *)
          (R0 @@ V0 ->r encode_hvc_func(Run) ∗ R1 @@ V0 ->r encode_vmid(i) ∗
          (* VMProp of pvm *)
          (* if i yielding, we give following resources back to pvm *)
          VMProp V0 (
            (* R0 and R1 of pvm *)
            R0 @@ V0 ->r encode_hvc_func(Yield) ∗ R1 @@ V0 ->r encode_vmid(i) ∗
            (* exclusive access pagetable entries + mem *)
            (exclusive_access_pages i pgt) ∗
            (* shared/noaccess pagetable entries + shared mem *)
            (shared_or_noaccess_pages i pgt)
              (* TODO: recursive definition *)
          ) (1/2)%Qp ∗
          (* exclusive access pagetable entries + mem *)
          (exclusive_access_pages i pgt) ∗
          (* shared/noaccess pagetable entries + shared mem *)
          (shared_or_noaccess_pages i pgt))
          (* no scheduling, we finish the proof *)
          ∨ False
        ) (1/2)%Qp
      )%I.

End logrel.
