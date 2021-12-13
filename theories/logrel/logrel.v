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

  Notation V := ((leibnizO VMID) -n> (leibnizO page_table) -n> iPropO Σ).
  Notation E := ((leibnizO VMID) -n> iPropO Σ).
  Implicit Types i : (leibnizO VMID).
  Implicit Types interp_expr : (E).

  Program Definition V0 : VMID := (@nat_to_fin 0 _ _).
  Next Obligation.
  destruct hypconst. simpl. lia.
  Defined.

  Definition unknown_mem_page (p: PID) :=
    (∃ mem,
   [∗ map] a ↦ w ∈ mem,  ⌜a ∈ addr_of_page p⌝ -∗ (a ->a w))%I.

  (** definition **)
  Program Definition interp_execute: E :=
   λne (i: leibnizO VMID), (⌜ fin_to_nat i ≠ 0 ⌝ -∗
        (VMProp_holds i (1/2)%Qp -∗ WP ExecI @ i {{(λ _, True )}}))%I.

  Definition shared_or_noaccess_pages (i:VMID) (pgt: page_table) : iProp Σ:=
    (
      [∗ map] p ↦ perm ∈ pgt, let sacc := perm.2 in
                              (* no access, the full entry must be provided *)
                               ((⌜i ∉ sacc⌝ -∗ p -@{1}A> [sacc]) ∗
                              (* shared access, only need the i part *)
                              (* XXX: may need full entry for mem sharing? *)
                                (⌜∃ (j: VMID), j ≠ i ∧ j ∈ sacc⌝ -∗
                                  ∃ (q:frac), p -@{q}A> [{[i]}]))
    )%I.

  Definition exclusive_access_pages (i: VMID) (pgt: page_table) : iProp Σ:=
    [∗ map] p ↦ perm ∈ pgt, let sacc := perm.2 in
                              ⌜{[i]} = sacc⌝ -∗ p -@EA> i.

  (* Definition accessible_memory (i:VMID) (pgt: page_table) (mem:mem): iProp Σ := *)
  (*   [∗ map] p ↦ perm ∈ pgt, let sacc := perm.2 in *)
  (*                            ⌜i ∈ sacc⌝ -∗ unknown_mem_page p. *)

  Definition accessible_memory (i:VMID) (pgt: page_table) (mem:mem): iProp Σ :=
    [∗ map] a ↦ w ∈ mem, (∃ perm, ⌜pgt !! (tpa a) = Some perm⌝ ∗ ⌜i ∈ perm.2⌝) -∗ a ->a w.

  (* FIXME: replace gmap *)
  Definition total_reg_map (reg: gmap reg_name Addr) : iProp Σ := (∀ (r: reg_name), ⌜is_Some (reg !! r)⌝)%I.

  Definition total_pgt_map (pgt: gmap PID (VMID * (gset VMID))) : iProp Σ := (∀ (p: PID), ⌜is_Some (pgt !! p)⌝)%I.

  Definition total_mem_map (mem: gmap Addr Word) : iProp Σ := (∀ (a: Addr), ⌜is_Some (mem !! a)⌝)%I.

  Program Definition interp_access: V :=
    λne (i:leibnizO VMID) (pgt: page_table),
    (∃ regs ,
      (* registers *)
      (total_reg_map regs ∗ [∗ map] r ↦ w ∈ regs, r @@ i ->r w) ∗
      (* mailbox *)
      (∃ p, RX@i := p) ∗ (∃ p, TX@i := p) ∗
      (* VMProp *)
      VMProp i (
        ∃ mem (* pgt_act shandle *),
        (* pagetable is total *)
        total_pgt_map pgt ∗
        (* (* pgt, considering mem sharing *) *)
        (* ⌜dom (gset PID) pgt = dom (gset PID) pgt_act⌝ ∗ *)
        (* (* pgt is the upper bound of pgt_act in terms of accessibility of VM i*) *)
        (* ([∗ map] p ↦ pe ∈ pgt, ⌜i ∉ pe.2⌝ -∗ ⌜pgt_act !! p = Some pe⌝) ∗ *)
        (* ([∗ map] p ↦ pe ∈ pgt, ⌜i ∈ pe.2⌝ -∗ *)
        (* (∃ (pe_act: (VMID * gset VMID)), ⌜pgt_act !! p = Some pe_act⌝ ∗ ⌜pe.1 = pe_act.1⌝ ∗ (⌜pe_act.2 = pe.2⌝ *)
        (*    ∨ (⌜pe_act.2 = pe.2 ∖ {[i]}⌝ ∗ (∃wh v x y m f, wh->t{1}( v , x , y , m , f ) ∗ ⌜wh ∉ shandle⌝ ∨ True))))) ∗ *)
        (* (* handle pool *) *)
        (* hp{1}[shandle] ∗ *)
        (* memory is total *)
        total_mem_map mem ∗
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
               (* NOTE: if i will be scheduled arbitrary number of times, need recursive definition *)
               ) (1/2)%Qp ∗
        (* exclusive access pagetable entries *)
        (exclusive_access_pages i pgt) ∗
        (* shared/noaccess pagetable entries *)
        (shared_or_noaccess_pages i pgt) ∗
        (* accessible memory *)
        (accessible_memory i pgt mem) ∗
        (* status of RX *)
        (RX@ i :=() ∨ ∃ w s, RX@ i :=(w, s)))
        (* no scheduling, we finish the proof *)
        ∨ False
      ) (1/2)%Qp
    )%I.

End logrel.
