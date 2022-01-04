From iris.proofmode Require Import tactics.
From machine_program_logic.program_logic Require Import weakestpre.
From HypVeri.lang Require Import lang.
From HypVeri.algebra Require Import base base_extra mem.
Import uPred.

(**  unary logical relation *)
Section logrel.
  Context `{hypconst:HypervisorConstants}.
  Context `{hypparams:!HypervisorParameters}.
  Context `{vmG: !gen_VMG Σ}.

  Program Definition V0 : VMID := (@nat_to_fin 0 _ _).
  Next Obligation.
  destruct hypconst. simpl. lia.
  Defined.

  (* XXX: a better def using list zip? - no, gmap makes case analysis simpler*)
  Definition unknown_mem_page (p: PID) :=
    (∃ mem, ⌜dom (gset Addr) mem = list_to_set (addr_of_page p)⌝ ∗ [∗ map] a ↦ w ∈ mem, (a ->a w))%I.

  (** definition **)

  Context (i : (leibnizO VMID)).

  Program Definition interp_execute: iPropO Σ :=
   (⌜ fin_to_nat i ≠ 0 ⌝ -∗
        (VMProp_holds i (1/2)%Qp -∗ WP ExecI @ i {{(λ _, True )}}))%I.

  Definition pgt_entries_own_excl (ps: gset PID) (vo: VMID) (be:bool) : iProp Σ:=
    [∗ set] p ∈ ps, p -@O> vo ∗ p -@E> be.

  Definition tran_entries (trans: gmap Addr transaction) : iProp Σ:=
    [∗ map] h ↦ tran ∈ trans , h ->t tran.1 ∗ h ->re tran.2 .

  Definition tran_carried_pgt_entries (trans :gmap Addr transaction): iProp Σ:=
    [∗ map] h ↦ tran ∈ trans , if bool_decide ((tran.1.1.1.1.1 = i) ∨ (tran.1.2 = Donation)) then
                                 ∃v b, pgt_entries_own_excl tran.1.1.2 v b
                               else True.

  Definition accessible_memory_cells (ps : gset PID) (mem:mem): iProp Σ :=
    [∗ set] p ∈ ps, unknown_mem_page p.

  Definition ps_trans (trans: gmap Addr transaction) : gset PID :=
    map_fold (λ (k:Addr) (v:transaction) acc, v.1.1.2 ∪ acc) (∅: gset PID) trans.

  Program Definition interp_access: iPropO Σ:=
    (∃ regs,
      (* registers *)
      (⌜is_total_gmap regs⌝ ∗ [∗ map] r ↦ w ∈ regs, r @@ i ->r w) ∗
      (* mailbox *)
      (∃ p, RX@i := p) ∗ (∃ p, TX@i := p) ∗
      (* VMProp *)
      VMProp i
      ( (∃  mem ps_na ps_acc trans hpool,
            let ps_trans := ps_trans (trans) in
            let ps_oea := ps_acc ∖ ps_trans in
        (* lower bound *)
        LB@ i := [ps_na] ∗ ⌜ps_na ## ps_acc⌝ ∗
        (* resources *)
        i -@A> [ps_acc] ∗
        hp [hpool] ∗ tran_entries trans ∗
        pgt_entries_own_excl ps_oea i true ∗
        tran_carried_pgt_entries trans ∗
        accessible_memory_cells ps_acc mem ∗
        R0 @@ V0 ->r encode_hvc_func(Run) ∗ R1 @@ V0 ->r encode_vmid(i)) ∗
        (* if i yielding, we give following resources back to pvm *)
        VMProp V0 (
          ∃ mem ps_na ps_acc trans hpool,
            let ps_trans := ps_trans (trans) in
            let ps_oea := ps_acc ∖ ps_trans in
          (* lower bound *)
          LB@ i := [ps_na] ∗ ⌜ps_na ## ps_acc⌝ ∗
          (* resources *)
          i -@A> [ps_acc] ∗
          hp [hpool] ∗ tran_entries trans ∗
          pgt_entries_own_excl ps_oea i true ∗
          tran_carried_pgt_entries trans ∗
          accessible_memory_cells ps_acc mem ∗
          (* R0 and R1 of pvm *)
          (R0 @@ V0 ->r encode_hvc_func(Yield) ∗ R1 @@ V0 ->r encode_vmid(i))
          (* no scheduling, we finish the proof *)
          (* NOTE: if i will be scheduled arbitrary number of times, need recursive definition *)
          ∨ False) (1/2)%Qp ∗
        (* status of RX *)
        (RX@ i :=() ∨ ∃ w s, RX@ i :=(w, s)))
      (1/2)%Qp
    )%I.

End logrel.


(* TODO:
   - [] rewrite adequacy
   - [] fix mem_send_nz
 *)
