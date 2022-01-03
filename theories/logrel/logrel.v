From iris.proofmode Require Import tactics.
From machine_program_logic.program_logic Require Import weakestpre.
From HypVeri.lang Require Import lang.
From HypVeri.algebra Require Import base base_extra.
From HypVeri.rules Require Import rules_base.
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

  Definition unknown_mem_page (p: PID) :=
    (∃ mem, [∗ map] a ↦ w ∈ mem, ⌜a ∈ addr_of_page p⌝ -∗ (a ->a w))%I.

  (** definition **)

  Context (i : (leibnizO VMID)).

  Program Definition interp_execute: iPropO Σ :=
   (⌜ fin_to_nat i ≠ 0 ⌝ -∗
        (VMProp_holds i (1/2)%Qp -∗ WP ExecI @ i {{(λ _, True )}}))%I.


  Definition pagetable_entries (pgt: page_table) : iProp Σ:=
    [∗ map] p ↦ perm ∈ pgt, p -@A> [perm.2].

  Definition transaction_entries (trans: gmap Addr transaction) : iProp Σ:=
    [∗ map] h ↦ tran ∈ trans , h ->t tran.1.

  Global Instance filter_match_dec (pgt: page_table) (k:Word) : Decision ((match pgt !! (tpa k) with
                                   | Some perm => i ∈ perm.2
                                   | None => True
                                   end)).
  Proof.
    destruct (pgt !! tpa k).
    eapply _.
    eapply _.
  Qed.

  Definition accessible_memory_cells (pgt: page_table) (mem:mem): iProp Σ :=
    let mem' := filter (λ kv, (match pgt !! (tpa kv.1) with
                                   | Some perm => i ∈ perm.2
                                   | None => True
                                   end)) mem in
    [∗ map] a ↦ w ∈ mem', a ->a w.

  Definition lower_bound_sna_pgt_no_access (sna: gset PID) (pgt: page_table) :=
    set_Forall (λ p, match pgt !! p with
                       | Some perm => i ∉ perm.2
                       | None => False
               end) sna.

  Program Definition interp_access: iPropO Σ:=
    (∃ regs,
      (* registers *)
      (⌜total_gmap regs⌝ ∗ [∗ map] r ↦ w ∈ regs, r @@ i ->r w) ∗
      (* mailbox *)
      (∃ p, RX@i := p) ∗ (∃ p, TX@i := p) ∗
      (* VMProp *)
      VMProp i
      ( (∃ sna mem pgt hpool trans,
        (* totality *)
        ⌜is_total_gmap pgt⌝ ∗ ⌜is_total_gmap mem⌝ ∗
        (* consistency *)
        ⌜inv_trans_hpool_consistent' trans hpool⌝ ∗
        ⌜inv_trans_pgt_consistent' trans pgt⌝ ∗
        (* lower bound *)
        LB@ i := [sna] ∗ ⌜lower_bound_sna_pgt_no_access sna pgt⌝ ∗
        (* resources *)
        hp [hpool] ∗ transaction_entries trans ∗
        pagetable_entries pgt ∗
        accessible_memory_cells pgt mem ∗
        R0 @@ V0 ->r encode_hvc_func(Run) ∗ R1 @@ V0 ->r encode_vmid(i)) ∗
        (* if i yielding, we give following resources back to pvm *)
        VMProp V0 (
          ∃ sna mem pgt hpool trans,
          (* totality *)
          ⌜is_total_gmap pgt⌝ ∗ ⌜is_total_gmap mem⌝ ∗
          (* consistency *)
          ⌜inv_trans_hpool_consistent' trans hpool⌝ ∗
          ⌜inv_trans_pgt_consistent' trans pgt⌝ ∗
          (* lower bound *)
          LB@ i := [sna] ∗ ⌜lower_bound_sna_pgt_no_access sna pgt⌝ ∗
          (* resources *)
          hp [hpool] ∗ transaction_entries trans ∗
          pagetable_entries pgt ∗
          accessible_memory_cells pgt mem ∗
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
   - [] fix mem_send_nz
   - [] rewrite adequacy
 *)
