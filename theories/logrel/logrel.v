From iris.proofmode Require Import tactics.
From machine_program_logic.program_logic Require Import weakestpre.
From HypVeri.lang Require Import lang.
From HypVeri Require Import machine_extra.
From HypVeri.algebra Require Import base base_extra mem.
Import uPred.

(**  unary logical relation *)
Section logrel.
  Context `{hypconst:HypervisorConstants}.
  Context `{hypparams:!HypervisorParameters}.
  Context `{vmG: !gen_VMG Σ}.


  (* XXX: a better def using list zip? - no, gmap makes case analysis simpler*)
  Definition unknown_mem_page (p: PID) :=
    (∃ mem, ⌜∀ (a:Addr), a ∈ (addr_of_page p) -> is_Some (mem !! a)⌝ ∗ [∗ map] a ↦ w ∈ mem, (a ->a w))%I.

  (** definition **)

  Context (i : (leibnizO VMID)).

  Program Definition interp_execute: iPropO Σ :=
   (⌜i ≠ V0⌝ -∗
        (VMProp_holds i (1/2)%Qp -∗ WP ExecI @ i {{(λ _, True )}}))%I.

  Definition pgt_own (ps: gset PID) (vo: VMID) : iProp Σ :=
    [∗ set] p ∈ ps, p -@O> vo.

  Definition pgt_excl (ps: gset PID) (be: bool) : iProp Σ :=
    [∗ set] p ∈ ps, p -@E> be.

  Definition tran_half (trans: gmap Addr transaction) : iProp Σ:=
    [∗ map] h ↦ tran ∈ trans, h -{1/2}>t tran.1.

  Definition retri (trans: gmap Addr transaction) : iProp Σ:=
    [∗ map] h ↦ tran ∈ trans, h ->re tran.2.

  Definition pgt_own_excl_in_tran (trans: gmap Addr transaction) : iProp Σ:=
    [∗ map] h ↦ tran ∈ trans, pgt_own tran.1.1.2 tran.1.1.1.1.1 ∗ pgt_excl tran.1.1.2 (bool_decide (tran.1.2 ≠ Sharing)).


  Definition trans_memory_in_trans (trans : gmap Word transaction) :=
   filter (λ kv, (kv.2.1.1.1.1.1 = i ∧ ¬(kv.2.2 = true ∧ kv.2.1.2 = Lending)) ∨ kv.2.1.1.1.2 = i) trans.

  Definition trans_own_excl_transferred (trans: gmap Word transaction) :=
    filter (λ kv, kv.2.1.2 = Donation ∧ (kv.2.1.1.1.2 = i ∨ kv.2.1.1.1.1.1 = i)) trans.

  Definition trans_own_excl_owned (trans: gmap Word transaction) :=
    filter (λ kv,  kv.2.1.1.1.1.1 = i ∧ kv.2.1.2 ≠ Donation) trans.

  Definition trans_tran_transferred (trans: gmap Word transaction) :=
    filter (λ kv, (kv.2.1.1.1.2 = i ∨ kv.2.1.1.1.1.1 = i) ∧ kv.2.1.2 = Donation) trans.

  Definition trans_tran_owned (trans: gmap Addr transaction) :=
    filter (λ kv, kv.2.1.1.1.1.1 = i ∧ kv.2.1.2 ≠ Donation) trans.

  Definition trans_retri_transferred (trans: gmap Word transaction) :=
    filter (λ kv, (kv.2.1.1.1.2 = i ∨ kv.2.1.1.1.1.1 = i)) trans.

  Definition set_of_addr (ps:gset PID) := (set_fold (λ p (acc:gset Addr), list_to_set (addr_of_page p) ∪ acc) ∅ ps).

  Definition memory_pages (ps :gset PID): iProp Σ:=
    ∃ mem, (⌜dom (gset Addr) mem = set_of_addr ps⌝ ∗ [∗ map] k ↦ v ∈ mem, k ->a v)%I.

  Definition pages_in_trans (trans: gmap Word transaction) : gset PID :=
    map_fold (λ (k:Addr) v acc, v.1.1.2 ∪ acc) (∅: gset PID) trans.

  Definition VMProp_unknown p_tx p_rx trans :=
    VMProp i
           (∃ ps_na' ps_acc' (trans' : gmap Word transaction) hpool' rx_state ,
               let ps_mem_in_trans := pages_in_trans (trans_memory_in_trans trans) in
               let ps_oea := ps_acc' ∖ {[p_rx;p_tx]} ∖ ps_mem_in_trans in
               let ps_mem_in_trans' := pages_in_trans (trans_memory_in_trans trans') in
               let ps_oea' := ps_acc' ∖ {[p_rx;p_tx]} ∖ ps_mem_in_trans' in
               (* lower bound *)
               i -@{1/2}A> [ps_acc'] ∗
               LB@ i := [ps_na'] ∗
               ⌜ps_na' ## ps_acc'⌝ ∗
               (* we need this to ensure all transaction entries are transferred *)
               ⌜inv_trans_hpool_consistent' trans' hpool'⌝ ∗
               ⌜{[p_rx;p_tx]} ## ps_mem_in_trans'⌝ ∗
               (* transaction entries *)
               hp [hpool'] ∗
               (* All of half of transactions are required, as we don't know which one would be used by i.
                  Only *half* is needed so that related vms can remember transactions by keeping the other half. *)
               tran_half trans' ∗
               tran_half (trans_tran_transferred trans') ∗
               (tran_half (trans_tran_owned trans) -∗ tran_half (trans_tran_owned trans')) ∗
               retri (trans_retri_transferred trans') ∗
               (* page table entries *)
               pgt_own_excl_in_tran (trans_own_excl_transferred trans') ∗
               (pgt_own_excl_in_tran (trans_own_excl_owned trans) -∗ pgt_own_excl_in_tran (trans_own_excl_owned trans')) ∗
               (pgt_own ps_oea i ∗ pgt_excl ps_oea true -∗ pgt_own ps_oea' i ∗ pgt_excl ps_oea' true) ∗
               (* mem *)
               memory_pages ps_mem_in_trans' ∗
               (memory_pages ps_oea ∗
                memory_pages ps_mem_in_trans' -∗
                memory_pages (ps_acc' ∖ {[p_rx;p_tx]} ∪ ps_mem_in_trans')) ∗
               R0 @@ V0 ->r encode_hvc_func(Run) ∗ R1 @@ V0 ->r encode_vmid(i) ∗
               (* status of RX *)
               RX_state@ i := rx_state ∗
                  (* RX *)
                  (RX@i := p_rx ∗ p_tx -@O> - ∗ p_tx -@E> true) ∗
                  memory_pages {[p_rx]} ∗
               (* if i yielding, we give following resources back to pvm *)
               VMProp V0
                      ((∃ ps_na'' ps_acc'' trans'' hpool'',
                           let ps_mem_in_trans'' := pages_in_trans (trans_memory_in_trans trans'') in
                           (* lower bound *)
                           i -@{1/2}A> [ps_acc''] ∗
                           LB@ i := [ps_na''] ∗
                           ⌜ps_na' ## ps_acc''⌝ ∗
                           (* we need this to ensure all transaction entries are transferred *)
                           ⌜inv_trans_hpool_consistent' trans'' hpool''⌝ ∗
                           ⌜{[p_rx;p_tx]} ## ps_mem_in_trans''⌝ ∗
                           (* transaction entries *)
                           hp [hpool''] ∗
                           tran_half trans'' ∗
                           tran_half (trans_tran_transferred trans'') ∗
                           tran_half (trans_tran_owned trans'') ∗
                           retri (trans_retri_transferred trans'') ∗
                           (* page table entries *)
                           pgt_own_excl_in_tran (trans_own_excl_transferred trans'') ∗
                           pgt_own_excl_in_tran (trans_own_excl_owned trans'') ∗
                           (* mem *)
                           memory_pages ps_mem_in_trans'' ∗
                           R0 @@ V0 ->r encode_hvc_func(Run) ∗ R1 @@ V0 ->r encode_vmid(i) ∗
                           (* status of RX *)
                           (match rx_state with
                              | None => RX_state@ i := None
                              | Some _ => RX_state@ i := None ∨ RX_state@i := rx_state
                            end) ∗
                           (* RX *)
                           (RX@i := p_rx ∗ p_tx -@O> - ∗ p_tx -@E> true) ∗
                           memory_pages {[p_rx]})
                           (* no scheduling, we finish the proof *)
                           ∨ False) (1/2)%Qp
             ) (1/2)%Qp.

  Program Definition interp_access ps_acc trans p_tx p_rx : iPropO Σ:=
    (
      let ps_mem_in_trans := pages_in_trans (trans_memory_in_trans trans) in
      let ps_oea := ps_acc ∖ {[p_rx;p_tx]} ∖ ps_mem_in_trans in
      (* registers *)
      (∃ regs, ⌜is_total_gmap regs⌝ ∗ [∗ map] r ↦ w ∈ regs, r @@ i ->r w) ∗
      (* TX *)
      (TX@i := p_tx ∗ p_tx -@O> - ∗ p_tx -@E> true ∗ memory_pages {[p_tx]}) ∗
      (* access *)
      i -@{1/2}A> [ps_acc] ∗
      (* own & excl *)
      pgt_own ps_oea i ∗
      pgt_excl ps_oea true ∗
      pgt_own_excl_in_tran (trans_own_excl_owned trans) ∗
      (* transaction *)
      tran_half (trans_tran_owned trans) ∗
      (* (* mem *) *)
      memory_pages ps_oea ∗
      (* VMProp *)
      VMProp_unknown p_tx p_rx trans
      )%I.

End logrel.
