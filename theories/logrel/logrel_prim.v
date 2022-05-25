From iris.proofmode Require Import tactics.
From machine_program_logic.program_logic Require Import weakestpre.
From HypVeri.lang Require Import lang.
From HypVeri.algebra Require Import base base_extra mem mailbox trans.
From HypVeri.logrel Require Export logrel logrel_extra big_sepSS.

Section logrel_prim.

  Context `{hypconst:HypervisorConstants}.
  Context `{hypparams:!HypervisorParameters}.
  Context `{vmG: !gen_VMG Σ}.

  (* Definition trans_rel_primary (i:VMID) (trans trans': gmap Word transaction): Prop := *)
  (*  map_Forall (λ h tran, *)
  (*         ((tran.1.1.1.1 ≠ i ∧ tran.1.1.1.2 ≠ i) -> ∃ tran', trans' !! h = Some tran' ∧ tran = tran') ∧ *)
  (*         ((tran.1.1.1.2 = V0 ∧ tran.2 = true) -> ∃ tran', trans' !! h = Some tran' ∧ tran = tran') ∧ *)
  (*         ((tran.1.1.1.1 = V0 ∧ tran.1.2 ≠ Donation) -> ∃ tran', trans' !! h = Some tran' ∧ tran.1 = tran'.1) *)
  (*    ) trans. *)

  Definition transferred_memory_slice (trans : gmap Addr transaction) (i: VMID) (j:VMID): iProp Σ:=
    big_sepFM trans (λ kv, (kv.2.1.1.1.1 = i ∧ kv.2.1.1.1.2 = j) ∧ ¬(kv.2.2 = true ∧ kv.2.1.2 = Lending)) (λ _ tran, (∃ mem , memory_pages tran.1.1.2 mem)%I).

  Definition retrievable_transaction_transferred_slice (trans : gmap Addr transaction) (i:VMID) (j: VMID) : iProp Σ :=
    (big_sepFM trans (λ kv, kv.2.1.1.1.1 = i ∧ kv.2.1.1.1.2 = j) (λ k v, k -{1/2}>re v.2 )%I) ∗
    (big_sepFM trans (λ kv, (kv.2.1.1.1.1 = i ∧ kv.2.1.1.1.2 = j) ∧ kv.2.2 = false) (λ k v, k -{1/4}>t v.1 ∗ k -{1/2}>re v.2)%I).

  Definition transaction_pagetable_entries_transferred_slice (trans: gmap Addr transaction) (i: VMID) (j: VMID) : iProp Σ :=
    big_sepFM trans (λ kv, (kv.2.1.1.1.1 = i ∧ kv.2.1.1.1.2 = j) ∧ kv.2.1.2 = Donation) (λ k v, k -{1/4}>t v.1 ∗ pgt_1_4 v.1.1.2 v.1.1.1.1 true)%I.

  Definition set_of_vmids : gset VMID := (list_to_set list_of_vmids).

  Definition trans_preserve_slice i j (trans trans': (gmap Addr transaction)):=
    filter (λ kv, kv.2.1.1.1.1 = i ∧ kv.2.1.1.1.2 = j) trans
                        = filter (λ kv, kv.2.1.1.1.1 = i ∧ kv.2.1.1.1.2 = j) trans'.

  Definition trans_preserve_only i (trans trans': (gmap Addr transaction)) :=
    filter (λ kv, kv.2.1.1.1.1 = i ∨ kv.2.1.1.1.2 = i) trans
                        = filter (λ kv, kv.2.1.1.1.1 = i ∨ kv.2.1.1.1.2 = i) trans'.

  (*TODO*)
  Definition trans_preserve_except i (trans trans': (gmap Addr transaction)) :=
    map_Forall (λ h tran, ¬(tran.1.1.1.1 = i ∨ tran.1.1.1.2 = i) -> ∃ tran', trans' !! h = Some tran' ∧ tran = tran') trans.

  Definition slice_wf (Φ: (gmap Addr transaction) -> VMID -> VMID -> iProp Σ) :=
    ∀ i j trans trans', trans_preserve_slice i j trans trans'->
    (Φ trans i j ⊣⊢ Φ trans' i j).

  Definition slice_wf2 (Φ: (gmap Addr transaction) -> VMID -> VMID -> iProp Σ) :=
    ∀ i j (trans trans' : gmap Addr transaction),
    dom (gset _) (filter (λ kv, kv.2.1.1.1.1 = i ∧ kv.2.1.1.1.2 = j)%type trans') ⊆ dom _ trans ->
    ([∗ map] h ↦ tran ∈ trans, h -{1/2}>t tran.1) ⊢
    (Φ trans' i j) ∗-∗ (Φ (map_zip (fst<$>trans) (snd <$>trans')) i j).

  Class SliceWf (Φ: (gmap Addr transaction) -> VMID -> VMID-> iProp Σ):=
    {
      slice : (slice_wf Φ);
      agree : (slice_wf2 Φ)
    }.

  Program Definition interp_access_prim Φ p_tx p_rx ps_acc trans `(!SliceWf Φ): iPropO Σ:=
    (
      (* let ps_macc_trans := (transferred_memory_pages_all trans) in *)
      let ps_oea := ps_acc ∖ {[p_rx;p_tx]} ∖ (currently_accessible_in_trans_memory_pages V0 trans) in
      (∃ regs, ⌜is_total_gmap regs⌝ ∗ [∗ map] r ↦ w ∈ regs, r @@ V0 ->r w) ∗
      (tx_page V0 p_tx ∗ ∃ mem_tx, memory_page p_tx mem_tx) ∗
      V0 -@A> ps_acc ∗
      ⌜{[p_tx;p_rx]} ⊆ ps_acc⌝ ∗ ⌜currently_accessible_in_trans_memory_pages V0 trans ⊆ ps_acc ∖ {[p_tx;p_rx]}⌝ ∗
      pagetable_entries_excl_owned V0 ps_oea ∗
      transaction_pagetable_entries_owned V0 trans ∗
      retrieved_transaction_owned V0 trans ∗
      (∃ mem_oea, memory_pages (ps_oea ∪ (retrieved_lending_memory_pages V0 trans)) mem_oea) ∗
      VMProp V0 True 1%Qp ∗
      (* transferred *)
      (∃ rx_state, RX_state@ V0 := rx_state) ∗ (rx_page V0 p_rx) ∗ (∃ mem_rx, memory_page p_rx mem_rx) ∗
      transaction_hpool_global_transferred trans ∗
      rx_pages (list_to_set (list_of_vmids) ∖ {[V0]}) ∗
      (big_sepSS set_of_vmids (Φ trans)) ∗
      (* transaction_pagetable_entries_transferred_all trans ∗ *)
      (* retrievable_transaction_transferred_all trans ∗ *)
      (* (∃ mem_trans, memory_pages ps_macc_trans mem_trans) ∗ *)
      [∗ set] i ∈ set_of_vmids ∖ {[V0]}, VMProp (i:VMID) (vmprop_unknown i p_tx p_rx) (1/2)%Qp
    )%I.

End logrel_prim.
