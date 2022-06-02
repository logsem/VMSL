From iris.proofmode Require Import tactics.
From machine_program_logic.program_logic Require Import weakestpre.
From HypVeri.lang Require Import lang.
From HypVeri.algebra Require Import base base_extra mem mailbox trans.
From HypVeri.logrel Require Export logrel logrel_extra big_sepSS.

Section slice_trans.
  Context `{hypconst:HypervisorConstants}.

  Definition set_of_vmids : gset VMID := (list_to_set list_of_vmids).

  Context `{vmG: !gen_VMG Σ}.
  Context (Φ : (gmap Addr transaction) -> VMID -> VMID -> iProp Σ).

  Definition trans_preserve_slice i j (trans trans': (gmap Addr transaction)):=
    filter (λ kv, kv.2.1.1.1.1 = i ∧ kv.2.1.1.1.2 = j) trans
                        = filter (λ kv, kv.2.1.1.1.1 = i ∧ kv.2.1.1.1.2 = j) trans'.

  Class SliceTransWf :=
    {
      slice_trans_valid : ∀ i j trans trans',
        trans_preserve_slice i j trans trans'-> (Φ trans i j ⊣⊢ Φ trans' i j);
      (* slice_trans_agree : ∀ i j (trans trans' : gmap Addr transaction), *)
      (*   dom (gset _) (filter (λ kv, kv.2.1.1.1.1 = i ∧ kv.2.1.1.1.2 = j)%type trans') ⊆ dom _ trans -> *)
      (*   ([∗ map] h ↦ tran ∈ trans, h -{1/2}>t tran.1) ⊢ *)
      (*   (Φ trans' i j) ∗-∗ (Φ (map_zip (fst<$>trans) (snd <$>trans')) i j); *)
      (* (* slice_trans_agree : ∀ i j (trans trans' : gmap Addr transaction), *) *)
      (* (*   ([∗ map] h ↦ tran ∈ trans, h -{1/2}>t tran.1) ∗ (Φ trans' i j) ⊢ *) *)
      (* (*  ⌜trans_preserve_slice_fst i j trans trans'⌝; *) *)
      slice_trans_timeless : ∀ i j trans, Timeless (Φ trans i j)
    }.

  End slice_trans.

Section slice_rxs.
  Context `{hypconst:HypervisorConstants}.
  Context `{vmG: !gen_VMG Σ}.
  Context (Φ :VMID -> option (Word * VMID)-> VMID -> iProp Σ).

  Class SliceRxsWf :=
    {
      slice_rxs_empty :  ∀ i j, Φ i None j ⊣⊢ True;
      slice_rxs_sym : ∀ i os k k',
        (match os with
         | None => True
         | Some (_,j) => j ≠ V0
         end) -> Φ i os k ⊣⊢ Φ i os k';
      slice_rxs_timeless : ∀ i os j, Timeless (Φ i os j)
    }.

  End slice_rxs.

  Section vmprop.
  Context `{HypervisorConstants}.
  Context `{!HypervisorParameters}.
  Context `{vmG: !gen_VMG Σ}.
  Context (i : VMID).
  Context (Φ_t : (gmap Addr transaction) -> VMID -> VMID -> iProp Σ).
  Context (Φ_r : VMID -> option (Word * VMID)-> VMID -> iProp Σ).

  Definition rx_states_transferred (rxs: gmap VMID (option (Word*VMID))) : iProp Σ :=
    [∗ map]i ↦ os ∈ rxs, match os with
                           | None => True
                           | Some s => Φ_r i os V0
                          end.

  Definition rx_states_owned (rxs: gmap VMID (option (Word*VMID))) : iProp Σ :=
    [∗ map]i ↦ os ∈ rxs, match os with
                           | None => True
                           | Some s => if bool_decide (s.2 = V0) then Φ_r i os i else True
                          end.

  Definition return_reg_rx i (rs : option (Word * VMID)) (rxs :gmap VMID (option(Word*VMID))): iProp Σ:=
    ((R0 @@ V0 ->r encode_hvc_func(Yield) ∨
      R0 @@ V0 ->r encode_hvc_func(Wait) ∗ ⌜rs = None⌝)
     ∗ rx_states_global (delete i rxs)
     ∗ R1 @@ V0 ->r encode_vmid(i) ∗ ∃ r2, R2 @@ V0 ->r r2) ∨
    (R0 @@ V0 ->r encode_hvc_func(Send)
      ∗ ∃ l j, Φ_r j (Some (l,i)) V0
      ∗ rx_states_global (<[j:=Some(l,i)]>(delete i rxs))
      ∗ (∃r1, R1 @@ V0 ->r r1 ∗ ⌜decode_vmid r1 = Some j⌝) ∗  R2 @@ V0 ->r l).

  Definition only (trans: gmap Word transaction) := (filter (λ (kv :Word*transaction), (kv.2.1.1.1.1 = i ∨ kv.2.1.1.1.2 = i)) trans).

  Definition except (trans: gmap Word transaction) := (filter (λ (kv :Word*transaction), ¬(kv.2.1.1.1.1 = i ∨ kv.2.1.1.1.2 = i)) trans).

  Definition vmprop_zero_pre (Ψ: iPropO Σ) : (gmap Word transaction) -d> (gmap VMID (option(Word * VMID))) -d> iPropO Σ :=
    λ trans rxs, (∃ (trans' :gmap Word transaction) rs',
                     let trans_ret := (only trans') ∪ trans in
                           (* ⌜only trans' ##ₘ except trans⌝ *)
                           transaction_hpool_global_transferred (trans_ret) ∗
                           big_sepSS_singleton set_of_vmids i (Φ_t trans_ret) ∗
                           rx_state_match i rs' ∗ Φ_r i rs' V0 ∗
                           return_reg_rx i rs' rxs ∗
                           VMProp i (Ψ) (1/2)%Qp)%I.

  Definition vmprop_unknown_pre
    (Ψ : iPropO Σ) : iPropO Σ :=
    (∃ (trans : gmap Word transaction) (rxs : gmap VMID (option(Word * VMID))),
               (* transaction and pagetable entries *)
               transaction_hpool_global_transferred trans ∗
               big_sepSS_singleton set_of_vmids i (Φ_t trans) ∗
               (∃ r0, R0 @@ V0 ->r r0 ∗ ⌜decode_hvc_func r0 = Some Run⌝) ∗ (∃ r1, R1 @@ V0 ->r r1 ∗ ⌜decode_vmid r1 = Some i⌝)∗ (∃ r2, R2 @@ V0 ->r r2) ∗
               (∀ rs : option (Addr * VMID), ⌜rxs !! i = Some rs⌝ -∗ rx_state_match i rs ∗ Φ_r i rs i) ∗
               (* rx pages for all other VMs *)
               (rx_states_global (delete i rxs)) ∗ ⌜is_total_gmap rxs⌝ ∗
               (* if i yielding, we give following resources back to pvm *)
               VMProp V0 (vmprop_zero_pre Ψ trans rxs) (1/2)%Qp)%I.

  Local Instance vmprop_unknown_pre_contractive : Contractive (vmprop_unknown_pre).
  Proof.
    rewrite /vmprop_unknown_pre => n vmprop_unknown vmprop_unknown' Hvmprop_unknown /=.
    do 12 f_equiv.
    rewrite /VMProp /=.
    do 6 f_equiv.
    f_contractive.
    rewrite /vmprop_zero_pre.
    do 9 f_equiv.
    rewrite /VMProp.
    repeat f_equiv.
    apply Hvmprop_unknown.
  Qed.

  Definition vmprop_unknown:= fixpoint (vmprop_unknown_pre).

  Definition vmprop_zero := vmprop_zero_pre vmprop_unknown.

  Lemma vmprop_unknown_def : vmprop_unknown ≡
    (∃ (trans : gmap Word transaction) (rxs : gmap VMID (option(Word * VMID))),
               (* transaction and pagetable entries *)
               transaction_hpool_global_transferred trans ∗
               big_sepSS_singleton set_of_vmids i (Φ_t trans) ∗
               (∃ r0, R0 @@ V0 ->r r0 ∗ ⌜decode_hvc_func r0 = Some Run⌝) ∗ (∃ r1, R1 @@ V0 ->r r1 ∗ ⌜decode_vmid r1 = Some i⌝)∗ (∃ r2, R2 @@ V0 ->r r2) ∗
               (∀ rs : option (Addr * VMID), ⌜rxs !! i = Some rs⌝ -∗ rx_state_match i rs ∗ Φ_r i rs i) ∗
               (* rx pages for all other VMs *)
               (rx_states_global (delete i rxs)) ∗ ⌜is_total_gmap rxs⌝ ∗
               (* if i yielding, we give following resources back to pvm *)
          VMProp V0 (vmprop_zero trans rxs) (1/2)%Qp)%I.
  Proof.
    rewrite /vmprop_unknown //.
    rewrite (fixpoint_unfold vmprop_unknown_pre).
    setoid_reflexivity.
  Qed.

  Lemma vmprop_unknown_eq : vmprop_unknown ⊣⊢
    (∃ (trans : gmap Word transaction) (rxs : gmap VMID (option(Word * VMID))),
               (* transaction and pagetable entries *)
               transaction_hpool_global_transferred trans ∗
               big_sepSS_singleton set_of_vmids i (Φ_t trans) ∗
               (∃ r0, R0 @@ V0 ->r r0 ∗ ⌜decode_hvc_func r0 = Some Run⌝) ∗ (∃ r1, R1 @@ V0 ->r r1 ∗ ⌜decode_vmid r1 = Some i⌝)∗ (∃ r2, R2 @@ V0 ->r r2) ∗
               (∀ rs : option (Addr * VMID), ⌜rxs !! i = Some rs⌝ -∗ rx_state_match i rs ∗ Φ_r i rs i) ∗
               (* rx pages for all other VMs *)
               (rx_states_global (delete i rxs)) ∗ ⌜is_total_gmap rxs⌝ ∗
               (* if i yielding, we give following resources back to pvm *)
          VMProp V0 (vmprop_zero trans rxs) (1/2)%Qp)%I.
  Proof.
    rewrite /vmprop_unknown.
    apply (fixpoint_unfold vmprop_unknown_pre).
  Qed.

  End vmprop.

Section logrel_prim.

  Context `{HypervisorConstants}.
  Context `{!HypervisorParameters}.
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

  Definition slice_transfer_all :=
    (λ trans i j, transaction_pagetable_entries_transferred_slice trans i j
                ∗ retrievable_transaction_transferred_slice trans i j
                ∗ transferred_memory_slice trans i j)%I.

  Definition slice_rx_state (j : VMID) (os : option (Word * VMID)) : iProp Σ :=
    ∃ p_rx, RX@ j := p_rx ∗ (RX_state{1/2}@j := os) ∗ (∃ mem_rx, memory_page p_rx mem_rx).

  Definition interp_access_prim Φ_t Φ_r (p_tx p_rx :PID) (ps_acc: gset PID) (trans: gmap Word transaction)
    (rxs : gmap VMID (option (Word * VMID))) `{!SliceTransWf Φ_t} `{!SliceRxsWf Φ_r}: iPropO Σ:=
    (
      (* making sure we have enough resources for V0 *)
      ⌜∀ i j trans, (i = V0 ∨ j = V0) -> Φ_t trans i j ⊣⊢ slice_transfer_all trans i j⌝ ∗
      ⌜∀ i os, (match os with
                 | None => True
                 | Some (_,j) => j = V0
                end) -> Φ_r i os i ⊣⊢ slice_rx_state i os⌝ ∗
      ⌜∀ i j os, (match os with
                 | None => True
                 | Some (_,j) => j = V0
                end) -> j ≠ i -> j ≠ V0 -> Φ_r i os j ⊣⊢ True⌝ ∗
      ⌜∀ i, Φ_r V0 i V0 ⊣⊢ slice_rx_state V0 i⌝ ∗
      let ps_oea := ps_acc ∖ {[p_rx;p_tx]} ∖ (currently_accessible_in_trans_memory_pages V0 trans) in
      (∃ regs, ⌜is_total_gmap regs⌝ ∗ [∗ map] r ↦ w ∈ regs, r @@ V0 ->r w) ∗
      (tx_page V0 p_tx ∗ ∃ mem_tx, memory_page p_tx mem_tx) ∗
      (rx_page V0 p_rx) ∗
      V0 -@A> ps_acc ∗
      ⌜{[p_tx;p_rx]} ⊆ ps_acc⌝ ∗ ⌜currently_accessible_in_trans_memory_pages V0 trans ⊆ ps_acc ∖ {[p_tx;p_rx]}⌝ ∗
      pagetable_entries_excl_owned V0 ps_oea ∗
      transaction_pagetable_entries_owned V0 trans ∗
      retrieved_transaction_owned V0 trans ∗
      (∃ mem_oea, memory_pages (ps_oea ∪ (retrieved_lending_memory_pages V0 trans)) mem_oea) ∗
      (∃ P0, VMProp V0 P0 1%Qp) ∗
      (* transferred *)
      transaction_hpool_global_transferred trans ∗
      ⌜is_total_gmap rxs⌝ ∗
      rx_states_global rxs ∗
      rx_states_transferred Φ_r rxs ∗
      (* rx_states_owned Φ_r rxs ∗ *)
      (big_sepSS set_of_vmids (Φ_t trans)) ∗
      [∗ set] i ∈ set_of_vmids ∖ {[V0]}, VMProp (i:VMID) (vmprop_unknown i Φ_t Φ_r) (1/2)%Qp
    )%I.

  Definition interp_execute_prim: iPropO Σ :=
    WP ExecI @ V0 {{(λ _, True )}}%I.

End logrel_prim.
