From iris.proofmode Require Import tactics.
From machine_program_logic.program_logic Require Import weakestpre.
From HypVeri.lang Require Import lang.
From HypVeri.algebra Require Import base base_extra mem mailbox trans.
From HypVeri.logrel Require Export logrel logrel_extra big_sepSS.

Section slice.
  Context `{hypconst:HypervisorConstants}.

  Definition set_of_vmids : gset VMID := (list_to_set list_of_vmids).

  Context `{vmG: !gen_VMG Σ}.

  Context (Φ : (gmap Addr transaction) -> VMID -> VMID -> iProp Σ).
  (*TODO*)
  Definition trans_preserve_except i (trans trans': (gmap Addr transaction)) :=
    map_Forall (λ h tran, ¬(tran.1.1.1.1 = i ∨ tran.1.1.1.2 = i) -> ∃ tran', trans' !! h = Some tran' ∧ tran = tran') trans.

  Definition trans_preserve_slice i j (trans trans': (gmap Addr transaction)):=
    filter (λ kv, kv.2.1.1.1.1 = i ∧ kv.2.1.1.1.2 = j) trans
                        = filter (λ kv, kv.2.1.1.1.1 = i ∧ kv.2.1.1.1.2 = j) trans'.

  Definition trans_preserve_only i (trans trans': (gmap Addr transaction)) :=
    filter (λ kv, kv.2.1.1.1.1 = i ∨ kv.2.1.1.1.2 = i) trans
                        = filter (λ kv, kv.2.1.1.1.1 = i ∨ kv.2.1.1.1.2 = i) trans'.
  Definition slice_wf :=
    ∀ i j trans trans', trans_preserve_slice i j trans trans'->
    (Φ trans i j ⊣⊢ Φ trans' i j).

  Definition slice_wf2 :=
    ∀ i j (trans trans' : gmap Addr transaction),
    dom (gset _) (filter (λ kv, kv.2.1.1.1.1 = i ∧ kv.2.1.1.1.2 = j)%type trans') ⊆ dom _ trans ->
    ([∗ map] h ↦ tran ∈ trans, h -{1/2}>t tran.1) ⊢
    (Φ trans' i j) ∗-∗ (Φ (map_zip (fst<$>trans) (snd <$>trans')) i j).

  Class SliceWf :=
    {
      valid : slice_wf;
      agree : slice_wf2
    }.

  End slice.

  Section vmprop.
  Context `{HypervisorConstants}.
  Context `{!HypervisorParameters}.
  Context (i : VMID).
  Context `{vmG: !gen_VMG Σ}.
  Context (Φ_t : (gmap Addr transaction) -> VMID -> VMID -> iProp Σ).
  Context (Φ_r : VMID -> VMID -> iProp Σ).

  Definition rx_state_yield (j : VMID) rx_state : iProp Σ :=
     (∃ p_rx, RX@ j := p_rx ∗  RX_state{1/2}@j := rx_state ∗
                  match rx_state with
                  | None => (RX_state{1/2}@j := rx_state ∗ ∃ mem_rx, memory_page p_rx mem_rx)
                  | Some (_,v) => True
                  end)%I.

  Definition rx_state_run (i j : VMID) rx_state : iProp Σ :=
     (∃ p_rx, RX@ j := p_rx ∗  RX_state{1/2}@j := rx_state ∗
                  match rx_state with
                  | None => (RX_state{1/2}@j := rx_state ∗ ∃ mem_rx, memory_page p_rx mem_rx)
                  | Some (_,v) => if bool_decide(i = j) then Φ_r v j else True
                  end)%I.

  Definition return_reg_rx i : iProp Σ:=
    ((R0 @@ V0 ->r encode_hvc_func(Yield) ∗ (∃ rx_state'', rx_state_yield i rx_state'') ∨
      R0 @@ V0 ->r encode_hvc_func(Wait) ∗ rx_state_yield i None) ∗ R1 @@ V0 ->r encode_vmid(i) ∗ ∃ r2, R2 @@ V0 ->r r2) ∨
    (R0 @@ V0 ->r encode_hvc_func(Send) ∗ (∃ rx_state'', rx_state_yield i rx_state'') ∗ ∃ j l, ⌜j ≠ i⌝ ∗
                          (∃r1, R1 @@ V0 ->r r1 ∗ ⌜decode_vmid r1 = Some j⌝) ∗  R2 @@ V0 ->r l ∗
                              (Φ_r i j)).

  Definition vmprop_zero_pre (Ψ: PID -d> PID -d> iPropO Σ) :PID -d> PID -d> iPropO Σ :=
    λ p_tx p_rx, (∃ trans'',
                           (* transaction and pagetable entries *)
                           transaction_hpool_global_transferred trans'' ∗
                           big_sepSS_singleton set_of_vmids i (Φ_t trans'') ∗
                           (* RX *)
                           rx_page i p_rx ∗
                           ([∗ set] j ∈ set_of_vmids ∖ {[i]}, ∃ rx_state', rx_state_yield j rx_state') ∗
                           return_reg_rx i ∗
                           VMProp i (Ψ p_tx p_rx) (1/2)%Qp)%I.

  Definition vmprop_unknown_pre
    (Ψ : PID -d> PID -d> iPropO Σ)
    :PID -d> PID -d> iPropO Σ :=
    λ p_tx p_rx,
    (∃ (trans' : gmap Word transaction),
               (* transaction and pagetable entries *)
               transaction_hpool_global_transferred trans' ∗
               big_sepSS_singleton set_of_vmids i (Φ_t trans') ∗
               R0 @@ V0 ->r encode_hvc_func(Run) ∗ R1 @@ V0 ->r encode_vmid(i) ∗ (∃ r2, R2 @@ V0 ->r r2) ∗
               (* RX *)
               (rx_page i p_rx) ∗
               (* rx pages for all other VMs *)
               ([∗ set] j ∈ set_of_vmids, ∃ rx_state', rx_state_run i j rx_state') ∗
               (* if i yielding, we give following resources back to pvm *)
               VMProp V0 (vmprop_zero_pre Ψ p_tx p_rx) (1/2)%Qp)%I.

  Local Instance vmprop_unknown_pre_contractive : Contractive (vmprop_unknown_pre).
  Proof.
    rewrite /vmprop_unknown_pre => n vmprop_unknown vmprop_unknown' Hvmprop_unknown p_tx p_rx /=.
    do 9 f_equiv.
    rewrite /VMProp /=.
    do 6 f_equiv.
    f_contractive.
    rewrite /vmprop_zero_pre.
    do 7 f_equiv.
    rewrite /VMProp.
    repeat f_equiv.
  Qed.

  Definition vmprop_unknown:= fixpoint (vmprop_unknown_pre).

  Definition vmprop_zero := vmprop_zero_pre vmprop_unknown.

  Lemma vmprop_unknown_def : vmprop_unknown ≡
    λ p_tx p_rx,
      (∃ (trans' : gmap Word transaction),
          transaction_hpool_global_transferred trans' ∗
          big_sepSS_singleton set_of_vmids i (Φ_t trans') ∗
          R0 @@ V0 ->r encode_hvc_func(Run) ∗ R1 @@ V0 ->r encode_vmid(i) ∗ (∃ r2, R2 @@ V0 ->r r2) ∗
          (rx_page i p_rx) ∗
          ([∗ set] j ∈ set_of_vmids, ∃ rx_state', rx_state_run i j rx_state') ∗
          VMProp V0 (vmprop_zero p_tx p_rx) (1/2)%Qp)%I.
  Proof.
    rewrite /vmprop_unknown //.
    rewrite (fixpoint_unfold vmprop_unknown_pre).
    setoid_reflexivity.
  Qed.

  Global Instance vmprop_unknown_proper: Proper ((=) ==> (=) ==> (⊣⊢)) vmprop_unknown.
  Proof. apply _. Qed.

  Lemma vmprop_unknown_eq (p_tx p_rx:PID) : vmprop_unknown p_tx p_rx ⊣⊢
      (∃ (trans' : gmap Word transaction),
               transaction_hpool_global_transferred trans' ∗
               big_sepSS_singleton set_of_vmids i (Φ_t trans') ∗
               R0 @@ V0 ->r encode_hvc_func(Run) ∗ R1 @@ V0 ->r encode_vmid(i) ∗ (∃ r2, R2 @@ V0 ->r r2) ∗
               (rx_page i p_rx) ∗
               ([∗ set] j ∈ set_of_vmids, ∃ rx_state', rx_state_run i j rx_state') ∗
               VMProp V0 (vmprop_zero p_tx p_rx) (1/2)%Qp)%I.
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

  Definition slice_rx_state (i j: VMID) : iProp Σ :=
    ∃ p_rx, RX@ j := p_rx ∗ (∃ l,  RX_state{1/2}@j := Some(l, i)) ∗ (∃ mem_rx, memory_page p_rx mem_rx).

  Program Definition interp_access_prim Φ_t Φ_r p_tx p_rx ps_acc trans `{!SliceWf Φ_t}: iPropO Σ:=
    (
      (* making sure we have enough resources for V0 *)
      ⌜∀ i j trans, (i = V0 ∨ j = V0) -> Φ_t trans i j ⊣⊢ slice_transfer_all trans i j⌝ ∗
      ⌜∀ i, Φ_r i V0 ⊣⊢ slice_rx_state i V0 ⌝ ∗
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
      (rx_page V0 p_rx) ∗
      transaction_hpool_global_transferred trans ∗
      ([∗ set] j ∈ set_of_vmids, ∃rx_state', rx_state_run Φ_r V0 j rx_state') ∗
      (big_sepSS set_of_vmids (Φ_t trans)) ∗
      [∗ set] i ∈ set_of_vmids ∖ {[V0]}, VMProp (i:VMID) (vmprop_unknown i Φ_t Φ_r p_tx p_rx) (1/2)%Qp
    )%I.

  Program Definition interp_execute_prim: iPropO Σ :=
    WP ExecI @ V0 {{(λ _, True )}}%I.

End logrel_prim.
