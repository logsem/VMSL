From iris.proofmode Require Import tactics.
From machine_program_logic.program_logic Require Import weakestpre.
From HypVeri.lang Require Import lang.
From HypVeri Require Import big_sepFM machine_extra.
From HypVeri.algebra Require Import base base_extra mem mailbox trans.
From HypVeri.logrel Require Import big_sepSS.
Import uPred.


Section slice_trans.
  Context `{hypconst:HypervisorConstants}.
  Context `{vmG: !gen_VMG Σ}.
  Context (Φ : (gmap Addr transaction) -> VMID -> VMID -> iProp Σ).

  Definition trans_preserve_slice i j (trans trans': (gmap Addr transaction)):=
    filter (λ kv, kv.2.1.1.1.1 = i ∧ kv.2.1.1.1.2 = j) trans
                        = filter (λ kv, kv.2.1.1.1.1 = i ∧ kv.2.1.1.1.2 = j) trans'.

  Class SliceTransWf :=
    {
      slice_trans_valid : ∀ i j trans trans',
        trans_preserve_slice i j trans trans'-> (Φ trans i j ⊣⊢ Φ trans' i j)
    }.


End slice_trans.

Global Arguments SliceTransWf {_} {_} _.
Global Arguments slice_trans_valid {_} {_} _ {_} {_} {_} {_} {_} _.
Global Hint Mode SliceTransWf + + ! : typeclass_instances.

Section slice_rxs.
  Context `{hypconst:HypervisorConstants}.
  Context `{vmG: !gen_VMG Σ}.
  Context (Φ :VMID -> option (Word * VMID)-> VMID -> iProp Σ).

  Class SliceRxsWf :=
    {
      slice_rxs_empty : ∀ i j, Φ i None j ⊣⊢ True;
      slice_rxs_sym : ∀ i os k k',
        (match os with
         | None => True
         | Some (_,j) => j ≠ V0 ->  Φ i os k ⊣⊢ Φ i os k'
         end);
    }.

End slice_rxs.

Global Arguments SliceRxsWf {_} {_} _.
Global Arguments slice_rxs_empty {_} {_} _ {_} _ _.
Global Arguments slice_rxs_sym {_} {_} _ {_} {_} {_} _ _.
Global Hint Mode SliceRxsWf + + ! : typeclass_instances.

(**  unary logical relation **)
Section logrel.
  Context `{hypconst:HypervisorConstants}.
  Context `{hypparams:!HypervisorParameters}.
  Context `{vmG: !gen_VMG Σ}.

  Definition set_of_vmids : gset VMID := (list_to_set list_of_vmids).
  Definition lift_option_gmap`{Countable K} {V: Type} (m: gmap K V) := (λ v, Some v) <$> m.
  Definition pages_in_trans (trans: gmap Word transaction) : gset PID :=
    pages_in_trans' (lift_option_gmap trans).

  Definition trans_ps_disj trans := inv_trans_ps_disj' (lift_option_gmap trans).

  Definition pgt (ps: gset PID) q (vo: VMID) (be: bool) : iProp Σ :=
    [∗ set] p ∈ ps, p -@{q}O> vo ∗ p -@{q}E> be.

  Definition pgt_full ps vo be := pgt ps 1 vo be.
  Definition pgt_3_4 ps vo be : iProp Σ := pgt ps (1/4) vo be ∗ pgt ps (1/2) vo be.
  Definition pgt_1_4 ps vo be : iProp Σ := pgt ps (1/4) vo be.

  (** definitions **)

   (* [transaction_pagetable_entries_transferred] : For donation, the half of transaction entries that are kept by sender in case
      of sharing and lending are also be passed around between the sender and the receiver, as retrieval in this case also requires
      full entries.
      Pagetable entries are transferred along as both sender and receiver could be the exclusive owner of those pages. *)
  Definition transaction_pagetable_entries_transferred i (trans: gmap Addr transaction) : iProp Σ:=
    big_sepFM trans (λ kv, (kv.2.1.1.1.1 = i ∨ kv.2.1.1.1.2 = i) ∧ kv.2.1.2 = Donation) (λ k v, k -{1/4}>t v.1 ∗ pgt_1_4 v.1.1.2 v.1.1.1.1 true)%I.

  (* [retrieval entries]: half of all retrieval entries of i-related transactions are required.
     For transactions where i is the sender, we need the corresponding retrieval entries to check if it is allowed for i to reclaim,
     for the cases when i is the receiver, they are required so that i can retrieve or relinquish *)
  (* There are also some cases when we need the second half, as in those cases we may update/remove the retrival state *)
  (* XXX: How to relate retrieval and transaction entries? Using option(frac_agree transaction,option bool)? or is it unnecessary? *)
  Definition retrievable_transaction_transferred i (trans: gmap Addr transaction) : iProp Σ:=
    (big_sepFM trans (λ kv, kv.2.1.1.1.1 = i ∨ kv.2.1.1.1.2 = i) (λ k v, k -{1/2}>re v.2 )%I) ∗
    (big_sepFM trans (λ kv, (kv.2.1.1.1.1 = i ∨ kv.2.1.1.1.2 = i) ∧ kv.2.2 = false) (λ k v, k -{1/4}>t v.1 ∗ k -{1/2}>re v.2)%I).

  (* [transaction_pagetable_entries_owned]: transaction and page table entries that are owned initially by i,
     i.e. they are not transferred by VMProp, so we doesn't need to take care of them when reasoning the primary VM.
     As the invoker of sharing and lending transactions, i always has the ownership of involved pages.
     Therefore, i ownes these pagetable entries even if they are in some transactions.
     Furthermore, since it is suffice for the receiver to retrieve or relinquish with half of transacitons entries,
     while the sender needs full to reclaim, we let i always own half and only pass the otner half around with VMProp*)
  (* [TODO] relation to [pagetable_entries_excl_owned] *)
  Definition transaction_pagetable_entries_owned i (trans: gmap Addr transaction) : iProp Σ:=
    big_sepFM trans (λ kv, kv.2.1.1.1.1 = i ∧ kv.2.1.2 ≠ Donation) (λ k v, k -{1/4}>t v.1 ∗ pgt_1_4 v.1.1.2 v.1.1.1.1 (bool_decide (v.1.2 ≠ Sharing)))%I.

  Context (i : (leibnizO VMID)).

  (* [TODO] *)
  Definition retrieved_transaction_owned i (trans: gmap Addr transaction) : iProp Σ:=
    (big_sepFM trans (λ kv, kv.2.1.1.1.2 = i ∧ kv.2.2 = true) (λ k v, k -{1/4}>t v.1 ∗ k -{1/2}>re v.2)%I).

  Program Definition interp_execute: iPropO Σ :=
   (⌜i ≠ V0⌝ -∗
        (VMProp_holds i (1/2)%Qp -∗ WP ExecI @ i {{(λ _, True )}}))%I.

  (* [pagetable_entries_excl_owned]: For pages that are exclusively accessible and owned by i, i keeps the entries. *)
  Definition pagetable_entries_excl_owned (i:VMID) (ps: gset PID) := pgt ps 1 i true.

  (* [transaction_hpool_global_transferred]: All of half of transactions, as we don't know which one would be used by i. *)
  (* We need the pure proposition to ensure all transaction entries are transferred.
     Only half is needed so that the invokers can remember transactions by keeping the other half.*)
  Definition transaction_hpool_global_transferred (trans: gmap Addr transaction) : iProp Σ:=
    ∃ hpool,  ⌜hpool ∪ dom trans = valid_handles⌝ ∗ fresh_handles 1 hpool
       ∗ ([∗ map] h ↦ tran ∈ trans, h -{1/2}>t tran.1 ∗ pgt_3_4 tran.1.1.2 tran.1.1.1.1 (bool_decide (tran.1.2 ≠ Sharing))).

  (* [transferred_memory_pages]: some memory points-to predicates are transferred by VMProp.
      NOTE: we exclude the case when the type of transaction is lending and has been retrieved,
      as the associated memory pages in this case is exclusively owned by the receiver*)
  Definition transferred_memory_pages (trans : gmap Word transaction) :=
    pages_in_trans (filter (λ kv, (kv.2.1.1.1.1 = i ∨ kv.2.1.1.1.2 = i) ∧ ¬(kv.2.2 = true ∧ kv.2.1.2 = Lending)) trans).

  (* [retrieved_lending_memory_pages]: the memory of these pages are owned by the receiver *)
  Definition retrieved_lending_memory_pages (trans : gmap Word transaction) :=
    pages_in_trans (filter (λ kv, kv.2.1.1.1.2 = i ∧ (kv.2.2 = true ∧ kv.2.1.2 = Lending)) trans).

  (* [accessible_in_trans_memory_pages] (maybe) accessible memory pages associated with transactions *)
  Definition accessible_in_trans_memory_pages (trans : gmap Word transaction) :=
    pages_in_trans (filter (λ kv, (kv.2.1.1.1.1 = i ∧ ¬(kv.2.2 = true ∧ kv.2.1.2 = Lending)) ∨ kv.2.1.1.1.2 = i) trans).

  (* [currently_accessible_in_trans_memory_pages] currently accessible memory pages associated with transactions *)
  Definition currently_accessible_in_trans_memory_pages (trans : gmap Word transaction) :=
    pages_in_trans (filter (λ kv, (kv.2.1.1.1.1 = i ∧ kv.2.1.2 = Sharing) ∨ (kv.2.1.1.1.2 = i ∧ kv.2.2 = true)) trans).

  Definition trans_rel_wand (P : gmap Word transaction -d> iPropO Σ) (trans trans': gmap Word transaction ): iProp Σ:=
    □(P trans -∗ P trans').

  Definition trans_rel_eq (P : gmap Word transaction -> gset PID) (trans trans': gmap Word transaction ): Prop:=
    P trans = P trans'.

  Definition rx_state_match i os : iProp Σ :=
    match os with
    | None => RX_state@i := None ∗ ∃p_rx, RX@ i := p_rx ∗ (∃ mem_rx, memory_page p_rx mem_rx)
    | Some s => RX_state{1/2}@i := Some(s)
    end.

  Definition rx_states_global (rxs: gmap VMID (option (Word*VMID))) : iProp Σ :=
    [∗ map]i ↦ os ∈ rxs, rx_state_match i os.

  Definition rx_state_get (i:VMID) (rxs: gmap VMID (option (Word*VMID))) :iProp Σ:=
    ∀ rs, ⌜rxs !! i = Some rs⌝ -∗ RX_state@i := rs.

  (* (* [TODO] *) *)
  (* Definition return_reg_rx i (rs : option (Word * VMID)) (rxs :gmap VMID (option(Word*VMID))): iProp Σ:= *)
  (*   ((R0 @@ V0 ->r encode_hvc_func(Yield) ∨ *)
  (*     R0 @@ V0 ->r encode_hvc_func(Wait) ∗ ⌜rs = None⌝) *)
  (*    ∗ rx_states_global (delete i rxs) *)
  (*    ∗ R1 @@ V0 ->r encode_vmid(i) ∗ ∃ r2, R2 @@ V0 ->r r2) ∨ *)
  (*   (R0 @@ V0 ->r encode_hvc_func(Send) *)
  (*     ∗ ∃ l j, RX_state{1/2}@j := Some(l,i) ∗ (∃ p_rx, RX@ j := p_rx ∗ ∃ mem_rx, memory_page p_rx mem_rx) *)
  (*     ∗ rx_states_global (<[j:=Some(l,i)]>(delete i rxs)) ∗ ⌜rxs !! j = Some None⌝ *)
  (*     ∗ (∃r1, R1 @@ V0 ->r r1 ∗ ⌜decode_vmid r1 = Some j⌝) ∗  R2 @@ V0 ->r l). *)

  Definition only (trans: gmap Word transaction) := (filter (λ (kv :Word*transaction), (kv.2.1.1.1.1 = i ∨ kv.2.1.1.1.2 = i)) trans).

  Definition except (trans: gmap Word transaction) := (filter (λ (kv :Word*transaction), ¬(kv.2.1.1.1.1 = i ∨ kv.2.1.1.1.2 = i)) trans).

  (* [trans_rel_secondary] relates [trans], the transactions at the beginning of the proof, and
                [trans'], those at the point of switching to i. These assumptions are (I believe) necessary to prove FTLR.
                Moreover, they are provable because of that fact that i as the invoker is the only vm can manipulate
                the state of some transactions, and since, i is not scheduled during the time between starting pvm
                and switching to i, states of those transactions are immutable. *)
  Definition trans_rel_secondary (i:VMID) (trans trans': gmap Word transaction): Prop :=
    (λ tran, tran.1) <$> filter (λ kv, (kv.2.1.1.1.1 = i ∧ kv.2.1.2 ≠ Donation)) trans' =
    (λ tran, tran.1) <$> filter (λ kv, (kv.2.1.1.1.1 = i ∧ kv.2.1.2 ≠ Donation)) trans
    ∧
    (filter (λ kv, (kv.2.1.1.1.2 = i ∧ kv.2.2 = true)) trans') =
    (filter (λ kv, (kv.2.1.1.1.2 = i ∧ kv.2.2 = true)) trans).
  (* Definition trans_rel_pre (i:VMID) (trans trans': gmap Word transaction): Prop := *)
  (*   dom (filter (λ kv, (kv.2.1.1.1.1 = i ∧ kv.2.1.2 ≠ Donation)) trans') *)
  (*     ⊆ dom (filter (λ kv, (kv.2.1.1.1.1 = i ∧ kv.2.1.2 ≠ Donation)) trans) *)
  (*   ∧ *)
  (*   dom (filter (λ kv, (kv.2.1.1.1.2 = i ∧ kv.2.2 = true)) trans') *)
  (*   ⊆ dom (filter (λ kv, (kv.2.1.1.1.2 = i ∧ kv.2.2 = true)) trans). *)

(* Section vmprop. *)
(*   Context `{HypervisorConstants}. *)
(*   Context `{!HypervisorParameters}. *)
(*   Context `{vmG: !gen_VMG Σ}. *)
  (* Context (i : VMID). *)
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
      ∗ rx_states_global (<[j:=Some(l,i)]>(delete i rxs)) ∗ ⌜rxs !! j = Some None⌝
      ∗ (∃r1, R1 @@ V0 ->r r1 ∗ ⌜decode_vmid r1 = Some j⌝) ∗  R2 @@ V0 ->r l).

  Definition vmprop_zero_pre (Ψ: (gmap Word transaction) -d> iPropO Σ) : (gmap Word transaction) -d> (gmap VMID (option(Word * VMID))) -d> iPropO Σ :=
    λ trans rxs, (∃ (trans' :gmap Word transaction) rs',
                     let trans_ret := (only trans') ∪ (except trans) in
                           ⌜dom (only trans') ## dom (except trans)⌝ ∗
                           ⌜∀ x, x ≠ i -> trans_rel_secondary x trans trans_ret⌝ ∗
                           transaction_hpool_global_transferred (trans_ret) ∗
                           big_sepSS_singleton set_of_vmids i (Φ_t trans_ret) ∗
                           rx_state_match i rs' ∗ Φ_r i rs' V0 ∗
                           return_reg_rx i rs' rxs ∗
                           VMProp i (Ψ trans_ret) (1/2)%Qp)%I.

  Definition vmprop_unknown_pre
    (Ψ :(gmap Word transaction) -d> iPropO Σ) : (gmap Word transaction) -d> iPropO Σ :=
   λ trans, (∃ (trans' : gmap Word transaction) (rxs : gmap VMID (option(Word * VMID))),
               ⌜trans_rel_secondary i trans trans'⌝ ∗
               (* transaction and pagetable entries *)
               transaction_hpool_global_transferred trans' ∗
               big_sepSS_singleton set_of_vmids i (Φ_t trans') ∗
               (∃ r0, R0 @@ V0 ->r r0 ∗ ⌜decode_hvc_func r0 = Some Run⌝) ∗ (∃ r1, R1 @@ V0 ->r r1 ∗ ⌜decode_vmid r1 = Some i⌝)∗ (∃ r2, R2 @@ V0 ->r r2) ∗
               (∀ rs : option (Addr * VMID), ⌜rxs !! i = Some rs⌝ -∗ rx_state_match i rs ∗ Φ_r i rs i) ∗
               (* rx pages for all other VMs *)
               (rx_states_global (delete i rxs)) ∗ ⌜is_total_gmap rxs⌝ ∗
               (* if i yielding, we give following resources back to pvm *)
               VMProp V0 (vmprop_zero_pre Ψ trans' rxs) (1/2)%Qp)%I.

  Local Instance vmprop_unknown_pre_contractive : Contractive (vmprop_unknown_pre).
  Proof.
    rewrite /vmprop_unknown_pre => n vmprop_unknown vmprop_unknown' Hvmprop_unknown trans /=.
    do 13 f_equiv.
    rewrite /VMProp /=.
    do 6 f_equiv.
    f_contractive.
    rewrite /vmprop_zero_pre.
    do 10 f_equiv.
    rewrite /VMProp.
    repeat f_equiv.
  Qed.

  Definition vmprop_unknown:= fixpoint (vmprop_unknown_pre).

  Definition vmprop_zero := vmprop_zero_pre vmprop_unknown.

  Lemma vmprop_unknown_eq trans: vmprop_unknown trans ⊣⊢
    (∃ (trans' : gmap Word transaction) (rxs : gmap VMID (option(Word * VMID))),
               ⌜trans_rel_secondary i trans trans'⌝ ∗
               (* transaction and pagetable entries *)
               transaction_hpool_global_transferred trans' ∗
               big_sepSS_singleton set_of_vmids i (Φ_t trans') ∗
               (∃ r0, R0 @@ V0 ->r r0 ∗ ⌜decode_hvc_func r0 = Some Run⌝) ∗ (∃ r1, R1 @@ V0 ->r r1 ∗ ⌜decode_vmid r1 = Some i⌝)∗ (∃ r2, R2 @@ V0 ->r r2) ∗
               (∀ rs : option (Addr * VMID), ⌜rxs !! i = Some rs⌝ -∗ rx_state_match i rs ∗ Φ_r i rs i) ∗
               (* rx pages for all other VMs *)
               (rx_states_global (delete i rxs)) ∗ ⌜is_total_gmap rxs⌝ ∗
               (* if i yielding, we give following resources back to pvm *)
          VMProp V0 (vmprop_zero trans' rxs) (1/2)%Qp)%I.
  Proof.
    rewrite /vmprop_unknown.
    apply (fixpoint_unfold vmprop_unknown_pre).
  Qed.

  (* Definition vmprop_zero_pre (Ψ: (gmap Word transaction) -d> iPropO Σ) : (gmap Word transaction) -d> (gmap VMID (option(Word*VMID))) -d> iPropO Σ := *)
  (*   λ trans rxs, (∃ trans' rs', *)
  (*                    let trans_ret := (only trans') ∪ (except trans) in *)
  (*                          ⌜dom (only trans') ## dom (except trans)⌝ ∗ *)
  (*                          ⌜∀ x, x ≠ i -> trans_rel_secondary x trans trans_ret⌝ ∗ *)
  (*                          (* transaction and pagetable entries *) *)
  (*                          transaction_hpool_global_transferred trans_ret ∗ *)
  (*                          transaction_pagetable_entries_transferred i trans_ret ∗ *)
  (*                          retrievable_transaction_transferred i trans_ret ∗ *)
  (*                          (* memory *) *)
  (*                          (∃ mem_trans, memory_pages (transferred_memory_pages trans_ret) mem_trans) ∗ *)
  (*                          (RX_state@i:= rs') ∗ (∃p_rx, RX@i := p_rx ∗ (∃ mem_rx, memory_page p_rx mem_rx)) ∗ *)
  (*                          return_reg_rx i rs' rxs ∗ *)
  (*                          VMProp i (Ψ trans_ret) (1/2)%Qp)%I. *)

  (* Definition vmprop_unknown_pre (Φ: (gmap Word transaction) -d> iPropO Σ) : (gmap Word transaction) -d> iPropO Σ := *)
  (*  λ trans, (∃ (trans' : gmap Word transaction) (rxs : gmap VMID (option(Word * VMID))), *)
  (*              ⌜trans_rel_secondary i trans trans'⌝ ∗ *)
  (*              (* transaction and pagetable entries *) *)
  (*              transaction_hpool_global_transferred trans' ∗ *)
  (*              transaction_pagetable_entries_transferred i trans' ∗ *)
  (*              retrievable_transaction_transferred i trans' ∗ *)
  (*              (* memory *) *)
  (*              (∃ mem_trans, memory_pages (transferred_memory_pages trans') mem_trans) ∗ *)
  (*              (∃ r0, R0 @@ V0 ->r r0 ∗ ⌜decode_hvc_func r0 = Some Run⌝) ∗ (∃ r1, R1 @@ V0 ->r r1 ∗ ⌜decode_vmid r1 = Some i⌝)∗ (∃ r2, R2 @@ V0 ->r r2) ∗ *)
  (*              (rx_state_get i rxs ∗ (∃p_rx, RX@i := p_rx ∗ (∃ mem_rx, memory_page p_rx mem_rx))) ∗ *)
  (*              (* rx pages for all other VMs *) *)
  (*              rx_states_global (delete i rxs) ∗ ⌜is_total_gmap rxs⌝ ∗ *)
  (*              (* if i yielding, we give following resources back to pvm *) *)
  (*              VMProp V0 (vmprop_zero_pre Φ trans' rxs) (1/2)%Qp)%I. *)

  (* Local Instance vmprop_unknown_pre_contractive : Contractive (vmprop_unknown_pre). *)
  (* Proof. *)
  (*   rewrite /vmprop_unknown_pre => n vmprop_unknown vmprop_unknown' Hvmprop_unknown trans /=. *)
  (*   do 15 f_equiv. *)
  (*   rewrite /VMProp /=. *)
  (*   do 6 f_equiv. *)
  (*   f_contractive. *)
  (*   rewrite /vmprop_zero_pre. *)
  (*   do 12 f_equiv. *)
  (*   rewrite /VMProp. *)
  (*   repeat f_equiv. *)
  (*   (* apply Hvmprop_unknown. *) *)
  (* Qed. *)

  (* Definition vmprop_unknown := fixpoint (vmprop_unknown_pre). *)

  (* Definition vmprop_zero := vmprop_zero_pre vmprop_unknown. *)

  (* Lemma vmprop_unknown_eq trans : vmprop_unknown trans ⊣⊢ *)
  (*   (∃ (trans' : gmap Word transaction) (rxs : gmap VMID (option(Word * VMID))), *)
  (*              ⌜trans_rel_secondary i trans trans'⌝ ∗ *)
  (*              (* transaction and pagetable entries *) *)
  (*              transaction_hpool_global_transferred trans' ∗ *)
  (*              transaction_pagetable_entries_transferred i trans' ∗ *)
  (*              retrievable_transaction_transferred i trans' ∗ *)
  (*              (* memory *) *)
  (*              (∃ mem_trans, memory_pages (transferred_memory_pages trans') mem_trans) ∗ *)
  (*              (∃ r0, R0 @@ V0 ->r r0 ∗ ⌜decode_hvc_func r0 = Some Run⌝) ∗ (∃ r1, R1 @@ V0 ->r r1 ∗ ⌜decode_vmid r1 = Some i⌝)∗ (∃ r2, R2 @@ V0 ->r r2) ∗ *)
  (*              (rx_state_get i rxs ∗ (∃p_rx, RX@i := p_rx ∗ (∃ mem_rx, memory_page p_rx mem_rx))) ∗ *)
  (*              (* rx pages for all other VMs *) *)
  (*              rx_states_global (delete i rxs) ∗ ⌜is_total_gmap rxs⌝ ∗ *)
  (*              (* if i yielding, we give following resources back to pvm *) *)
  (*              VMProp V0 (vmprop_zero trans' rxs) (1/2)%Qp)%I. *)
  (*   Proof. *)
  (*     rewrite /vmprop_unknown. *)
  (*     apply (fixpoint_unfold vmprop_unknown_pre). *)
  (*   Qed. *)

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
    (RX_state{1/2}@j := os) ∗ ∃ p_rx, RX@ j := p_rx ∗ (∃ mem_rx, memory_page p_rx mem_rx).

  Definition interp_access p_tx p_rx ps_acc trans: iPropO Σ:=
    (
      (* exclusively owned pages are pages i has access to, but ain't in any transactions related to i. *)
      (* [ps_oea], we exclude all pages involved in in-flight transactions,
       NOTE: it has to be (currently_accessible_in_trans_memory_pages)*)
      let ps_oea := ps_acc ∖ {[p_rx;p_tx]} ∖ (currently_accessible_in_trans_memory_pages trans) in
      ⌜∀ k j trans, (k = i ∨ j = i) -> Φ_t trans k j ⊣⊢ slice_transfer_all trans k j⌝ ∗
      ⌜∀ os, (match os with
                 | None => True
                 | _ => Φ_r i os i ⊣⊢ slice_rx_state i os
                end)⌝ ∗
      ⌜∀ os, (match os with
                 | None => True
                 | _ => Φ_r i os V0 ⊣⊢ slice_rx_state i os
                end)⌝ ∗
      ⌜∀ k os, (match os with
          | None => True
          | Some (_, j) => j = i -> Φ_r k os V0 ⊣⊢ slice_rx_state k os
          end)⌝ ∗
      ⌜∀ i j, Φ_r i None j ⊣⊢ True⌝ ∗
      (* registers *)
      (∃ regs, ⌜is_total_gmap regs⌝ ∗ [∗ map] r ↦ w ∈ regs, r @@ i ->r w) ∗
      (* TX page and its memory *)
      (tx_page i p_tx ∗ ∃ mem_tx, memory_page p_tx mem_tx) ∗
      rx_page i p_rx ∗
      (* access *)
      i -@A> ps_acc ∗
      ⌜{[p_tx;p_rx]} ⊆ ps_acc⌝ ∗ ⌜currently_accessible_in_trans_memory_pages trans ⊆ ps_acc ∖ {[p_tx;p_rx]}⌝ ∗
      pagetable_entries_excl_owned i ps_oea ∗
      transaction_pagetable_entries_owned i trans ∗
      retrieved_transaction_owned i trans ∗
      (∃ mem_oea, memory_pages (ps_oea ∪ (retrieved_lending_memory_pages trans)) mem_oea) ∗
      VMProp i (vmprop_unknown trans) (1/2)%Qp
    )%I.

End logrel.
