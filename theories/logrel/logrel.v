From iris.proofmode Require Import tactics.
From machine_program_logic.program_logic Require Import weakestpre.
From HypVeri.lang Require Import lang.
From HypVeri Require Import machine_extra.
From HypVeri.algebra Require Import base base_extra mem mailbox trans.
Import uPred.

(**  unary logical relation **)
Section logrel.
  Context `{hypconst:HypervisorConstants}.
  Context `{hypparams:!HypervisorParameters}.
  Context `{vmG: !gen_VMG Σ}.

  Definition pages_in_trans (trans: gmap Word transaction) : gset PID :=
    map_fold (λ (k:Addr) v acc, v.1.1.2 ∪ acc) (∅: gset PID) trans.

  Definition trans_ps_disj trans := map_Forall (λ h tran, tran.1.1.2 ## pages_in_trans (delete h trans)) trans.

  Definition pgt (ps: gset PID) q (vo: VMID) (be: bool) : iProp Σ :=
    ([∗ set] p ∈ ps, p -@{q}O> vo) ∗ [∗ set] p ∈ ps, p -@{q}E> be.

  (** definitions **)

  Context (i : (leibnizO VMID)).

  Program Definition interp_execute: iPropO Σ :=
   (⌜i ≠ V0⌝ -∗
        (VMProp_holds i (1/2)%Qp -∗ WP ExecI @ i {{(λ _, True )}}))%I.

  (* [pagetable_entries_excl_owned]: For pages that are exclusively accessible and owned by i, i keeps the entries. *)
  Definition pagetable_entries_excl_owned (i:VMID) (ps: gset PID) := pgt ps 1 i true.

  (* [transaction_hpool_global_transferred]: All of half of transactions, as we don't know which one would be used by i. *)
  (* We need the pure proposition to ensure all transaction entries are transferred.
     Only half is needed so that the invokers can remember transactions by keeping the other half.*)
  Definition transaction_hpool_global_transferred (trans: gmap Addr transaction) : iProp Σ:=
    ∃ hpool,  ⌜hpool ∪ dom (gset _ ) trans = hs_all⌝ ∗ fresh_handles 1 hpool ∗ ⌜trans_ps_disj trans⌝ ∗ [∗ map] h ↦ tran ∈ trans, h -{1/2}>t tran.1.

  (* [transaction_pagetable_entries_owned]: transaction and page table entries that are owned initially by i,
     i.e. they are not transferred by VMProp, so we doesn't need to take care of them when reasoning the primary VM.
     As the invoker of sharing and lending transactions, i always has the ownership of involved pages.
     Therefore, i ownes these pagetable entries even if they are in some transactions.
     Furthermore, since it is suffice for the receiver to retrieve or relinquish with half of transacitons entries,
     while the sender needs full to reclaim, we let i always own half and only pass the otner half around with VMProp*)
  (* [TODO] relation to [pagetable_entries_excl_owned] *)
  Definition transaction_pagetable_entries_owned (trans: gmap Addr transaction) : iProp Σ:=
    big_sepFM trans (λ kv, kv.2.1.1.1.1 = i ∧ kv.2.1.2 ≠ Donation) (λ k v, k -{1/2}>t v.1 ∗ pgt v.1.1.2 1 v.1.1.1.1 (bool_decide (v.1.2 ≠ Sharing)))%I.

   (* [transaction_pagetable_entries_transferred] : For donation, the half of transaction entries that are kept by sender in case
      of sharing and lending are also be passed around between the sender and the receiver, as retrieval in this case also requires
      full entries.
      Pagetable entries are transferred along as both sender and receiver could be the exclusive owner of those pages. *)
  Definition transaction_pagetable_entries_transferred (trans: gmap Addr transaction) : iProp Σ:=
    big_sepFM trans (λ kv, kv.2.1.2 = Donation ∧ (kv.2.1.1.1.2 = i ∨ kv.2.1.1.1.1 = i)) (λ k v, k -{1/2}>t v.1 ∗ pgt v.1.1.2 1 v.1.1.1.1 true)%I.

  (* [retrieval entries]: half of all retrieval entries of i-related transactions are required.
     For transactions where i is the sender, we need the corresponding retrieval entries to check if it is allowed for i to reclaim,
     for the cases when i is the receiver, they are required so that i can retrieve or relinquish *)
  (* There are also some cases when we need the second half, as in those cases we may update/remove the retrival state *)
  (* XXX: How to relate retrieval and transaction entries? Using option(frac_agree transaction,option bool)? or is it unnecessary? *)
  Definition retrieval_entries_transferred(trans: gmap Addr transaction) : iProp Σ:=
    (big_sepFM trans (λ kv, kv.2.1.1.1.2 = i ∨ kv.2.1.1.1.1 = i) (λ k v, k -{1/2}>re v.2 )%I) ∗
    (big_sepFM trans (λ kv, (kv.2.1.1.1.1 = i ∨ kv.2.1.1.1.2 = i) ∧ kv.2.2 = false) (λ k v, k -{1/2}>re v.2)%I).

  (* [TODO] *)
  Definition retrieval_entries_owned(trans: gmap Addr transaction) : iProp Σ:=
    (big_sepFM trans (λ kv, kv.2.1.1.1.2 = i ∧ kv.2.2 = true) (λ k v, k -{1/2}>re v.2)%I).

  (* [memory_transferred]: some memory points-to predicates are transferred by VMProp.
     the memory is the memory of pages associated with a transaction and i has or may have access to. *)
  Definition trans_memory_in_trans (trans : gmap Word transaction) :=
    filter (λ kv, (kv.2.1.1.1.1 = i ∧ ¬(kv.2.2 = true ∧ kv.2.1.2 = Lending)) ∨ kv.2.1.1.1.2 = i) trans.
  Definition memory_transferred (trans : gmap Word transaction) (mem: mem) :=
   memory_pages (pages_in_trans (trans_memory_in_trans trans)) mem.

  (* [TODO] *)
  Definition rx_pages (s: gset VMID) : iProp Σ :=
    [∗ set] j ∈ s, ∃ p_rx, RX@ j := p_rx ∗ ∃ rx_state, RX_state{1/2}@j := rx_state ∗
                  (⌜rx_state = None⌝ -∗ RX_state{1/2}@j := rx_state ∗ ∃ mem_rx, memory_page p_rx mem_rx).

  (* [TODO] *)
  Definition return_reg_rx i : iProp Σ:=
    ((R0 @@ V0 ->r encode_hvc_func(Yield) ∗ (∃ rx_state'', RX_state@ i := rx_state'')  ∨
      R0 @@ V0 ->r encode_hvc_func(Wait) ∗ RX_state@ i :=None) ∗ R1 @@ V0 ->r encode_vmid(i) ∗ ∃ r2, R2 @@ V0 ->r r2) ∨
    (R0 @@ V0 ->r encode_hvc_func(Send) ∗ (∃ rx_state'', RX_state@ i := rx_state'') ∗ ∃ j p_rx l, ⌜j ≠ i⌝ ∗ RX@ j := p_rx ∗ RX_state{1/2}@j := Some(l,i)
                          ∗ (∃r1, R1 @@ V0 ->r r1 ∗ ⌜decode_vmid r1 = Some j⌝) ∗  R2 @@ V0 ->r l ∗ ∃ mem_rx, memory_page p_rx mem_rx).

  Definition vmprop_zero p_rx : iProp Σ :=
    ((∃ ps_na'' ps_acc'' trans'' ,
                           let ps_macc_trans'' := pages_in_trans (trans_memory_in_trans trans'') in
                           (* lower bound *)
                           i -@{1/2}A> ps_acc'' ∗
                           LB@ i := [ps_na''] ∗
                           ⌜ps_na'' ## ps_acc'' ∪ ps_macc_trans''⌝ ∗
                           (* transaction and pagetable entries *)
                           transaction_hpool_global_transferred trans'' ∗
                           transaction_pagetable_entries_transferred trans'' ∗
                           retrieval_entries_transferred trans'' ∗
                           (* memory *)
                           (∃ mem_trans, memory_pages ps_macc_trans'' mem_trans) ∗
                           (* status of RX *)
                           (* RX *)
                           rx_page i p_rx ∗ (∃ mem_rx, memory_page p_rx mem_rx) ∗
                           rx_pages ((list_to_set (list_of_vmids)) ∖ {[i]}) ∗
                           return_reg_rx i)
                           (* no scheduling, we finish the proof *)
                           ∨ False).

  Definition vmprop_unknown p_tx p_rx trans : iProp Σ:=
    ∃ ps_na' ps_acc' (trans' : gmap Word transaction) rx_state,
               let ps_oea := ps_acc' ∖ {[p_rx;p_tx]} ∖ (pages_in_trans trans)  in
               let ps_macc_trans' := (pages_in_trans (trans_memory_in_trans trans')) in
               let ps_oea' := ps_acc' ∖ {[p_rx;p_tx]} ∖ pages_in_trans trans' in
               (* lower bound *)
               i -@{1/2}A> ps_acc' ∗
               LB@ i := [ps_na'] ∗
               (* NOTE: Just having [ps_acc'] seems not enough, which can be broken by getting access to pages in ps_na from some
                transaction. *)
               (* XXX: how to formulate this disjointness using RAs? making use of ownership and exclusiveness? *)
               ⌜ps_na' ## ps_acc' ∪ ps_macc_trans'⌝ ∗
               (* we can derive ⌜{[p_rx;p_tx]} ## ps_mem_in_trans''⌝ from rx_page/tx_page ∗ transaction_hpool_global_transferred *)
               (* transaction and pagetable entries *)
               transaction_hpool_global_transferred trans' ∗
               transaction_pagetable_entries_transferred trans' ∗
               retrieval_entries_transferred trans' ∗
               (* memory *)
               (∃ mem_trans, memory_transferred trans' mem_trans) ∗
               R0 @@ V0 ->r encode_hvc_func(Run) ∗ R1 @@ V0 ->r encode_vmid(i) ∗ (∃ r2, R2 @@ V0 ->r r2) ∗
               (* status of RX *)
               RX_state@ i := rx_state ∗
               (* RX *)
               (rx_page i p_rx) ∗
               (∃ mem_rx, memory_page p_rx mem_rx) ∗
               (* rx pages for all other VMs *)
               rx_pages (list_to_set (list_of_vmids) ∖ {[i]}) ∗
               (* other RXs *)
               (* Implications: these implications relate [trans], the transactions at the beginning of the proof, and
                [trans'], those at the point of switching to i. These assumptions are (I believe) necessary to prove FTLR.
                Moreover, they are provable because of that fact that i as the invoker is the only vm can manipulate
                the state of some transactions, and since, i is not scheduled during the time between starting pvm
                and switching to i, states of those transactions are immutable.
                There are other ways of expressing the relation, we choosed this as (I assume) it should be easier to prove it
                in a concrete example(as we give a concrete [trans] at the first and can reason about what should be the
                [trans'] that satisfies the relation as we know the behaviors of VMs) than in a general case. So we leave
                the proofs to the users of LR. *)
               (transaction_pagetable_entries_owned trans -∗ transaction_pagetable_entries_owned trans') ∗
               (pagetable_entries_excl_owned i ps_oea -∗ pagetable_entries_excl_owned i ps_oea') ∗
               (retrieval_entries_owned trans -∗ retrieval_entries_owned trans') ∗
               ((∃ mem_oea, memory_pages ps_oea mem_oea) ∗ (∃ mem_trans, memory_transferred trans' mem_trans) -∗
                ∃ mem_all, memory_pages (ps_acc' ∖ {[p_rx;p_tx]} ∪ ps_macc_trans') mem_all) ∗
               (* if i yielding, we give following resources back to pvm *)
               VMProp V0 (vmprop_zero p_rx) (1/2)%Qp.

  Program Definition interp_access p_tx p_rx ps_acc trans : iPropO Σ:=
    (
      (* let ps_mem_in_trans := pages_in_trans (trans_memory_in_trans trans) in *)
      (* exclusively owned pages are pages i has access to, but ain't in any transactions related to i. *)
      let ps_oea := ps_acc ∖ {[p_rx;p_tx]} ∖ (pages_in_trans trans) in
      (* registers *)
      (∃ regs, ⌜is_total_gmap regs⌝ ∗ [∗ map] r ↦ w ∈ regs, r @@ i ->r w) ∗
      (* TX page and its memory *)
      (tx_page i p_tx ∗ ∃ mem_tx, memory_page p_tx mem_tx) ∗
      (* access *)
      i -@{1/2}A> ps_acc ∗
      ⌜{[p_tx;p_rx]} ⊆ ps_acc⌝ ∗
      pagetable_entries_excl_owned i ps_oea ∗
      transaction_pagetable_entries_owned trans ∗
      retrieval_entries_owned trans ∗
      (∃ mem_oea, memory_pages ps_oea mem_oea) ∗
      VMProp i (vmprop_unknown p_tx p_rx trans) (1/2)%Qp
    )%I.

  (* Things we haven't really considerred:
   - [] the zero flag (it seems unnecessary,
                       unless we want to reason about examples in which zeroing memory is important.
                       I assume such examples would be about confidentiality? )
   - [x] message passing (seems we need RXs of all VMs?
                           - Yes, now the question is, do we need to provide full rx_state and memory_page if the rx is full)
   - [?] if we need more pure propositions to relate trans'' and other stuff
   *)

End logrel.
