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

  Definition lift_option_gmap`{Countable K} {V: Type} (m: gmap K V) := (λ v, Some v) <$> m.
  Definition pages_in_trans (trans: gmap Word transaction) : gset PID :=
    pages_in_trans' (lift_option_gmap trans).

  Definition trans_ps_disj trans := inv_trans_ps_disj' (lift_option_gmap trans).

  Definition pgt (ps: gset PID) q (vo: VMID) (be: bool) : iProp Σ :=
    ([∗ set] p ∈ ps, p -@{q}O> vo) ∗ [∗ set] p ∈ ps, p -@{q}E> be.

  (** definitions **)

   (* [transaction_pagetable_entries_transferred] : For donation, the half of transaction entries that are kept by sender in case
      of sharing and lending are also be passed around between the sender and the receiver, as retrieval in this case also requires
      full entries.
      Pagetable entries are transferred along as both sender and receiver could be the exclusive owner of those pages. *)
  Definition transaction_pagetable_entries_transferred i (trans: gmap Addr transaction) : iProp Σ:=
    big_sepFM trans (λ kv, kv.2.1.2 = Donation ∧ (kv.2.1.1.1.2 = i ∨ kv.2.1.1.1.1 = i)) (λ k v, k -{1/4}>t v.1 ∗ pgt v.1.1.2 1 v.1.1.1.1 true)%I.

  (* [retrieval entries]: half of all retrieval entries of i-related transactions are required.
     For transactions where i is the sender, we need the corresponding retrieval entries to check if it is allowed for i to reclaim,
     for the cases when i is the receiver, they are required so that i can retrieve or relinquish *)
  (* There are also some cases when we need the second half, as in those cases we may update/remove the retrival state *)
  (* XXX: How to relate retrieval and transaction entries? Using option(frac_agree transaction,option bool)? or is it unnecessary? *)
  Definition retrievable_transaction_transferred i (trans: gmap Addr transaction) : iProp Σ:=
    (big_sepFM trans (λ kv, kv.2.1.1.1.2 = i ∨ kv.2.1.1.1.1 = i) (λ k v, k -{1/2}>re v.2 )%I) ∗
    (big_sepFM trans (λ kv, (kv.2.1.1.1.1 = i ∨ kv.2.1.1.1.2 = i) ∧ kv.2.2 = false) (λ k v, k -{1/4}>t v.1 ∗ k -{1/2}>re v.2)%I).

  (* [transaction_pagetable_entries_owned]: transaction and page table entries that are owned initially by i,
     i.e. they are not transferred by VMProp, so we doesn't need to take care of them when reasoning the primary VM.
     As the invoker of sharing and lending transactions, i always has the ownership of involved pages.
     Therefore, i ownes these pagetable entries even if they are in some transactions.
     Furthermore, since it is suffice for the receiver to retrieve or relinquish with half of transacitons entries,
     while the sender needs full to reclaim, we let i always own half and only pass the otner half around with VMProp*)
  (* [TODO] relation to [pagetable_entries_excl_owned] *)
  Definition transaction_pagetable_entries_owned i (trans: gmap Addr transaction) : iProp Σ:=
    big_sepFM trans (λ kv, kv.2.1.1.1.1 = i ∧ kv.2.1.2 ≠ Donation) (λ k v, k -{1/4}>t v.1 ∗ pgt v.1.1.2 1 v.1.1.1.1 (bool_decide (v.1.2 ≠ Sharing)))%I.

  Context (i : (leibnizO VMID)).

  (* [TODO] *)
  Definition retrieved_transaction_owned i (trans: gmap Addr transaction) : iProp Σ:=
    (big_sepFM trans (λ kv, kv.2.1.1.1.2 = i ∧ kv.2.2 = true) (λ k v, k -{1/4}>t v.1 ∗ k -{1/2}>re v.2)%I).

  (* Definition transaction_pagetable_entries_transferred_except (i: VMID) (trans: gmap Addr transaction) : iProp Σ:= *)
  (*   big_sepFM trans (λ kv, kv.2.1.2 = Donation ∧ ¬(kv.2.1.1.1.2 = i ∨ kv.2.1.1.1.1 = i)) (λ k v, k -{1/2}>t v.1 ∗ pgt v.1.1.2 1 v.1.1.1.1 true)%I. *)

  (* Definition retrieval_entries_transferred_except (i: VMID) (trans: gmap Addr transaction) : iProp Σ:= *)
  (*   (big_sepFM trans (λ kv, ¬(kv.2.1.1.1.2 = i ∨ kv.2.1.1.1.1 = i)) (λ k v, k -{1/2}>re v.2 )%I) ∗ *)
  (*   (big_sepFM trans (λ kv, ¬(kv.2.1.1.1.2 = i ∨ kv.2.1.1.1.1 = i) ∧ kv.2.2 = false) (λ k v, k -{1/2}>re v.2)%I). *)

  Program Definition interp_execute: iPropO Σ :=
   (⌜i ≠ V0⌝ -∗
        (VMProp_holds i (1/2)%Qp -∗ WP ExecI @ i {{(λ _, True )}}))%I.

  (* [pagetable_entries_excl_owned]: For pages that are exclusively accessible and owned by i, i keeps the entries. *)
  Definition pagetable_entries_excl_owned (i:VMID) (ps: gset PID) := pgt ps 1 i true.

  (* [transaction_hpool_global_transferred]: All of half of transactions, as we don't know which one would be used by i. *)
  (* We need the pure proposition to ensure all transaction entries are transferred.
     Only half is needed so that the invokers can remember transactions by keeping the other half.*)
  Definition transaction_hpool_global_transferred (trans: gmap Addr transaction) : iProp Σ:=
    ∃ hpool,  ⌜hpool ∪ dom (gset _ ) trans = valid_handles⌝ ∗ fresh_handles 1 hpool ∗ ⌜trans_ps_disj trans⌝ ∗ [∗ map] h ↦ tran ∈ trans, h -{1/2}>t tran.1.

  (* [transferred_memory_pages]: some memory points-to predicates are transferred by VMProp.
      NOTE: we exclude the case when the type of transaction is lending and has been retrieved,
      as the associated memory pages in this case is exclusively owned by the receiver*)
  Definition transferred_memory_pages (trans : gmap Word transaction) :=
    pages_in_trans (filter (λ kv, (kv.2.1.1.1.1 = i  ∨ kv.2.1.1.1.2 = i) ∧ ¬(kv.2.2 = true ∧ kv.2.1.2 = Lending)) trans).

  (* [retrieved_lending_memory_pages]: the memory of these pages are owned by the receiver *)
  Definition retrieved_lending_memory_pages (trans : gmap Word transaction) :=
    pages_in_trans (filter (λ kv, kv.2.1.1.1.2 = i ∧ (kv.2.2 = true ∧ kv.2.1.2 = Lending)) trans).

  (* [accessible_in_trans_memory_pages] (maybe) accessible memory pages associated with transactions *)
  Definition accessible_in_trans_memory_pages (trans : gmap Word transaction) :=
    pages_in_trans (filter (λ kv, (kv.2.1.1.1.1 = i  ∧ ¬(kv.2.2 = true ∧ kv.2.1.2 = Lending)) ∨ kv.2.1.1.1.2 = i) trans).

  (* [currently_accessible_in_trans_memory_pages] currently accessible memory pages associated with transactions *)
  Definition currently_accessible_in_trans_memory_pages (trans : gmap Word transaction) :=
    pages_in_trans (filter (λ kv, (kv.2.1.1.1.1 = i  ∧ kv.2.1.2 = Sharing) ∨ (kv.2.1.1.1.2 = i ∧ kv.2.2 = true)) trans).

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

  Definition trans_rel_wand (P : gmap Word transaction -d> iPropO Σ) (trans trans': gmap Word transaction ): iProp Σ:=
    □(P trans -∗ P trans').

  Definition trans_rel_eq (P : gmap Word transaction -> gset PID) (trans trans': gmap Word transaction ): Prop:=
    P trans = P trans'.

  Definition vmprop_zero_pre (Ψ: PID -d> PID -d> iPropO Σ) :PID -d> PID -d> iPropO Σ :=
    λ p_tx p_rx, (∃ trans'',
                           let ps_macc_trans'' := (transferred_memory_pages trans'') in
                           (* lower bound *)
                           (* i -@{1/2}A> ps_acc'' ∗ *)
                           (* LB@ i := [ps_na''] ∗ *)
                           (* ⌜ps_na'' ## ps_acc'' ∪ ps_macc_trans''⌝ ∗ *)
                           (* transaction and pagetable entries *)
                           transaction_hpool_global_transferred trans'' ∗
                           transaction_pagetable_entries_transferred i trans'' ∗
                           retrievable_transaction_transferred i trans'' ∗
                           (* memory *)
                           (∃ mem_trans, memory_pages ps_macc_trans'' mem_trans) ∗
                           (* status of RX *)
                           (* RX *)
                           rx_page i p_rx ∗ (∃ mem_rx, memory_page p_rx mem_rx) ∗
                           rx_pages ((list_to_set (list_of_vmids)) ∖ {[i]}) ∗
                           return_reg_rx i ∗
                           (* XXX: implications, to be proved later.. or not?? *)
                           (* (trans' -{{(transaction_pagetable_entries_transferred_except i)}}∗ trans'') ∗ *)
                           (* (trans' -{{(retrieval_entries_transferred_except i)}}∗ trans'') ∗ *)
                           (* (trans' -{{(transaction_pagetable_entries_owned V0)}}∗ trans'') ∗ *)
                           VMProp i (Ψ p_tx p_rx) (1/2)%Qp)%I.

  Definition vmprop_unknown_pre
    (Φ: PID -d> PID -d> iPropO Σ)
    :PID -d> PID -d> iPropO Σ :=
    λ p_tx p_rx,
    (∃ (trans' : gmap Word transaction) rx_state,
               let ps_macc_trans' := (transferred_memory_pages trans') in
               (* [ps_oea], we exclude all pages involved in in-flight transactions,
                NOTE: it has to be (accessible_in_trans_memory_pages), ps_macc_trans doesn't make sense(even if we can complete the FTLR proof)*)
               (* let ps_oea' := ps_acc' ∖ {[p_rx;p_tx]} ∖ (currently_accessible_in_trans_memory_pages trans') in *)
               (* lower bound *)
               (* i -@{1/2}A> ps_acc' ∗ *)
               (* LB@ i := [ps_na'] ∗ *)
               (* NOTE: Just having [ps_acc'] seems not enough, which can be broken by getting access to pages in ps_na from some
                transaction. *)
               (* XXX: how to formulate this disjointness using RAs? making use of ownership and exclusiveness? *)
               (* ⌜ps_na' ## ps_acc' ∪ (accessible_in_trans_memory_pages trans')⌝ ∗ *)
               (* we can derive ⌜{[p_rx;p_tx]} ## ps_mem_in_trans''⌝ from rx_page/tx_page ∗ transaction_hpool_global_transferred *)
               (* transaction and pagetable entries *)
               transaction_hpool_global_transferred trans' ∗
               transaction_pagetable_entries_transferred i trans' ∗
               retrievable_transaction_transferred i trans' ∗
               (* memory *)
               (∃ mem_trans, memory_pages ps_macc_trans' mem_trans) ∗
               R0 @@ V0 ->r encode_hvc_func(Run) ∗ R1 @@ V0 ->r encode_vmid(i) ∗ (∃ r2, R2 @@ V0 ->r r2) ∗
               (* status of RX *)
               RX_state@ i := rx_state ∗
               (* RX *)
               (rx_page i p_rx) ∗
               (∃ mem_rx, memory_page p_rx mem_rx) ∗
               (* rx pages for all other VMs *)
               rx_pages (list_to_set (list_of_vmids) ∖ {[i]}) ∗
               (* Implications: these implications relate [trans], the transactions at the beginning of the proof, and
                [trans'], those at the point of switching to i. These assumptions are (I believe) necessary to prove FTLR.
                Moreover, they are provable because of that fact that i as the invoker is the only vm can manipulate
                the state of some transactions, and since, i is not scheduled during the time between starting pvm
                and switching to i, states of those transactions are immutable.
                There are other ways of expressing the relation, we choosed this as (I assume) it should be easier to prove it
                in a concrete example(as we give a concrete [trans] at the first and can reason about what should be the
                [trans'] that satisfies the relation as we know the behaviors of VMs) than in a general case. So we leave
                the proofs to the users of LR. *)
               (* ((∃ mem_oea, memory_pages ps_oea mem_oea) ∗ (∃ mem_trans, memory_transferred trans' mem_trans) -∗ *)
               (*  ∃ mem_all, memory_pages (ps_acc' ∖ {[p_rx;p_tx]} ∪ ps_macc_trans') mem_all) ∗ *)
               (* (pagetable_entries_excl_owned i ps_oea -∗ pagetable_entries_excl_owned i ps_oea') ∗ *)
               (* TODO derive below with trans_rel *)
               (* ⌜ps_oea = ps_oea'⌝ ∗ ⌜retrieved_lending_memory_pages trans = retrieved_lending_memory_pages trans' ⌝ ∗ *)
               (* (trans -{{transaction_pagetable_entries_owned i}}∗ trans') ∗ *)
               (* (trans -{{retrieval_entries_owned i}}∗ trans') ∗ *)
               (* if i yielding, we give following resources back to pvm *)
               VMProp V0 (vmprop_zero_pre Φ p_tx p_rx) (1/2)%Qp)%I.

  Local Instance vmprop_unknown_pre_contractive : Contractive (vmprop_unknown_pre).
  Proof.
    rewrite /vmprop_unknown_pre => n vmprop_unknown vmprop_unknown' Hvmprop_unknown p_tx p_rx /=.
    do 15 f_equiv.
    rewrite /VMProp  /=.
    do 6 f_equiv.
    f_contractive.
    rewrite /vmprop_zero_pre.
    do 10 f_equiv.
    rewrite /VMProp.
    repeat f_equiv.
  Qed.

  Definition vmprop_unknown:= fixpoint (vmprop_unknown_pre).

  Definition vmprop_zero := vmprop_zero_pre vmprop_unknown.

  Lemma vmprop_unknown_def : vmprop_unknown ≡
    λ p_tx p_rx,
      (∃ (trans' : gmap Word transaction) rx_state,
          let ps_macc_trans' := (transferred_memory_pages trans') in
          (* let ps_oea' := ps_acc' ∖ {[p_rx;p_tx]} ∖ (accessible_in_trans_memory_pages trans') in *)
          (* i -@{1/2}A> ps_acc' ∗ *)
          (* LB@ i := [ps_na'] ∗ *)
          (* ⌜ps_na' ## ps_acc' ∪ (accessible_in_trans_memory_pages trans')⌝ ∗ *)
          transaction_hpool_global_transferred trans' ∗
          transaction_pagetable_entries_transferred i trans' ∗
          retrievable_transaction_transferred i trans' ∗
          (∃ mem_trans, memory_pages ps_macc_trans' mem_trans) ∗
          R0 @@ V0 ->r encode_hvc_func(Run) ∗ R1 @@ V0 ->r encode_vmid(i) ∗ (∃ r2, R2 @@ V0 ->r r2) ∗
          RX_state@ i := rx_state ∗
          (rx_page i p_rx) ∗
          (∃ mem_rx, memory_page p_rx mem_rx) ∗
          rx_pages (list_to_set (list_of_vmids) ∖ {[i]}) ∗
          (* ⌜ps_oea = ps_oea'⌝ ∗ ⌜retrieved_lending_memory_pages trans = retrieved_lending_memory_pages trans' ⌝ ∗ *)
          (* (trans -{{transaction_pagetable_entries_owned i}}∗ trans') ∗ *)
          (* (trans -{{retrieval_entries_owned i}}∗ trans') ∗ *)
          VMProp V0 (vmprop_zero p_tx p_rx) (1/2)%Qp)%I.
  Proof.
    rewrite /vmprop_unknown //.
    rewrite (fixpoint_unfold vmprop_unknown_pre).
    setoid_reflexivity.
  Qed.

  Global Instance vmprop_unknown_proper: Proper ((=) ==> (=) ==> (⊣⊢)) vmprop_unknown.
  Proof. apply _. Qed.

  Lemma vmprop_unknown_eq (p_tx p_rx:PID) : vmprop_unknown p_tx p_rx ⊣⊢
      (∃ (trans' : gmap Word transaction) rx_state,
               let ps_macc_trans' := (transferred_memory_pages trans') in
               (* let ps_oea' := ps_acc' ∖ {[p_rx;p_tx]} ∖ (accessible_in_trans_memory_pages trans') in *)
               (* i -@{1/2}A> ps_acc' ∗ *)
               (* LB@ i := [ps_na'] ∗ *)
               (* ⌜ps_na' ## ps_acc' ∪ (accessible_in_trans_memory_pages trans')⌝ ∗ *)
               transaction_hpool_global_transferred trans' ∗
               transaction_pagetable_entries_transferred i trans' ∗
               retrievable_transaction_transferred i trans' ∗
               (∃ mem_trans, memory_pages ps_macc_trans' mem_trans) ∗
               R0 @@ V0 ->r encode_hvc_func(Run) ∗ R1 @@ V0 ->r encode_vmid(i) ∗ (∃ r2, R2 @@ V0 ->r r2) ∗
               RX_state@ i := rx_state ∗
               (rx_page i p_rx) ∗
               (∃ mem_rx, memory_page p_rx mem_rx) ∗
               rx_pages (list_to_set (list_of_vmids) ∖ {[i]}) ∗
               (* ⌜ps_oea = ps_oea'⌝ ∗ ⌜retrieved_lending_memory_pages trans = retrieved_lending_memory_pages trans' ⌝ ∗ *)
               (* (trans -{{transaction_pagetable_entries_owned i}}∗ trans') ∗ *)
               (* (trans -{{retrieval_entries_owned i}}∗ trans') ∗ *)
               VMProp V0 (vmprop_zero p_tx p_rx) (1/2)%Qp)%I.
    Proof.
      rewrite /vmprop_unknown.
      (* be patient, this line takes 30+ sec.. *)
      apply (fixpoint_unfold vmprop_unknown_pre).
    Qed.

  Program Definition interp_access p_tx p_rx ps_acc trans : iPropO Σ:=
    (
      (* exclusively owned pages are pages i has access to, but ain't in any transactions related to i. *)
      let ps_macc_trans := (transferred_memory_pages trans) in
      let ps_oea := ps_acc ∖ {[p_rx;p_tx]} ∖ (currently_accessible_in_trans_memory_pages trans) in
      (* registers *)
      (∃ regs, ⌜is_total_gmap regs⌝ ∗ [∗ map] r ↦ w ∈ regs, r @@ i ->r w) ∗
      (* TX page and its memory *)
      (tx_page i p_tx ∗ ∃ mem_tx, memory_page p_tx mem_tx) ∗
      (* access *)
      i -@A> ps_acc ∗
      ⌜{[p_tx;p_rx]} ⊆ ps_acc⌝ ∗ ⌜ currently_accessible_in_trans_memory_pages trans ⊆ ps_acc ∖ {[p_tx;p_rx]}⌝ ∗
      pagetable_entries_excl_owned i ps_oea ∗
      transaction_pagetable_entries_owned i trans ∗
      retrieved_transaction_owned i trans ∗
      (∃ mem_oea, memory_pages (ps_oea ∪ (retrieved_lending_memory_pages trans)) mem_oea) ∗
      VMProp i (vmprop_unknown p_tx p_rx) (1/2)%Qp
    )%I.

  Definition trans_rel_secondary (i:VMID) (trans trans': gmap Word transaction): Prop :=
   map_Forall (λ h tran,
            ((tran.1.1.1.1 = i ∧ tran.1.2 ≠ Donation) -> ∃ tran', trans' !! h = Some tran' ∧ tran.1 = tran'.1) ∧
            ((tran.1.1.1.2 = i ∧ tran.2 = true) -> ∃ tran', trans' !! h = Some tran' ∧ tran = tran')
     ) trans.
End logrel.

Section logrel_prim.

  Context `{hypconst:HypervisorConstants}.
  Context `{hypparams:!HypervisorParameters}.
  Context `{vmG: !gen_VMG Σ}.

  Definition trans_rel_primary (i:VMID) (trans trans': gmap Word transaction): Prop :=
   map_Forall (λ h tran,
          ((tran.1.1.1.1 ≠ i ∧ tran.1.1.1.2 ≠ i) -> ∃ tran', trans' !! h = Some tran' ∧ tran = tran') ∧
          ((tran.1.1.1.1 = i ∧ tran.2 = true) -> ∃ tran', trans' !! h = Some tran' ∧ tran = tran') ∧
          ((tran.1.1.1.2= i ∧ tran.1.2 ≠ Donation) -> ∃ tran', trans' !! h = Some tran' ∧ tran.1 = tran'.1)
     ) trans.

  Definition transaction_pagetable_entries_transferred_all (trans: gmap Addr transaction) : iProp Σ:=
    big_sepFM trans (λ kv, kv.2.1.2 = Donation) (λ k v, k -{1/4}>t v.1 ∗ pgt v.1.1.2 1 v.1.1.1.1 true)%I.

  Definition retrievable_transaction_transferred_all(trans: gmap Addr transaction) : iProp Σ:=
    (big_sepFM trans (λ kv, True) (λ k v, k -{1/2}>re v.2 )%I) ∗
    (big_sepFM trans (λ kv, kv.2.2 = false) (λ k v, k -{1/4}>t v.1 ∗ k -{1/2}>re v.2)%I).

  Program Definition interp_access_prim p_tx p_rx ps_acc trans rx_state: iPropO Σ:=
    (
      let ps_macc_trans := (transferred_memory_pages V0 trans) in
      let ps_oea := ps_acc ∖ {[p_rx;p_tx]} ∖ (currently_accessible_in_trans_memory_pages V0 trans) in
      (∃ regs, ⌜is_total_gmap regs⌝ ∗ [∗ map] r ↦ w ∈ regs, r @@ V0 ->r w) ∗
      (tx_page V0 p_tx ∗ ∃ mem_tx, memory_page p_tx mem_tx) ∗
      V0 -@A> ps_acc ∗
      ⌜{[p_tx;p_rx]} ⊆ ps_acc⌝ ∗
      pagetable_entries_excl_owned V0 ps_oea ∗
      transaction_pagetable_entries_owned V0 trans ∗ transaction_hpool_global_transferred trans ∗
      transaction_pagetable_entries_transferred_all trans ∗
      retrieved_transaction_owned V0 trans ∗ retrievable_transaction_transferred_all trans ∗
      (∃ mem_oea, memory_pages ps_oea mem_oea) ∗
      (∃ mem_trans, memory_pages ps_macc_trans mem_trans) ∗
      RX_state@ V0 := rx_state ∗ (rx_page V0 p_rx) ∗
      (∃ mem_rx, memory_page p_rx mem_rx) ∗
      rx_pages (list_to_set (list_of_vmids) ∖ {[V0]}) ∗
      VMProp V0 True 1%Qp ∗
      [∗ set] i ∈ list_to_set (list_of_vmids) ∖ {[V0]}, VMProp (i:VMID) (vmprop_unknown i p_tx p_rx) (1/2)%Qp
    )%I.

End logrel_prim.
