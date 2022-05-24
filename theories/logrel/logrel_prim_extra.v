From iris.proofmode Require Import tactics.
From machine_program_logic.program_logic Require Import weakestpre.
From HypVeri.lang Require Import lang.
From HypVeri.algebra Require Import base base_extra mem pagetable trans.
From HypVeri.logrel Require Import logrel_prim big_sepSS.
From HypVeri Require Import proofmode.
From stdpp Require fin_map_dom.
Import uPred.


Section logrel_prim_extra.
  Context `{hypconst:HypervisorConstants}.
  Context `{hypparams:!HypervisorParameters}.
  Context `{vmG: !gen_VMG Σ}.

  (* slice *)
  Definition trans_preserve_only i (trans trans': (gmap Addr transaction)) :=
    map_Forall (λ h tran, tran.1.1.1.1 = i ∨ tran.1.1.1.2 = i -> ∃ tran', trans' !! h = Some tran' ∧ tran = tran') trans.

  Definition trans_preserve_except i (trans trans': (gmap Addr transaction)) :=
    map_Forall (λ h tran, ¬(tran.1.1.1.1 = i ∨ tran.1.1.1.2 = i) -> ∃ tran', trans' !! h = Some tran' ∧ tran = tran') trans.

  Lemma slice_preserve_singleton (Φ: (gmap Addr transaction) -> (VMID * VMID)-> iProp Σ) trans trans' i:
    slice_wf Φ ->
    trans_preserve_only i trans trans'->
    big_sepSS_singleton set_of_vmids i (Φ trans) ⊣⊢ big_sepSS_singleton set_of_vmids i (Φ trans').
  Proof.
  Admitted.

  Lemma slice_preserve_except (Φ: (gmap Addr transaction) -> (VMID * VMID)-> iProp Σ) trans trans' i:
    slice_wf Φ ->
    trans_preserve_except i trans trans'->
    big_sepSS_except set_of_vmids i (Φ trans) ⊣⊢ big_sepSS_except set_of_vmids i (Φ trans').
  Proof.
  Admitted.

  Lemma slice_union_unify (Φ: (gmap Addr transaction) -> (VMID * VMID)-> iProp Σ) trans trans' i:
    big_sepSS_except set_of_vmids i (Φ trans) ∗ big_sepSS_singleton set_of_vmids i (Φ trans')
    ⊣⊢ ∃ trans'', big_sepSS set_of_vmids (Φ trans'') ∗ ⌜trans_preserve_except i trans trans'' ∧ trans_preserve_only i trans' trans''⌝.
  Proof.
  Admitted.

  Lemma big_sepFM_trans_split i (trans: gmap Addr transaction) `{∀ x, Decision (Q x)} (Φ: _ -> _ -> iPropO Σ):
    map_Forall (λ k (v:transaction), v.1.1.1.1 ≠ v.1.1.1.2) trans ->
    big_sepFM trans (λ kv : Addr * transaction, ((kv.2.1.1.1.1 = i ∨ kv.2.1.1.1.2 = i) ∧ (Q kv))%type) Φ
    ⊣⊢
    (big_sepFM trans (λ kv : Addr * transaction, (kv.2.1.1.1.1 = i ∧ (Q kv))%type) Φ ∗
     big_sepFM trans (λ kv : Addr * transaction, (kv.2.1.1.1.2 = i ∧ (Q kv))%type) Φ).
  Proof.
    intros Hfalse.
    rewrite -big_sepFM_split_lor_weak.
    2:{ intros ? ? ? [[? _ ] [? _]].
        eapply (Hfalse);eauto.
        rewrite H1 H2 //.
    }
    apply big_sepFM_iff.
    intros. split.
    intros [[|] ];eauto.
    intros [[]|[]];eauto.
  Qed.

  Lemma elem_of_set_of_vmids i:
    i ∈ set_of_vmids.
  Proof.
    rewrite /set_of_vmids.
    rewrite elem_of_list_to_set.
    rewrite elem_of_list_In.
    apply in_list_of_vmids.
  Qed.

  Lemma big_sepFM_big_sepS_trans_sndr i (trans: gmap Addr transaction) `{∀ x, Decision (Q x)} (Φ: _ -> _ -> iPropO Σ):
  ([∗ set] y ∈ set_of_vmids,  big_sepFM trans (λ kv : Addr * transaction, (kv.2.1.1.1.1 = i ∧ kv.2.1.1.1.2 = y ∧ Q kv)%type) Φ)
  ⊣⊢ big_sepFM trans (λ kv : Addr * transaction, (kv.2.1.1.1.1 = i ∧ Q kv)%type) Φ.
  Proof.
    rewrite (big_sepFM_iff (Q:= (λ kv, kv.2.1.1.1.1 = i ∧ kv.2.1.1.1.2 ∈ set_of_vmids ∧ Q kv))).
    2:{
      intros. split.
      intros []. split;auto;split;auto. apply elem_of_set_of_vmids.
      intros [? []]. split;done.
    }
    iInduction set_of_vmids as [|x s Hin] "IH" using set_ind_L.
    {
      iSplit; iIntros.
      iApply big_sepFM_False.
      intros ? [_ [? _]].
      set_solver.
      by iApply big_sepS_empty.
    }
    {
      rewrite big_sepS_union //.
      2: set_solver+ Hin.
      rewrite big_sepS_singleton.
      rewrite (big_sepFM_iff
                 (P:= (λ kv , (kv.2.1.1.1.1 = i ∧ kv.2.1.1.1.2 ∈ {[x]} ∪ s ∧ Q kv)))
                 (Q:= (λ kv, (kv.2.1.1.1.1 = i ∧ kv.2.1.1.1.2 = x ∧ Q kv ∨ kv.2.1.1.1.1 = i ∧ kv.2.1.1.1.2 ∈ s ∧ Q kv )%type))).
      2:{
        intros kv. rewrite elem_of_union. split.
        intros [? [[|] ?]]. left;split;auto;split;auto. set_solver.
        right;split;auto.
        intros [[? []]|[?[]]];split;auto;split;auto.
        left;set_solver.
      }
      rewrite big_sepFM_split_lor.
      2:{ intros ? (?&?&?&?). set_solver. }
      iSplit;iIntros "[$ ?]"; by iApply "IH".
    }
  Qed.

  Lemma big_sepFM_big_sepS_trans_rcvr i (trans: gmap Addr transaction) `{∀ x, Decision (Q x)} (Φ: _ -> _ -> iPropO Σ):
  ([∗ set] y ∈ set_of_vmids,  big_sepFM trans (λ kv : Addr * transaction, (kv.2.1.1.1.1 = y ∧ kv.2.1.1.1.2 = i ∧ Q kv)%type) Φ)
  ⊣⊢ big_sepFM trans (λ kv : Addr * transaction, (kv.2.1.1.1.2 = i ∧ Q kv)%type) Φ.
  Proof.
    rewrite (big_sepFM_iff (Q:= (λ kv, kv.2.1.1.1.1 ∈ set_of_vmids ∧ kv.2.1.1.1.2 = i ∧ Q kv))).
    2:{
      intros. split.
      intros []. split;auto. apply elem_of_set_of_vmids.
      intros [? []]. split;done.
    }
    iInduction set_of_vmids as [|x s Hin] "IH" using set_ind_L.
    {
      iSplit; iIntros.
      iApply big_sepFM_False.
      intros ? [? _]. set_solver.
      by iApply big_sepS_empty.
    }
    {
      rewrite big_sepS_union //.
      2: set_solver+ Hin.
      rewrite big_sepS_singleton.
      rewrite (big_sepFM_iff
                 (P:= (λ kv , (kv.2.1.1.1.1 ∈ {[x]} ∪ s ∧ kv.2.1.1.1.2 = i ∧ Q kv)))
                 (Q:= (λ kv, (kv.2.1.1.1.1 = x ∧ kv.2.1.1.1.2 = i ∧ Q kv ∨ kv.2.1.1.1.1 ∈ s ∧ kv.2.1.1.1.2 = i ∧ Q kv )%type))).
      2:{
        intros kv. rewrite elem_of_union. split.
        intros [[|] [? ?]]. left;split;auto. set_solver.
        right;split;auto.
        intros [[? []]|[?[]]];split;auto.
        left;set_solver.
      }
      rewrite big_sepFM_split_lor.
      2:{ intros ? (?&?&?&?). set_solver. }
      iSplit;iIntros "[$ ?]"; by iApply "IH".
    }
  Qed.

  Lemma transaction_pagetable_entries_transferred_equiv i (trans: gmap Addr transaction):
    map_Forall (λ k (v:transaction), v.1.1.1.1 ≠ v.1.1.1.2) trans ->
    big_sepSS_singleton set_of_vmids i (λ ij, transaction_pagetable_entries_transferred_slice ij.1 ij.2 trans) ⊣⊢
      transaction_pagetable_entries_transferred i trans.
  Proof.
    intros Hfalse.
    rewrite /transaction_pagetable_entries_transferred.
    rewrite (big_sepFM_iff (Q:= (λ kv : Addr * transaction,((kv.2.1.1.1.1 = i ∨ kv.2.1.1.1.2 = i) ∧ kv.2.1.2 = Donation)%type))).
    2:{  intros. split; intros [? ?];done. }
    rewrite big_sepFM_trans_split //.
    rewrite /big_sepSS_singleton.
    rewrite big_sepS_sep /=.
    rewrite /transaction_pagetable_entries_transferred_slice.
    iSplit.
    iIntros "[H1 H2]";iSplitL "H1";first iApply big_sepFM_big_sepS_trans_sndr.
    iApply big_sepS_proper.
    2: iExact "H1".
    intros. iApply big_sepFM_iff.
    intros. split;intros [[] []];split;eauto.
    iApply big_sepFM_big_sepS_trans_rcvr.
    iApply big_sepS_proper.
    2: iExact "H2".
    intros. iApply big_sepFM_iff.
    intros. split;intros [[] []];split;eauto.
    iIntros "[H1 H2]";iSplitL "H1".
    iDestruct (big_sepFM_big_sepS_trans_sndr with "H1") as "H1".
    iApply big_sepS_proper.
    2: iExact "H1".
    intros. iApply big_sepFM_iff.
    intros. split;intros [[] []];split;eauto.
    iDestruct (big_sepFM_big_sepS_trans_rcvr with "H2") as "H2".
    iApply big_sepS_proper.
    2: iExact "H2".
    intros. iApply big_sepFM_iff.
    intros. split;intros [[] []];split;eauto.
   Qed.

  Lemma retrievable_transaction_transferred_equiv i (trans: gmap Addr transaction):
    big_sepSS_singleton set_of_vmids i (λ ij, retrievable_transaction_transferred_slice ij.1 ij.2 trans) ⊣⊢
    retrievable_transaction_transferred i trans.
  Proof.
  Admitted.

  Lemma transferred_memory_pages_equiv i (trans: gmap Addr transaction):
    trans_ps_disj trans ->
    big_sepSS_singleton set_of_vmids i (λ ij, ∃mem, memory_pages (transferred_memory_pages_slice ij.1 ij.2 trans) mem) ⊣⊢
    ∃mem, memory_pages (transferred_memory_pages i trans) mem.
  Proof.
  Admitted.

End logrel_prim_extra.
