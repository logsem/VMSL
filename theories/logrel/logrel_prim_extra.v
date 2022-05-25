From iris.proofmode Require Import tactics.
From machine_program_logic.program_logic Require Import weakestpre.
From HypVeri.lang Require Import lang.
From HypVeri.algebra Require Import base base_extra mem pagetable trans.
From HypVeri.logrel Require Export logrel_prim big_sepSS.
From HypVeri Require Import proofmode.
From stdpp Require fin_map_dom.
Import uPred.


Section logrel_prim_extra.
  Context `{hypconst:HypervisorConstants}.
  Context `{hypparams:!HypervisorParameters}.
  Context `{vmG: !gen_VMG Σ}.

  (* slice *)

  Lemma slice_wf_sep `{slice_wf1:!SliceWf Φ1} `{slice_wf2:!SliceWf Φ2} :
    SliceWf (λ trans i j, ((Φ1 trans i j) :iProp Σ) ∗ ((Φ2 trans i j) :iProp Σ))%I.
  Proof.
  Admitted.

  Instance slice_transaction_pagetable_entries_transferred_wf
    : SliceWf transaction_pagetable_entries_transferred_slice.
  Proof.
    split.
    {
      intros i j trans trans' Heq.
      rewrite /transaction_pagetable_entries_transferred_slice /=.
      iInduction trans as [|k v m Hlk] "IH" using map_ind forall (trans' Heq).
      rewrite /trans_preserve_slice map_filter_empty in Heq.
      iSplit.
      {
        iIntros "_".
        symmetry in Heq.
        apply map_filter_empty_iff in Heq.
        iApply big_sepFM_False_weak.
        intros ? ? ? [? ?].
        efeed specialize Heq;eauto.
      }
      {
        iIntros "_".
        iApply big_sepFM_empty.
      }
      destruct (decide (((v.1.1.1.1 = i ∧ v.1.1.1.2 = j) ∧ v.1.2 = Donation))).
      {
        admit.
      }
      {
        admit.
      }
    }
    {
      intros i j trans trans' Hsubset.
      rewrite /transaction_pagetable_entries_transferred_slice /=.
      iIntros "global".
      iInduction trans as [|k v m Hlk] "IH" using map_ind forall (trans' Hsubset).
      iSplit.
      iIntros "_".
      rewrite fmap_empty.
      (* TODO show lemmas about map_zip *)
      admit.
      admit.
      admit.
    }
    Admitted.

  Instance slice_retrievable_transaction_transferred_wf
    : SliceWf retrievable_transaction_transferred_slice.
  Proof.
    Admitted.

  Instance slice_transferred_memory_pages_wf
    : SliceWf transferred_memory_slice.
  Proof.
    Admitted.

  Instance slice_transfer_all_wf : SliceWf slice_transfer_all.
  Proof.
    rewrite /slice_transfer_all /=.
  Admitted.

  (* TODO *)
  Lemma slice_preserve_only i Φ `{Hwf:!SliceWf Φ} trans trans':
    trans_preserve_only i trans trans'->
    big_sepSS_singleton set_of_vmids i (Φ trans) ⊣⊢ big_sepSS_singleton set_of_vmids i (Φ trans').
  Proof.
  Admitted.

  (* TODO *)
  Lemma slice_preserve_except i Φ `{Hwf:!SliceWf Φ} trans trans':
    slice_wf Φ ->
    trans_preserve_except i trans trans'->
    big_sepSS_except set_of_vmids i (Φ trans) ⊣⊢ big_sepSS_except set_of_vmids i (Φ trans').
  Proof.
  Admitted.

  (* Lemma slice_union_unify (Φ: (gmap Addr transaction) -> (VMID * VMID)-> iProp Σ) trans trans' i: *)
  (*   big_sepSS_except set_of_vmids i (Φ trans) ∗ big_sepSS_singleton set_of_vmids i (Φ trans') *)
  (*   ⊣⊢ ∃ trans'', big_sepSS set_of_vmids (Φ trans'') ∗ ⌜trans_preserve_except i trans trans'' ∧ trans_preserve_only i trans' trans''⌝. *)
  (* Proof. *)
  (* Admitted. *)

  (* TODO: the most important lemma! *)
  Lemma slice_global_unify Φ `{Hwf:!SliceWf Φ} trans trans' i:
    big_sepSS_except set_of_vmids i (Φ trans) ∗
      big_sepSS_singleton set_of_vmids i (Φ trans') ∗
      ([∗ map] h ↦ tran ∈ trans', h -{1/2}>t tran.1)
    ⊢ ∃ trans'', big_sepSS set_of_vmids (Φ trans'') ∗ [∗ map] h ↦ tran ∈ trans'', h -{1/2}>t tran.1.
  (* trans'' = map_zip (fst <$>trans') ((snd<$> (filter (λ kv, kv.2.1.1.1.1 = i ∨ kv.2.1.1.1.2 = i)trans)) ∪ (snd<$> (filter (λ kv, ¬ (kv.2.1.1.1.1 = i ∨ kv.2.1.1.1.2 = i))trans))) *)
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

  (* Lemma in_set_of_vmids: *)
  (*   ∀ i, i ∈ set_of_vmids. *)
  (* Proof. *)
  (*   rewrite /set_of_vmids. *)
  (*   intros. *)
  (*   rewrite elem_of_list_to_set. *)
  (*   rewrite elem_of_list_In. *)
  (*   apply in_list_of_vmids. *)
  (* Qed. *)

  Lemma big_sepFM_big_sepS_trans_sndr i (trans: gmap Addr transaction) `{∀ x, Decision (Q x)} (Φ: _ -> _ -> iPropO Σ):
  ([∗ set] y ∈ set_of_vmids, big_sepFM trans (λ kv : Addr * transaction, ((kv.2.1.1.1.1 = i ∧ kv.2.1.1.1.2 = y) ∧ Q kv)%type) Φ)
  ⊣⊢ big_sepFM trans (λ kv : Addr * transaction, (kv.2.1.1.1.1 = i ∧ Q kv)%type) Φ.
  Proof.
    rewrite (big_sepFM_iff (Q:= (λ kv, (kv.2.1.1.1.1 = i ∧ kv.2.1.1.1.2 ∈ set_of_vmids) ∧ Q kv))).
    2:{
      intros. split.
      intros []. split;auto;split;auto. apply elem_of_set_of_vmids.
      intros [[] ?]. split;done.
    }
    iInduction set_of_vmids as [|x s Hin] "IH" using set_ind_L.
    {
      iSplit; iIntros.
      iApply big_sepFM_False.
      intros ? [[_ ?] _].
      set_solver.
      by iApply big_sepS_empty.
    }
    {
      rewrite big_sepS_union //.
      2: set_solver+ Hin.
      rewrite big_sepS_singleton.
      rewrite (big_sepFM_iff
                 (P:= (λ kv, ((kv.2.1.1.1.1 = i ∧ kv.2.1.1.1.2 ∈ {[x]} ∪ s) ∧ Q kv)))
                 (Q:= (λ kv, ((kv.2.1.1.1.1 = i ∧ kv.2.1.1.1.2 = x) ∧ Q kv ∨ (kv.2.1.1.1.1 = i ∧ kv.2.1.1.1.2 ∈ s) ∧ Q kv)%type))).
      2:{
        intros kv. rewrite elem_of_union. split.
        intros [[? [|]] ?]. left;split;auto;split;auto. set_solver.
        right;split;auto.
        intros [[[] ?]|[[] ?]];split;auto;split;auto.
        left;set_solver.
      }
      rewrite big_sepFM_split_lor.
      2:{ intros ? ([[] ?]&[]&?). set_solver. }
      iSplit;iIntros "[$ ?]"; by iApply "IH".
    }
  Qed.

  Lemma big_sepFM_big_sepS_trans_rcvr i (trans: gmap Addr transaction) `{∀ x, Decision (Q x)} (Φ: _ -> _ -> iPropO Σ):
  ([∗ set] y ∈ set_of_vmids, big_sepFM trans (λ kv : Addr * transaction, ((kv.2.1.1.1.1 = y ∧ kv.2.1.1.1.2 = i) ∧ Q kv)%type) Φ)
  ⊣⊢ big_sepFM trans (λ kv : Addr * transaction, (kv.2.1.1.1.2 = i ∧ Q kv)%type) Φ.
  Proof.
    rewrite (big_sepFM_iff (Q:= (λ kv, (kv.2.1.1.1.1 ∈ set_of_vmids ∧ kv.2.1.1.1.2 = i) ∧ Q kv))).
    2:{
      intros. split.
      intros []. split;auto;split;auto. apply elem_of_set_of_vmids.
      intros [[] ?]. split;done.
    }
    iInduction set_of_vmids as [|x s Hin] "IH" using set_ind_L.
    {
      iSplit; iIntros.
      iApply big_sepFM_False.
      intros ? [[? _] _].
      set_solver.
      by iApply big_sepS_empty.
    }
    {
      rewrite big_sepS_union //.
      2: set_solver+ Hin.
      rewrite big_sepS_singleton.
      rewrite (big_sepFM_iff
                 (P:= (λ kv, ((kv.2.1.1.1.1 ∈ {[x]} ∪ s ∧ kv.2.1.1.1.2 = i) ∧ Q kv)))
                 (Q:= (λ kv, ((kv.2.1.1.1.1 = x ∧ kv.2.1.1.1.2 = i) ∧ Q kv ∨ (kv.2.1.1.1.1 ∈ s ∧ kv.2.1.1.1.2 = i) ∧ Q kv)%type))).
      2:{
        intros kv. rewrite elem_of_union. split.
        intros [[[|] ?] ?]. left;split;auto. set_solver.
        right;split;auto.
        intros [[[] ?]|[[] ?]];split;auto.
        split;set_solver.
      }
      rewrite big_sepFM_split_lor.
      2:{ intros ? ([[]?]&[]&?). set_solver. }
      iSplit;iIntros "[$ ?]"; by iApply "IH".
    }
  Qed.

  (* TODO *)
  Lemma big_sepSS_singleton_trans_unify `{Hwf:!SliceWf Φ} i trans trans':
    filter (λ kv, kv.2.1.1.1.1 = i ∨ kv.2.1.1.1.2 = i) trans
    = filter (λ kv, kv.2.1.1.1.1 = i ∨ kv.2.1.1.1.2 = i) trans' ->
    big_sepSS_singleton set_of_vmids i (Φ trans) ⊣⊢
      big_sepSS_singleton set_of_vmids i (Φ trans').
  Proof.
    intros Heq.
    rewrite /big_sepSS_singleton.
    rewrite big_sepS_sep.
  Admitted.

  Definition trans_neq (trans: gmap Addr transaction) :=
      map_Forall (λ (k:Addr) (v:transaction), v.1.1.1.1 ≠ v.1.1.1.2) trans.

  Lemma transaction_pagetable_entries_transferred_equiv i (trans: gmap Addr transaction):
    trans_neq trans ->
    big_sepSS_singleton set_of_vmids i (transaction_pagetable_entries_transferred_slice trans) ⊣⊢
      transaction_pagetable_entries_transferred i trans.
  Proof.
    intros Hfalse.
    rewrite /transaction_pagetable_entries_transferred.
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
    trans_neq trans ->
    big_sepSS_singleton set_of_vmids i (retrievable_transaction_transferred_slice trans) ⊣⊢
    retrievable_transaction_transferred i trans.
  Proof.
    iIntros (Hneq).
    rewrite /retrievable_transaction_transferred.
    rewrite big_sepFM_trans_split //.
    rewrite (big_sepFM_iff
               (P:= (λ kv, kv.2.1.1.1.1 = i ∨ kv.2.1.1.1.2 = i))
               (Q:= (λ kv, (kv.2.1.1.1.1 = i ∨ kv.2.1.1.1.2 = i) ∧ (True:Prop)))).
    2: { intros ?;split;eauto;intro. destruct H; done. }
    rewrite big_sepFM_trans_split //.
    rewrite /big_sepSS_singleton.
    rewrite big_sepS_sep /=.
    rewrite /retrievable_transaction_transferred_slice.
    rewrite 2?big_sepS_sep /=.
    iSplit.
    iIntros "[[H11 H12] [H21 H22]]";iSplitL "H11 H21".
    iSplitL "H11";  [iApply big_sepFM_big_sepS_trans_sndr | iApply big_sepFM_big_sepS_trans_rcvr];
    iApply big_sepS_mono; iFrame;
    iIntros (??) "H";iApply (big_sepFM_iff with "H"); (intros; split;intros [];done).
    iSplitL "H12";  [iApply big_sepFM_big_sepS_trans_sndr | iApply big_sepFM_big_sepS_trans_rcvr];
    iApply big_sepS_mono; iFrame;
    iIntros (??) "H";iApply (big_sepFM_iff with "H"); (intros; split;intros [];done).
    iIntros "[[H11 H12] [H21 H22]]";iSplitL "H11 H21".
    iSplitL "H11";  rewrite -big_sepFM_big_sepS_trans_sndr.
    iApply big_sepS_mono; iFrame;
    iIntros (??) "H";iApply (big_sepFM_iff with "H"); (intros; split;intros [];done).
    iApply big_sepS_mono; iFrame;
    iIntros (??) "H";iApply (big_sepFM_iff with "H"); (intros; split;intros [];done).
    iSplitL "H12";  rewrite -big_sepFM_big_sepS_trans_rcvr.
    iApply big_sepS_mono; iFrame;
    iIntros (??) "H";iApply (big_sepFM_iff with "H"); (intros; split;intros [];done).
    iApply big_sepS_mono; iFrame;
    iIntros (??) "H";iApply (big_sepFM_iff with "H"); (intros; split;intros [];done).
   Qed.

  Lemma transferred_memory_slice_empty i j: ⊢ transferred_memory_slice ∅ i j.
  Proof.
    iIntros.
    rewrite /transferred_memory_slice.
    iApply big_sepFM_empty.
  Qed.

  Lemma transferred_memory_equiv i trans:
    trans_neq trans ->
    trans_ps_disj trans ->
    big_sepSS_singleton set_of_vmids i (transferred_memory_slice trans) ⊣⊢
    ∃ mem, memory_pages (transferred_memory_pages i trans) mem.
  Proof.
    iIntros (Hneq Hdisj).
    iInduction trans as [|h tran m Hlk] "IH" using map_ind.
    {
      iSplit; iIntros "H".
      iExists ∅.
      rewrite /transferred_memory_pages.
      rewrite map_filter_empty.
      rewrite pages_in_trans_empty //.
      iApply memory_pages_empty.
      rewrite /big_sepSS_singleton.
      rewrite big_sepS_proper.
      erewrite big_sepS_emp. done.
      intros. iSplit;auto.
      iIntros "_".
      rewrite /transferred_memory_slice.
      iSplitL; iApply big_sepFM_empty.
    }
    {
      rewrite /big_sepSS_singleton.
      rewrite 2?big_sepS_sep.
      rewrite /transferred_memory_slice.
      rewrite 2?big_sepFM_big_sepS_trans_sndr.
      rewrite 2?big_sepFM_big_sepS_trans_rcvr.
      rewrite /trans_neq map_Forall_insert // in Hneq.
      destruct Hneq as [Hneq Hneq'].
      apply trans_ps_disj_insert_2 in Hdisj;auto.
      destruct Hdisj as [Hdisj Hdisj'].
      iSpecialize ("IH" $! Hneq' Hdisj').
      destruct (decide(((tran.1.1.1.1 = i ∨ tran.1.1.1.2 = i) ∧ ¬ (tran.2 = true ∧ tran.1.2 = Lending)))).
      {
        destruct (decide (tran.1.1.1.1 = i)).
        {
          rewrite big_sepFM_insert_True //=.
          2: destruct a;auto.
          rewrite big_sepFM_insert_False //=.
          2: {
            intros []. subst i. done.
          }
          rewrite -sep_assoc.
          rewrite /transferred_memory_pages.
          rewrite map_filter_insert_True //.
          rewrite pages_in_trans_insert //.
          2: { rewrite map_filter_lookup_None. left;done. }
          rewrite memory_pages_split_union'.
          iSplit; iIntros "[$ ?]"; by iApply "IH".
          assert (pages_in_trans (filter
          (λ kv : Addr * (leibnizO VMID * leibnizO VMID * gset PID * transaction_type * bool),
             (kv.2.1.1.1.1 = i ∨ kv.2.1.1.1.2 = i) ∧ ¬ (kv.2.2 = true ∧ kv.2.1.2 = Lending)) m) ⊆ pages_in_trans m).
          apply pages_in_trans_subseteq.
          apply map_filter_subseteq.
          set_solver + Hdisj H.
        }
        {
          rewrite big_sepFM_insert_False //=.
          2: {
            intros []. done.
          }
          rewrite big_sepFM_insert_True //=.
          2: {
            destruct a as [[|]?];eauto. done.
          }
          rewrite /transferred_memory_pages.
          rewrite map_filter_insert_True //.
          rewrite pages_in_trans_insert //.
          2: { rewrite map_filter_lookup_None. left;done. }
          rewrite memory_pages_split_union'.
          iSplit. iIntros "[? [? ?]]". iFrame. iApply "IH". iFrame.
          iIntros "[? ?]". iFrame. iApply "IH". iFrame.
          assert (pages_in_trans (filter
          (λ kv : Addr * (leibnizO VMID * leibnizO VMID * gset PID * transaction_type * bool),
             (kv.2.1.1.1.1 = i ∨ kv.2.1.1.1.2 = i) ∧ ¬ (kv.2.2 = true ∧ kv.2.1.2 = Lending)) m) ⊆ pages_in_trans m).
          apply pages_in_trans_subseteq.
          apply map_filter_subseteq.
          set_solver + Hdisj H.
        }
      }
      {
        rewrite 2?big_sepFM_insert_False //=.
        2: {
          intros [] ;apply n. split;eauto.
        }
        2: {
          intros [] ;apply n. split;eauto.
        }
        rewrite /transferred_memory_pages.
        rewrite map_filter_insert_False //.
        rewrite delete_notin //.
      }
    }
  Qed.

  Lemma slice_transfer_all_equiv k (trans: gmap Addr transaction) Φ:
      (∀ i j trans, (i = k ∨ j = k) -> Φ trans i j ⊣⊢ slice_transfer_all trans i j) ->
      big_sepSS_singleton set_of_vmids k (Φ trans) ⊣⊢ big_sepSS_singleton set_of_vmids k (slice_transfer_all trans).
  Proof.
    intros HΦ.
    rewrite /big_sepSS_singleton.
    apply big_sepS_proper.
    intros.
    rewrite (HΦ k x);last (left;done).
    rewrite (HΦ x k);last (right;done).
    done.
  Qed.

  Lemma transferred_only_equiv k (trans: gmap Addr transaction) Φ:
      (∀ i j trans, (i = k ∨ j = k) -> Φ trans i j ⊣⊢ slice_transfer_all trans i j) ->
      trans_neq trans ->
      trans_ps_disj trans ->
      big_sepSS_singleton set_of_vmids k (Φ trans) ⊣⊢
      transaction_pagetable_entries_transferred k trans ∗
      retrievable_transaction_transferred k trans ∗
      (∃ mem_trans, memory_pages (transferred_memory_pages k trans) mem_trans).
  Proof.
    intros HΦ Hneq Hdisj.
    rewrite slice_transfer_all_equiv //.
    rewrite /big_sepSS_singleton.
    rewrite !big_sepS_sep.
    rewrite -transaction_pagetable_entries_transferred_equiv //.
    rewrite -retrievable_transaction_transferred_equiv //.
    rewrite -transferred_memory_equiv //.
    rewrite /big_sepSS_singleton.
    rewrite !big_sepS_sep.
    iSplit.
    iIntros "[($ & $ & $) ($ & $ & $)]".
    iIntros "([$ $] & [$ $] & [$ $])".
  Qed.

  Lemma get_trans_neq trans:
    transaction_hpool_global_transferred trans ⊢ ⌜trans_neq trans⌝.
  Proof.
    iIntros "(%s & %Hall & fresh & global_tran)".
    iIntros (h tran Hlk).
    iDestruct (big_sepM_lookup with "global_tran") as "[mp _]";eauto.
    iDestruct (trans_valid_tran_Some with "mp") as %Hvalid.
    iPureIntro. done.
  Qed.


End logrel_prim_extra.
