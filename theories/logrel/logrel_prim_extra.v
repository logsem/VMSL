From iris.proofmode Require Import tactics.
From machine_program_logic.program_logic Require Import weakestpre.
From HypVeri.lang Require Import lang.
From HypVeri.algebra Require Import base base_extra mem pagetable trans mailbox.
From HypVeri.logrel Require Export logrel_prim big_sepSS map_zip_extra.
From HypVeri Require Import proofmode.
From stdpp Require fin_map_dom.
Import uPred.

Section logrel_prim_extra.
  Context `{hypconst:HypervisorConstants}.
  Context `{hypparams:!HypervisorParameters}.
  Context `{vmG: !gen_VMG Σ}.

  (* slice *)

  Lemma slice_wf_sep `{slice_wf1:!SliceTransWf Φ1} `{slice_wf2:!SliceTransWf Φ2} :
    SliceTransWf (λ trans i j, ((Φ1 trans i j) :iProp Σ) ∗ ((Φ2 trans i j) :iProp Σ))%I.
  Proof.
  Admitted.

  Instance slice_transaction_pagetable_entries_transferred_wf
    : SliceTransWf transaction_pagetable_entries_transferred_slice.
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
      admit.
    }
    Admitted.

  Instance slice_retrievable_transaction_transferred_wf
    : SliceTransWf retrievable_transaction_transferred_slice.
  Proof.
  Admitted.

  Instance slice_transferred_memory_pages_wf
    : SliceTransWf transferred_memory_slice.
  Proof.
  Admitted.

  Instance slice_transfer_all_wf : SliceTransWf slice_transfer_all.
  Proof.
    rewrite /slice_transfer_all /=.
  Admitted.

  Lemma except_only_union i trans trans':
    except i trans  = except i (only i trans' ∪ trans).
  Proof.
   rewrite /only.
   induction trans' using map_ind.
   rewrite map_filter_empty.
   f_equal.
   rewrite map_empty_union //.
   rewrite map_filter_insert.
   case_decide.
   {
     rewrite /except.
     admit.
   }
   {
     rewrite delete_notin //.
   }
   Admitted.

  Lemma except_idemp i trans :
    except i trans  = except i (except i trans).
  Proof.
  Admitted.

  (* TODO *)
  Lemma slice_preserve_except i (Φ : _ -> _ -> _ -> iProp Σ) `{!SliceTransWf Φ} trans trans':
    except i trans = except i trans' ->
    big_sepSS_except set_of_vmids i (Φ trans) ⊣⊢ big_sepSS_except set_of_vmids i (Φ trans').
  Proof.
    iIntros (Heq).
    rewrite /big_sepSS_except.
    rewrite /big_sepSS.
    iApply big_sepS_proper.
    iIntros (? Hin).
    iApply big_sepS_proper.
    iIntros (? Hin').
    iApply (slice_trans_valid Φ).
    rewrite /trans_preserve_slice.
    admit.
  Admitted.

  (* Lemma slice_union_unify (Φ: (gmap Addr transaction) -> (VMID * VMID)-> iProp Σ) trans trans' i: *)
  (*   big_sepSS_except set_of_vmids i (Φ trans) ∗ big_sepSS_singleton set_of_vmids i (Φ trans') *)
  (*   ⊣⊢ ∃ trans'', big_sepSS set_of_vmids (Φ trans'') ∗ ⌜trans_preserve_except i trans trans'' ∧ trans_preserve_only i trans' trans''⌝. *)
  (* Proof. *)
  (* Admitted. *)

  Lemma elem_of_set_of_vmids i:
    i ∈ set_of_vmids.
  Proof.
    rewrite /set_of_vmids.
    rewrite elem_of_list_to_set.
    rewrite elem_of_list_In.
    apply in_list_of_vmids.
  Qed.

  Lemma slice_trans_unify (Φ: _ -> _ -> _ -> iProp Σ) `{Hwf:!SliceTransWf Φ} trans trans' i:
    big_sepSS_except set_of_vmids i (Φ trans) ∗
      big_sepSS_singleton set_of_vmids i (Φ (only i trans' ∪ trans))
    ⊢  big_sepSS set_of_vmids (Φ (only i trans' ∪ trans)).
  Proof.
    iIntros "(except & only)".
    assert (set_of_vmids = (set_of_vmids ∖ {[i]}) ∪ {[i]}).
    pose proof (elem_of_set_of_vmids i). rewrite difference_union_L. set_solver + H.
    rewrite H.
    iApply big_sepSS_union_singleton. set_solver +.
    rewrite -H. iSplitL "except".
    {
      iApply (slice_preserve_except with "except").
      symmetry.
      apply except_only_union.
    }
    {
      done.
    }
  Qed.

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

  (* (* TODO *) *)
  (* Lemma big_sepSS_singleton_trans_unify `{Hwf:!SliceTransWf Φ} i trans trans': *)
  (*   filter (λ kv, kv.2.1.1.1.1 = i ∨ kv.2.1.1.1.2 = i) trans *)
  (*   = filter (λ kv, kv.2.1.1.1.1 = i ∨ kv.2.1.1.1.2 = i) trans' -> *)
  (*   big_sepSS_singleton set_of_vmids i (Φ trans) ⊣⊢ *)
  (*     big_sepSS_singleton set_of_vmids i (Φ trans'). *)
  (* Proof. *)
  (*   intros Heq. *)
  (*   rewrite /big_sepSS_singleton. *)
  (*   rewrite big_sepS_sep. *)
  (* Admitted. *)

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

  Lemma rx_states_split_zero {Φ_r} rxs:
      is_total_gmap rxs ->
      (∀ j, Φ_r V0 j V0 ⊣⊢ slice_rx_state V0 j) ->
      rx_states_global rxs ∗
      rx_states_transferred Φ_r rxs ∗
      rx_states_owned Φ_r rxs
      ⊢
      rx_states_global (delete V0 rxs) ∗
      rx_states_transferred Φ_r (delete V0 rxs) ∗
      rx_states_owned Φ_r (delete V0 rxs) ∗
      rx_state_get V0 rxs ∗
      ∃ p_rx, RX@V0 := p_rx ∗
      (∃ mem_rx, memory_page p_rx mem_rx).
  Proof.
    iIntros (Htotal Hequiv) "(global & transferred & owned)".
    rewrite /rx_states_global /rx_states_owned /rx_states_transferred.
    pose proof (Htotal V0) as [rs Hlookup_rs].
    iDestruct (big_sepM_delete with "global") as "[rs global]";eauto.
    iDestruct (big_sepM_delete with "transferred") as "[t transferred]";eauto.
    iDestruct (big_sepM_delete with "owned") as "[_ owned]";eauto.
    iFrame.
    destruct rs.
    {
      iDestruct (Hequiv (Some p) with "t") as "[% (? & R & ?)]".
      rewrite /rx_state_match  /slice_rx_state /=.
      iSplitL "rs R".
      rewrite /rx_state_get.
      iIntros (?) "%Hlk".
      rewrite Hlookup_rs in Hlk.
      inversion Hlk.
      iApply (rx_state_split V0 _ (Some p)). iFrame.
      iExists p_rx. iFrame.
    }
    {
      rewrite /rx_state_match.
      iDestruct "rs" as "[? R]".
      iSplitR "R".
      rewrite /rx_state_get.
      iIntros (?) "%Hlk".
      rewrite Hlookup_rs in Hlk.
      inversion Hlk.
      done.
      done.
    }
  Qed.

  Lemma rx_state_merge_zero {Φ_r} rxs:
      is_total_gmap rxs ->
      (∀ j, Φ_r V0 j V0 ⊣⊢ slice_rx_state V0 j) ->
      rx_states_global (delete V0 rxs) ∗
      rx_states_transferred Φ_r (delete V0 rxs) ∗
      rx_states_owned Φ_r (delete V0 rxs) ∗
      rx_state_get V0 rxs ∗
      (∃ p_rx, RX@V0 := p_rx ∗
      (∃ mem_rx, memory_page p_rx mem_rx))
      ⊢
      rx_states_global rxs ∗
      rx_states_transferred Φ_r rxs ∗
      rx_states_owned Φ_r rxs.
  Proof.
    iIntros (Htotal Hequiv) "(global & transferred & owned & rx_state & rx)".
    rewrite /rx_states_global /rx_states_owned /rx_states_transferred.
    pose proof (Htotal V0) as [rs Hlookup_rs].
    rewrite (big_sepM_delete _ rxs V0 rs);auto.
    iFrame "global".
    rewrite (big_sepM_delete _ rxs V0 rs);auto.
    iFrame "transferred".
    rewrite (big_sepM_delete _ rxs V0 rs);auto.
    iFrame "owned".
    iDestruct ("rx_state" $! rs with "[]") as "rx_state". done.
    destruct rs.
    {
      rewrite /rx_state_match.
      case_bool_decide.
      iDestruct "rx_state" as "[_ %]".
      done.
      iDestruct (rx_state_split with "rx_state") as "[? ?]".
      iFrame.
      iSplitL;last done.
      rewrite (Hequiv (Some p)).
      rewrite /slice_rx_state.
      iFrame.
    }
    {
      rewrite /rx_state_match.
      iFrame.
      done.
    }
Qed.

  Lemma rx_states_split {Φ_r} `{!SliceRxsWf Φ_r} (i:VMID) rxs:
      (∀ i os,
         match os with
         | None => True
         | Some (_ ,k) => k = V0
        end ->
         Φ_r i os i ⊣⊢ Φ_r i os V0) ->
      is_total_gmap rxs ->
      rx_states_global rxs ∗
      rx_states_transferred Φ_r rxs
      ⊢
      rx_states_global (delete i rxs) ∗
      rx_states_transferred Φ_r (delete i rxs) ∗
      (∀ rs : option (Addr * VMID), ⌜rxs !! i = Some rs⌝ -∗ rx_state_match i rs ∗ Φ_r i rs i).
  Proof.
    iIntros (H Htotal) "(global & transferred)".
    rewrite /rx_states_global /rx_states_owned /rx_states_transferred.
    pose proof (Htotal i) as [rs Hlookup_rs].
    iDestruct (big_sepM_delete with "global") as "[rs global]";eauto.
    iDestruct (big_sepM_delete with "transferred") as "[t transferred]";eauto.
    iFrame.
    iIntros (?) "%Hlk".
    rewrite Hlookup_rs in Hlk.
    inversion Hlk. subst rs0.
    destruct rs.
    {
      iFrame.
      destruct p.
      destruct (decide (v = V0)).
      iDestruct (H with "t") as "t";done.
      iDestruct (slice_rxs_sym Φ_r i (Some (f,v)) i with "t") as "t";done.
    }
    {
      rewrite (slice_rxs_empty).
      iSplitL. iFrame "rs". done.
    }
  Qed.

End logrel_prim_extra.
