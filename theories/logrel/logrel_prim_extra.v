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
  Global Instance slice_trans_wf_sep Φ1 Φ2:
    SliceTransWf Φ1 ->
    SliceTransWf Φ2 ->
    SliceTransWf (λ trans i j, ((Φ1 trans i j) :iProp Σ) ∗ ((Φ2 trans i j) :iProp Σ))%I.
  Proof.
    intros.
    split.
    intros.
    rewrite (slice_trans_valid Φ1) //.
    rewrite (slice_trans_valid Φ2) //.
  Qed.

  Global Instance slice_trans_wf_later Φ1 :
    SliceTransWf Φ1 ->
    SliceTransWf (λ trans i j, ▷ (Φ1 trans i j) :iProp Σ)%I.
  Proof.
    intros.
    split.
    intros.
    rewrite (slice_trans_valid Φ1) //.
  Qed.

  Instance slice_transaction_pagetable_entries_transferred_wf
    : SliceTransWf transaction_pagetable_entries_transferred_slice.
  Proof.
    split.
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
    assert (trans_preserve_slice i j m (delete k trans')).
    {
      rewrite /trans_preserve_slice in Heq.
      rewrite /trans_preserve_slice.
      destruct (decide (v.1.1.1.1 = i ∧ v.1.1.1.2 = j)).
      rewrite map_filter_insert_True // in Heq.
      rewrite map_filter_delete.
      rewrite -Heq.
      rewrite delete_insert //.
      rewrite map_filter_lookup_None;left;done.
      rewrite map_filter_insert_False // in Heq.
      rewrite map_filter_delete in Heq.
      rewrite map_filter_delete.
      rewrite -Heq.
      rewrite delete_idemp.
      rewrite -map_filter_delete.
      rewrite delete_notin //.
    }
    destruct (decide ((v.1.1.1.1 = i ∧ v.1.1.1.2 = j))).
    {
      iSpecialize ("IH" $! (delete k trans') H).
      assert (trans' !! k = Some v).
      {
        rewrite /trans_preserve_slice in Heq.
        rewrite map_filter_insert_True // in Heq.
        assert (filter
                  (λ kv : Addr * (VMID * VMID * gset PID * transaction_type * bool),
                      kv.2.1.1.1.1 = i ∧ kv.2.1.1.1.2 = j) trans' !! k = Some v).
        rewrite -Heq lookup_insert //.
        rewrite map_filter_lookup_Some in H0.
        destruct H0;done.
      }
      iSplit.
      iIntros "H".
      destruct (decide (v.1.2 = Donation)).
      rewrite big_sepFM_insert_True //.
      iApply big_sepFM_lookup_Some'. eauto.
      split;done.
      iDestruct "H" as "[$ ?]".
      iApply "IH";done.
      rewrite big_sepFM_insert_False //.
      2: intros [_ ?];done.
      iApply big_sepFM_delete_False.
      eauto. intros [_ ?];done.
      by iApply "IH".
      iIntros "H".
      destruct (decide (v.1.2 = Donation)).
      rewrite big_sepFM_insert_True //.
      iDestruct (big_sepFM_lookup_Some with "H") as "[$ H]". auto.
      split;done.
      by iApply "IH".
      rewrite big_sepFM_insert_False //.
      iApply "IH".
      iApply (big_sepFM_delete_False with "H").
      eauto. intros [_ ?];done.
      intros [_ ?];done.
    }
    {
      rewrite big_sepFM_insert_False //.
      2: intros [? _];done.
      assert (trans_preserve_slice i j m trans').
      {
        rewrite /trans_preserve_slice in Heq.
        rewrite /trans_preserve_slice.
        rewrite -Heq.
        rewrite map_filter_insert_False.
        2: intro;done.
        rewrite delete_notin //.
      }
      iSpecialize ("IH" $! (delete k trans') H0).
      iApply "IH".
    }
    Qed.

  Instance slice_retrievable_transaction_transferred_wf
    : SliceTransWf retrievable_transaction_transferred_slice.
  Proof.
    split.
    intros i j trans trans' Heq.
    rewrite /retrievable_transaction_transferred_slice /=.
    iInduction trans as [|k v m Hlk] "IH" using map_ind forall (trans' Heq).
    rewrite /trans_preserve_slice map_filter_empty in Heq.
    iSplit.
    {
      iIntros "_".
      symmetry in Heq.
      apply map_filter_empty_iff in Heq.
      iSplitL.
      iApply big_sepFM_False_weak.
      intros ? ? ? [? ?].
      efeed specialize Heq;eauto.
      iApply big_sepFM_False_weak.
      intros ? ? ? [? ?].
      efeed specialize Heq;eauto.
    }
    {
      iIntros "_".
      iSplitL; iApply big_sepFM_empty.
    }
    assert (trans_preserve_slice i j m (delete k trans')).
    {
      rewrite /trans_preserve_slice in Heq.
      rewrite /trans_preserve_slice.
      destruct (decide (v.1.1.1.1 = i ∧ v.1.1.1.2 = j)).
      rewrite map_filter_insert_True // in Heq.
      rewrite map_filter_delete.
      rewrite -Heq.
      rewrite delete_insert //.
      rewrite map_filter_lookup_None;left;done.
      rewrite map_filter_insert_False // in Heq.
      rewrite map_filter_delete in Heq.
      rewrite map_filter_delete.
      rewrite -Heq.
      rewrite delete_idemp.
      rewrite -map_filter_delete.
      rewrite delete_notin //.
    }
    destruct (decide ((v.1.1.1.1 = i ∧ v.1.1.1.2 = j))).
    {
      iSpecialize ("IH" $! (delete k trans') H).
      assert (trans' !! k = Some v).
      {
        rewrite /trans_preserve_slice in Heq.
        rewrite map_filter_insert_True // in Heq.
        assert (filter
                  (λ kv : Addr * (VMID * VMID * gset PID * transaction_type * bool),
                      kv.2.1.1.1.1 = i ∧ kv.2.1.1.1.2 = j) trans' !! k = Some v).
        rewrite -Heq lookup_insert //.
        rewrite map_filter_lookup_Some in H0.
        destruct H0;done.
      }
      iDestruct "IH" as "[IH1 IH2]".
      iSplit.
      {
        iIntros "H".
        destruct (decide (v.2 = false)).
        rewrite big_sepFM_insert_True //.
        rewrite big_sepFM_insert_True //.
        iDestruct "H" as "[[k H1] [k' H2]]".
        iDestruct ("IH1" with "[$H1 $H2]") as "[H1 H2]".
        iSplitL "k H1".
        iApply big_sepFM_lookup_Some'. eauto. done. iFrame.
        iApply big_sepFM_lookup_Some'. eauto. done. iFrame.
        rewrite big_sepFM_insert_True //.
        iDestruct "H" as "[[k H1] H2]".
        rewrite big_sepFM_insert_False //.
        2: intros [_ ?];done.
        iDestruct ("IH1" with "[$H1 $H2]") as "[H1 H2]".
        iSplitL "k H1".
        iApply big_sepFM_lookup_Some'. eauto. done. iFrame.
        iApply big_sepFM_delete_False. eauto. intros [_ ?]. done. iFrame.
      }
      {
      iIntros "H".
      iDestruct "H" as "[H1 H2]".
      destruct (decide (v.2 = false)).
      rewrite big_sepFM_insert_True //.
      rewrite big_sepFM_insert_True //.
      iDestruct (big_sepFM_lookup_Some with "H1") as "[$ H1]". auto. done.
      iDestruct (big_sepFM_lookup_Some with "H2") as "[$ H2]". auto. done.
      iApply "IH2". iFrame.
      rewrite big_sepFM_insert_True //.
      rewrite big_sepFM_insert_False //.
      2: intros [_ ?];done.
      iDestruct (big_sepFM_lookup_Some with "H1") as "[$ H1]". auto. done.
      iDestruct (big_sepFM_delete_False with "H2") as "H2". auto. done. intros [_ ?];done.
      iApply "IH2".
      iFrame.
      }
    }
    {
      rewrite big_sepFM_insert_False //.
      rewrite big_sepFM_insert_False //.
      2: intros [? _];done.
      assert (trans_preserve_slice i j m trans').
      {
        rewrite /trans_preserve_slice in Heq.
        rewrite /trans_preserve_slice.
        rewrite -Heq.
        rewrite map_filter_insert_False.
        2: intro;done.
        rewrite delete_notin //.
      }
      iSpecialize ("IH" $! (delete k trans') H0).
      iApply "IH".
    }
  Qed.

  (* almost same proof! *)
  Instance slice_transferred_memory_pages_wf
    : SliceTransWf transferred_memory_slice.
  Proof.
    split.
    intros i j trans trans' Heq.
    rewrite /transferred_memory_slice /=.
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
    assert (trans_preserve_slice i j m (delete k trans')).
    {
      rewrite /trans_preserve_slice in Heq.
      rewrite /trans_preserve_slice.
      destruct (decide (v.1.1.1.1 = i ∧ v.1.1.1.2 = j)).
      rewrite map_filter_insert_True // in Heq.
      rewrite map_filter_delete.
      rewrite -Heq.
      rewrite delete_insert //.
      rewrite map_filter_lookup_None;left;done.
      rewrite map_filter_insert_False // in Heq.
      rewrite map_filter_delete in Heq.
      rewrite map_filter_delete.
      rewrite -Heq.
      rewrite delete_idemp.
      rewrite -map_filter_delete.
      rewrite delete_notin //.
    }
    destruct (decide ((v.1.1.1.1 = i ∧ v.1.1.1.2 = j))).
    {
      iSpecialize ("IH" $! (delete k trans') H).
      assert (trans' !! k = Some v).
      {
        rewrite /trans_preserve_slice in Heq.
        rewrite map_filter_insert_True // in Heq.
        assert (filter
                  (λ kv : Addr * (VMID * VMID * gset PID * transaction_type * bool),
                      kv.2.1.1.1.1 = i ∧ kv.2.1.1.1.2 = j) trans' !! k = Some v).
        rewrite -Heq lookup_insert //.
        rewrite map_filter_lookup_Some in H0.
        destruct H0;done.
      }
      iSplit.
      iIntros "H".
      destruct (decide (¬ ((k, v).2.2 = true ∧ (k, v).2.1.2 = Lending))).
      rewrite big_sepFM_insert_True //.
      iApply big_sepFM_lookup_Some'. eauto.
      split;done.
      iDestruct "H" as "[$ ?]".
      iApply "IH";done.
      rewrite big_sepFM_insert_False //.
      2: intros [_ ?];done.
      iApply big_sepFM_delete_False.
      eauto. intros [_ ?];done.
      by iApply "IH".
      iIntros "H".
      destruct (decide (¬ ((k, v).2.2 = true ∧ (k, v).2.1.2 = Lending))).
      rewrite big_sepFM_insert_True //.
      iDestruct (big_sepFM_lookup_Some with "H") as "[$ H]". eauto.
      split;done.
      by iApply "IH".
      rewrite big_sepFM_insert_False //.
      iApply "IH".
      iApply (big_sepFM_delete_False with "H").
      eauto. intros [_ ?];done.
      intros [_ ?];done.
    }
    {
      rewrite big_sepFM_insert_False //.
      2: intros [? _];done.
      assert (trans_preserve_slice i j m trans').
      {
        rewrite /trans_preserve_slice in Heq.
        rewrite /trans_preserve_slice.
        rewrite -Heq.
        rewrite map_filter_insert_False.
        2: intro;done.
        rewrite delete_notin //.
      }
      iSpecialize ("IH" $! (delete k trans') H0).
      iApply "IH".
    }
  Qed.

  Global Instance slice_transfer_all_wf : SliceTransWf slice_transfer_all.
  Proof.
    rewrite /slice_transfer_all /=. apply _.
  Qed.

  Global Instance slice_transfer_all_timeless i j trans: Timeless (slice_transfer_all trans i j).
  Proof.
    rewrite /slice_transfer_all /=. apply _.
  Qed.

  (* Global Instance slice_rxs_wf_sep Φ1 Φ2: *)
  (*   SliceRxsWf Φ1 -> *)
  (*   SliceRxsWf Φ2 -> *)
  (*   SliceRxsWf (λ trans i j, ((Φ1 trans i j) :iProp Σ) ∗ ((Φ2 trans i j) :iProp Σ))%I. *)
  (* Proof. *)
  (*   intros. *)
  (*   split. *)
  (*   { *)
  (*     intros. *)
  (*     rewrite (slice_rxs_empty Φ1) //. *)
  (*     rewrite (slice_rxs_empty Φ2) //. *)
  (*     iSplit;done. *)
  (*   } *)
  (*   { *)
  (*     intros. *)
  (*     rewrite (slice_rxs_sym Φ1) //. *)
  (*     rewrite (slice_rxs_sym Φ2) //. *)
  (*   } *)
  (* Qed. *)

  Lemma slice_preserve_except i s {Φ : _ -> _ -> _ -> iProp Σ} `{!SliceTransWf Φ} trans trans':
    except i trans = except i trans' ->
    big_sepSS_except s i (Φ trans) ⊣⊢ big_sepSS_except s i (Φ trans').
  Proof.
    iIntros (Heq).
    rewrite /big_sepSS_except. rewrite /big_sepSS.
    iApply big_sepS_proper. iIntros (? Hin).
    iApply big_sepS_proper. iIntros (? Hin').
    iApply (slice_trans_valid Φ).
    rewrite /trans_preserve_slice.
    assert (x ≠ i). set_solver + Hin.
    assert (x0 ≠ i). set_solver + Hin'.
    rewrite /except in Heq.
    apply map_eq. intros.
    destruct (filter
    (λ kv : Addr * (VMID * VMID * gset PID * transaction_type * bool),
       kv.2.1.1.1.1 = x ∧ kv.2.1.1.1.2 = x0) trans !! i0) eqn:Hlk.
    symmetry.
    rewrite map_filter_lookup_Some in Hlk.
    destruct Hlk as [Hlk [? ?]].
    assert (filter (λ kv : Addr * transaction, ¬ (kv.2.1.1.1.1 = i ∨ kv.2.1.1.1.2 = i))
          trans !! i0 = Some t).
    rewrite map_filter_lookup_Some.
    split;first done.
    intros [? |?];subst i;[subst x|subst x0];done.
    rewrite Heq in H3.
    rewrite map_filter_lookup_Some in H3.
    destruct H3 as [Hlk' nP].
    rewrite map_filter_lookup_Some.
    split;first done. split;done.
    symmetry.
    rewrite map_filter_lookup_None in Hlk.
    rewrite map_filter_lookup_None.
    destruct Hlk as [Hlk | ?].
    rewrite -(delete_notin trans i0 ) //in Heq.
    rewrite map_filter_delete in Heq.
    assert (filter (λ kv : Addr * transaction, ¬ (kv.2.1.1.1.1 = i ∨ kv.2.1.1.1.2 = i))
          trans' !! i0 = None).
    rewrite -Heq lookup_delete //.
    rewrite map_filter_lookup_None in H1.
    destruct H1.
    { left;done. }
    {
      right. intros.
      specialize (H1 x1 H2).
      intros []. simpl in *. apply H1.
      intros [|]. rewrite H5 in H3. done. rewrite H5 in H4. done.
    }
    right. intros. intros [].
    assert (filter (λ kv : Addr * transaction, ¬ (kv.2.1.1.1.1 = i ∨ kv.2.1.1.1.2 = i))
          trans' !! i0 = Some x1).
    rewrite map_filter_lookup_Some.
    split;first done.
    intros [? |?];subst i;[subst x|subst x0];done.
    rewrite -Heq in H5.
    rewrite map_filter_lookup_Some in H5.
    destruct H5.
    specialize (H1 x1 H5).
    apply H1.
    split;done.
  Qed.

  Lemma elem_of_set_of_vmids i:
    i ∈ set_of_vmids.
  Proof.
    rewrite /set_of_vmids.
    rewrite elem_of_list_to_set.
    rewrite elem_of_list_In.
    apply in_list_of_vmids.
  Qed.

  Lemma slice_trans_unify (Φ: _ -> _ -> _ -> iProp Σ) `{Hwf:!SliceTransWf Φ} trans trans' i:
    dom (only i trans') ## dom (except i trans) ->
    big_sepSS_except set_of_vmids i (Φ trans) ∗
    big_sepSS_singleton set_of_vmids i (Φ (only i trans' ∪ trans))
    ⊢  big_sepSS set_of_vmids (Φ (only i trans' ∪ trans)).
  Proof.
    iIntros (Hdisj) "(except & only)".
    assert (set_of_vmids = (set_of_vmids ∖ {[i]}) ∪ {[i]}).
    pose proof (elem_of_set_of_vmids i). rewrite difference_union_L. set_solver + H.
    rewrite H.
    iApply big_sepSS_union_singleton. set_solver +.
    rewrite -H. iSplitL "except".
    {
      iApply (slice_preserve_except with "except").
      symmetry.
      rewrite -except_only_union //.
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

  Lemma transaction_pagetable_entries_transferred_only_equiv i v (trans: gmap Addr transaction):
    trans_neq trans ->
    i ≠ v ->
    (transaction_pagetable_entries_transferred_slice trans i v) ∗ (transaction_pagetable_entries_transferred_slice trans v i) ⊣⊢
      transaction_pagetable_entries_transferred i (only v trans).
  Proof.
    intros ? Hne.
    rewrite /only.
    rewrite /transaction_pagetable_entries_transferred_slice.
    rewrite /transaction_pagetable_entries_transferred.
    rewrite big_sepFM_filter.
    rewrite (big_sepFM_iff_weak (P:=(λ x : Addr * transaction,
          (((x.2.1.1.1.1 = i ∨ x.2.1.1.1.2 = i) ∧ x.2.1.2 = Donation)
           ∧ (x.2.1.1.1.1 = v ∨ x.2.1.1.1.2 = v))%type))
              (Q:= (λ x : Addr * transaction,
          (((x.2.1.1.1.1 = i ∧ x.2.1.1.1.2 = v) ∧ x.2.1.2 = Donation)
           ∨ ((x.2.1.1.1.1 = v ∧ x.2.1.1.1.2 = i) ∧ x.2.1.2 = Donation))%type))).
    rewrite big_sepFM_split_lor_weak //.
    intros ???.
    specialize (H _ _ H0).
    intros [[[] ?] [[] ?]].
    subst i. simpl in H. simpl in H5. done.
    intros ???.
    split.
    intros [[] ?].
    destruct H1.
    left.
    destruct H3.
    rewrite H1 // in H3.
    split;auto.
    destruct H3.
    right;done.
    rewrite H1 // in H3.
    intros [[[] ?]| [[] ?]].
    split;auto.
    split;auto.
  Qed.

  Lemma transaction_pagetable_entries_transferred_equiv i (trans: gmap Addr transaction):
    trans_neq trans ->
    big_sepSS_singleton set_of_vmids i (transaction_pagetable_entries_transferred_slice trans) ⊣⊢
      transaction_pagetable_entries_transferred i trans.
  Proof.
    intros Hfalse.
    rewrite /transaction_pagetable_entries_transferred.
    rewrite big_sepFM_trans_split //.
    rewrite /big_sepSS_singleton.
    pose proof (elem_of_set_of_vmids i).
    case_decide; last done. clear H0.
    assert (transaction_pagetable_entries_transferred_slice trans i i ⊣⊢ emp%I) as Hemp.
    rewrite /transaction_pagetable_entries_transferred_slice.
    iSplit;iIntros "_"; first done.
    iApply big_sepFM_False_weak.
    intros ??? [[] _]. specialize (Hfalse _ _ H0). subst i. simpl in Hfalse;done.
    rewrite <-sep_emp. rewrite -Hemp. rewrite sep_comm. rewrite sep_assoc.
    rewrite -(big_sepS_singleton (λ x, transaction_pagetable_entries_transferred_slice
                                         trans i x ∗
   transaction_pagetable_entries_transferred_slice trans x i)%I i).
   rewrite -big_sepS_union;last set_solver+.
    assert ({[i]} ∪ set_of_vmids ∖ {[i]} = set_of_vmids) as ->. rewrite union_comm_L.
    rewrite difference_union_L. set_solver.
    rewrite big_sepS_sep /=.
    iSplit.
    iIntros "(H1 & H2)";iSplitL "H1";
      first iApply big_sepFM_big_sepS_trans_sndr.
    iApply big_sepS_proper.
    2: iExact "H1".
    intros. iApply big_sepFM_iff.
    intros. split;intros [[] []];split;eauto.
    iApply big_sepFM_big_sepS_trans_rcvr.
    iApply big_sepS_proper.
    2: iExact "H2".
    intros. iApply big_sepFM_iff.
    intros. split;intros [[] []];split;eauto.
    iIntros "[H1 H2]". iSplitL "H1".
    iDestruct (big_sepFM_big_sepS_trans_sndr with "H1") as "H1". done.
    iApply big_sepFM_big_sepS_trans_rcvr. done.
   Qed.

  Lemma transaction_pagetable_entries_transferred_split i j trans:
    transaction_pagetable_entries_transferred i trans ⊣⊢
    transaction_pagetable_entries_transferred i (only j trans) ∗
    transaction_pagetable_entries_transferred i (except j trans).
  Proof.
    rewrite /only /except.
    rewrite /transaction_pagetable_entries_transferred.
    rewrite 2?big_sepFM_filter.
    rewrite -big_sepFM_split_lor.
    2: intros ? [[] []];done.
    iApply big_sepFM_iff.
    intros. split.
    intros [? ?].
    destruct (decide (kv.2.1.1.1.1 = j ∨ kv.2.1.1.1.2 = j));[left|right];done.
    intros [[? _]|[? _]];done.
  Qed.

  Lemma retrievable_transaction_transferred_only_equiv i v (trans: gmap Addr transaction):
    trans_neq trans ->
    i ≠ v ->
    (retrievable_transaction_transferred_slice trans i v) ∗ (retrievable_transaction_transferred_slice trans v i) ⊣⊢
      retrievable_transaction_transferred i (only v trans).
  Proof.
    intros ? Hne.
    rewrite /only.
    rewrite /retrievable_transaction_transferred_slice.
    rewrite /retrievable_transaction_transferred.
    rewrite 2!big_sepFM_filter.
    rewrite (big_sepFM_iff_weak (P:=(λ x : Addr * transaction,
          (((x.2.1.1.1.1 = i ∨ x.2.1.1.1.2 = i) ∧ x.2.2 = false)
           ∧ (x.2.1.1.1.1 = v ∨ x.2.1.1.1.2 = v))%type))
              (Q:= (λ x : Addr * transaction,
          (((x.2.1.1.1.1 = i ∧ x.2.1.1.1.2 = v) ∧ x.2.2 = false)
           ∨ ((x.2.1.1.1.1 = v ∧ x.2.1.1.1.2 = i) ∧ x.2.2 = false))%type))).
    rewrite big_sepFM_split_lor_weak //.
    rewrite (big_sepFM_iff_weak (P:=(λ x : Addr * transaction,
          ((x.2.1.1.1.1 = i ∨ x.2.1.1.1.2 = i)
           ∧ (x.2.1.1.1.1 = v ∨ x.2.1.1.1.2 = v))%type))
              (Q:= (λ x : Addr * transaction,
          ((x.2.1.1.1.1 = i ∧ x.2.1.1.1.2 = v)
           ∨ (x.2.1.1.1.1 = v ∧ x.2.1.1.1.2 = i))%type))).
    rewrite big_sepFM_split_lor_weak //.
    rewrite -2?sep_assoc //. f_equiv.
    rewrite sep_comm -sep_assoc. f_equiv. rewrite sep_comm //.
    intros ???. specialize (H _ _ H0).
    intros [[[] ?] [[] ?]]. subst v. simpl in H. simpl in H2. done.
    intros ???. split.
    intros [[] ?].
    destruct H1. left. destruct H2. rewrite H1 // in Hne. split;auto.
    destruct H2. right;done. rewrite -H1 // in Hne.
    intros [[[] ?]| [[] ?]]. split;auto. split;auto.
    intros ???. specialize (H _ _ H0).
    intros [[[] ?] [[] ?]].
    subst v. simpl in H. simpl in H4. done.
    intros ???. split.
    intros [[] ?].
    destruct H1. left. destruct H3. rewrite H1 // in H3. split;auto.
    destruct H3. right; done. rewrite H1 // in H3.
    intros [[[] ?]| [[] ?]]. split;auto. split;auto.
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
    pose proof (elem_of_set_of_vmids i).
    case_decide; last done. clear H0.
    assert (retrievable_transaction_transferred_slice trans i i ⊣⊢ emp%I) as Hemp.
    iSplit;iIntros "_"; first done.
    rewrite /retrievable_transaction_transferred_slice.
    iSplitL; iApply big_sepFM_False_weak.
    intros ??? [[]]. specialize (Hneq _ _ H0). simpl in Hneq;done.
    intros ??? [[] _]. subst i. specialize (Hneq _ _ H0). simpl in Hneq;done.
    rewrite <-sep_emp. rewrite -Hemp. rewrite sep_comm.
    rewrite sep_assoc.
    rewrite -(big_sepS_singleton (λ x, retrievable_transaction_transferred_slice trans i x ∗
                                         retrievable_transaction_transferred_slice trans x i)%I i).
    rewrite -big_sepS_union;last set_solver.
    assert ({[i]} ∪ set_of_vmids ∖ {[i]} = set_of_vmids) as ->. rewrite union_comm_L.
    rewrite difference_union_L. set_solver.
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

  Lemma retrievable_transaction_transferred_split i j trans:
    retrievable_transaction_transferred i trans ⊣⊢
    retrievable_transaction_transferred i (only j trans) ∗
    retrievable_transaction_transferred i (except j trans).
  Proof.
    rewrite /only /except.
    rewrite /retrievable_transaction_transferred.
    rewrite 4?big_sepFM_filter.
    rewrite -sep_assoc.
    rewrite (sep_comm (big_sepFM trans
    (λ x : Addr * transaction, (((x.2.1.1.1.1 = i ∨ x.2.1.1.1.2 = i) ∧ x.2.2 = false) ∧ (x.2.1.1.1.1 = j ∨ x.2.1.1.1.2 = j))%type)
    (λ (k : Addr) (v : transaction), k -{1 / 4}>t v.1 ∗ k -{1 / 2}>re v.2)%I)).
    rewrite -sep_assoc.
    rewrite -big_sepFM_split_lor.
    rewrite sep_assoc.
    rewrite -big_sepFM_split_lor.
    2: intros ? [[] []];done.
    2: intros ? [[] []];done.
    f_equiv.
    apply big_sepFM_iff.
    intros. split.
    intros ?.
    destruct (decide (kv.2.1.1.1.1 = j ∨ kv.2.1.1.1.2 = j));[left|right];done.
    intros [[? _]|[? _]];done.
    apply big_sepFM_iff.
    intros. split.
    intros [? ?].
    destruct (decide (kv.2.1.1.1.1 = j ∨ kv.2.1.1.1.2 = j));[right|left];done.
    intros [[? _]|[? _]];done.
  Qed.

  Lemma transferred_memory_only_equiv i v trans:
  trans_neq trans ->
  trans_ps_disj trans ->
  i ≠ v ->
  transferred_memory_slice trans v i ∗ transferred_memory_slice trans i v ⊣⊢
    ∃ mem, memory_pages (transferred_memory_pages i (only v trans)) mem.
  Proof.
    iIntros (Hneq Hdisj Hneqi).
    rewrite /transferred_memory_slice.
    rewrite -big_sepFM_split_lor.
    2: { intros ? [[[] _] [[] _]]. apply Hneqi. subst i v. done. }
    rewrite /only /transferred_memory_pages.
    rewrite map_filter_filter.
    simpl.
    iInduction trans as [|h tran m Hlk] "IH" using map_ind.
    {
      iSplit; iIntros "H".
      iExists ∅.
      rewrite /transferred_memory_pages.
      rewrite map_filter_empty.
      rewrite pages_in_trans_empty //.
      iApply memory_pages_empty.
      iApply big_sepFM_empty.
    }
    {
      rewrite /trans_neq map_Forall_insert // in Hneq.
      destruct Hneq as [Hneq Hneq'].
      apply trans_ps_disj_insert_2 in Hdisj;auto.
      destruct Hdisj as [Hdisj Hdisj'].
      iSpecialize ("IH" $! Hneq' Hdisj').
      destruct (decide((tran.1.1.1.1 = v ∧ tran.1.1.1.2 = i) ∧ ¬ (tran.2 = true ∧ tran.1.2 = Lending)
               ∨ (tran.1.1.1.1 = i ∧ tran.1.1.1.2 = v) ∧ ¬ (tran.2 = true ∧ tran.1.2 = Lending))).
      {
        destruct (decide ((tran.1.1.1.1 = v ∧ tran.1.1.1.2 = i) ∧ ¬ (tran.2 = true ∧ tran.1.2 = Lending))).
        {
          rewrite big_sepFM_insert_True //=.
          (* 2: { destruct a;auto. } *)
          rewrite map_filter_insert_True //.
          rewrite pages_in_trans_insert //.
          2: { rewrite map_filter_lookup_None. left;done. }
          rewrite memory_pages_split_union'.
          iSplit; iIntros "[$ ?]"; by iApply "IH".
          set s := (pages_in_trans (filter (λ '(_, x), ((x.1.1.1.1 = i ∨ x.1.1.1.2 = i) ∧ ¬ (x.2 = true ∧ x.1.2 = Lending)) ∧ (x.1.1.1.1 = v ∨ x.1.1.1.2 = v)) m)).
          assert (s ⊆ pages_in_trans m).
          apply pages_in_trans_subseteq.
          apply map_filter_subseteq.
          set_solver + Hdisj H.
          destruct a as [[] ?]. split;auto. 
        }
        {
          rewrite big_sepFM_insert_True //=.
          rewrite map_filter_insert_True //.
          rewrite pages_in_trans_insert //.
          2: { rewrite map_filter_lookup_None. left;done. }
          rewrite memory_pages_split_union'.
          iSplit. iIntros "[? ?]". iFrame. iApply "IH". iFrame.
          iIntros "[? ?]". iFrame. iApply "IH". iFrame.
          set s := (pages_in_trans (filter (λ '(_, x), ((x.1.1.1.1 = i ∨ x.1.1.1.2 = i) ∧ ¬ (x.2 = true ∧ x.1.2 = Lending)) ∧ (x.1.1.1.1 = v ∨ x.1.1.1.2 = v)) m)).
          assert (s ⊆ pages_in_trans m).
          apply pages_in_trans_subseteq.
          apply map_filter_subseteq.
          set_solver + Hdisj H.
          destruct o as [|];first done.
          destruct H as [[] ?]. split;auto. 
        }
      }
      {
        rewrite big_sepFM_insert_False //=.
        rewrite map_filter_insert_False //.
        rewrite delete_notin //.
          intros [[[] ?] []].
          rewrite -H -H1 // in Hneqi.
          apply n. right;split;auto.
          apply n. left;split;auto.
          rewrite -H -H1 // in Hneqi.
      }
    }
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
    rewrite /big_sepSS_singleton.
    pose proof (elem_of_set_of_vmids i).
    case_decide; last done. clear H0.
    assert (transferred_memory_slice trans i i⊣⊢ emp%I) as Hemp.
    iSplit;iIntros "_"; first done.
    rewrite /transferred_memory_slice.
    iApply big_sepFM_False_weak.
    intros ??? [[]]. specialize (Hneq _ _ H0). subst i. simpl in Hneq;done.
    rewrite <-sep_emp. rewrite -Hemp. rewrite sep_comm. rewrite sep_assoc.
    rewrite -(big_sepS_singleton (λ x, transferred_memory_slice trans i x ∗
                                         transferred_memory_slice trans x i)%I i).
    rewrite -big_sepS_union;last set_solver.
    assert ({[i]} ∪ set_of_vmids ∖ {[i]} = set_of_vmids) as ->. rewrite union_comm_L.
    rewrite difference_union_L. set_solver.
    clear Hemp.
    iInduction trans as [|h tran m Hlk] "IH" using map_ind.
    {
      iSplit; iIntros "H".
      iExists ∅.
      rewrite /transferred_memory_pages.
      rewrite map_filter_empty.
      rewrite pages_in_trans_empty //.
      iApply memory_pages_empty.
      rewrite big_sepS_proper.
      erewrite big_sepS_emp. done.
      intros. iSplit;auto.
      iIntros "_".
      rewrite /transferred_memory_slice.
      iSplitL; iApply big_sepFM_empty.
    }
    {
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
          set_solver + Hdisj H0.
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
          set_solver + Hdisj H0.
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

  Lemma transferred_memory_split i v trans:
    trans_neq trans ->
    trans_ps_disj trans ->
    (∃ mem, memory_pages (transferred_memory_pages i trans) mem)
    ⊣⊢ (∃ mem, memory_pages (transferred_memory_pages i (only v trans)) mem) ∗
    ∃ mem, memory_pages (transferred_memory_pages i (except v trans)) mem.
  Proof.
    iIntros (Hneq Hdisj).
    rewrite /transferred_memory_pages.
    pose proof (only_except_disjoint v trans).
    pose proof (map_filter_subseteq (λ kv : Addr * (leibnizO VMID * leibnizO VMID * gset PID * transaction_type * bool),
          (kv.2.1.1.1.1 = i ∨ kv.2.1.1.1.2 = i) ∧ ¬ (kv.2.2 = true ∧ kv.2.1.2 = Lending))).
    pose proof (H0 (only v trans)).
    pose proof (H0 (except v trans)).
    apply subseteq_dom in H1.
    apply subseteq_dom in H2.
    rewrite -memory_pages_split_union'.
    rewrite -pages_in_trans_union.
    rewrite -map_filter_union.
    rewrite only_except_union //.
    rewrite map_disjoint_dom //.
    set_solver + H H1 H2.
    apply (pages_in_trans_disj _ _ trans);auto.
    transitivity (only v trans). done. apply only_subseteq.
    transitivity (except v trans). done. apply except_subseteq.
    set_solver + H H1 H2.
  Qed.

  Lemma slice_transfer_all_equiv k (trans: gmap Addr transaction) Φ:
      (∀ i j trans, (i = k ∨ j = k) -> Φ trans i j ⊣⊢ slice_transfer_all trans i j) ->
      big_sepSS_singleton set_of_vmids k (Φ trans) ⊣⊢ big_sepSS_singleton set_of_vmids k (slice_transfer_all trans).
  Proof.
    intros HΦ.
    rewrite /big_sepSS_singleton.
    pose proof (elem_of_set_of_vmids k).
    case_decide; last done. clear H0 H.
    rewrite (HΦ k k);last (left;done).
    iSplit.
    iIntros "[$ H]".
    iApply (big_sepS_proper with "H").
    intros.
    rewrite -(HΦ k x);last (left;done).
    rewrite -(HΦ x k);last (right;done).
    done.
    iIntros "[$ H]".
    iApply (big_sepS_proper with "H").
    intros.
    rewrite -(HΦ k x);last (left;done).
    rewrite -(HΦ x k);last (right;done).
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
    pose proof (elem_of_set_of_vmids k).
    case_decide; last done. clear H0 H.
    rewrite !big_sepS_sep.
    rewrite -transaction_pagetable_entries_transferred_equiv //.
    rewrite -retrievable_transaction_transferred_equiv //.
    rewrite -transferred_memory_equiv //.
    rewrite /big_sepSS_singleton.
    pose proof (elem_of_set_of_vmids k).
    case_decide; last done. clear H0 H.
    rewrite !big_sepS_sep.
    iSplit.
    iIntros "(? & ($ & $ & $) & ($ & $ & $))".
    rewrite /slice_transfer_all //.
    iIntros "([? [$ $]] & [? [$ $]] & [? [$ $]])".
    rewrite /slice_transfer_all. iFrame.
  Qed.

  Lemma slice_transfer_all_equiv_later k (trans: gmap Addr transaction) Φ:
      (∀ i j trans, (i = k ∨ j = k) -> Φ trans i j ⊣⊢ slice_transfer_all trans i j) ->
      big_sepSS_singleton set_of_vmids k (λ i j, ▷ Φ trans i j) ⊣⊢ big_sepSS_singleton set_of_vmids k (λ i j, ▷ slice_transfer_all trans i j).
  Proof.
    intros HΦ.
    rewrite /big_sepSS_singleton.
    pose proof (elem_of_set_of_vmids k).
    case_decide; last done. clear H0 H.
    rewrite (HΦ k k);last (left;done).
    iSplit.
    iIntros "[$ H]".
    iApply (big_sepS_proper with "H").
    intros.
    rewrite -(HΦ k x);last (left;done).
    rewrite -(HΦ x k);last (right;done).
    done.
    iIntros "[$ H]".
    iApply (big_sepS_proper with "H").
    intros.
    rewrite -(HΦ k x);last (left;done).
    rewrite -(HΦ x k);last (right;done).
    done.
  Qed.

  Lemma transferred_only_equiv_later k (trans: gmap Addr transaction) Φ:
      (∀ i j trans, (i = k ∨ j = k) -> Φ trans i j ⊣⊢ slice_transfer_all trans i j) ->
      trans_neq trans ->
      trans_ps_disj trans ->
      big_sepSS_singleton set_of_vmids k (λ i j, ▷ Φ trans i j) ⊣⊢
      ▷ (transaction_pagetable_entries_transferred k trans ∗
      retrievable_transaction_transferred k trans ∗
      (∃ mem_trans, memory_pages (transferred_memory_pages k trans) mem_trans)).
  Proof.
    intros HΦ Hneq Hdisj.
    rewrite slice_transfer_all_equiv_later //.
    rewrite /big_sepSS_singleton.
    pose proof (elem_of_set_of_vmids k).
    case_decide; last done. clear H0 H.
    rewrite !big_sepS_sep.
    rewrite -transaction_pagetable_entries_transferred_equiv //.
    rewrite -retrievable_transaction_transferred_equiv //.
    rewrite -transferred_memory_equiv //.
    rewrite /big_sepSS_singleton.
    pose proof (elem_of_set_of_vmids k).
    case_decide; last done. clear H0 H.
    iSplit.
    iIntros "(? & H)".
    iNext.
    rewrite !big_sepS_sep.
    iDestruct "H" as "[($&$&$) ($&$&$)]".
    rewrite /slice_transfer_all //.
    iIntros "(H1 & H2)".
    rewrite -2?big_sepS_later.
    rewrite -2?later_sep.
    iNext.
    rewrite !big_sepS_sep.
    iDestruct "H1" as "[$ [$ $]]".
    iDestruct "H2" as "[[$ [$ $]] [$ [$ $]]]".
  Qed.

  Lemma rx_states_split_zero {Φ_r} rxs:
      is_total_gmap rxs ->
      (∀ os, match os with
              | None => True
              | _ => Φ_r V0 os V0 ⊣⊢ slice_rx_state V0 os
              end) ->
      rx_states_global rxs ∗
      rx_states_transferred Φ_r rxs
      ⊢
      rx_states_global (delete V0 rxs) ∗
      rx_states_transferred Φ_r (delete V0 rxs) ∗
      rx_state_get V0 rxs ∗
      ∃ p_rx, RX@V0 := p_rx ∗
      (∃ mem_rx, memory_page p_rx mem_rx).
  Proof.
    iIntros (Htotal Hequiv) "(global & transferred)".
    rewrite /rx_states_global /rx_states_transferred.
    pose proof (Htotal V0) as [rs Hlookup_rs].
    iDestruct (big_sepM_delete with "global") as "[rs global]";eauto.
    iDestruct (big_sepM_delete with "transferred") as "[t transferred]";eauto.
    iFrame.
    destruct rs.
    {
      iDestruct (Hequiv  (Some p) with "t") as "[R ( % & ? & ?)]".
      rewrite /rx_state_match /slice_rx_state /=.
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

  Lemma rx_states_split_zero_later {Φ_r} rxs:
      is_total_gmap rxs ->
      (∀ os, match os with
              | None => True
              | _ => Φ_r V0 os V0 ⊣⊢ slice_rx_state V0 os
              end) ->
      rx_states_global rxs ∗
      ▷ rx_states_transferred Φ_r rxs
      ⊢
      rx_states_global (delete V0 rxs) ∗
      ▷ rx_states_transferred Φ_r (delete V0 rxs) ∗
      ▷ rx_state_get V0 rxs ∗
      ▷ ∃ p_rx, RX@V0 := p_rx ∗
      (∃ mem_rx, memory_page p_rx mem_rx).
  Proof.
    iIntros (Htotal Hequiv) "(global & transferred)".
    rewrite /rx_states_global /rx_states_transferred.
    pose proof (Htotal V0) as [rs Hlookup_rs].
    iDestruct (big_sepM_delete with "global") as "[rs global]";eauto.
    iDestruct (big_sepM_delete with "transferred") as "[t transferred]";eauto.
    iFrame.
    destruct rs.
    {
      iDestruct (Hequiv (Some p) with "t") as "t".
      rewrite /rx_state_match /slice_rx_state /=.
      rewrite !later_sep.
      iDestruct ("t") as "(R & ?)".
      iSplitL "rs R".
      rewrite /rx_state_get.
      iIntros (?) "%Hlk".
      rewrite Hlookup_rs in Hlk.
      inversion Hlk.
      iApply (rx_state_split V0 _ (Some p)). iFrame.
      rewrite later_sep //.
      done.
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
      (∀ os, match os with
              | None => True
              | _ => Φ_r V0 os V0 ⊣⊢ slice_rx_state V0 os
              end) ->
      rx_states_global (delete V0 rxs) ∗
      rx_states_transferred Φ_r (delete V0 rxs) ∗
      rx_state_get V0 rxs ∗
      (∃ p_rx, RX@V0 := p_rx ∗
      (∃ mem_rx, memory_page p_rx mem_rx))
      ⊢
      rx_states_global rxs ∗
      rx_states_transferred Φ_r rxs.
  Proof.
    iIntros (Htotal Hequiv) "(global & transferred & rx_state & rx)".
    rewrite /rx_states_global /rx_states_transferred.
    pose proof (Htotal V0) as [rs Hlookup_rs].
    rewrite (big_sepM_delete _ rxs V0 rs);auto.
    iFrame "global".
    rewrite (big_sepM_delete _ rxs V0 rs);auto.
    iFrame "transferred".
    iDestruct ("rx_state" $! rs with "[]") as "rx_state". done.
    destruct rs.
    {
      rewrite /rx_state_match.
      iDestruct (rx_state_split with "rx_state") as "[$ ?]".
      rewrite (Hequiv (Some p)).
      rewrite /slice_rx_state.
      iFrame.
    }
    {
      rewrite /rx_state_match.
      iFrame.
    }
  Qed.

  Lemma rx_state_merge_zero_later {Φ_r} rxs:
      is_total_gmap rxs ->
      (∀ os, match os with
              | None => True
              | _ => Φ_r V0 os V0 ⊣⊢ slice_rx_state V0 os
              end) ->
      rx_states_global (delete V0 rxs) ∗
      ▷ rx_states_transferred Φ_r (delete V0 rxs) ∗
      rx_state_get V0 rxs ∗
      (∃ p_rx, RX@V0 := p_rx ∗
      (∃ mem_rx, memory_page p_rx mem_rx))
      ⊢
      rx_states_global rxs ∗
      ▷ rx_states_transferred Φ_r rxs.
  Proof.
    iIntros (Htotal Hequiv) "(global & transferred & rx_state & rx)".
    rewrite /rx_states_global /rx_states_transferred.
    pose proof (Htotal V0) as [rs Hlookup_rs].
    rewrite (big_sepM_delete _ rxs V0 rs);auto.
    iFrame "global".
    rewrite (big_sepM_delete _ rxs V0 rs);auto.
    iFrame "transferred".
    iDestruct ("rx_state" $! rs with "[]") as "rx_state". done.
    destruct rs.
    {
      rewrite /rx_state_match.
      iDestruct (rx_state_split with "rx_state") as "[$ ?]".
      rewrite (Hequiv (Some p)).
      rewrite /slice_rx_state.
      iFrame.
    }
    {
      rewrite /rx_state_match.
      iFrame.
      iNext. done.
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
      pose proof (@slice_rxs_sym _ _ Φ_r _ i (Some (f, v))).
      simpl in H0.
      rewrite H0 //.
    }
    {
      rewrite (slice_rxs_empty).
      iSplitL. iFrame "rs". done.
    }
  Qed.

  Lemma rx_states_split_later {Φ_r} `{!SliceRxsWf Φ_r} (i:VMID) rxs:
      (∀ i os,
         match os with
         | None => True
         | Some (_ ,k) => k = V0
        end ->
         Φ_r i os i ⊣⊢ Φ_r i os V0) ->
      is_total_gmap rxs ->
      rx_states_global rxs ∗
      ▷ rx_states_transferred Φ_r rxs
      ⊢
      rx_states_global (delete i rxs) ∗
      ▷ rx_states_transferred Φ_r (delete i rxs) ∗
      ▷ (∀ rs : option (Addr * VMID), ⌜rxs !! i = Some rs⌝ -∗ rx_state_match i rs ∗ Φ_r i rs i).
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
      pose proof (@slice_rxs_sym _ _ Φ_r _ i (Some (f, v))).
      simpl in H0.
      rewrite H0 //.
    }
    {
      rewrite (slice_rxs_empty).
      iSplitL. iFrame "rs". done.
    }
  Qed.

  Lemma rx_states_merge_yield {Φ_r} `{!SliceRxsWf Φ_r} v rxs rs:
    is_total_gmap rxs ->
    rx_state_match v rs ∗
    ▷ Φ_r v rs V0 ∗
    rx_states_global (delete v rxs) ∗
    ▷ rx_states_transferred Φ_r (delete v rxs) ⊢
    rx_states_global  (<[v := rs]> rxs) ∗
    ▷ rx_states_transferred Φ_r (<[v := rs]> rxs).
    Proof.
      iIntros (Htotal) "(rx_state & Φ & global & transferred)".
      rewrite /rx_states_global.
      rewrite big_sepM_insert_delete.
      iFrame.
      rewrite /rx_states_transferred.
      rewrite big_sepM_insert_delete.
      iFrame.
      destruct rs;done.
    Qed.

  (* XXX: to show equiv, we need rxs!! j = Some None (and more?) *)
  Lemma rx_states_merge_send {Φ_r} `{!SliceRxsWf Φ_r} v rxs rs l j:
    is_total_gmap rxs ->
    rx_state_match v rs ∗
    ▷ Φ_r v rs V0 ∗
    ▷ Φ_r j (Some(l,v)) V0 ∗
    rx_states_global (<[j:= Some (l,v)]>(delete v rxs)) ∗
    ▷ rx_states_transferred Φ_r (delete v rxs) ⊢
    rx_states_global  (<[j:= Some (l,v)]>(<[v := rs]> rxs)) ∗
    ▷ rx_states_transferred Φ_r (<[j:= Some (l,v)]>(<[v := rs]> rxs)).
  Proof.
    iIntros (Htotal) "(rx_match & Φv & Φj & global & transferred)".
    rewrite /rx_states_global.
    rewrite big_sepM_insert_delete.
    rewrite big_sepM_insert_delete.
    iDestruct "global" as "[match_j global]".
    iAssert (⌜j ≠ v⌝)%I with "[match_j]" as "%Hneq".
    {
      iDestruct "match_j" as "[_ %]".
      simpl in H. done.
    }
    iFrame.
    rewrite delete_insert_ne //.
    rewrite big_sepM_insert_delete.
    rewrite delete_commute.
    iFrame.
    rewrite /rx_states_transferred.
    rewrite big_sepM_insert_delete.
    rewrite delete_insert_ne //.
    rewrite big_sepM_insert_delete.
    iFrame.
    specialize (Htotal j) as [? ?].
    rewrite (big_sepM_delete _ _ j).
    rewrite delete_commute //.
    iDestruct "transferred" as "[_ $]".
    destruct rs;done.
    rewrite lookup_delete_ne //.
  Qed.

End logrel_prim_extra.
