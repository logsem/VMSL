From iris.proofmode Require Import tactics.
From machine_program_logic.program_logic Require Import weakestpre.
From HypVeri.lang Require Import lang.
From HypVeri.algebra Require Import base base_extra mem pagetable trans.
From HypVeri.logrel Require Import logrel_prim.
From HypVeri Require Import proofmode.
From stdpp Require fin_map_dom.
Import uPred.

Section logrel_prim_extra.
  Context `{hypconst:HypervisorConstants}.
  Context `{hypparams:!HypervisorParameters}.
  Context `{vmG: !gen_VMG Σ}.

  (* Lemmas about relationships between transferred_all, transferred, and transferred_except *)
  Lemma transaction_pagetable_entries_transferred_split i trans:
    transaction_pagetable_entries_transferred_all trans ⊣⊢ transaction_pagetable_entries_transferred i trans ∗
                                                 transaction_pagetable_entries_transferred_except i trans.
  Proof. iApply (big_sepFM_split_decide). Qed.

  Lemma retrievable_transaction_transferred_split i trans:
   retrievable_transaction_transferred_all trans ⊣⊢ retrievable_transaction_transferred i trans ∗
                                                 retrievable_transaction_transferred_except i trans.
  Proof.
    rewrite /retrievable_transaction_transferred /retrievable_transaction_transferred_all /retrievable_transaction_transferred_except.
    iSplit.
    iIntros "(H1 & H2)".
    iDestruct (big_sepFM_split_decide (Q:= (λ kv, kv.2.1.1.1.2 = i ∨ kv.2.1.1.1.1 = i)) with "H1") as "[H11 H12]".
    rewrite (big_sepFM_iff (Q:= (λ kv, kv.2.1.1.1.2 = i ∨ kv.2.1.1.1.1 = i))). iFrame "H11".
    rewrite (big_sepFM_iff (Q:= (λ kv, ¬ (kv.2.1.1.1.2 = i ∨ kv.2.1.1.1.1 = i)))). iFrame "H12".
    iDestruct (big_sepFM_split_decide (Q:= (λ kv, kv.2.1.1.1.1 = i ∨ kv.2.1.1.1.2 = i)) with "H2") as "[H21 H22]".
    iSplitL "H21".
    iApply (big_sepFM_iff with "H21"). intros. split;intros [? ?];auto.
    iApply (big_sepFM_iff with "H22"). intros. split;intros [? ?];split;auto. intro Hor;apply H;destruct Hor;eauto.
    intro Hor;apply H0;destruct Hor;eauto.
    intros. split;intros H;eauto. destruct H;done.
    intros. split;intros H;eauto. destruct H;done.
    iIntros "([H11 H12] & [H21 H22])".
    iSplitL "H11 H21".
    iApply (big_sepFM_split_decide (Q:= (λ kv, kv.2.1.1.1.2 = i ∨ kv.2.1.1.1.1 = i))).
    rewrite (big_sepFM_iff (Q:= (λ kv, kv.2.1.1.1.2 = i ∨ kv.2.1.1.1.1 = i))). iFrame "H11".
    rewrite (big_sepFM_iff (Q:= (λ kv, ¬ (kv.2.1.1.1.2 = i ∨ kv.2.1.1.1.1 = i)))). iFrame "H21".
    intros. split;intros H;eauto. destruct H;done.
    intros. split;intros H;eauto. destruct H;done.
    iApply (big_sepFM_split_decide (Q:= (λ kv, kv.2.1.1.1.1 = i ∨ kv.2.1.1.1.2 = i))).
    iSplitL "H12".
    iApply big_sepFM_iff. 2: iFrame "H12".
    intros. split;intros H;eauto. destruct H;auto. destruct H;split;auto.
    iApply big_sepFM_iff. 2: iFrame "H22".
    intros. split;intros H;eauto. destruct H as [? H];split;auto.
    intro. apply H. destruct H1;auto.
    destruct H as [? H];split;auto.
    intro. apply H0. destruct H1;auto.
  Qed.

End logrel_prim_extra.
