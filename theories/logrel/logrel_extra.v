From iris.proofmode Require Import tactics.
From machine_program_logic.program_logic Require Import weakestpre.
From HypVeri.lang Require Import lang.
From HypVeri.algebra Require Import base base_extra mem pagetable trans.
From HypVeri.logrel Require Import logrel big_sepFM big_sepM_split.
From HypVeri Require Import proofmode stdpp_extra.
From stdpp Require fin_map_dom.
Import uPred.

Lemma half_of_half: (1/2/2)%Qp = (1/4)%Qp.
Proof.
  apply (bool_decide_unpack _).
  by compute.
Qed.

Section big_sep.
  Context `{Countable K} {A : Type}.
  Context {PROP : bi}.
  Implicit Types s : gset K.

  Lemma big_sepS_union_acc s s' (Φ: K → PROP) `{!∀ s s' s'', Absorbing (([∗ set] x ∈ s'', Φ x)
              -∗ [∗ set] x ∈ (s ∖ s' ∪ s'') , Φ x)}:
    s' ⊆ s ->
    ([∗ set] x ∈ s, Φ x) ⊢
    ([∗ set] x ∈ s', Φ x) ∗
      (∀ s'', ⌜s'' ## (s ∖ s')⌝
              -∗ ([∗ set] x ∈ s'', Φ x)
              -∗ [∗ set] x ∈ (s ∖ s' ∪ s'') , Φ x).
  Proof.
    iIntros (Hsubseteq) "Hset".
    pose proof(union_split_difference_intersection_subseteq_L Hsubseteq) as [Heq Hdisj].
    rewrite Heq.
    iDestruct (big_sepS_union with "Hset") as "[Hset1 Hset2]".
    done.
    iFrame "Hset2".
    iIntros (?) "%Hdisj' Hset'".
    rewrite -Heq.
    rewrite -Heq in Hdisj'.
    iApply big_sepS_union.
    done.
    iFrame.
  Qed.

End big_sep.

Section logrel_extra.
  Context `{hypconst:HypervisorConstants}.
  Context `{hypparams:!HypervisorParameters}.
  Context `{vmG: !gen_VMG Σ}.

  (** pgt **)
  Lemma pgt_split_half ps q vo be:
    pgt ps q vo be ⊣⊢ pgt ps (q/2) vo be ∗ pgt ps (q/2) vo be.
  Proof.
    rewrite /pgt.
    rewrite -big_sepS_sep.
    rewrite (big_sepS_proper _ (λ y, (y -@{q / 2}O> vo ∗ y -@{q / 2}E> be) ∗ y -@{q / 2}O> vo ∗ y -@{q / 2}E> be)%I) //.
    iIntros (? Hin).
    iSplit.
    iIntros "[H1 H2]".
    iDestruct (own_split with "H1") as "[$ $]".
    by iApply excl_split.
    iIntros "([H1 H2] & H3 & H4)".
    iDestruct (own_split with "[$H1 $H3]") as "$".
    iApply excl_split. iFrame.
  Qed.

   Lemma pgt_split_quarter ps vo be:
    pgt_full ps vo be ⊣⊢ pgt_1_4 ps vo be ∗ pgt_3_4 ps vo be.
  Proof.
    rewrite /pgt_full.
    rewrite (pgt_split_half _ 1).
    rewrite /pgt_1_4 /pgt_3_4.
    rewrite -half_of_half.
    rewrite (pgt_split_half _ (1/2)).
    rewrite -sep_assoc //.
  Qed.

  (** registers **)
  (* we provide lookup, so r and w can be implicit *)
  Lemma reg_big_sepM_split i {reg r w}:
    reg !! r = Some w ->
    (([∗ map] k↦y ∈ reg, k @@ i ->r y)%I
     ⊢  (r @@ i ->r w) ∗ ( r @@ i ->r w -∗ [∗ map] k↦y ∈ reg, k @@ i ->r y))%I.
  Proof.
    rewrite /reg_file.
    iIntros (Hlookup).
    iApply (ra_big_sepM_split reg r w Hlookup).
  Qed.

  Lemma reg_big_sepM_split_upd i {reg r w}:
    reg !! r = Some w ->
    ((⌜is_total_gmap (reg: gmap reg_name Addr)⌝ ∗ [∗ map] k↦y ∈ reg, k @@ i ->r y)%I
     ⊢  (r @@ i ->r w) ∗ (∀ w', r @@ i ->r w' -∗ ⌜is_total_gmap (<[r := w']>reg)⌝ ∗ [∗ map] k↦y ∈  <[r := w']>reg, k @@ i ->r y))%I.
  Proof.
    rewrite /reg_file /is_total_gmap.
    iIntros (Hlookup).
    iApply (ra_big_sepM_split_upd_with_total reg r w Hlookup).
  Qed.

  Lemma reg_big_sepM_split_upd2 i {reg r1 w1 r2 w2}:
    reg !! r1 = Some w1 ->
    reg !! r2 = Some w2 ->
    r1 ≠ r2 ->
    ((⌜is_total_gmap reg⌝ ∗ [∗ map] k↦y ∈ reg, k @@ i ->r y)%I
     ⊢  (r1 @@ i ->r w1) ∗ (r2 @@ i ->r w2) ∗
          (∀ w1' w2', r1 @@ i ->r w1' ∗ r2 @@ i ->r w2'-∗ ∃ reg', (⌜is_total_gmap reg'⌝ ∗ [∗ map] k↦y ∈ reg', k @@ i ->r y)))%I.
  Proof.
    iIntros ( Hlookup1 Hlookup2 Hneq).
    iApply (ra_big_sepM_split_upd2 reg r1 r2 w1 w2 Hneq Hlookup1 Hlookup2).
  Qed.

  Lemma reg_big_sepM_split_upd3 i {reg r1 w1 r2 w2 r3 w3}:
    reg !! r1 = Some w1 ->
    reg !! r2 = Some w2 ->
    reg !! r3 = Some w3 ->
    r1 ≠ r2 ->
    r1 ≠ r3 ->
    r2 ≠ r3 ->
    ((⌜is_total_gmap reg⌝ ∗ [∗ map] k↦y ∈ reg, k @@ i ->r y)%I
     ⊢  (r1 @@ i ->r w1) ∗ (r2 @@ i ->r w2) ∗ (r3 @@ i ->r w3) ∗
          (∀ w1' w2' w3', r1 @@ i ->r w1' ∗ r2 @@ i ->r w2' ∗ r3 @@ i ->r w3' -∗ ∃ reg', (⌜is_total_gmap reg'⌝ ∗ [∗ map] k↦y ∈ reg', k @@ i ->r y)))%I.
  Proof.
    iIntros (Hlookup1 Hlookup2 Hlookup3 Hneq1 Hneq2 Hneq3).
    iApply (ra_big_sepM_split_upd3 reg r1 r2 r3 w1 w2 w3);eauto.
  Qed.

  Lemma reg_big_sepM_split_upd4 i {reg r1 w1 r2 w2 r3 w3 r4 w4}:
    reg !! r1 = Some w1 ->
    reg !! r2 = Some w2 ->
    reg !! r3 = Some w3 ->
    reg !! r4 = Some w4 ->
    r1 ≠ r2 ->
    r1 ≠ r3 ->
    r2 ≠ r3 ->
    r1 ≠ r4 ->
    r4 ≠ r3 ->
    r2 ≠ r4 ->
    ((⌜is_total_gmap reg⌝ ∗ [∗ map] k↦y ∈ reg, k @@ i ->r y)%I
     ⊢  (r1 @@ i ->r w1) ∗ (r2 @@ i ->r w2) ∗ (r3 @@ i ->r w3) ∗ (r4 @@ i ->r w4) ∗
          (∀ w1' w2' w3' w4', r1 @@ i ->r w1' ∗ r2 @@ i ->r w2' ∗ r3 @@ i ->r w3' ∗ r4 @@ i ->r w4' -∗ ∃ reg', (⌜is_total_gmap reg'⌝ ∗ [∗ map] k↦y ∈ reg', k @@ i ->r y)))%I.
  Proof.
    iIntros (Hlookup1 Hlookup2 Hlookup3 Hlookup4 Hneq1 Hneq2 Hneq3 ? ? ? ).
    iApply (ra_big_sepM_split_upd4 reg r1 r2 r3 r4 w1 w2 w3 w4);eauto.
  Qed.

  (** memory **)
  Lemma mem_big_sepM_split (mem: gmap Addr Word) {a w} {f: _ -> _ -> iProp Σ}:
    mem !! a = Some w->
    (([∗ map] k↦y ∈ mem, f k y)
     ⊢  (f a w) ∗ (f a w -∗
                   ( [∗ map] k↦y ∈ mem, f k y)))%I.
  Proof.
    iIntros (Hlookup).
    iApply (ra_big_sepM_split mem a w Hlookup).
  Qed.

  Lemma mem_big_sepM_split_upd (mem: gmap Addr Word) {a w} {f: _ -> _ -> iProp Σ}:
    mem !! a = Some w->
    (([∗ map] k↦y ∈ mem, f k y)%I
     ⊢  (f a w) ∗ (∀ (w' : Word) , f a w' -∗
                                   ( [∗ map] k↦y ∈ <[a := w']>mem, f k y)))%I.
  Proof.
    iIntros (Hlookup).
    iApply (ra_big_sepM_split_upd mem a w Hlookup).
  Qed.

  Lemma mem_big_sepM_split2 (mem: gmap Addr Word) {a1 a2 w1 w2} {f: _ -> _ -> iProp Σ}:
    a1 ≠ a2 ->
    mem !! a1 = Some w1->
    mem !! a2 = Some w2->
    (([∗ map] k↦y ∈ mem, f k y)
     ⊢  f a1 w1 ∗ f a2 w2 ∗ ((f a1 w1 ∗ f a2 w2) -∗
                            ( [∗ map] k↦y ∈ mem, f k y)))%I.
  Proof.
    iIntros (Hne Hlookup1 Hlookup2).
    iApply (ra_big_sepM_split2 mem a1 a2 w1 w2); auto.
  Qed.

  Lemma mem_big_sepM_split_upd2 (mem: gmap Addr Word) {a1 a2 w1 w2} {f: _ -> _ -> iProp Σ}:
    a1 ≠ a2 ->
    mem !! a1 = Some w1->
    mem !! a2 = Some w2->
    (([∗ map] k↦y ∈ mem, f k y)%I
     ⊢  f a1 w1 ∗ f a2 w2 ∗ (∀ (w1' w2' : Word) , (f a1 w1' ∗ f a2 w2') -∗
                          ([∗ map] k↦y ∈ <[a1 := w1']>(<[a2 := w2']>mem), f k y)))%I.
  Proof.
    iIntros (Hne Hlookup1 Hlookup2).
    iApply (ra_big_sepM_split_upd2' mem a1 a2 w1 w2 Hne Hlookup1 Hlookup2).
  Qed.

  (* Lemmas about relationships between transferred_all, transferred, and transferred_except  *)
  (* Lemma transaction_pagetable_entries_transferred_split i trans: *)
  (*   transaction_pagetable_entries_transferred_all trans ⊣⊢ transaction_pagetable_entries_transferred i trans ∗ *)
  (*                                                transaction_pagetable_entries_transferred_except i trans. *)
  (* Proof. *)
  (*   iApply big_sepFM_split_decide. *)
  (* Qed. *)

  (* Lemma retrieval_entries_transferred_split i trans: *)
  (*  retrieval_entries_transferred_all trans ⊣⊢ retrieval_entries_transferred i trans ∗ *)
  (*                                                retrieval_entries_transferred_except i trans. *)
  (* Proof. *)
  (*   rewrite /retrieval_entries_transferred *)
  (*   /retrieval_entries_transferred_all *)
  (*   /retrieval_entries_transferred_except. *)
  (*   iSplit. *)
  (*   iIntros "(H1 & H2)". *)
  (*   iDestruct (big_sepFM_split_decide (Q:= (λ kv, kv.2.1.1.1.2 = i ∨ kv.2.1.1.1.1 = i)) with "H1") as "[H11 H12]". *)
  (*   rewrite (big_sepFM_iff (Q:= (λ kv, kv.2.1.1.1.2 = i ∨ kv.2.1.1.1.1 = i))). iFrame "H11". *)
  (*   rewrite (big_sepFM_iff (Q:= (λ kv, ¬ (kv.2.1.1.1.2 = i ∨ kv.2.1.1.1.1 = i)))). iFrame "H12". *)
  (*   iDestruct (big_sepFM_split_decide (Q:= (λ kv, kv.2.1.1.1.1 = i ∨ kv.2.1.1.1.2 = i)) with "H2") as "[H21 H22]". *)
  (*   iSplitL "H21". *)
  (*   iApply (big_sepFM_iff with "H21"). intros. split;intros [? ?];auto. *)
  (*   iApply (big_sepFM_iff with "H22"). intros. split;intros [? ?];split;auto. intro Hor;apply H;destruct Hor;eauto. *)
  (*   intro Hor;apply H0;destruct Hor;eauto. *)
  (*   intros. split;intros H;eauto. destruct H;done. *)
  (*   intros. split;intros H;eauto. destruct H;done. *)
  (*   iIntros "([H11 H12] & [H21 H22])". *)
  (*   iSplitL "H11 H21". *)
  (*   iApply (big_sepFM_split_decide (Q:= (λ kv, kv.2.1.1.1.2 = i ∨ kv.2.1.1.1.1 = i))). *)
  (*   rewrite (big_sepFM_iff (Q:= (λ kv, kv.2.1.1.1.2 = i ∨ kv.2.1.1.1.1 = i))). iFrame "H11". *)
  (*   rewrite (big_sepFM_iff (Q:= (λ kv, ¬ (kv.2.1.1.1.2 = i ∨ kv.2.1.1.1.1 = i)))). iFrame "H21". *)
  (*   intros. split;intros H;eauto. destruct H;done. *)
  (*   intros. split;intros H;eauto. destruct H;done. *)
  (*   iApply (big_sepFM_split_decide (Q:= (λ kv, kv.2.1.1.1.1 = i ∨ kv.2.1.1.1.2 = i))). *)
  (*   iSplitL "H12". *)
  (*   iApply big_sepFM_iff. 2: iFrame "H12". *)
  (*   intros. split;intros H;eauto. destruct H;auto. destruct H;split;auto. *)
  (*   iApply big_sepFM_iff. 2: iFrame "H22". *)
  (*   intros. split;intros H;eauto. destruct H as [? H];split;auto. *)
  (*   intro. apply H. destruct H1;auto. *)
  (*   destruct H as [? H];split;auto. *)
  (*   intro. apply H0. destruct H1;auto. *)
  (* Qed. *)

  (* lemmas about pages_in_trans *)
  Lemma elem_of_pages_in_trans p trans:
    p ∈ pages_in_trans trans <-> ∃h tran, trans !! h = Some tran ∧ p ∈ tran.1.1.2.
  Proof.
    rewrite /pages_in_trans.
    rewrite elem_of_pages_in_trans'.
    split.
    intros [h [tran [Hlk Hin]]].
    exists h, tran.
    split;auto.
    rewrite /lift_option_gmap in Hlk.
    rewrite lookup_fmap_Some in Hlk.
    destruct Hlk as [? [Heq Hlk]].
    inversion Heq;subst x.
    done.
    intros [h [tran [Hlk Hin]]].
    exists h, tran.
    split;auto.
    rewrite /lift_option_gmap.
    rewrite lookup_fmap_Some.
    exists tran.
    split;done.
  Qed.

  Lemma pages_in_trans_union trans trans':
    dom (gset _) trans ## dom (gset _) trans' ->
    pages_in_trans (trans ∪ trans') = pages_in_trans trans ∪ pages_in_trans trans'.
  Proof.
    intros Hdisj.
    rewrite set_eq.
    intros.
    rewrite elem_of_pages_in_trans.
    split.
    {
      intros (h & t & Hlk & Hin).
      destruct (trans !! h) eqn:Hlk'.
      {
        apply elem_of_union_l.
        rewrite elem_of_pages_in_trans.
        eexists. eexists. split;eauto.
        apply (lookup_union_Some_l _ trans') in Hlk'.
        rewrite Hlk' in Hlk; by inversion Hlk.
      }
      apply (lookup_union_Some_inv_r) in Hlk;auto.
      apply elem_of_union_r.
      rewrite elem_of_pages_in_trans.
      eexists. eexists. split;eauto.
    }
    {
      intros H.
      rewrite elem_of_union in H.
      destruct H as [Hin |Hin];
        rewrite elem_of_pages_in_trans in Hin;
        destruct Hin as (? & ? & ? & ?);
        (eexists; eexists; split;eauto);
        try (by apply lookup_union_Some_l).
      apply lookup_union_Some_r;eauto.
      rewrite map_disjoint_dom //.
    }
  Qed.

  Lemma pages_in_trans_insert{h tran trans}:
    trans !! h = None ->
    pages_in_trans (<[h := tran]> trans) =tran.1.1.2 ∪ pages_in_trans trans.
  Proof.
    intros Hlk.
    rewrite /pages_in_trans.
    rewrite /lift_option_gmap fmap_insert /=.
    apply pages_in_trans_insert_None'.
    rewrite lookup_fmap.
    rewrite Hlk //.
  Qed.

  Lemma pages_in_trans_subseteq m m':
    m' ⊆ m -> pages_in_trans m' ⊆ pages_in_trans m.
  Proof.
    intros Hsub.
    rewrite /pages_in_trans.
    apply pages_in_trans_subseteq'.
    rewrite map_subseteq_spec in Hsub.
    rewrite map_subseteq_spec.

    intros.
    rewrite /lift_option_gmap in H.
    apply lookup_fmap_Some in H.
    destruct H as [? [<- Hlk]].
    apply Hsub in Hlk.
    rewrite /lift_option_gmap.
    rewrite lookup_fmap_Some.
    exists x0.
    split;auto.
  Qed.

  Lemma subseteq_pages_in_trans h tran trans:
    trans !! h = Some tran ->
    tran.1.1.2 ⊆ pages_in_trans trans.
  Proof.
    intros Hlk.
    rewrite /pages_in_trans.
    apply (subseteq_pages_in_trans' h).
    rewrite /lift_option_gmap.
    rewrite lookup_fmap_Some.
    exists tran. split;done.
  Qed.

  Lemma pages_in_trans_insert'{h tran tran' trans}:
    trans !! h = Some tran ->
    tran.1 = tran'.1 ->
    pages_in_trans (<[h := tran']> trans) = pages_in_trans trans.
  Proof.
    intros Hlk.
    rewrite /pages_in_trans.
    rewrite /lift_option_gmap fmap_insert /=.
    apply pages_in_trans_insert_Some'.
    rewrite lookup_fmap.
    rewrite Hlk //.
  Qed.

  Lemma pages_in_trans_delete {h tran trans}:
    trans !! h = Some tran ->
    trans_ps_disj trans ->
    pages_in_trans (delete h trans) = pages_in_trans trans ∖ tran.1.1.2.
  Proof.
    intros Hlk Hdisj.
    rewrite /pages_in_trans.
    rewrite /lift_option_gmap.
    rewrite fmap_delete.
    apply pages_in_trans_delete'.
    rewrite lookup_fmap.
    rewrite Hlk //.
    done.
  Qed.

  (* lemmas for trans_ps_disj *)

  Lemma get_trans_ps_disj trans {Φ : _ -> iProp Σ}:
    (([∗ map] h ↦ tran ∈ trans , Φ tran) ∗
       (∀ v1 v2, Φ v1 ∗ Φ v2 -∗ ⌜v1.1.1.2 ## v2.1.1.2⌝)
     ⊢ ⌜trans_ps_disj trans⌝)%I.
  Proof.
    rewrite /trans_ps_disj.
    iIntros "[m Hfalse]".
    iIntros (k v Hlookup).
    rewrite /lift_option_gmap in Hlookup.
    rewrite lookup_fmap_Some in Hlookup.
    destruct Hlookup as [? [<- Hlookup]].
    rewrite elem_of_disjoint.
    iIntros (p Hin Hin').
    iDestruct (big_sepM_delete with "m") as "[Φ m]".
    exact Hlookup.
    apply elem_of_pages_in_trans' in Hin' as [h [v' [Hlookup' Hin'']]].
    iDestruct (big_sepM_delete with "m") as "[Φ' m]".
    rewrite /lift_option_gmap in Hlookup'.
    rewrite -fmap_delete in Hlookup'.
    rewrite lookup_fmap_Some in Hlookup'.
    destruct Hlookup' as [? [? Hlookup']].
    inversion H. subst x0.
    exact Hlookup'.
    iDestruct ("Hfalse" $! x v' with "[$ Φ $ Φ']") as %Hdisj.
    set_solver + Hdisj Hin Hin''.
  Qed.

  Lemma trans_ps_disj_insert h tran trans :
    trans_ps_disj trans ->
    trans !! h = None ->
    tran.1.1.2 ## pages_in_trans trans <->
    trans_ps_disj (<[h:=tran]> trans).
  Proof.
    rewrite /pages_in_trans.
    rewrite /trans_ps_disj.
    rewrite /lift_option_gmap.
    rewrite fmap_insert.
    intros Hdisj Hlk.
    split.
    intro Hdisj'.
    apply trans_ps_disj_insert';auto.
    rewrite lookup_fmap.
    rewrite Hlk //.
    intro Hdisj'.
    rewrite /inv_trans_ps_disj' /= in Hdisj'.
    rewrite map_Forall_insert in Hdisj'.
    2:{ rewrite lookup_fmap. rewrite Hlk //. }
    destruct Hdisj' as [? ?].
    rewrite delete_insert // in H.
    rewrite lookup_fmap. rewrite Hlk //.
  Qed.

  Lemma trans_ps_disj_subseteq m m':
    trans_ps_disj m -> m' ⊆ m -> trans_ps_disj m'.
  Proof.
    rewrite /trans_ps_disj.
    intros Hdisj Hsub.
    apply (trans_ps_disj_subseteq' (lift_option_gmap m)).
    done.
    rewrite map_subseteq_spec in Hsub.
    rewrite /lift_option_gmap.
    rewrite map_subseteq_spec.
    intros.
    rewrite lookup_fmap.
    rewrite lookup_fmap in H.
    destruct (m' !! i) eqn:Hlk.
    simpl in H.
    inversion H.
    apply Hsub in Hlk.
    rewrite Hlk //.
    done.
  Qed.

  Lemma trans_ps_disj_update{trans h tran tran'}:
    trans_ps_disj trans ->
    trans !! h = Some tran->
    tran.1 = tran'.1 ->
    trans_ps_disj (<[h:=tran']> trans).
  Proof.
    rewrite /trans_ps_disj /lift_option_gmap.
    intros Hdisj Hlk Heq.
    rewrite fmap_insert.
    eapply trans_ps_disj_update'.
    apply Hdisj.
    2: exact Heq.
    rewrite lookup_fmap Hlk //.
  Qed.

(* lemmas for tran_rel *)
  Lemma derive_trans_rel_secondary i trans trans':
    transaction_hpool_global_transferred trans' ∗ retrievable_transaction_transferred i trans' ∗
    transaction_pagetable_entries_owned i trans ∗ retrieved_transaction_owned i trans
    ⊢ ⌜trans_rel_secondary i trans trans'⌝.
  Proof.
    iIntros "((%s & %Hall & fresh & _ & global_tran) & [global_re _] & tran1 & tran2)".
    rewrite /transaction_pagetable_entries_owned.
    rewrite /retrieved_transaction_owned.
    rewrite /trans_rel_secondary.
    iInduction trans as [|h x tran Hlk] "IH" using map_ind; first done.
    rewrite map_Forall_insert;last done.
    destruct (decide (x.1.1.1.1 = i ∧ x.1.2 ≠ Donation)).
    {
      iDestruct (big_sepFM_insert_True with "tran1") as "[[tran _] tran1]";auto.
      iDestruct (trans.not_elem_of_fresh_handles with "[$fresh $tran]") as "%Hnin".
      iDestruct (trans.trans_valid_handle_Some with "tran") as "%Hvalid".
      assert (Hlk': h ∈ dom (gset Addr) trans') by set_solver + Hvalid Hnin Hall.
      rewrite elem_of_dom in Hlk'.
      destruct Hlk' as [tran' Hlk'].
      iDestruct (big_sepM_lookup_acc _ _ h with "global_tran") as "[tran' global_tran_acc]";eauto.
      iDestruct (trans_agree with "[$tran $tran']") as %Heq.
      destruct (decide (x.1.1.1.2 = i ∧ x.2 = true)).
      {
        iDestruct (big_sepFM_insert_True with "tran2") as "[[tran'' re] tran2]";auto.
        iDestruct (big_sepFM_lookup_Some_acc Hlk' with "global_re") as "[re' global_re_acc]";auto.
        simpl. left. destruct a0. repeat destruct x as [x ?]. repeat destruct tran' as [tran' ?]. simpl in *.
        inversion Heq. subst v0. done.
        iDestruct (retri_agree with "[$re $re']") as %Heq_re.
        iSplitR.
        iPureIntro.
        split;intros.
        eexists. split;eauto.
        eexists. split. eauto. destruct x, tran'. simpl in *. subst m0 b0. done.
        iApply ("IH" with "fresh [global_tran_acc tran'] [re' global_re_acc] tran1 tran2").
        by iApply "global_tran_acc".
        iDestruct("global_re_acc" $! tran') as "global_re".
        case_decide.
        iDestruct ("global_re" with "re'") as "global_re".
        rewrite insert_id //.
        exfalso. apply H. left. destruct a0. repeat destruct x as [x ?]. repeat destruct tran' as [tran' ?]. simpl in *.
        inversion Heq. subst v0. done.
      }
      {
        iSplitR.
        iPureIntro.
        split;intros.
        eexists. split;eauto.
        done.
        iApply ("IH" with "fresh [global_tran_acc tran'] global_re tran1 [tran2]").
        by iApply "global_tran_acc".
        rewrite big_sepFM_insert_False //.
      }
    }
    rewrite big_sepFM_insert_False //.
    destruct (decide (x.1.1.1.2 = i ∧ x.2 = true)).
    {
      iDestruct (big_sepFM_insert_True with "tran2") as "[[tran re] tran2]";auto.
      iDestruct (trans.not_elem_of_fresh_handles with "[$fresh $tran]") as "%Hnin".
      iDestruct (trans.trans_valid_handle_Some with "tran") as "%Hvalid".
      assert (Hlk': h ∈ dom (gset Addr) trans') by set_solver + Hvalid Hnin Hall.
      rewrite elem_of_dom in Hlk'.
      destruct Hlk' as [tran' Hlk'].
      iDestruct (big_sepM_lookup_acc _ _ h with "global_tran") as "[tran' global_tran_acc]";eauto.
      iDestruct (trans_agree with "[$tran $tran']") as %Heq.
      iDestruct (big_sepFM_lookup_Some_acc Hlk' with "global_re") as "[re' global_re_acc]";auto.
      simpl. left. destruct a. repeat destruct x as [x ?]. repeat destruct tran' as [tran' ?]. simpl in *.
      inversion Heq. subst v0. done.
      iDestruct (retri_agree with "[$re $re']") as %Heq_re.
      iSplitR.
      iPureIntro.
      split;intros.
      done.
      eexists. split. eauto. destruct x, tran'. simpl in *. subst m0 b0. done.
      iApply ("IH" with "fresh [global_tran_acc tran'] [re' global_re_acc] tran1 tran2").
      by iApply "global_tran_acc".
      iDestruct("global_re_acc" $! tran') as "global_re".
      case_decide.
      iDestruct ("global_re" with "re'") as "global_re".
      rewrite insert_id //.
      exfalso. apply H. left. destruct a. repeat destruct x as [x ?]. repeat destruct tran' as [tran' ?]. simpl in *.
      inversion Heq. subst v0. done.
    }
    {
      iSplitR.
      iPureIntro.
      split;intros.
      done. done.
      iApply ("IH" with "fresh global_tran global_re tran1 [tran2]").
      rewrite big_sepFM_insert_False //.
    }
  Qed.

  Lemma trans_rel_secondary_retrieved_lending_memory_page i trans trans':
    trans_rel_secondary i trans trans' ->
    trans_rel_eq (retrieved_lending_memory_pages i) trans trans'.
  Proof.
  Admitted.

  Lemma trans_rel_secondary_currently_accessible_memory_pages i trans trans':
    trans_rel_secondary i trans trans' ->
    trans_rel_eq (currently_accessible_in_trans_memory_pages i) trans trans'.
  Proof.
  Admitted.

  Lemma trans_rel_secondary_transaction_pagetable_entries_owned i trans trans':
    trans_rel_secondary i trans trans' ->
    ⊢ trans_rel_wand (transaction_pagetable_entries_owned i) trans trans'.
  Proof.
  Admitted.

  Lemma trans_rel_secondary_retrieved_transaction_owned i trans trans':
    trans_rel_secondary i trans trans' ->
    ⊢ trans_rel_wand (retrieved_transaction_owned i) trans trans'.
  Proof.
  Admitted.

  (* lemmas *)
  Lemma transferred_accessible_memory_pages_subseteq i trans:
    transferred_memory_pages i trans ⊆ accessible_in_trans_memory_pages i trans.
  Proof.
  Admitted.

  Lemma currently_accessible_accessible_memory_pages_subseteq i trans:
    currently_accessible_in_trans_memory_pages i trans ⊆ accessible_in_trans_memory_pages i trans.
  Proof.
  Admitted.

  Lemma retrieved_lending_currently_accessible_memory_pages_subseteq i trans:
    retrieved_lending_memory_pages i trans ⊆ currently_accessible_in_trans_memory_pages i trans.
  Proof.
  Admitted.

  Lemma transferred_retrieved_lending_memory_pages_union i trans:
    transferred_memory_pages i trans ∪ retrieved_lending_memory_pages i trans = accessible_in_trans_memory_pages i trans.
  Proof.
  Admitted.

  Lemma transferred_retrieved_lending_memory_pages_disj i trans: transferred_memory_pages i trans ## retrieved_lending_memory_pages i trans.
  Proof.
  Admitted.

  Lemma accessible_retrieved_lending_memory_pages_difference i trans:
    transferred_memory_pages i trans = accessible_in_trans_memory_pages i trans ∖ retrieved_lending_memory_pages i trans.
  Proof.
  Admitted.

  Lemma accessible_in_trans_memory_pages_insert_True i trans h tran:
    (tran.1.1.1.1 = i  ∧ ¬(tran.2 = true ∧ tran.1.2 = Lending)) ∨ tran.1.1.1.2 = i ->
    accessible_in_trans_memory_pages i (<[h:= tran]>trans) = accessible_in_trans_memory_pages i trans ∪ tran.1.1.2.
  Proof.
  Admitted.

  Lemma accessible_in_trans_memory_pages_insert_False i trans h tran:
    ¬((tran.1.1.1.1 = i  ∧ ¬(tran.2 = true ∧ tran.1.2 = Lending)) ∨ tran.1.1.1.2 = i) ->
    accessible_in_trans_memory_pages i (<[h:= tran]>trans) = accessible_in_trans_memory_pages i trans.
  Proof.
  Admitted.

  Lemma accessible_in_trans_memory_pages_lookup_True i trans h tran:
    trans !! h = Some tran ->
    ((tran.1.1.1.1 = i  ∧ ¬(tran.2 = true ∧ tran.1.2 = Lending)) ∨ tran.1.1.1.2 = i) ->
    tran.1.1.2 ⊆ (accessible_in_trans_memory_pages i trans).
  Proof.
  Admitted.

  Lemma accessible_in_trans_memory_pages_lookup_False i trans h tran:
    trans !! h = Some tran ->
    ¬((tran.1.1.1.1 = i  ∧ ¬(tran.2 = true ∧ tran.1.2 = Lending)) ∨ tran.1.1.1.2 = i) ->
    tran.1.1.2 ## (accessible_in_trans_memory_pages i trans).
  Proof.
  Admitted.

  Lemma accessible_in_trans_memory_pages_delete_True i trans h tran:
    trans !! h = Some tran ->
    (tran.1.1.1.1 = i  ∧ ¬(tran.2 = true ∧ tran.1.2 = Lending)) ∨ tran.1.1.1.2 = i ->
    trans_ps_disj trans ->
    accessible_in_trans_memory_pages i (delete h trans) = accessible_in_trans_memory_pages i trans ∖ tran.1.1.2.
  Proof.
  Admitted.

  Lemma accessible_in_trans_memory_pages_delete_False i trans h tran:
    trans !! h = Some tran ->
    ¬((tran.1.1.1.1 = i  ∧ ¬(tran.2 = true ∧ tran.1.2 = Lending)) ∨ tran.1.1.1.2 = i) ->
    trans_ps_disj trans ->
    accessible_in_trans_memory_pages i (delete h trans) = accessible_in_trans_memory_pages i trans.
  Proof.
  Admitted.

  Lemma currently_accessible_in_trans_memory_pages_insert_True i trans h tran:
    (tran.1.1.1.1 = i ∧ tran.1.2 = Sharing) ∨ (tran.1.1.1.2 = i ∧ tran.2 = true) ->
    currently_accessible_in_trans_memory_pages i (<[h:= tran]>trans) = currently_accessible_in_trans_memory_pages i trans ∪ tran.1.1.2.
  Proof.
  Admitted.

  Lemma currently_accessible_in_trans_memory_pages_insert_False i trans h tran:
    ¬((tran.1.1.1.1 = i ∧ tran.1.2 = Sharing) ∨ (tran.1.1.1.2 = i ∧ tran.2 = true)) ->
    currently_accessible_in_trans_memory_pages i (<[h:= tran]>trans) = currently_accessible_in_trans_memory_pages i trans.
  Proof.
  Admitted.

  Lemma currently_accessible_in_trans_memory_pages_lookup_True i trans h tran:
    trans !! h = Some tran ->
    ((tran.1.1.1.1 = i ∧ tran.1.2 = Sharing) ∨ (tran.1.1.1.2 = i ∧ tran.2 = true)) ->
    tran.1.1.2 ⊆ (currently_accessible_in_trans_memory_pages i trans).
  Proof.
  Admitted.

  Lemma currently_accessible_in_trans_memory_pages_lookup_False i trans h tran:
    trans !! h = Some tran ->
    ¬((tran.1.1.1.1 = i ∧ tran.1.2 = Sharing) ∨ (tran.1.1.1.2 = i ∧ tran.2 = true)) ->
    tran.1.1.2 ## (currently_accessible_in_trans_memory_pages i trans).
  Proof.
  Admitted.

  Lemma currently_accessible_in_trans_memory_pages_delete_True i trans h tran:
    trans !! h = Some tran ->
    (tran.1.1.1.1 = i ∧ tran.1.2 = Sharing) ∨ (tran.1.1.1.2 = i ∧ tran.2 = true) ->
    trans_ps_disj trans ->
    currently_accessible_in_trans_memory_pages i (delete h trans) = currently_accessible_in_trans_memory_pages i trans ∖ tran.1.1.2.
  Proof.
  Admitted.

  Lemma currently_accessible_in_trans_memory_pages_delete_False i trans h tran:
    trans !! h = Some tran ->
    ¬((tran.1.1.1.1 = i ∧ tran.1.2 = Sharing) ∨ (tran.1.1.1.2 = i ∧ tran.2 = true)) ->
    trans_ps_disj trans ->
    currently_accessible_in_trans_memory_pages i (delete h trans) = currently_accessible_in_trans_memory_pages i trans.
  Proof.
  Admitted.

  Lemma memory_pages_oea_transferred {i} ps_acc p_rx p_tx trans':
    let ps_macc_trans' := (transferred_memory_pages i trans') in
    let ps_oea' := ps_acc ∖ {[p_rx;p_tx]} ∖ (currently_accessible_in_trans_memory_pages i trans') in
    trans_ps_disj trans' ->
    ((∃ mem_oea, memory_pages (ps_oea' ∪ (retrieved_lending_memory_pages i trans')) mem_oea)
     ∗ (∃ mem_trans, memory_pages ps_macc_trans' mem_trans) -∗
    ∃ mem_all, memory_pages (ps_acc ∖ {[p_rx;p_tx]} ∪ (accessible_in_trans_memory_pages i trans')) mem_all).
    Proof.
      iIntros (? ? Hdisj) "[oea trans]".
      iDestruct (memory_pages_union' (ps_oea' ∪ retrieved_lending_memory_pages i trans') ps_macc_trans' with "[oea trans]") as "mem".
      iFrame.
      replace (ps_oea' ∪ retrieved_lending_memory_pages i trans' ∪ ps_macc_trans')
        with  (ps_acc ∖ {[p_rx; p_tx]} ∪ accessible_in_trans_memory_pages i trans');auto.
      {
        rewrite -union_assoc_L.
        rewrite (union_comm_L (retrieved_lending_memory_pages i trans')).
        rewrite union_assoc_L.
        rewrite -union_assoc_L.
        rewrite /ps_oea'.
        replace (ps_macc_trans' ∪ retrieved_lending_memory_pages i trans') with (accessible_in_trans_memory_pages i trans').
        assert (currently_accessible_in_trans_memory_pages i trans' ⊆ accessible_in_trans_memory_pages i trans').
        {
          rewrite /currently_accessible_in_trans_memory_pages /accessible_in_trans_memory_pages.
          apply pages_in_trans_subseteq.
          rewrite map_subseteq_spec.

          intros h tran.
          rewrite 2?map_filter_lookup_Some.
          intros [Hlk P].
          split;auto.
          destruct P as [[? H0]| [? ?]].
          left. split;auto. intros [_ H1]. rewrite H0 in H1. inversion H1.
          right. done.
        }
        symmetry.
        by apply difference_union_subseteq.
        rewrite /ps_macc_trans' /transferred_memory_pages.
        rewrite /retrieved_lending_memory_pages.
        rewrite -pages_in_trans_union.
        2:{
            intros h.
            rewrite 2?elem_of_dom.
            intros [? Hlk] [? Hlk'].
            rewrite map_filter_lookup_Some in Hlk.
            rewrite map_filter_lookup_Some in Hlk'.
            destruct Hlk as [Hlk [? ?]].
            destruct Hlk' as [Hlk' [? ?]].
            rewrite Hlk' in Hlk;inversion Hlk.
            subst. contradiction.
        }
        clear p_rx p_tx ps_acc ps_oea' ps_macc_trans' Hdisj.
        rewrite /accessible_in_trans_memory_pages. f_equal.
        induction trans' using map_ind.
        rewrite !map_filter_empty. rewrite map_union_empty //.
        rewrite map_filter_insert.
        case_decide.
        destruct H0.
        {
          rewrite !map_filter_insert.
          case_decide;
            case_decide.
          destruct H0, H2;contradiction.
          rewrite IHtrans' insert_union_l.
          rewrite delete_notin //.
          destruct H0, H2;contradiction.
          exfalso. apply H1.
          destruct H0.
          split; eauto.
        }
        {
          rewrite !map_filter_insert.
          case_decide;
            case_decide.
          destruct H1, H2;contradiction.
          rewrite IHtrans' insert_union_l.
          rewrite delete_notin //.
          rewrite delete_notin //.
          rewrite map_union_comm.
          rewrite IHtrans'. rewrite map_union_comm. rewrite insert_union_l //.
          { apply map_disjoint_dom_2.
            intros h.
            rewrite 2?elem_of_dom.
            intros [? Hlk] [? Hlk'].
            rewrite map_filter_lookup_Some in Hlk.
            rewrite map_filter_lookup_Some in Hlk'.
            destruct Hlk as [Hlk [? ?]].
            destruct Hlk' as [Hlk' [? ?]].
            rewrite Hlk' in Hlk;inversion Hlk.
            subst. contradiction.
          }
          { apply map_disjoint_dom_2.
            intros h.
            rewrite 2?elem_of_dom.
            intros [? Hlk] [? Hlk'].
            rewrite map_filter_lookup_Some in Hlk.
            assert (Hneq: i0 ≠ h).
            {
              destruct (decide (i0 = h)); auto.
              subst.
              destruct Hlk as [Hlk ?].
              rewrite Hlk in H. inversion H.
            }
            rewrite lookup_insert_ne // in Hlk'.
            rewrite map_filter_lookup_Some in Hlk'.
            destruct Hlk as [Hlk [? ?]].
            destruct Hlk' as [Hlk' [? ?]].
            rewrite Hlk' in Hlk;inversion Hlk.
            subst. contradiction.
          }
          exfalso. apply H1.
          split;eauto.
        }
        rewrite !map_filter_insert.
        case_decide; case_decide.
        exfalso. apply H0.
        right;destruct H2;auto.
        exfalso. apply H0.
        destruct H1.
        destruct H1.
        left;auto.
        right;auto.
        exfalso. apply H1.
        split;destruct H2;eauto.
        rewrite !delete_notin //.
        }
      Qed.

End logrel_extra.
