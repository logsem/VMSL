From iris.proofmode Require Import tactics.
From machine_program_logic.program_logic Require Import weakestpre.
From HypVeri.lang Require Import lang.
From HypVeri.algebra Require Import base base_extra mem pagetable trans.
From HypVeri.logrel Require Import logrel.
From HypVeri.logrel Require Export big_sepFM big_sepM_split.
From HypVeri Require Import proofmode.
From HypVeri Require Export stdpp_extra.
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
    pose proof(union_split_difference_intersection_subseteq_L _ _ Hsubseteq) as [Heq Hdisj].
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

  Lemma pgt_valid ps (q1 q2:Qp) vo1 be1 vo2 be2:
  pgt ps q1 vo1 be1 ∗ pgt ps q2 vo2 be2 ⊢ ⌜(q1 + q2 ≤ 1)%Qp⌝.
  Proof.
    Admitted.

  Lemma pgt_invalid_3_4 ps vo1 be1 vo2 be2:
  pgt_3_4 ps vo1 be1 ∗ pgt_3_4 ps vo2 be2 ⊢ False.
  Proof.
    Admitted.

  Lemma pgt_valid_3_4 ps1 ps2 vo1 be1 vo2 be2:
  pgt_3_4 ps1 vo1 be1 ∗ pgt_3_4 ps2 vo2 be2 ⊢ ⌜ps1 ## ps2⌝.
  Proof.
    Admitted.

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

  Lemma pages_in_trans_empty:
    pages_in_trans ∅ = ∅.
  Proof.
    rewrite /pages_in_trans /pages_in_trans'.
    rewrite /lift_option_gmap.
    rewrite fmap_empty map_fold_empty //.
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

  Lemma pages_in_trans_insert_strong{h tran tran' trans}:
    trans !! h = Some tran ->
    trans_ps_disj trans ->
    pages_in_trans (<[h := tran']> trans) = pages_in_trans trans ∖ tran.1.1.2 ∪ tran'.1.1.2.
  Proof.
    intros Hlk Hdisj.
    rewrite /pages_in_trans.
    rewrite /lift_option_gmap fmap_insert /=.
    apply pages_in_trans_insert_Some_strong'.
    rewrite lookup_fmap.
    rewrite Hlk //.
    done.
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

  Lemma pages_in_trans_delete_None {h trans}:
    trans !! h = None ->
    pages_in_trans (delete h trans) = pages_in_trans trans.
  Proof.
    intros Hlk.
    rewrite delete_notin //.
  Qed.

  (* lemmas for trans_ps_disj *)

  Lemma get_trans_ps_disj' trans {Φ : _ -> _ -> iProp Σ}:
    (([∗ map] h ↦ tran ∈ trans , Φ h tran) ∗
       (∀ k1 k2 v1 v2, Φ k1 v1 ∗ Φ k2 v2 -∗ ⌜v1.1.1.2 ## v2.1.1.2⌝)
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
    iDestruct ("Hfalse" $! k h x v' with "[$ Φ $ Φ']") as %Hdisj.
    set_solver + Hdisj Hin Hin''.
  Qed.

  Lemma trans_ps_disj_insert_2 h tran trans :
    trans !! h = None ->
    trans_ps_disj (<[h:=tran]> trans) ->
    tran.1.1.2 ## pages_in_trans trans ∧ trans_ps_disj trans.
  Proof.
    rewrite /pages_in_trans.
    rewrite /trans_ps_disj.
    rewrite /lift_option_gmap.
    rewrite fmap_insert.
    intros Hlk.
    intro Hdisj'.
    rewrite /inv_trans_ps_disj' /= in Hdisj'.
    rewrite map_Forall_insert in Hdisj'.
    2:{ rewrite lookup_fmap. rewrite Hlk //. }
    destruct Hdisj' as [? ?].
    rewrite delete_insert // in H.
    split. done.  2:{ rewrite lookup_fmap. rewrite Hlk //. }
    rewrite /inv_trans_ps_disj' /= .
    intro h0. intros.
    destruct x;auto.
    specialize (H0 h0 (Some p) H1).
    simpl in H0.
    destruct (decide (h = h0)).
    subst.
    rewrite delete_insert in H0.
    rewrite -fmap_delete.
    rewrite delete_notin //.
    rewrite lookup_fmap.
    rewrite Hlk //.
    rewrite delete_insert_ne // in H0.
    rewrite pages_in_trans_insert_None' in H0.
    set_solver + H0.
    rewrite lookup_delete_ne //.
    rewrite lookup_fmap Hlk //.
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
    apply (trans_ps_disj_insert_2 h);auto.
    rewrite /trans_ps_disj.
    rewrite /lift_option_gmap.
    rewrite fmap_insert.
    done.
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
  Lemma get_trans_rel_secondary i trans trans':
    transaction_hpool_global_transferred trans' ∗ retrievable_transaction_transferred i trans' ∗
    transaction_pagetable_entries_owned i trans ∗ retrieved_transaction_owned i trans
    ⊢ ⌜trans_rel_secondary i trans trans'⌝.
  Proof.
    iIntros "((%s & %Hall & fresh & global_tran) & [global_re _] & tran1 & tran2)".
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
      iDestruct (big_sepM_lookup_acc _ _ h with "global_tran") as "[[tran' pgt] global_tran_acc]";eauto.
      iDestruct (trans_agree with "[$tran $tran']") as %Heq.
      destruct (decide (x.1.1.1.2 = i ∧ x.2 = true)).
      {
        iDestruct (trans_valid_tran_Some with "tran") as %Hvalid_h.
        destruct a,a0 as [? _].
        rewrite /valid_transaction H H1 // in Hvalid_h.
      }
      {
        iSplitR.
        iPureIntro.
        split;intros.
        eexists. split;eauto.
        done.
        iApply ("IH" with "fresh [global_tran_acc tran' pgt] global_re tran1 [tran2]").
        iApply "global_tran_acc". iFrame.
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
      iDestruct (big_sepM_lookup_acc _ _ h with "global_tran") as "[[tran' pgt] global_tran_acc]";eauto.
      iDestruct (trans_agree with "[$tran $tran']") as %Heq.
      iDestruct (big_sepFM_lookup_Some_acc Hlk' with "global_re") as "[re' global_re_acc]";auto.
      simpl. right. destruct a;repeat destruct x as [x ?]. simpl in *. rewrite -Heq //.
      iDestruct (retri_agree with "[$re $re']") as %Heq_re.
      iSplitR. iPureIntro. split;intros. done.
      eexists. split. eauto. destruct x, tran'. simpl in *. subst m0 b0. done.
      iApply ("IH" with "fresh [global_tran_acc tran' pgt] [re' global_re_acc] tran1 tran2").
      iApply "global_tran_acc". iFrame.
      iDestruct("global_re_acc" $! tran') as "global_re".
      case_decide.
      iDestruct ("global_re" with "re'") as "global_re".
      rewrite insert_id //.
      exfalso. apply H. right. destruct a. repeat destruct x as [x ?]. simpl in *.
      rewrite -Heq //.
    }
    {
      iSplitR. iPureIntro. split;intros. done. done.
      iApply ("IH" with "fresh global_tran global_re tran1 [tran2]").
      rewrite big_sepFM_insert_False //.
    }
  Qed.

  Lemma get_trans_ps_disj trans:
    transaction_hpool_global_transferred trans ⊢ ⌜trans_ps_disj trans⌝.
  Proof.
    iIntros "(%s & %Hall & fresh & global_tran)".
    iApply (get_trans_ps_disj' with "[$global_tran]").
    iIntros (????) "[[_ pgt1] [_ pgt2]]".
    iApply pgt_valid_3_4.
    iFrame.
  Qed.

  Definition valid_accessible_in_trans_memory_pages ps_acc i trans :=
    ps_acc ∩ (accessible_in_trans_memory_pages i trans) = currently_accessible_in_trans_memory_pages i trans.

  (* TODO *)
  Lemma get_valid_accessible_in_trans_memory_pages ps_acc i trans :
    currently_accessible_in_trans_memory_pages i trans ⊆ ps_acc ->
    transaction_hpool_global_transferred trans ∗
    pagetable_entries_excl_owned i (ps_acc ∖ currently_accessible_in_trans_memory_pages i trans)
    ⊢ ⌜valid_accessible_in_trans_memory_pages ps_acc i trans⌝%I.
  Proof.
    Admitted.

  (* TODO *)
  Lemma trans_rel_secondary_retrieved_lending_memory_pages i trans trans':
    trans_rel_secondary i trans trans' ->
    trans_rel_eq (retrieved_lending_memory_pages i) trans trans'.
  Proof.
  Admitted.

  (* TODO *)
  Lemma trans_rel_secondary_currently_accessible_memory_pages i trans trans':
    trans_rel_secondary i trans trans' ->
    trans_rel_eq (currently_accessible_in_trans_memory_pages i) trans trans'.
  Proof.
  Admitted.

  (* TODO *)
  Lemma trans_rel_secondary_transaction_pagetable_entries_owned i trans trans':
    trans_rel_secondary i trans trans' ->
    ⊢ trans_rel_wand (transaction_pagetable_entries_owned i) trans trans'.
  Proof.
  Admitted.

  (* TODO *)
  Lemma trans_rel_secondary_retrieved_transaction_owned i trans trans':
    trans_rel_secondary i trans trans' ->
    ⊢ trans_rel_wand (retrieved_transaction_owned i) trans trans'.
  Proof.
  Admitted.

  (* lemmas *)
  Lemma transferred_accessible_memory_pages_subseteq i trans:
    transferred_memory_pages i trans ⊆ accessible_in_trans_memory_pages i trans.
  Proof.
    apply pages_in_trans_subseteq.
    apply map_filter_imp.
    intros.
    destruct H as [[|] ].
    left;done.
    right;done.
  Qed.

  Lemma currently_accessible_accessible_memory_pages_subseteq i trans:
    currently_accessible_in_trans_memory_pages i trans ⊆ accessible_in_trans_memory_pages i trans.
  Proof.
    apply pages_in_trans_subseteq.
    apply map_filter_imp.
    intros.
    destruct H as [[]|[]].
    left;split;auto.
    intro.
    destruct H1.
    rewrite H2 //in H0.
    right;done.
  Qed.

  Lemma retrieved_lending_currently_accessible_memory_pages_subseteq i trans:
    retrieved_lending_memory_pages i trans ⊆ currently_accessible_in_trans_memory_pages i trans.
  Proof.
    apply pages_in_trans_subseteq.
    apply map_filter_imp.
    intros.
    destruct H as [? []].
    right;split;done.
  Qed.

  (* TODO: make a general lemma *)
  Lemma transferred_retrieved_lending_memory_pages_disj i trans:
    trans_ps_disj trans ->
    transferred_memory_pages i trans ## retrieved_lending_memory_pages i trans.
  Proof.
    intros Hdisj.
    induction trans using map_ind. done.
    rewrite /transferred_memory_pages /retrieved_lending_memory_pages.
    rewrite 2?map_filter_insert.
    case_decide;case_decide.
    {
      destruct H0.
      destruct H1. done.
    }
    {
      rewrite pages_in_trans_insert.
      rewrite delete_notin //.
      assert (x.1.1.2 ## pages_in_trans (filter
                                           (λ kv : Addr *
                                                     (VMID * leibnizO VMID * gset PID * transaction_type * bool),
                                               kv.2.1.1.1.2 = i ∧ kv.2.2 = true ∧ kv.2.1.2 = Lending)
                                           m)).
      apply trans_ps_disj_insert_2 in Hdisj;auto.
      pose proof ( pages_in_trans_subseteq m (filter (λ kv : Addr * (VMID * leibnizO VMID * gset PID * transaction_type * bool), kv.2.1.1.1.2 = i ∧ kv.2.2 = true ∧ kv.2.1.2 = Lending) m)).
      feed specialize H2.
      apply map_filter_subseteq.
      set_solver + H2 Hdisj.
      apply trans_ps_disj_insert_2 in Hdisj;auto.
      destruct Hdisj as [Hdisj Hdisj_t].
      apply IHtrans in Hdisj_t.
      rewrite /transferred_memory_pages /retrieved_lending_memory_pages in Hdisj_t.
      set_solver + H2 Hdisj Hdisj_t.
      rewrite map_filter_lookup_None.
      left;done.
    }
    {
      rewrite pages_in_trans_insert.
      rewrite delete_notin //.
      assert (x.1.1.2 ##  pages_in_trans
                (filter
                   (λ kv : Addr * (leibnizO VMID * leibnizO VMID * gset PID * transaction_type * bool),
                       (kv.2.1.1.1.1 = i ∨ kv.2.1.1.1.2 = i) ∧ ¬ (kv.2.2 = true ∧ kv.2.1.2 = Lending)) m)).
      apply trans_ps_disj_insert_2 in Hdisj;auto.
      pose proof (pages_in_trans_subseteq m (filter
                                               (λ kv : Addr * (leibnizO VMID * leibnizO VMID * gset PID * transaction_type * bool),
                                                   (kv.2.1.1.1.1 = i ∨ kv.2.1.1.1.2 = i) ∧ ¬ (kv.2.2 = true ∧ kv.2.1.2 = Lending)) m)).
      feed specialize H2.
      apply map_filter_subseteq.
      set_solver + H2 Hdisj.
      apply trans_ps_disj_insert_2 in Hdisj;auto.
      destruct Hdisj as [Hdisj Hdisj_t].
      apply IHtrans in Hdisj_t.
      rewrite /transferred_memory_pages /retrieved_lending_memory_pages in Hdisj_t.
      set_solver + H2 Hdisj Hdisj_t.
      rewrite map_filter_lookup_None.
      left;done.
    }
    {
      rewrite 2?delete_notin //.

      apply trans_ps_disj_insert_2 in Hdisj;auto.
      apply IHtrans.
      destruct Hdisj as [];done.
    }
  Qed.

  (* TODO: make a general lemma *)
  Lemma transferred_retrieved_lending_memory_pages_union i trans:
    transferred_memory_pages i trans ∪ retrieved_lending_memory_pages i trans
    = accessible_in_trans_memory_pages i trans.
  Proof.
    rewrite -pages_in_trans_union.
    rewrite /accessible_in_trans_memory_pages.
    f_equal.
    2:{
      induction trans using map_ind.
      set_solver +.
      rewrite !map_filter_insert.
      case_decide.
      rewrite dom_insert_L.
      rewrite delete_notin //.
      case_decide.
      destruct H0, H1;done.
      assert (i0 ∉ dom (gset Addr)
                (filter (λ kv : Addr * (VMID * leibnizO VMID * gset PID * transaction_type * bool), kv.2.1.1.1.2 = i ∧ kv.2.2 = true ∧ kv.2.1.2 = Lending) m)).
      apply not_elem_of_dom.
      rewrite map_filter_lookup_None;left;done.
      set_solver + H2 IHtrans.
      case_decide.
      rewrite dom_insert_L.
      rewrite delete_notin //.
      assert (i0 ∉ dom (gset Addr)
                (filter
                   (λ kv : Addr * (leibnizO VMID * leibnizO VMID * gset PID * transaction_type * bool),
                       (kv.2.1.1.1.1 = i ∨ kv.2.1.1.1.2 = i) ∧ ¬ (kv.2.2 = true ∧ kv.2.1.2 = Lending)) m)).
      apply not_elem_of_dom.
      rewrite map_filter_lookup_None;left;done.
      set_solver + H2 IHtrans.
      rewrite 2?delete_notin //.
    }
    induction trans using map_ind. rewrite !map_filter_empty. apply map_union_empty.
    rewrite !map_filter_insert.
    case_decide.
    {
      case_decide.
      destruct H0.
      destruct H1.
      done.
      case_decide.
      {
        rewrite -insert_union_l.
        f_equal.
        rewrite delete_notin //.
      }
      exfalso.
      apply H2.
      destruct H0 as [[|] ?];[left|right];done.
    }
    {
      rewrite delete_notin //.
      case_decide.
      case_decide.
      {
        rewrite -insert_union_r.
        f_equal.
        done.
        rewrite map_filter_lookup_None.
        left;done.
      }
      exfalso.
      apply H2.
      right.
      destruct H1;done.
      case_decide.
      exfalso.
      apply H0.
      destruct H2 as [[??]|].
      split;auto.
      split;auto.
      apply IHtrans.
    }
  Qed.

  Lemma accessible_retrieved_lending_memory_pages_difference i trans:
    trans_ps_disj trans ->
    transferred_memory_pages i trans = accessible_in_trans_memory_pages i trans ∖ retrieved_lending_memory_pages i trans.
  Proof.
    intro Hdisj.
    pose proof (transferred_retrieved_lending_memory_pages_union i trans).
    pose proof (transferred_retrieved_lending_memory_pages_disj i trans Hdisj).
    set_solver.
  Qed.

  Lemma acc_transferred_memory_pages_difference ps_acc i trans trans':
    trans_rel_secondary i trans trans' ->
    currently_accessible_in_trans_memory_pages i trans ⊆ ps_acc ->
    valid_accessible_in_trans_memory_pages ps_acc i trans ->
    trans_ps_disj trans ->
    valid_accessible_in_trans_memory_pages ps_acc i trans' ->
    trans_ps_disj trans' ->
    ps_acc ∖ transferred_memory_pages i trans = ps_acc ∖ transferred_memory_pages i trans'.
  Proof.
    intros Hrel Hsubset Hvalid Hdisj Hvalid' Hdisj'.
    rewrite 2?accessible_retrieved_lending_memory_pages_difference;auto.
    rewrite 2?difference_difference_union.
    2 : {
      erewrite (trans_rel_secondary_currently_accessible_memory_pages) in Hsubset;eauto.
      pose proof(retrieved_lending_currently_accessible_memory_pages_subseteq i trans').
      set_solver.
    }
    2 : {
      pose proof(retrieved_lending_currently_accessible_memory_pages_subseteq i trans).
      set_solver.
    }
    rewrite intersection_difference.
    rewrite Hvalid.
    erewrite (trans_rel_secondary_currently_accessible_memory_pages);eauto.
    rewrite -Hvalid'.
    rewrite -intersection_difference.
    erewrite (trans_rel_secondary_retrieved_lending_memory_pages);eauto.
  Qed.

  Lemma acc_accessible_in_trans_memory_pages_union ps_acc i trans:
    trans_ps_disj trans ->
  currently_accessible_in_trans_memory_pages i trans ⊆ ps_acc  ->
        ps_acc ∖ transferred_memory_pages i trans ∪ transferred_memory_pages i trans
            = ps_acc ∪ accessible_in_trans_memory_pages i trans.
  Proof.
    intros.
    rewrite accessible_retrieved_lending_memory_pages_difference;auto.
      pose proof (retrieved_lending_currently_accessible_memory_pages_subseteq i trans).
    rewrite difference_difference_union.
    2: {
      set_solver.
    }
    rewrite -union_assoc_L.
    rewrite (union_comm_L (retrieved_lending_memory_pages i trans)).
    rewrite difference_union_L.
    pose proof (currently_accessible_accessible_memory_pages_subseteq i trans).
    rewrite (union_comm_L _ (retrieved_lending_memory_pages i trans)).
    rewrite (subseteq_union_1_L (retrieved_lending_memory_pages i trans)).
    2: set_solver.
    apply difference_union_L.
  Qed.

  (** accessible_in_trans_memory_pages **)
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

  Lemma accessible_in_trans_memory_pages_insert_True_None i trans h tran:
    trans !! h = None ->
    (tran.1.1.1.1 = i  ∧ ¬(tran.2 = true ∧ tran.1.2 = Lending)) ∨ tran.1.1.1.2 = i ->
    accessible_in_trans_memory_pages i (<[h:= tran]>trans) = accessible_in_trans_memory_pages i trans ∪ tran.1.1.2.
  Proof.
  Admitted.

  Lemma accessible_in_trans_memory_pages_insert_True_Some i trans h tran tran':
    trans !! h = Some tran ->
    (tran'.1.1.1.1 = i  ∧ ¬(tran'.2 = true ∧ tran'.1.2 = Lending)) ∨ tran'.1.1.1.2 = i ->
    accessible_in_trans_memory_pages i (<[h:= tran']>trans) = accessible_in_trans_memory_pages i trans  ∖ tran.1.1.2 ∪ tran'.1.1.2.
  Proof.
  Admitted.

  Lemma accessible_in_trans_memory_pages_insert_False_None i trans h tran:
    trans !! h = None ->
    ¬((tran.1.1.1.1 = i  ∧ ¬(tran.2 = true ∧ tran.1.2 = Lending)) ∨ tran.1.1.1.2 = i) ->
    accessible_in_trans_memory_pages i (<[h:= tran]>trans) = accessible_in_trans_memory_pages i trans.
  Proof.
  Admitted.

  Lemma accessible_in_trans_memory_pages_insert_False_Some i trans h tran tran':
    trans !! h = Some tran ->
    ¬((tran'.1.1.1.1 = i  ∧ ¬(tran'.2 = true ∧ tran'.1.2 = Lending)) ∨ tran'.1.1.1.2 = i) ->
    trans_ps_disj trans ->
    accessible_in_trans_memory_pages i (<[h:= tran']>trans) = accessible_in_trans_memory_pages i trans ∖ tran.1.1.2.
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

  (** currently_accessible_in_trans_memory_pages **)
  Lemma currently_accessible_in_trans_memory_pages_lookup_True i trans h tran:
    trans !! h = Some tran ->
    ((tran.1.1.1.1 = i ∧ tran.1.2 = Sharing) ∨ (tran.1.1.1.2 = i ∧ tran.2 = true)) ->
    tran.1.1.2 ⊆ (currently_accessible_in_trans_memory_pages i trans).
  Proof.
  Admitted.

  Lemma currently_accessible_in_trans_memory_pages_lookup_False i trans h tran:
    trans !! h = Some tran ->
    ¬((tran.1.1.1.1 = i ∧ tran.1.2 = Sharing) ∨ (tran.1.1.1.2 = i ∧ tran.2 = true)) ->
    trans_ps_disj trans ->
    tran.1.1.2 ## (currently_accessible_in_trans_memory_pages i trans).
  Proof.
  Admitted.

  Lemma currently_accessible_in_trans_memory_pages_insert_True_None i trans h tran:
    trans !! h = None ->
    (tran.1.1.1.1 = i ∧ tran.1.2 = Sharing) ∨ (tran.1.1.1.2 = i ∧ tran.2 = true) ->
    currently_accessible_in_trans_memory_pages i (<[h:= tran]>trans) = currently_accessible_in_trans_memory_pages i trans ∪ tran.1.1.2.
  Proof.
    intros.
    rewrite /currently_accessible_in_trans_memory_pages.
    rewrite map_filter_insert_True //.
    rewrite pages_in_trans_insert //.
    set_solver +.
    rewrite map_filter_lookup_None.
    left;done.
  Qed.

  Lemma currently_accessible_in_trans_memory_pages_insert_True_Some i trans h tran tran':
    trans !! h = Some tran ->
    (tran'.1.1.1.1 = i ∧ tran'.1.2 = Sharing) ∨ (tran'.1.1.1.2 = i ∧ tran'.2 = true) ->
    trans_ps_disj trans ->
    currently_accessible_in_trans_memory_pages i (<[h:= tran']>trans) = currently_accessible_in_trans_memory_pages i trans ∖ tran.1.1.2 ∪ tran'.1.1.2.
  Proof.
    intros Hlk P' Hdisj.
    rewrite /currently_accessible_in_trans_memory_pages.
    rewrite map_filter_insert_True //.
    destruct (decide ((tran.1.1.1.1 = i ∧ tran.1.2 = Sharing) ∨ (tran.1.1.1.2 = i ∧ tran.2 = true))).
    {
      apply pages_in_trans_insert_strong.
      rewrite map_filter_lookup_Some.
      split;auto.
      eapply trans_ps_disj_subseteq;eauto.
      apply map_filter_subseteq.
    }
    {
      rewrite pages_in_trans_insert.
      2: {
        rewrite map_filter_lookup_None.
        right;simpl. intros ? Hlk'.
        rewrite Hlk' in Hlk.
        inversion Hlk.
        done.
      }
      feed pose proof(currently_accessible_in_trans_memory_pages_lookup_False i trans h tran);auto.
      set_solver + H.
    }
  Qed.

  Lemma currently_accessible_in_trans_memory_pages_insert_False_None i trans h tran:
    trans !! h = None ->
    ¬((tran.1.1.1.1 = i ∧ tran.1.2 = Sharing) ∨ (tran.1.1.1.2 = i ∧ tran.2 = true)) ->
    currently_accessible_in_trans_memory_pages i (<[h:= tran]>trans) = currently_accessible_in_trans_memory_pages i trans.
  Proof.
    intros.
    rewrite /currently_accessible_in_trans_memory_pages.
    rewrite map_filter_insert_False //.
    rewrite map_filter_delete.
    rewrite pages_in_trans_delete_None //.
    rewrite map_filter_lookup_None.
    left;done.
  Qed.

   Lemma currently_accessible_in_trans_memory_pages_insert_False_Some i trans h tran tran':
    trans !! h = Some tran ->
    ¬((tran'.1.1.1.1 = i ∧ tran'.1.2 = Sharing) ∨ (tran'.1.1.1.2 = i ∧ tran'.2 = true)) ->
    trans_ps_disj trans ->
    currently_accessible_in_trans_memory_pages i (<[h:= tran']>trans) = currently_accessible_in_trans_memory_pages i trans ∖ tran.1.1.2.
  Proof.
    intros Hlk nP' Hdisj.
    rewrite /currently_accessible_in_trans_memory_pages.
    rewrite map_filter_insert_False //.
    rewrite map_filter_delete.
    destruct (decide ((tran.1.1.1.1 = i ∧ tran.1.2 = Sharing) ∨ (tran.1.1.1.2 = i ∧ tran.2 = true))).
    {
      apply pages_in_trans_delete.
      rewrite map_filter_lookup_Some.
      split;auto.
      eapply trans_ps_disj_subseteq;eauto.
      apply map_filter_subseteq.

    }
    {
      feed pose proof(currently_accessible_in_trans_memory_pages_lookup_False i trans h tran);auto.
      rewrite pages_in_trans_delete_None.
      2: {
        rewrite map_filter_lookup_None.
        right;simpl. intros ? Hlk'.
        rewrite Hlk' in Hlk.
        inversion Hlk.
        done.
      }
      set_solver + H.
    }
  Qed.

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

  Lemma memory_pages_merge_mb {i p_rx p_tx ps_acc trans mem_tx mem_rx mem_all}:
  let ps_mem_in_trans := accessible_in_trans_memory_pages i trans in
  p_rx ∉ ps_acc ∖ {[p_rx; p_tx]} ∪ ps_mem_in_trans ->
  p_tx ∉ ps_acc ∖ {[p_rx; p_tx]} ∪ ps_mem_in_trans ->
   {[p_tx; p_rx]}⊆ ps_acc  ->
   memory_pages (ps_acc ∖ {[p_rx; p_tx]} ∪ ps_mem_in_trans) mem_all ∗
   memory_page p_tx mem_tx ∗
   memory_page p_rx mem_rx
   ⊢ ∃ mem, memory_pages (ps_acc ∪ ps_mem_in_trans) mem.
  Proof.
    iIntros (? Hnin_rx Hnin_tx Hsubset_mb) "(mem & mem_tx & mem_rx)".
    iExists (mem_all ∪ mem_rx ∪ mem_tx).
    assert (accessible_in_trans_memory_pages i trans ## {[p_tx]}) as Hdisj_ps_tx' by set_solver.
    assert (accessible_in_trans_memory_pages i trans ## {[p_rx]}) as Hdisj_ps_rx' by set_solver.
    assert (ps_acc ∖ {[p_rx; p_tx]} ∪ ps_mem_in_trans ∪ {[p_rx; p_tx]} = (ps_acc ∪ ps_mem_in_trans)) as <-.
    {
      rewrite -union_assoc_L.
      rewrite (union_comm_L _ {[p_rx; p_tx]}).
      rewrite union_assoc_L.
      rewrite difference_union_L.
      f_equal.
      rewrite union_comm_L.
      rewrite subseteq_union_1_L //.
      set_solver + Hsubset_mb.
    }
    iApply (memory_pages_split_union with "[mem mem_rx mem_tx]").
    { set_solver. }
    iDestruct (memory_page_neq with "[$mem_tx $mem_rx]") as %Hneq_tx_rx.
    iExists mem_all, (mem_rx ∪ mem_tx). iFrame "mem".
    rewrite memory_pages_split_union.
    iSplit.
    iExists mem_rx, mem_tx. rewrite 2!memory_pages_singleton. iFrame "mem_rx mem_tx".
    done.
    iPureIntro. rewrite map_union_assoc //. set_solver + Hneq_tx_rx.
  Qed.

  Lemma vmprop_zero_equiv_rxs{p_tx p_rx} i rxs rxs' :
  delete i rxs = delete i rxs' ->
  VMProp V0 (vmprop_zero i p_tx p_rx rxs) (1 / 2) ⊣⊢
  VMProp V0 (vmprop_zero i p_tx p_rx rxs') (1 / 2).
  Proof.
    intro.
    rewrite /VMProp /=.
    do 7 f_equiv.
    rewrite /vmprop_zero.
    rewrite /vmprop_zero_pre.
    do 12 f_equiv.
    rewrite /return_reg_rx.
    do 4 f_equiv.
    done.
    do 12 f_equiv.
    done.
  Qed.


End logrel_extra.
