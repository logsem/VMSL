From iris.proofmode Require Import tactics.
From machine_program_logic.program_logic Require Import weakestpre.
From HypVeri.lang Require Import lang.
From HypVeri.algebra Require Import base.
From HypVeri.logrel Require Import logrel.
From HypVeri Require Import proofmode.
From stdpp Require fin_map_dom.
Import uPred.


Section sep_map.
  Context `{Countable K} {A : Type}.
  Context {PROP : bi}.
  Implicit Types m : gmap K A.
  Implicit Types Φ Ψ : K → A → PROP.


  (* NOTE: The following lemmas are for spliting the accessor to get resources
          at more than one place in the proof from a big_sepM *)
  (* We are not using them for two reasons:
    1. big_sepM_union_acc depends on big_sepM_acc_diff, which is (I think) not provable;
    2. We actually _can_ get all resource by only splitting a big_sepM once in the ftlr proof;
    3. Proving big_sepM_union_acc was really painfull and dull ...
    *)
  (* Lemma big_sepM_acc_diff m m1 Φ: *)
  (*     m1 ⊆ m -> *)
  (*     (([∗ map] k↦y ∈ m1, Φ k y) -∗ [∗ map] k↦y ∈ (m1 ∪ m), Φ k y) *)
  (*    ⊢ [∗ map] k↦y ∈ (m ∖ m1), Φ k y. *)
  (*   Proof. *)
  (*     Admitted. *)

  (* Lemma big_sepM_union_acc m m1 m2 Φ `{!∀ m m'', Absorbing (([∗ map] k↦y ∈ m'', Φ k y) -∗ ([∗ map] k↦y ∈ m1, Φ k y) -∗ [∗ map] k↦y ∈ (m'' ∪ m1 ∪ m), Φ k y)} : *)
  (*   m1 ⊆ m -> *)
  (*   m2 ⊆ m ∖ m1 -> *)
  (*   ( ([∗ map] k↦y ∈ m1, Φ k y) *)
  (*    -∗ [∗ map] k↦y ∈ (m1 ∪ m) , Φ k y) *)
  (*   ⊢ *)
  (*   ([∗ map] k↦y ∈ m2, Φ k y) ∗ *)
  (*     (∀ m2', ⌜ (dom (gset K) m2) = (dom (gset K) m2') ⌝ *)
  (*             -∗ ([∗ map] k↦y ∈ m2', Φ k y) *)
  (*             -∗ ([∗ map] k↦y ∈ m1, Φ k y) *)
  (*             -∗ [∗ map] k↦y ∈ (m2' ∪ m1 ∪ m) , Φ k y). *)
  (* Proof. *)
  (*   iIntros (Hsubseteq1 Hsubseteq2) "Hmap". *)
  (*   pose proof (map_difference_union m2 (m ∖ m1) Hsubseteq2) as Hrewrite. *)
  (*   iDestruct(big_sepM_acc_diff with "Hmap") as "Hmap". *)
  (*   done. *)
  (*   rewrite <-Hrewrite. *)
  (*   iDestruct (big_sepM_union with "Hmap") as "[Hmap1 Hmap_restore]". *)
  (*   apply map_disjoint_difference_r; auto. *)
  (*   iSplitL "Hmap1"; first iFrame. *)
  (*   iIntros (m''). *)
  (*   iApply pure_wand_forall. *)
  (*   iIntros (Hdomeq) "Hmap1 Hmap2". *)
  (*   iCombine "Hmap1 Hmap_restore" as "Hmap". *)
  (*   rewrite <-(big_opM_union _ m'' (m ∖ m1 ∖ m2)). *)
  (*   2:{ *)
  (*     rewrite map_disjoint_dom. *)
  (*     rewrite -Hdomeq. *)
  (*     rewrite -map_disjoint_dom. *)
  (*     apply map_disjoint_difference_r; auto. *)
  (*   } *)
  (*   iCombine "Hmap2 Hmap" as "Hmap". *)
  (*   assert(Hdom_disj: m1 ##ₘm2). *)
  (*   { *)
  (*     rewrite map_disjoint_dom. *)
  (*     apply subseteq_dom in Hsubseteq2. *)
  (*     rewrite dom_difference in Hsubseteq2. *)
  (*     set_solver. *)
  (*   } *)
  (*   rewrite -big_opM_union. *)
  (*   2:{ *)
  (*     rewrite map_disjoint_dom. *)
  (*     rewrite dom_union. *)
  (*     rewrite !dom_difference. *)
  (*     rewrite disjoint_union_r . *)
  (*     split. *)
  (*     rewrite -Hdomeq. *)
  (*     rewrite -map_disjoint_dom //. *)
  (*     apply disjoint_difference_r2. *)
  (*     set_solver. *)
  (*   } *)
  (*   assert (m1 ∪ (m'' ∪ m ∖ m1 ∖ m2) = (m'' ∪ (m1 ∪ m ∖ m1) ∖ m2)) as ->. *)
  (*   { *)
  (*     apply map_eq_iff. *)
  (*     intro. *)
  (*     destruct ((m'' ∪ (m1 ∪ m ∖ m1) ∖ m2) !! i) eqn:Heqn. *)
  (*     - apply lookup_union_Some in Heqn. *)
  (*       2:{ *)
  (*         apply map_disjoint_dom. *)
  (*         rewrite dom_difference. *)
  (*         rewrite Hdomeq. *)
  (*         set_solver + Hdomeq. *)
  (*       } *)
  (*       destruct Heqn as [Hlookup|Hlookup]. *)
  (*       + *)
  (*         assert (is_Some (m'' !! i)) as Hsome_m''. *)
  (*         by exists a. *)
  (*                   apply elem_of_dom in Hsome_m''. *)
  (*                   destruct ((m'' ∪ m1 ∪ m) !! i) eqn:Hlookup'. *)
  (*                   * apply lookup_union_Some_raw. *)
  (*                     right. *)
  (*                     split. *)
  (*                     apply not_elem_of_dom. *)
  (*                     rewrite map_disjoint_dom in Hdom_disj. *)
  (*                     rewrite Hdomeq in Hdom_disj. *)
  (*                     set_solver. *)
  (*                     apply lookup_union_Some_raw in Hlookup'. *)
  (*                     destruct Hlookup'. *)
  (*                     { *)
  (*                       apply lookup_union_Some in H1. *)
  (*                       destruct H1. *)
  (*                       rewrite H1 in Hlookup. *)
  (*                       inversion Hlookup. *)
  (*                       subst a0. *)
  (*                       apply lookup_union_Some_raw. *)
  (*                       left. *)
  (*                       done. *)
  (*                       assert (is_Some (m1 !! i)) as Hsome_m1. *)
  (*                       by exists a0. *)
  (*                                 apply elem_of_dom in Hsome_m1. *)
  (*                                 apply map_disjoint_dom in Hdom_disj. *)
  (*                                 rewrite -Hdomeq in Hsome_m''. *)
  (*                                 set_solver. *)
  (*                                 apply map_disjoint_dom. *)
  (*                                 rewrite -Hdomeq. *)
  (*                                 apply map_disjoint_dom in Hdom_disj. *)
  (*                                 set_solver. *)
  (*                     } *)
  (*                     destruct H1. *)
  (*                     apply lookup_union_None in H1. *)
  (*                     destruct H1. *)
  (*                     rewrite H1 //in Hlookup. *)
  (*                   * rewrite !lookup_union_None in Hlookup'. *)
  (*                     destruct Hlookup' as [[Hlookup' _] _]. *)
  (*                     rewrite Hlookup' //in Hlookup. *)
  (*                   + *)
  (*                     assert (m1 ∪ m ∖ m1 = m1 ∪ m) as Heq. *)
  (*                     { *)
  (*                       apply map_eq_iff. *)
  (*                       intro. *)
  (*                       destruct ((m1 ∪ m ∖ m1) !! i0) eqn:Heqn. *)
  (*                       - apply lookup_union_Some in Heqn. *)
  (*                         2:{ *)
  (*                           apply map_disjoint_dom. *)
  (*                           set_solver +. *)
  (*                         } *)
  (*                         destruct Heqn as [Hlookup'|Hlookup'];symmetry. *)
  (*                         + *)
  (*                           apply lookup_union_Some_raw. *)
  (*                           left;done. *)
  (*                         + apply lookup_union_Some_raw. *)
  (*                           right. *)
  (*                           apply lookup_difference_Some in Hlookup'. *)
  (*                           destruct Hlookup'. *)
  (*                           split;eauto. *)
  (*                       - symmetry. *)
  (*                         apply lookup_union_None. *)
  (*                         apply lookup_union_None in Heqn. *)
  (*                         destruct Heqn as [Hlookup1 Hlookup2]. *)
  (*                         split;first done. *)
  (*                         apply  lookup_difference_None in Hlookup2. *)
  (*                         destruct Hlookup2 as [Hlookup_none|Hlookup_some]. *)
  (*                         done. *)
  (*                         destruct Hlookup_some. *)
  (*                         rewrite H1 // in Hlookup1. *)
  (*                     } *)
  (*                     rewrite Heq in Hlookup. *)
  (*                     apply lookup_difference_Some in Hlookup. *)
  (*                     destruct Hlookup. *)
  (*                     clear Heq. *)
  (*                     destruct ((m'' ∪ m1 ∪ m) !! i) eqn:Hlookup'. *)
  (*                     * apply lookup_union_Some_raw. *)
  (*                       apply lookup_union_Some_raw in H1. *)
  (*                       destruct H1. *)
  (*                       { *)
  (*                         left. *)
  (*                         apply lookup_union_Some_raw in Hlookup'. *)
  (*                         destruct Hlookup'. *)
  (*                         rewrite lookup_union_Some in H3. *)
  (*                         done. *)
  (*                         rewrite map_disjoint_dom. *)
  (*                         rewrite -Hdomeq. *)
  (*                         rewrite map_disjoint_dom in Hdom_disj. *)
  (*                         set_solver. *)
  (*                         done. *)
  (*                       } *)
  (*                       { *)
  (*                         right. *)
  (*                         destruct H1. *)
  (*                         split;eauto. *)
  (*                         apply lookup_union_Some_raw. *)
  (*                         right. *)
  (*                         split. *)
  (*                         apply not_elem_of_dom. *)
  (*                         apply not_elem_of_dom in H2. *)
  (*                         rewrite -Hdomeq //. *)
  (*                         rewrite !lookup_union_Some_raw in Hlookup'. *)
  (*                         destruct Hlookup'. *)
  (*                         destruct H4. *)
  (*                         apply not_elem_of_dom in H2. *)
  (*                         rewrite Hdomeq in H2. *)
  (*                         assert (is_Some (m'' !! i)) as Hsome_m''. *)
  (*                         by exists a0. *)
  (*                                   apply elem_of_dom in Hsome_m''. *)
  (*                                   set_solver. *)
  (*                                   destruct H4. *)
  (*                                   rewrite H5 //in H1. *)
  (*                                   destruct H4. *)
  (*                                   rewrite !lookup_difference_Some;split;try(split);done. *)
  (*                       } *)
  (*                     *  rewrite lookup_union_None in Hlookup'. *)
  (*                        rewrite lookup_union_Some_raw in H1. *)
  (*                        destruct H1. *)
  (*                        rewrite !lookup_union_None in Hlookup'. *)
  (*                        destruct Hlookup' as [[_ Hlookup1] _]. *)
  (*                        rewrite H1 //in Hlookup1. *)
  (*                        rewrite !lookup_union_None in Hlookup'. *)
  (*                        destruct H1. *)
  (*                        destruct Hlookup' as [_ Hlookup']. *)
  (*                        rewrite H3 // in Hlookup'. *)
  (*                   - *)
  (*                     rewrite lookup_union_None in Heqn. *)
  (*                     rewrite lookup_difference_None in Heqn. *)
  (*                     rewrite !lookup_union_None in Heqn. *)
  (*                     rewrite lookup_difference_None in Heqn. *)
  (*                     destruct Heqn. *)
  (*                     destruct H2. *)
  (*                     destruct H2. *)
  (*                     destruct H3. *)
  (*                     rewrite !lookup_union_None. *)
  (*                     rewrite !lookup_difference_None. *)
  (*                     repeat split;eauto. *)
  (*                     destruct H3. *)
  (*                     rewrite H3 // in H2. *)
  (*                     apply elem_of_dom in H2. *)
  (*                     apply not_elem_of_dom in H1. *)
  (*                     rewrite Hdomeq in H2. *)
  (*                     set_solver. *)
  (*   } *)
  (*   assert ( m1 ∪ m ∖ m1 = m1 ∪ m) as ->. *)
  (*   { *)
  (*     apply map_eq_iff. *)
  (*     intro. *)
  (*     destruct ((m1 ∪ m ∖ m1) !! i) eqn:Heqn. *)
  (*     - apply lookup_union_Some in Heqn. *)
  (*       2:{ *)
  (*         apply map_disjoint_dom. *)
  (*         set_solver +. *)
  (*       } *)
  (*       destruct Heqn as [Hlookup|Hlookup];symmetry. *)
  (*       + *)
  (*         apply lookup_union_Some_raw. *)
  (*         left;done. *)
  (*       + apply lookup_union_Some_raw. *)
  (*         right. *)
  (*         apply lookup_difference_Some in Hlookup. *)
  (*         destruct Hlookup. *)
  (*         split;eauto. *)
  (*     - symmetry. *)
  (*       apply lookup_union_None. *)
  (*       apply lookup_union_None in Heqn. *)
  (*       destruct Heqn as [Hlookup1 Hlookup2]. *)
  (*       split;first done. *)
  (*       apply  lookup_difference_None in Hlookup2. *)
  (*       destruct Hlookup2 as [Hlookup_none|Hlookup_some]. *)
  (*       done. *)
  (*       destruct Hlookup_some. *)
  (*       rewrite H1 // in Hlookup1. *)
  (*   } *)
  (*   rewrite -!map_union_assoc. *)
  (*   assert (m'' ∪ (m1 ∪ m) = (m'' ∪ (m1 ∪ m) ∖ m2)) as ->. *)
  (*   { *)
  (*     apply map_eq_iff. *)
  (*     intro. *)
  (*     destruct ((m'' ∪ (m1 ∪ m) ∖ m2) !! i) eqn:Heqn. *)
  (*     - apply lookup_union_Some in Heqn. *)
  (*       2:{ *)
  (*         apply map_disjoint_dom. *)
  (*         rewrite -Hdomeq. *)
  (*         rewrite dom_difference. *)
  (*         set_solver +. *)
  (*       } *)
  (*       destruct Heqn as [Hlookup|Hlookup]. *)
  (*       + apply lookup_union_Some_raw. *)
  (*         left;done. *)
  (*       + apply lookup_union_Some_raw. *)
  (*         right. *)
  (*         apply lookup_difference_Some in Hlookup. *)
  (*         destruct Hlookup. *)
  (*         split. *)
  (*         apply not_elem_of_dom. *)
  (*         rewrite -Hdomeq. *)
  (*         by apply not_elem_of_dom. *)
  (*         done. *)
  (*     - apply lookup_union_None. *)
  (*       apply lookup_union_None in Heqn. *)
  (*       destruct Heqn as [Hlookup1 Hlookup2]. *)
  (*       split;first done. *)
  (*       apply  lookup_difference_None in Hlookup2. *)
  (*       destruct Hlookup2 as [Hlookup_none|Hlookup_some]. *)
  (*       done. *)
  (*       apply not_elem_of_dom in Hlookup1. *)
  (*       rewrite -Hdomeq in Hlookup1. *)
  (*       apply not_elem_of_dom in Hlookup1. *)
  (*       destruct Hlookup_some as [? Hlookup_some]. *)
  (*       rewrite Hlookup1 in Hlookup_some. *)
  (*       inversion Hlookup_some. *)
  (*   } *)
  (*   done. *)
  (* Qed. *)

(* TODO: move to iris.algebra.big_op *)

  Lemma big_sepM_union_acc m m' Φ `{!∀ m m'', Absorbing (([∗ map] k↦y ∈ m'', Φ k y)
              -∗ [∗ map] k↦y ∈ (m'' ∪  m) , Φ k y)} :
    m' ⊆ m ->
    ([∗ map] k↦y ∈ m, Φ k y) ⊢
    ([∗ map] k↦y ∈ m', Φ k y) ∗
      (∀ m'', ⌜ (dom (gset K) m') = (dom (gset K) m'') ⌝
              -∗ ([∗ map] k↦y ∈ m'', Φ k y)
              -∗ [∗ map] k↦y ∈ (m'' ∪  m) , Φ k y).
  Proof.
    iIntros (Hsubseteq) "Hmap".
    pose proof (map_difference_union m' m Hsubseteq) as Hrewrite.
    rewrite <-Hrewrite.
    iDestruct (big_sepM_union with "Hmap") as "[Hmap1 Hmap2]".
    apply map_disjoint_difference_r; auto.
    iSplitL "Hmap1"; first iFrame.
    iIntros (m'').
    iApply pure_wand_forall.
    iIntros (Hdomeq) "Hmap1".
    iCombine "Hmap1 Hmap2" as "Hmap".
    rewrite <-(big_opM_union _ m'' (m ∖ m')).
    2:{
     rewrite map_disjoint_dom.
     rewrite -Hdomeq.
     rewrite -map_disjoint_dom.
     apply map_disjoint_difference_r; auto.
    }
    rewrite Hrewrite.
    assert (m'' ∪ m = (m'' ∪ m ∖ m')) as ->;last done.
    apply map_eq_iff.
    intro.
    destruct ((m'' ∪ m ∖ m') !! i) eqn:Heqn.
    - apply lookup_union_Some in Heqn.
      2:{
      apply map_disjoint_dom.
      rewrite -Hdomeq.
      rewrite dom_difference.
      set_solver +.
      }
      destruct Heqn as [Hlookup|Hlookup].
      + apply lookup_union_Some_raw.
        left;done.
      + apply lookup_union_Some_raw.
        right.
        apply lookup_difference_Some in Hlookup.
        destruct Hlookup.
        split.
        apply not_elem_of_dom.
        rewrite -Hdomeq.
        by apply not_elem_of_dom.
        done.
    - apply lookup_union_None.
      apply lookup_union_None in Heqn.
      destruct Heqn as [Hlookup1 Hlookup2].
      split;first done.
      apply  lookup_difference_None in Hlookup2.
      destruct Hlookup2 as [Hlookup_none|Hlookup_some].
      done.
      apply not_elem_of_dom in Hlookup1.
      rewrite -Hdomeq in Hlookup1.
      apply not_elem_of_dom in Hlookup1.
      destruct Hlookup_some as [? Hlookup_some].
      rewrite Hlookup1 in Hlookup_some.
      inversion Hlookup_some.
  Qed.

End sep_map.

Section logrel_extra.

  Context `{hypconst:HypervisorConstants}.
  Context `{hypparams:!HypervisorParameters}.
  Context `{vmG: !gen_VMG Σ}.

  Lemma ra_big_sepM_split `{Countable K} { V :Type} (map : gmap K V) (k : K) (v:V)
         (f: K -> V -> iProp Σ)
    :
    map !! k = Some v ->
    (([∗ map] k↦y ∈ map, f k y)%I
     ⊢  (f k v) ∗ ( (f k v) -∗  [∗ map] k↦y ∈ map , f k y))%I.
  Proof.
    iIntros (Hlookup) "map".
    iDestruct (big_sepM_union_acc map {[k := v]} f with "map") as "[single Hacc]".
    {
      apply insert_subseteq_l ;first done.
      apply map_empty_subseteq.
    }
    iSplitL "single".
    {
      rewrite big_opM_singleton.
      iFrame.
    }
    iIntros "single".
      iDestruct ("Hacc" $! {[k := v]}) as "Hacc".
        assert (map = {[k := v]} ∪ map) as <-.
    {
      rewrite map_eq_iff.
      intro.
      destruct (decide (k = i)).
       - subst i.
         simplify_map_eq /=.
         done.
       - simplify_map_eq /=.
         rewrite lookup_union_r.
         done.
         apply lookup_singleton_None.
         done.
    }
    iApply "Hacc".
      iPureIntro. set_solver +.
      rewrite big_opM_singleton.
      iFrame.
  Qed.


  Lemma ra_big_sepM_split_upd `{Countable K} { V :Type} (map : gmap K V) (k : K) (v:V)
        (total:= (λ m, (∀ k,  ⌜is_Some (m !! k)⌝)%I) : gmap K V -> iProp Σ) (f: K -> V -> iProp Σ)
    :
    map !! k = Some v ->
    ((total map ∗ [∗ map] k↦y ∈ map, f k y)%I
     ⊢  (f k v) ∗ (∀ v', (f k v') -∗  total (<[k := v']>map) ∗ [∗ map] k↦y ∈ <[k := v']>map , f k y))%I.
  Proof.
    iIntros (Hlookup) "[#Htotal Hregs]".
    iPoseProof  ("Htotal" $! k) as "Hlookup".
    iDestruct (big_sepM_union_acc map {[k := v]} f with "Hregs") as "[Hsingle Hrestore]".
    {
      apply insert_subseteq_l ;first done.
      apply map_empty_subseteq.
    }
    iSplitL "Hsingle".
    {
      rewrite big_opM_singleton.
      iFrame.
    }
    iIntros (v') "Hsingle_upd".
    iSplitL "".
    {
      iIntros (?).
      iDestruct ("Htotal" $! k0) as "%Hlookup'".
      iPureIntro.
      destruct (decide (k = k0)).
       - subst k0.
         simplify_map_eq /=.
         done.
       - simplify_map_eq /=.
         done.
    }
    assert (<[k:= v']> map = {[k := v']} ∪ map) as ->.
    {
      rewrite map_eq_iff.
      intro.
      destruct (decide (k = i)).
       - subst i.
         simplify_map_eq /=.
         done.
       - simplify_map_eq /=.
         rewrite lookup_union_r.
         done.
         apply lookup_singleton_None.
         done.
    }
      iApply "Hrestore".
      iPureIntro. set_solver +.
      rewrite big_opM_singleton.
      iFrame.
  Qed.


  Lemma ra_big_sepM_split2 `{Countable K} { V :Type} (map : gmap K V) (k1 k2 : K) (v1 v2:V)
         (f: K -> V -> iProp Σ)
    :
    k1 ≠ k2 ->
    map !! k1 = Some v1 ->
    map !! k2 = Some v2 ->
    (([∗ map] k↦y ∈ map, f k y)%I
     ⊢  (f k1 v1) ∗ (f k2 v2) ∗ (((f k1 v1) ∗ (f k2 v2)) -∗  [∗ map] k↦y ∈ map , f k y))%I.
  Proof.
    iIntros (Hneq Hlookup1 Hlookup2) "map".
    iDestruct (big_sepM_union_acc map {[k1 := v1; k2:= v2]} f with "map") as "[singles Hacc]".
    {
      apply insert_subseteq_l ;first done.
      apply insert_subseteq_l ;first done.
      apply map_empty_subseteq.
    }
      rewrite !big_opM_insert.
    2: {
      done.
    }
    2: {
      apply lookup_singleton_None.
      done.
    }
    iDestruct "singles" as "(single1 & single2 & _)".
    iFrame.
    iIntros "single".
    iDestruct ("Hacc" $! {[k1 := v1; k2 := v2]}) as "Hacc".
    assert (map = {[k1 := v1; k2 := v2]} ∪ map) as <-.
    {
      rewrite map_eq_iff.
      intro.
      destruct (decide (k1 = i)).
      - subst i.
        simplify_map_eq /=.
        done.
      -
        destruct (decide (k2 = i)).
        + subst i.
          simplify_map_eq /=.
          symmetry.
          rewrite lookup_union_Some_raw.
          left.
          apply lookup_insert_Some.
          right.
          split;eauto.
          apply lookup_singleton_Some.
          done.
        + symmetry.
          destruct (map !! i) eqn:Hlookup.
          rewrite lookup_union_Some_raw.
          right.
          split;last done.
          rewrite !lookup_insert_None;repeat split;done.
          rewrite lookup_union_r.
          done.
          apply lookup_insert_None.
          split;eauto.
          apply lookup_singleton_None.
          done.
    }
    iApply "Hacc".
    iPureIntro. set_solver +.
    rewrite !big_opM_insert.
    iDestruct "single" as "[single1 single2]".
    iFrame.
    done.
      done.
      apply lookup_insert_None.
      split;done.
  Qed.

  Lemma ra_big_sepM_split_upd2 `{Countable K} { V :Type} (map : gmap K V) (k1 k2: K) (v1 v2:V)
        (total:= (λ m, (∀ k,  ⌜is_Some (m !! k)⌝)%I) : gmap K V -> iProp Σ) (f: K -> V -> iProp Σ):
    k1 ≠ k2 ->
    map !! k1 = Some v1 ->
    map !! k2 = Some v2 ->
    ((total map ∗ [∗ map] k↦y ∈ map, f k y)%I
     ⊢  (f k1 v1) ∗ (f k2 v2) ∗
          (∀ v1' v2', f k1 v1' ∗ f k2 v2'-∗ ∃ map', (total map' ∗ [∗ map] k↦y ∈ map', f k y)))%I.
  Proof.
    iIntros (Hneq Hlookup1 Hlookup2) "[%Htotal Hmaps]".
    pose proof (Htotal k1) as Hlookup_k1.
    pose proof (Htotal k2) as Hlookup_k2.
    simplify_map_eq.
    iDestruct (big_sepM_union_acc map {[k1 := v1 ; k2 := v2 ]} f with "Hmaps")
      as "[Hsingle Hrestore]".
    {
      apply insert_subseteq_l ;first done.
      apply insert_subseteq_l ;first done.
      apply map_empty_subseteq.
    }
    rewrite !big_opM_insert.
    2: {
      done.
    }
    2: {
      apply lookup_singleton_None.
      done.
    }
    iDestruct "Hsingle" as "(Hsingle1 & Hsingle2 & _)".
    iFrame "Hsingle1 Hsingle2".
    iIntros (v1' v2') "Hsingle_upd".
    iExists ({[k1 := v1'; k2:= v2']} ∪ map).
    iSplitL "".
    {
      iPureIntro.
      intro k0.
      specialize (Htotal k0).
      destruct Htotal as [? Hlookup_k0].
      destruct (decide (k1 = k0)).
      - subst k1.
        simplify_map_eq /=.
        done.
      - simplify_map_eq /=.
        destruct (decide (k2 = k0)).
        + exists v2'.
          rewrite lookup_union_Some_raw.
          left.
          subst k0.
          apply lookup_insert_Some.
          right.
          split;first done.
          apply lookup_insert_Some.
          left.
          rewrite Hlookup2 in Hlookup_k0.
          inversion Hlookup_k0;subst x. done.
        + exists x.
          rewrite lookup_union_Some_raw.
          right.
          split;last done.
          rewrite !lookup_insert_None;repeat split;done.
    }
    {
      iApply "Hrestore".
      iPureIntro. set_solver +.
      rewrite !big_opM_insert.
      iDestruct "Hsingle_upd" as "[Hsingle_upd1 Hsingle_upd2]".
      iFrame.
      done.
      done.
      apply lookup_insert_None.
      split;done.
    }
  Qed.

  Lemma ra_big_sepM_split_upd3 `{Countable K} { V :Type} (map : gmap K V) (k1 k2 k3: K) (v1 v2 v3:V)
        (total:= (λ m, (∀ k,  ⌜is_Some (m !! k)⌝)%I) : gmap K V -> iProp Σ) (f: K -> V -> iProp Σ):
    k1 ≠ k2 ->
    k1 ≠ k3 ->
    k2 ≠ k3 ->
    map !! k1 = Some v1 ->
    map !! k2 = Some v2 ->
    map !! k3 = Some v3 ->
    ((total map ∗ [∗ map] k↦y ∈ map, f k y)%I
     ⊢ f k1 v1 ∗ f k2 v2 ∗ f k3 v3 ∗
          (∀ v1' v2' v3', f k1 v1' ∗ f k2 v2' ∗ f k3 v3' -∗ ∃ map', (total map' ∗ [∗ map] k↦y ∈ map', f k y)))%I.
  Proof.
    iIntros (Hneq1 Hneq2 Hneq3 Hlookup1 Hlookup2 Hlookup3) "[%Htotal Hmaps]".
    pose proof (Htotal k1) as Hlookup_k1.
    pose proof (Htotal k2) as Hlookup_k2.
    pose proof (Htotal k3) as Hlookup_k3.
    simplify_map_eq.
    iDestruct (big_sepM_union_acc map {[k1 := v1 ; k2 := v2 ; k3 := v3]} f with "Hmaps")
      as "[Hsingle Hrestore]".
    {
      repeat apply insert_subseteq_l;eauto.
      apply map_empty_subseteq.
    }
    rewrite !big_opM_insert;try rewrite !lookup_insert_None;eauto.
    iDestruct "Hsingle" as "(single1 & single2 & single3 & _)".
    iFrame "single1 single2 single3".
    iIntros (v1' v2' v3') "Hsingle_upd".
    iExists ({[k1 := v1'; k2:= v2'; k3 := v3']} ∪ map).
    iSplitL "".
    {
      iPureIntro.
      intro k0.
      specialize (Htotal k0).
      destruct Htotal as [? Hlookup_k0].
      destruct (decide (k1 = k0)).
      - subst k1.
        simplify_map_eq /=.
        done.
      - simplify_map_eq /=.
        destruct (decide (k2 = k0)).
        + exists v2'.
          rewrite lookup_union_Some_raw.
          left.
          subst k0.
          apply lookup_insert_Some.
          right.
          split;first done.
          apply lookup_insert_Some.
          left.
          done.
        + destruct (decide (k3 = k0)).
          * simplify_map_eq /=.
            exists v3'.
            rewrite lookup_union_Some_raw.
            left.
            rewrite !lookup_insert_Some.
            right.
            split;first done.
            right.
            split;first done.
            left;done.
          * exists x.
            rewrite lookup_union_Some_raw.
            right.
            split;last done.
            rewrite !lookup_insert_None;repeat split;done.
    }
    {
      iApply "Hrestore".
      iPureIntro. set_solver +.
      rewrite !big_opM_insert.
      iDestruct "Hsingle_upd" as "(single_upd1 & single_upd2 & single_upd3)".
      iFrame.
      done.
      done.
      apply lookup_insert_None.
      split;done.
      rewrite !lookup_insert_None.
      repeat split;done.
    }
  Qed.

  (** registers **)
   (* we provide lookup, so r and w can be implicit *)
  Lemma reg_big_sepM_split reg i {r w}:
    reg !! r = Some w ->
    (([∗ map] k↦y ∈ reg, k @@ i ->r y)%I
     ⊢  (r @@ i ->r w) ∗ ( r @@ i ->r w -∗ [∗ map] k↦y ∈ reg, k @@ i ->r y))%I.
  Proof.
    rewrite /reg_file /total_reg_map.
    iIntros (Hlookup).
    iApply (ra_big_sepM_split reg r w (λ k v, k @@ i ->r v)%I Hlookup).
  Qed.


  Lemma reg_big_sepM_split_upd reg i {r w}:
    reg !! r = Some w ->
    ((total_reg_map (reg: gmap reg_name Addr) ∗ [∗ map] k↦y ∈ reg, k @@ i ->r y)%I
     ⊢  (r @@ i ->r w) ∗ (∀ w', r @@ i ->r w' -∗ total_reg_map (<[r := w']>reg) ∗ [∗ map] k↦y ∈  <[r := w']>reg, k @@ i ->r y))%I.
  Proof.
    rewrite /reg_file /total_reg_map.
    iIntros (Hlookup).
    iApply (ra_big_sepM_split_upd reg r w (λ k v, k @@ i ->r v)%I Hlookup).
  Qed.


  Lemma reg_big_sepM_split_upd2 reg i {r1 w1 r2 w2}:
    r1 ≠ r2 ->
    reg !! r1 = Some w1 ->
    reg !! r2 = Some w2 ->
    ((total_reg_map reg ∗ [∗ map] k↦y ∈ reg, k @@ i ->r y)%I
     ⊢  (r1 @@ i ->r w1) ∗ (r2 @@ i ->r w2) ∗
          (∀ w1' w2', r1 @@ i ->r w1' ∗ r2 @@ i ->r w2'-∗ ∃ reg', (total_reg_map reg' ∗ [∗ map] k↦y ∈ reg', k @@ i ->r y)))%I.
  Proof.
    iIntros (Hneq Hlookup1 Hlookup2) "[%Hfull Hregs]".
    iApply (ra_big_sepM_split_upd2 reg r1 r2 w1 w2 (λ k v, k @@ i ->r v)%I);eauto.
  Qed.

  Lemma reg_big_sepM_split_upd3 reg i {r1 w1 r2 w2 r3 w3}:
    r1 ≠ r2 ->
    r1 ≠ r3 ->
    r2 ≠ r3 ->
    reg !! r1 = Some w1 ->
    reg !! r2 = Some w2 ->
    reg !! r3 = Some w3 ->
    ((total_reg_map reg ∗ [∗ map] k↦y ∈ reg, k @@ i ->r y)%I
     ⊢  (r1 @@ i ->r w1) ∗ (r2 @@ i ->r w2) ∗ (r3 @@ i ->r w3) ∗
          (∀ w1' w2' w3', r1 @@ i ->r w1' ∗ r2 @@ i ->r w2' ∗ r3 @@ i ->r w3' -∗ ∃ reg', (total_reg_map reg' ∗ [∗ map] k↦y ∈ reg', k @@ i ->r y)))%I.
  Proof.
    iIntros (Hneq1 Hneq2 Hneq3 Hlookup1 Hlookup2 Hlookup3) "[%Hfull Hregs]".
    iApply (ra_big_sepM_split_upd3 reg r1 r2 r3 w1 w2 w3 (λ k v, k @@ i ->r v)%I);eauto.
  Qed.


(** pagetable **)
 Lemma pgt_big_sepM_split (pgt: gmap PID (VMID * gset VMID)) {p pe} {f: _ -> _ -> iProp Σ}:
    pgt !! p = Some pe->
    (( [∗ map] k↦y ∈ pgt, f k y)%I
     ⊢  (f p pe) ∗ (f p pe -∗ [∗ map] k↦y ∈ pgt, f k y))%I.
  Proof.
    rewrite /total_pgt_map.
    iIntros (Hlookup).
    iApply (ra_big_sepM_split pgt p pe f Hlookup).
  Qed.


 Lemma pgt_big_sepM_split2 (pgt: gmap PID (VMID * gset VMID)) {p1 p2 pe1 pe2} {f: _ -> _ -> iProp Σ}:
    p1 ≠ p2 ->
    pgt !! p1 = Some pe1 ->
    pgt !! p2 = Some pe2->
    (( [∗ map] k↦y ∈ pgt, f k y)%I
     ⊢  (f p1 pe1) ∗ (f p2 pe2) ∗ ((f p1 pe1 ∗ f p2 pe2 ) -∗ [∗ map] k↦y ∈ pgt, f k y))%I.
  Proof.
    rewrite /total_pgt_map.
    iIntros (Hneq Hlookup1 Hlookup2).
    iApply (ra_big_sepM_split2 pgt p1 p2 pe1 pe2 f);eauto.
  Qed.

  (* f is also implicit because coq can infer it from big_sepM *)
  Lemma pgt_big_sepM_split_upd2 (pgt: gmap PID (VMID * gset VMID)) {p1 p2 pe1 pe2} {f: _ -> _ -> iProp Σ}:
    p1 ≠ p2 ->
    pgt !! p1 = Some pe1->
    pgt !! p2 = Some pe2->
    ((total_pgt_map pgt ∗ [∗ map] k↦y ∈ pgt, f k y)%I
     ⊢  (f p1 pe1) ∗ (f p2 pe2)∗ (∀ (pe1' pe2' : VMID * gset VMID) , (f p1 pe1' ∗ f p2 pe2') -∗
                          ∃ (pgt': gmap PID (VMID * gset VMID) ), (total_pgt_map pgt' ∗ [∗ map] k↦y ∈ pgt', f k y)))%I.
  Proof.
    iIntros (Hneq Hlookup1 Hlookup2) "[%Htotal pgt]".
    iApply (ra_big_sepM_split_upd2 pgt p1 p2 pe1 pe2 f);eauto.
    Qed.

  (** memory **)

 Lemma mem_big_sepM_split (mem: gmap Addr Word) {a w} {f: _ -> _ -> iProp Σ}:
    mem !! a = Some w->
    (([∗ map] k↦y ∈ mem, f k y)
     ⊢  (f a w) ∗ (f a w -∗
                          ( [∗ map] k↦y ∈ mem, f k y)))%I.
  Proof.
    rewrite /total_mem_map.
    iIntros (Hlookup).
    iApply (ra_big_sepM_split mem a w f Hlookup).
  Qed.

  Lemma mem_big_sepM_split_upd (mem: gmap Addr Word) {a w} {f: _ -> _ -> iProp Σ}:
    mem !! a = Some w->
    ((total_mem_map mem ∗ [∗ map] k↦y ∈ mem, f k y)%I
     ⊢  (f a w) ∗ (∀ (w' : Word) , f a w' -∗
                          (total_mem_map (<[a := w']>mem) ∗ [∗ map] k↦y ∈ <[a := w']>mem, f k y)))%I.
  Proof.
    rewrite /total_mem_map.
    iIntros (Hlookup).
    iApply (ra_big_sepM_split_upd mem a w f Hlookup).
  Qed.

  Lemma mem_big_sepM_split2 (mem: gmap Addr Word) {a1 a2 w1 w2} {f: _ -> _ -> iProp Σ}:
    a1 ≠ a2 ->
    mem !! a1 = Some w1->
    mem !! a2 = Some w2->
    (([∗ map] k↦y ∈ mem, f k y)
     ⊢  f a1 w1 ∗ f a2 w2 ∗ ((f a1 w1 ∗ f a2 w2) -∗
                            ( [∗ map] k↦y ∈ mem, f k y)))%I.
  Proof.
    rewrite /total_mem_map.
    iIntros (Hneq Hlookup1 Hlookup2).
    iApply (ra_big_sepM_split2 mem a1 a2 w1 w2 f);eauto.
  Qed.

  Lemma mem_big_sepM_split_upd2 (mem: gmap Addr Word) {a1 a2 w1 w2} {f: _ -> _ -> iProp Σ}:
    a1 ≠ a2 ->
    mem !! a1 = Some w1->
    mem !! a2 = Some w2->
    ((total_mem_map mem ∗ [∗ map] k↦y ∈ mem, f k y)%I
     ⊢  f a1 w1 ∗ f a2 w2 ∗ (∀ (w1' w2' : Word) , (f a1 w1' ∗ f a2 w2') -∗
                          ∃ mem', (total_mem_map mem' ∗ [∗ map] k↦y ∈ mem', f k y)))%I.
  Proof.
    rewrite /total_mem_map.
    iIntros (Hneq Hlookup1 Hlookup2).
    iApply (ra_big_sepM_split_upd2 mem a1 a2 w1 w2 f);eauto.
  Qed.



  (* TODO: For memory chunks *)

End logrel_extra.
