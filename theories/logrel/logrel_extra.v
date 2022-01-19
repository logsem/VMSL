From iris.proofmode Require Import tactics.
From machine_program_logic.program_logic Require Import weakestpre.
From HypVeri.lang Require Import lang.
From HypVeri.algebra Require Import base base_extra.
From HypVeri.logrel Require Import logrel.
From HypVeri Require Import proofmode.
From stdpp Require fin_map_dom.
Import uPred.


Section sep_map.
  Context `{Countable K} {A : Type}.
  Context {PROP : bi}.
  Implicit Types m : gmap K A.
  Implicit Types Φ Ψ : K → A → PROP.


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
        (f: K -> V -> iProp Σ) :
    map !! k = Some v ->
    (([∗ map] k↦y ∈ map, f k y)%I
     ⊢  (f k v) ∗ (∀ v', (f k v') -∗ [∗ map] k↦y ∈ <[k := v']>map , f k y))%I.
  Proof.
    iIntros (Hlookup) "bigM".
    iDestruct (big_sepM_union_acc map {[k := v]} f with "bigM") as "[single Hrestore]".
    {
      apply insert_subseteq_l ;first done.
      apply map_empty_subseteq.
    }
    iSplitL "single".
    {
      rewrite big_opM_singleton.
      iFrame.
    }
    iIntros (v') "Hsingle_upd".
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

  Lemma ra_big_sepM_split_upd_with_total `{Countable K} { V :Type} (map : gmap K V) (k : K) (v:V)
        (total:= (λ m, (∀ k,  is_Some (m !! k))) : gmap K V -> Prop) (f: K -> V -> iProp Σ)
    :
    map !! k = Some v ->
    ((⌜total map⌝ ∗ [∗ map] k↦y ∈ map, f k y)%I
     ⊢  (f k v) ∗ (∀ v', (f k v') -∗  ⌜total (<[k := v']>map)⌝ ∗ [∗ map] k↦y ∈ <[k := v']>map , f k y))%I.
  Proof.
    iIntros (Hlookup) "[%Htotal Hregs]".
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
      iIntros (k0).
      iPureIntro.
      pose proof (Htotal k0) as Hlookup'.
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
        (total:= (λ m, (∀ k, is_Some (m !! k))) : gmap K V -> Prop) (f: K -> V -> iProp Σ):
    k1 ≠ k2 ->
    map !! k1 = Some v1 ->
    map !! k2 = Some v2 ->
    ((⌜total map⌝ ∗ [∗ map] k↦y ∈ map, f k y)%I
     ⊢  (f k1 v1) ∗ (f k2 v2) ∗
          (∀ v1' v2', f k1 v1' ∗ f k2 v2'-∗ ∃ map', (⌜total map'⌝ ∗ [∗ map] k↦y ∈ map', f k y)))%I.
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
        (total:= (λ m, (∀ k, is_Some (m !! k))) : gmap K V -> Prop) (f: K -> V -> iProp Σ):
    k1 ≠ k2 ->
    k1 ≠ k3 ->
    k2 ≠ k3 ->
    map !! k1 = Some v1 ->
    map !! k2 = Some v2 ->
    map !! k3 = Some v3 ->
    ((⌜total map⌝ ∗ [∗ map] k↦y ∈ map, f k y)%I
     ⊢ f k1 v1 ∗ f k2 v2 ∗ f k3 v3 ∗
          (∀ v1' v2' v3', f k1 v1' ∗ f k2 v2' ∗ f k3 v3' -∗ ∃ map', (⌜total map'⌝ ∗ [∗ map] k↦y ∈ map', f k y)))%I.
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
    rewrite /reg_file.
    iIntros (Hlookup).
    iApply (ra_big_sepM_split reg r w (λ k v, k @@ i ->r v)%I Hlookup).
  Qed.


  Lemma reg_big_sepM_split_upd reg i {r w}:
    reg !! r = Some w ->
    ((⌜is_total_gmap (reg: gmap reg_name Addr)⌝ ∗ [∗ map] k↦y ∈ reg, k @@ i ->r y)%I
     ⊢  (r @@ i ->r w) ∗ (∀ w', r @@ i ->r w' -∗ ⌜is_total_gmap (<[r := w']>reg)⌝ ∗ [∗ map] k↦y ∈  <[r := w']>reg, k @@ i ->r y))%I.
  Proof.
    rewrite /reg_file /is_total_gmap.
    iIntros (Hlookup).
    iApply (ra_big_sepM_split_upd_with_total reg r w (λ k v, k @@ i ->r v)%I Hlookup).
  Qed.


  Lemma reg_big_sepM_split_upd2 reg i {r1 w1 r2 w2}:
    r1 ≠ r2 ->
    reg !! r1 = Some w1 ->
    reg !! r2 = Some w2 ->
    ((⌜is_total_gmap reg⌝ ∗ [∗ map] k↦y ∈ reg, k @@ i ->r y)%I
     ⊢  (r1 @@ i ->r w1) ∗ (r2 @@ i ->r w2) ∗
          (∀ w1' w2', r1 @@ i ->r w1' ∗ r2 @@ i ->r w2'-∗ ∃ reg', (⌜is_total_gmap reg'⌝ ∗ [∗ map] k↦y ∈ reg', k @@ i ->r y)))%I.
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
    ((⌜is_total_gmap reg⌝ ∗ [∗ map] k↦y ∈ reg, k @@ i ->r y)%I
     ⊢  (r1 @@ i ->r w1) ∗ (r2 @@ i ->r w2) ∗ (r3 @@ i ->r w3) ∗
          (∀ w1' w2' w3', r1 @@ i ->r w1' ∗ r2 @@ i ->r w2' ∗ r3 @@ i ->r w3' -∗ ∃ reg', (⌜is_total_gmap reg'⌝ ∗ [∗ map] k↦y ∈ reg', k @@ i ->r y)))%I.
  Proof.
    iIntros (Hneq1 Hneq2 Hneq3 Hlookup1 Hlookup2 Hlookup3) "[%Hfull Hregs]".
    iApply (ra_big_sepM_split_upd3 reg r1 r2 r3 w1 w2 w3 (λ k v, k @@ i ->r v)%I);eauto.
  Qed.

  (* lemmas about [memory_pages] *)
  Notation fold_union_addr_of_page b ps :=
    (set_fold (λ (p : PID) (acc : gset Addr), list_to_set (addr_of_page p) ∪ acc) b ps).

  Lemma fold_union_addr_of_page_strong_assoc_comm (X : gset PID):
    ∀ (x1 x2 : PID) (b' : gset Addr),
    x1 ∈ X
    → x2 ∈ X
    → x1 ≠ x2
    → list_to_set (addr_of_page x1) ∪ (list_to_set (addr_of_page x2) ∪ b') =
        list_to_set (addr_of_page x2) ∪ (list_to_set (addr_of_page x1) ∪ b').
  Proof.
    intros ? ? b Hin1 Hin2 Hneq.
    rewrite assoc_L.
    rewrite assoc_L.
    f_equal.
    rewrite comm_L //.
  Qed.

  Lemma fold_union_addr_of_page_comm (s1 : gset PID) (s2 s3: gset Addr) :
    fold_union_addr_of_page (s3 ∪ s2) s1 = s3 ∪ fold_union_addr_of_page s2 s1.
  Proof.
    revert s1 s2 s3.
    induction s1 using set_ind_L.
    {
      intros.
      rewrite !set_fold_empty.
      done.
    }
    {
      intros.
      rewrite (set_fold_disj_union_strong _ _  (s3 ∪ s2) {[x]} X).
      {
        rewrite set_fold_singleton.
        assert ((list_to_set (addr_of_page x) ∪ (s3 ∪ s2)) = (s3 ∪ (list_to_set (addr_of_page x) ∪  s2))) as ->.
        {
          rewrite (union_assoc_L _ s3 s2).
          rewrite (union_comm_L _ s3).
          rewrite union_assoc_L //.
        }
        rewrite IHs1.
        rewrite (set_fold_disj_union_strong _ _ s2 {[x]} X).
        rewrite set_fold_singleton //.
        apply fold_union_addr_of_page_strong_assoc_comm.
        set_solver + H.
      }
      apply fold_union_addr_of_page_strong_assoc_comm.
      set_solver + H.
    }
  Qed.

  Lemma fold_union_addr_of_page_disj_aux (p: PID) (s1 : gset PID) (s2: gset Addr) : p ∉ s1 ->
    (list_to_set (addr_of_page p)) ## s2 ->
    (list_to_set (addr_of_page p)) ## (fold_union_addr_of_page s2 s1).
  Proof.
    revert s1 s2.
    induction s1 using set_ind_L.
    {
      intros.
      rewrite set_fold_empty.
      done.
    }
    {
      intros.
      rewrite (set_fold_disj_union_strong _ _ s2 {[x]} X).
      {
        rewrite set_fold_singleton.
        rewrite fold_union_addr_of_page_comm.
        apply disjoint_union_r.
        split.
        { apply addr_of_page_disj. set_solver + H0. }
        apply IHs1.
        set_solver + H0.
        done.
      }
      apply fold_union_addr_of_page_strong_assoc_comm.
      set_solver + H.
    }
  Qed.

  Lemma set_of_addr_disj (s1 s2 : gset PID) :
    s1 ## s2 ->
    (set_of_addr s1) ## (set_of_addr s2).
  Proof.
    revert s1 s2.
    rewrite /set_of_addr.
    induction s1 using set_ind_L.
    {
      intros.
      rewrite set_fold_empty.
      done.
    }
    {
      intros ? Hdisj.
      rewrite (set_fold_disj_union_strong _ _ _ {[x]} X).
      {
        rewrite set_fold_singleton.
        rewrite fold_union_addr_of_page_comm.
        apply disjoint_union_l.
        split.
        { apply fold_union_addr_of_page_disj_aux.
          set_solver + Hdisj.
          apply disjoint_empty_r.
        }
        { apply IHs1.
          set_solver + Hdisj. }
      }
      apply fold_union_addr_of_page_strong_assoc_comm.
      set_solver + H.
    }
  Qed.

  Lemma set_of_addr_union (s1 s2 : gset PID):
    s1 ## s2 ->
    set_of_addr (s1 ∪ s2) =
      (set_of_addr s1) ∪ (set_of_addr s2).
  Proof.
    intro Hdisj.
    rewrite /set_of_addr.
    rewrite (set_fold_disj_union_strong _ _ _ s1 s2).
    {
      rewrite -fold_union_addr_of_page_comm.
      rewrite union_empty_r_L //.
    }
    apply fold_union_addr_of_page_strong_assoc_comm.
    exact Hdisj.
  Qed.

  Lemma elem_of_set_of_addr a p ps:
    a ∈ addr_of_page p ->
    p ∈ ps ->
    a ∈ set_of_addr ps.
  Proof.
    revert ps.
    induction ps using set_ind_L.
    {
      intros.
      inversion H0.
    }
    intros Hin_a Hin_p.
    destruct (decide (p = x)).
    {
      subst x.
      rewrite set_of_addr_union.
      {
        apply elem_of_union_l.
        rewrite /set_of_addr.
        rewrite set_fold_singleton union_empty_r.
        rewrite elem_of_list_to_set //.
      }
      rewrite disjoint_singleton_l //.
    }
    {
      rewrite set_of_addr_union.
      {
       apply elem_of_union_r.
       apply IHps.
       done.
       apply elem_of_union in Hin_p.
       destruct Hin_p.
       rewrite elem_of_singleton // in H0.
       done.
      }
      rewrite disjoint_singleton_l //.
    }
    Qed.

  Lemma elem_of_set_of_addr_tpa a ps:
    (tpa a) ∈ ps -> a ∈ set_of_addr ps.
  Proof.
    apply elem_of_set_of_addr.
    apply elem_of_addr_of_page_tpa.
  Qed.

  Lemma elem_of_memory_pages_lookup (m: gmap Addr Word) a ps:
    (tpa a) ∈ ps ->
    dom (gset Addr) m = set_of_addr ps ->
    is_Some (m !! a).
  Proof.
    intros Hin Heq_dom.
    apply elem_of_set_of_addr_tpa in Hin.
    rewrite -Heq_dom in Hin.
    by apply elem_of_dom.
  Qed.

  Lemma set_of_addr_empty : set_of_addr ∅ = ∅.
  Proof.
    rewrite /set_of_addr set_fold_empty //.
  Qed.

  Lemma memory_pages_split_union (ps1 ps2 :gset PID) :
    ps1 ## ps2 ->
    memory_pages (ps1 ∪ ps2) ⊣⊢ memory_pages ps1 ∗ memory_pages ps2  .
  Proof.
    intro Hdisj.
    iSplit.
    {
      iIntros "[%m [%Hdom mem]]".
      rewrite set_of_addr_union in Hdom;last done.
      pose proof (dom_union_inv_L m _ _ (set_of_addr_disj _ _ Hdisj) Hdom) as Hsplit.
      destruct Hsplit as (m1 & m2 & Heq & Hdisj_m & Hdom1 & Hdom2).
      rewrite Heq.
      rewrite big_sepM_union;last done.
      iDestruct "mem" as "[mem1 mem2]".
      iSplitL "mem1".
      iExists m1.
      iSplitL "";done.
      iExists m2.
      iSplitL "";done.
    }
    {
      iIntros "[[%m1 [%Hdom1 mem1]] [%m2 [%Hdom2 mem2]]]".
      iExists (m1 ∪ m2).
      iSplitL "".
      iPureIntro.
      rewrite dom_union_L.
      rewrite Hdom1 Hdom2.
      rewrite /set_of_addr set_fold_disj_union_strong.
      {
        rewrite -fold_union_addr_of_page_comm.
        rewrite union_empty_r_L //.
      }
      apply fold_union_addr_of_page_strong_assoc_comm.
      exact Hdisj.
      rewrite big_sepM_union.
      iFrame.
      apply map_disjoint_dom.
      rewrite Hdom1 Hdom2.
      apply set_of_addr_disj.
      done.
    }
  Qed.

  Lemma memory_pages_split_diff s s' :
    s' ⊆ s ->
    memory_pages s ⊣⊢ memory_pages (s ∖ s') ∗ memory_pages s'.
  Proof.
    intro Hsub.
    rewrite -memory_pages_split_union;last set_solver +.
    assert (s ∖ s' ∪ s' = s) as ->.
    {
      rewrite difference_union_L.
      set_solver + Hsub.
    }
    done.
  Qed.

  Lemma memory_pages_split_singleton s p :
    p ∈ s ->
    memory_pages s ⊣⊢ memory_pages (s ∖ {[p]}) ∗ memory_pages {[p]} .
  Proof.
    intro Hin.
    apply memory_pages_split_diff.
    set_solver + Hin.
  Qed.

  Lemma big_sepM_not_disj`{Countable K} {V :Type} (m1 m2: gmap K V) (Φ: K -> V -> iProp Σ) :
    ¬ (m1 ##ₘ m2) ->
    (∀ k v1 v2, Φ k v1 ∗ Φ k v2 -∗ False) ⊢
    ([∗ map] k↦v ∈ m1, Φ k v) ∗ ([∗ map] k↦v ∈ m2, Φ k v) -∗ False.
  Proof.
    iIntros (Hnot_disj) "Hexcl [m1 m2]".
    assert (∃ k, is_Some(m1 !! k) ∧ is_Some(m2 !! k)) as Hexists.
    {
      rewrite map_disjoint_dom elem_of_disjoint in Hnot_disj.
      apply  not_set_Forall_Exists in Hnot_disj;last eapply _.
      destruct Hnot_disj as [k [Hin H']].
      exists k.
      split.
      rewrite elem_of_dom // in Hin.
      simpl in H'.
      apply dec_stable in H'.
      rewrite elem_of_dom // in H'.
    }
    destruct Hexists as [k [Hin1 Hin2]].
    destruct Hin1 as [v1 Hlookup1].
    destruct Hin2 as [v2 Hlookup2].
    iDestruct (big_sepM_lookup with "m1") as "m1";first exact Hlookup1.
    iDestruct (big_sepM_lookup with "m2") as "m2";first exact Hlookup2.
    iApply ("Hexcl" $! k).
    iFrame.
  Qed.
  
  Lemma memory_pages_disj_singleton p : memory_pages {[p]} ∗ memory_pages {[p]} ⊢ False.
  Proof.
    iIntros " [[%m1 [%Hdom1 mem1]] [%m2 [%Hdom2 mem2]]] ".
    rewrite /set_of_addr set_fold_singleton in Hdom1 Hdom2.
    rewrite union_empty_r_L in Hdom1 Hdom2.
    iApply (big_sepM_not_disj with "[] [$mem1 $mem2]").
    rewrite map_disjoint_dom.
    rewrite Hdom1 Hdom2.
    rewrite disjoint_intersection_L.
    pose proof (addr_of_page_not_empty_set p) as Hne.
    rewrite intersection_idemp_L.
    done.
    iIntros (k v1 v2) "[Hp1 Hp2]".
    rewrite mem_mapsto_eq /mem_mapsto_def.
    iDestruct (ghost_map_elem_valid_2 with "Hp1 Hp2") as "%Hvalid".
    destruct Hvalid as [Hvalid _].
    rewrite dfrac_op_own in Hvalid.
    rewrite -> dfrac_valid_own in Hvalid.
    exfalso.
    eauto using Qp_not_add_le_r.
  Qed.

  Lemma memory_pages_disj s1 s2 : memory_pages s1 ∗ memory_pages s2 ⊢ ⌜s1 ## s2⌝.
  Proof.
    iIntros "[mem1 mem2]".
    rewrite elem_of_disjoint.
    iIntros (p Hin1 Hin2).
    iDestruct (memory_pages_split_singleton s1 p Hin1 with "mem1") as "[mem1' mem1_p]".
    iDestruct (memory_pages_split_singleton s2 p Hin2 with "mem2") as "[mem2' mem2_p]".
    iApply (memory_pages_disj_singleton with "[$mem1_p $mem2_p]").
  Qed.

  Lemma memory_pages_empty : ⊢ memory_pages ∅.
  Proof.
    iIntros.
    rewrite /memory_pages.
    iExists ∅.
    iSplit.
    rewrite dom_empty_L set_of_addr_empty //.
    rewrite big_sepM_empty //.
  Qed.

(** pagetable **)
 (* Lemma pgt_big_sepM_split (pgt: gmap PID (VMID * gset VMID)) {p pe} {f: _ -> _ -> iProp Σ}: *)
 (*    pgt !! p = Some pe-> *)
 (*    (( [∗ map] k↦y ∈ pgt, f k y)%I *)
 (*     ⊢  (f p pe) ∗ (f p pe -∗ [∗ map] k↦y ∈ pgt, f k y))%I. *)
 (*  Proof. *)
 (*    rewrite /total_gmap. *)
 (*    iIntros (Hlookup). *)
 (*    iApply (ra_big_sepM_split pgt p pe f Hlookup). *)
 (*  Qed. *)


 (* Lemma pgt_big_sepM_split2 (pgt: gmap PID (VMID * gset VMID)) {p1 p2 pe1 pe2} {f: _ -> _ -> iProp Σ}: *)
 (*    p1 ≠ p2 -> *)
 (*    pgt !! p1 = Some pe1 -> *)
 (*    pgt !! p2 = Some pe2-> *)
 (*    (( [∗ map] k↦y ∈ pgt, f k y)%I *)
 (*     ⊢  (f p1 pe1) ∗ (f p2 pe2) ∗ ((f p1 pe1 ∗ f p2 pe2 ) -∗ [∗ map] k↦y ∈ pgt, f k y))%I. *)
 (*  Proof. *)
 (*    rewrite /total_gmap. *)
 (*    iIntros (Hneq Hlookup1 Hlookup2). *)
 (*    iApply (ra_big_sepM_split2 pgt p1 p2 pe1 pe2 f);eauto. *)
 (*  Qed. *)

 (*  (* f is also implicit because coq can infer it from big_sepM *) *)
 (*  Lemma pgt_big_sepM_split_upd2 (pgt: gmap PID (VMID * gset VMID)) {p1 p2 pe1 pe2} {f: _ -> _ -> iProp Σ}: *)
 (*    p1 ≠ p2 -> *)
 (*    pgt !! p1 = Some pe1-> *)
 (*    pgt !! p2 = Some pe2-> *)
 (*    ((⌜total_gmap pgt⌝ ∗ [∗ map] k↦y ∈ pgt, f k y)%I *)
 (*     ⊢  (f p1 pe1) ∗ (f p2 pe2)∗ (∀ (pe1' pe2' : VMID * gset VMID) , (f p1 pe1' ∗ f p2 pe2') -∗ *)
 (*                          ∃ (pgt': gmap PID (VMID * gset VMID) ), (⌜total_gmap pgt'⌝ ∗ [∗ map] k↦y ∈ pgt', f k y)))%I. *)
 (*  Proof. *)
 (*    iIntros (Hneq Hlookup1 Hlookup2) "[%Htotal pgt]". *)
 (*    iApply (ra_big_sepM_split_upd2 pgt p1 p2 pe1 pe2 f);eauto. *)
 (*    Qed. *)

  (** memory **)

  Lemma mem_big_sepM_split (mem: gmap Addr Word) {a w} {f: _ -> _ -> iProp Σ}:
    mem !! a = Some w->
    (([∗ map] k↦y ∈ mem, f k y)
     ⊢  (f a w) ∗ (f a w -∗
                   ( [∗ map] k↦y ∈ mem, f k y)))%I.
  Proof.
    iIntros (Hlookup).
    iApply (ra_big_sepM_split mem a w f Hlookup).
  Qed.

  Lemma mem_big_sepM_split_upd (mem: gmap Addr Word) {a w} {f: _ -> _ -> iProp Σ}:
    mem !! a = Some w->
    (([∗ map] k↦y ∈ mem, f k y)%I
     ⊢  (f a w) ∗ (∀ (w' : Word) , f a w' -∗
                                   ( [∗ map] k↦y ∈ <[a := w']>mem, f k y)))%I.
  Proof.
    iIntros (Hlookup).
    iApply (ra_big_sepM_split_upd mem a w f Hlookup).
  Qed.

 (*  Lemma mem_big_sepM_split2 (mem: gmap Addr Word) {a1 a2 w1 w2} {f: _ -> _ -> iProp Σ}: *)
 (*    a1 ≠ a2 -> *)
 (*    mem !! a1 = Some w1-> *)
 (*    mem !! a2 = Some w2-> *)
 (*    (([∗ map] k↦y ∈ mem, f k y) *)
 (*     ⊢  f a1 w1 ∗ f a2 w2 ∗ ((f a1 w1 ∗ f a2 w2) -∗ *)
 (*                            ( [∗ map] k↦y ∈ mem, f k y)))%I. *)
 (*  Proof. *)
 (*    rewrite /total_gmap. *)
 (*    iIntros (Hneq Hlookup1 Hlookup2). *)
 (*    iApply (ra_big_sepM_split2 mem a1 a2 w1 w2 f);eauto. *)
 (*  Qed. *)

 (*  Lemma mem_big_sepM_split_upd2 (mem: gmap Addr Word) {a1 a2 w1 w2} {f: _ -> _ -> iProp Σ}: *)
 (*    a1 ≠ a2 -> *)
 (*    mem !! a1 = Some w1-> *)
 (*    mem !! a2 = Some w2-> *)
 (*    ((⌜total_gmap mem⌝ ∗ [∗ map] k↦y ∈ mem, f k y)%I *)
 (*     ⊢  f a1 w1 ∗ f a2 w2 ∗ (∀ (w1' w2' : Word) , (f a1 w1' ∗ f a2 w2') -∗ *)
 (*                          ∃ mem', (⌜total_gmap mem'⌝ ∗ [∗ map] k↦y ∈ mem', f k y)))%I. *)
 (*  Proof. *)
 (*    rewrite /total_gmap. *)
 (*    iIntros (Hneq Hlookup1 Hlookup2). *)
 (*    iApply (ra_big_sepM_split_upd2 mem a1 a2 w1 w2 f);eauto. *)
 (*  Qed. *)

  (* TODO: For memory chunks *)

  (* lemmas about sets... *)
  Lemma union_split_difference_intersection_L `{Countable T} (A B: gset T):
    A = (A ∖ B) ∪ (A ∩ B) ∧ (A ∖ B) ## (A ∩ B).
  Proof.
    split.
    {
      rewrite union_intersection_l_L.
      rewrite difference_union_L.
      set_solver.
    }
    {
      set_solver.
    }
  Qed.

  Lemma union_split_difference_1_L `{Countable T} (A B: gset T):
    A ∪ B = A ∪ (B ∖ A) ∧ A ## (B ∖ A).
  Proof.
    split.
    {
      rewrite union_comm_L (union_comm_L _ (B ∖ A)).
      rewrite difference_union_L //.
    }
    {
      set_solver.
    }
  Qed.

  Lemma union_split_difference_2_L `{Countable T} (A B: gset T):
    A ∪ B = B ∪ (A ∖ B) ∧ B ## (A ∖ B).
  Proof.
    split.
    {
      rewrite  (union_comm_L _ (A ∖ B)).
      rewrite difference_union_L //.
    }
    {
      set_solver.
    }
  Qed.

End logrel_extra.
