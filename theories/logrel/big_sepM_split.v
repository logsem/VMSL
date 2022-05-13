From iris.proofmode Require Import tactics.
From iris.base_logic Require Import base_logic.
From HypVeri Require Import proofmode stdpp_extra.
From HypVeri.algebra Require Import base.
From HypVeri.logrel Require Import big_sepFM.
From stdpp Require fin_map_dom.
Import uPred.

Section big_sepM_split.
  Context `{PROP: bi}.
  Context `{Countable K} {V: Type}.
  Context `{f : K -> V -> PROP}.
  Context `{_: ∀ m m'', Absorbing (([∗ map] k↦y ∈ m'', f k y) -∗ [∗ map] k↦y ∈ (m'' ∪  m) , f k y)}.

  Implicit Type map : gmap K V.

  Lemma ra_big_sepM_split map (k : K) (v:V) :
    map !! k = Some v ->
    (([∗ map] k↦y ∈ map, f k y)%I
     ⊢  (f k v) ∗ ((f k v) -∗  [∗ map] k↦y ∈ map , f k y))%I.
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

  Lemma ra_big_sepM_split_upd map (k : K) (v:V) :
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

  Lemma ra_big_sepM_split_upd_with_total map (k : K) (v:V)
        (total:= (λ m, (∀ k,  is_Some (m !! k))) : gmap K V -> Prop):
    map !! k = Some v ->
    ((⌜total map⌝ ∗ [∗ map] k↦y ∈ map, f k y)
     ⊢  (f k v) ∗ (∀ v', (f k v') -∗  ⌜total (<[k := v']>map)⌝ ∗ [∗ map] k↦y ∈ <[k := v']>map , f k y)).
  Proof.
    iIntros (Hlookup) "[Htotal Hregs]".
    iDestruct "Htotal" as "%Htotal".
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
      rewrite /total.
      iPureIntro. intro k0.
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

  Lemma ra_big_sepM_split2 map (k1 k2 : K) (v1 v2:V):
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

  Lemma ra_big_sepM_split_upd2 map (k1 k2: K) (v1 v2:V) (total:= (λ m, (∀ k, is_Some (m !! k))) : gmap K V -> Prop):
    k1 ≠ k2 ->
    map !! k1 = Some v1 ->
    map !! k2 = Some v2 ->
    ((⌜total map⌝ ∗ [∗ map] k↦y ∈ map, f k y)%I
     ⊢  (f k1 v1) ∗ (f k2 v2) ∗
          (∀ v1' v2', f k1 v1' ∗ f k2 v2'-∗ ∃ map', (⌜total map'⌝ ∗ [∗ map] k↦y ∈ map', f k y)))%I.
  Proof.
    iIntros (Hneq Hlookup1 Hlookup2) "[Htotal Hmaps]".
    iDestruct "Htotal" as "%Htotal".
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
      rewrite -elem_of_dom.
      rewrite dom_union_L.
      specialize (Htotal k0).
      rewrite -elem_of_dom in Htotal.
      apply elem_of_union_r.
      done.
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

  Lemma ra_big_sepM_split_upd2' map (k1 k2: K) (v1 v2:V):
    k1 ≠ k2 ->
    map !! k1 = Some v1 ->
    map !! k2 = Some v2 ->
    (([∗ map] k↦y ∈ map, f k y)%I
     ⊢  (f k1 v1) ∗ (f k2 v2) ∗
          (∀ v1' v2', f k1 v1' ∗ f k2 v2'-∗ ([∗ map] k↦y ∈ <[k1 := v1']>(<[k2 := v2']>map), f k y)))%I.
  Proof.
    iIntros (Hneq Hlookup1 Hlookup2) "Hmaps".
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
    assert (<[k1:=v1']> (<[k2:=v2']> map) = ({[k1 := v1'; k2:= v2']} ∪ map)) as ->.
    {
      rewrite insert_union_singleton_l.
      rewrite insert_union_singleton_l.
      rewrite <-insert_union_l.
      rewrite <-insert_union_singleton_l.
      reflexivity.
    }
    iApply "Hrestore".
    iPureIntro. set_solver +.
    rewrite !big_opM_insert.
    iDestruct "Hsingle_upd" as "[Hsingle_upd1 Hsingle_upd2]".
    iFrame.
    done.
    done.
    apply lookup_insert_None.
    split;done.
  Qed.

  Lemma ra_big_sepM_split_upd3 map (k1 k2 k3: K) (v1 v2 v3:V) (total:= (λ m, (∀ k, is_Some (m !! k))) : gmap K V -> Prop):
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
    iIntros (Hneq1 Hneq2 Hneq3 Hlookup1 Hlookup2 Hlookup3) "[Htotal Hmaps]".
    iDestruct "Htotal" as "%Htotal".
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
      rewrite -elem_of_dom.
      rewrite dom_union_L.
      specialize (Htotal k0).
      rewrite -elem_of_dom in Htotal.
      apply elem_of_union_r.
      done.
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

  Lemma ra_big_sepM_split_upd4 map (k1 k2 k3 k4: K) (v1 v2 v3 v4:V) (total:= (λ m, (∀ k, is_Some (m !! k))) : gmap K V -> Prop):
    k1 ≠ k2 ->
    k1 ≠ k3 ->
    k2 ≠ k3 ->
    k1 ≠ k4 ->
    k4 ≠ k3 ->
    k2 ≠ k4 ->
    map !! k1 = Some v1 ->
    map !! k2 = Some v2 ->
    map !! k3 = Some v3 ->
    map !! k4 = Some v4 ->
    ((⌜total map⌝ ∗ [∗ map] k↦y ∈ map, f k y)%I
     ⊢ f k1 v1 ∗ f k2 v2 ∗ f k3 v3 ∗ f k4 v4 ∗
         (∀ v1' v2' v3' v4', f k1 v1' ∗ f k2 v2' ∗ f k3 v3' ∗ f k4 v4' -∗ ∃ map', (⌜total map'⌝ ∗ [∗ map] k↦y ∈ map', f k y)))%I.
  Proof.
    iIntros (Hneq1 Hneq2 Hneq3 Hneq4 Hneq5 Hneq6 Hlookup1 Hlookup2 Hlookup3 Hlookup4) "[Htotal Hmaps]".
    iDestruct "Htotal" as %Htotal.
    pose proof (Htotal k1) as Hlookup_k1.
    pose proof (Htotal k2) as Hlookup_k2.
    pose proof (Htotal k3) as Hlookup_k3.
    pose proof (Htotal k4) as Hlookup_k4.
    simplify_map_eq.
    iDestruct (big_sepM_union_acc map {[k1 := v1 ; k2 := v2 ; k3 := v3 ; k4 := v4]} f with "Hmaps")
      as "[Hsingle Hrestore]".
    {
      repeat apply insert_subseteq_l;eauto.
      apply map_empty_subseteq.
    }
    rewrite !big_opM_insert;try rewrite !lookup_insert_None;eauto.
    iDestruct "Hsingle" as "(single1 & single2 & single3 & single4 & _)".
    iFrame "single1 single2 single3 single4".
    iIntros (v1' v2' v3' v4') "Hsingle_upd".
    iExists ({[k1 := v1'; k2:= v2'; k3 := v3'; k4:= v4']} ∪ map).
    iSplitL "".
    {
      iPureIntro.
      intro k0.
      rewrite -elem_of_dom.
      rewrite dom_union_L.
      specialize (Htotal k0).
      rewrite -elem_of_dom in Htotal.
      apply elem_of_union_r.
      done.
    }
    {
      iApply "Hrestore".
      iPureIntro. set_solver +.
      rewrite !big_opM_insert.
      iDestruct "Hsingle_upd" as "(single_upd1 & single_upd2 & single_upd3 & single_upd4)".
      iFrame.
      done.
      done.
      apply lookup_insert_None.
      split;done.
      rewrite !lookup_insert_None.
      repeat split;done.
      rewrite !lookup_insert_None.
      repeat split;done.
    }
  Qed.

  End big_sepM_split.
