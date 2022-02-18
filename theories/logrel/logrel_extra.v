From iris.proofmode Require Import tactics.
From machine_program_logic.program_logic Require Import weakestpre.
From HypVeri.lang Require Import lang.
From HypVeri.algebra Require Import base base_extra.
From HypVeri.logrel Require Import logrel.
From HypVeri Require Import proofmode stdpp_extra.
From stdpp Require fin_map_dom.
Import uPred.

Section sets.
  Context `{Countable T}.
  Implicit Type A B C : gset T.

  (* lemmas about sets... *)
  Lemma union_split_difference_intersection_L A B:
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

  Lemma union_split_difference_intersection_subseteq_L A B:
    B ⊆ A ->
    A = (A ∖ B) ∪ B ∧ (A ∖ B) ## B.
  Proof.
    intro H0.
    pose proof (union_split_difference_intersection_L A B) as H1.
    assert (A∩ B = B).
    {
      set_solver + H0.
    }
    rewrite H2 in H1.
    done.
  Qed.

  Lemma union_split_difference_1_L A B:
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

  Lemma union_split_difference_2_L A B:
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

  Lemma not_subseteq A B:
    A ⊈ B -> ∃ a, a ∈ A ∧ a ∉ B.
  Proof.
    intros.
    induction A using set_ind_L.
    pose proof (empty_subseteq B) .
    done.
    destruct (decide (x ∈ B)).
    {
      assert (X ⊈ B).
      {
        intro.
        apply H0.
        set_solver.
      }
      apply IHA in H2 as [a [? ?]].
      exists a.
      split;auto.
      set_solver.
    }
    {
      exists x.
      split;auto.
      set_solver.
    }
  Qed.

 Lemma not_subseteq_diff A B C :
   A ⊆ B -> A ⊈ (B ∖ C) -> ∃ a, a ∈ A ∧ a ∈ C.
  Proof.
    intros Hsub1 Hsub2.
    apply not_subseteq in Hsub2 as [a [Hin Hnin]].
    rewrite elem_of_subseteq in Hsub1.
    exists a.
    split;auto.
    specialize (Hsub1 a Hin).
    set_solver.
  Qed.

End sets.

Section big_sep.
  Context `{Countable K} {A : Type}.
  Context {PROP : bi}.
  Implicit Types m : gmap K A.
  Implicit Types s : gset K.

  Lemma big_sepM_union_acc m m' (Φ: K → A → PROP) `{!∀ m m'', Absorbing (([∗ map] k↦y ∈ m'', Φ k y)
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

  Lemma big_sepM_union_acc_singleton k v m (Φ: K → A → PROP) `{!∀ m m'', Absorbing (([∗ map] k↦y ∈ m'', Φ k y)
              -∗ [∗ map] k↦y ∈ (m'' ∪  m) , Φ k y)} :
    m !! k = Some v ->
    ([∗ map] k↦y ∈ m, Φ k y) ⊢
    (Φ k v) ∗
    (∀ v',  Φ k v' -∗ [∗ map] k↦y ∈ <[k:= v']> m , Φ k y).
  Proof.
    iIntros (Hlookup) "Hmap".
    iDestruct (big_sepM_union_acc m {[k:= v]} with "Hmap") as "[Φ Hacc]".
    {
      rewrite map_subseteq_spec.
      intros ? ? Hlookup'.
      rewrite lookup_singleton_Some in Hlookup'.
      destruct Hlookup' as [-> ->].
      done.
    }
    rewrite big_sepM_singleton.
    iFrame.
    iIntros (v') "Φ'".
    iDestruct ("Hacc" $! {[k:= v']} with "[] [Φ']") as "Hmap".
    rewrite 2!dom_singleton_L //.
    rewrite big_sepM_singleton.
    iFrame.
    rewrite insert_union_singleton_l.
    iFrame.
  Qed.

  Lemma big_sepFM_lookup_Some_acc {m : gmap K A} {P : K * A -> Prop} `{∀ x, Decision (P x)}
        {Φ : K -> A -> PROP} {k : K} {v : A} :
    m !! k = Some v ->
    P (k,v) ->
    big_sepFM m P Φ ⊢ Φ k v ∗ (∀ v', if (decide (P (k,v'))) then (Φ k v' -∗ big_sepFM (<[k := v']>m) P Φ)
                                                                                  else big_sepFM (<[k := v']>m) P Φ).
  Proof.
    iIntros (Hlk P_v) "fm".
    rewrite /big_sepFM.
    iDestruct (big_sepM_delete _ _ k v with "fm") as "[Φ Hacc]".
    rewrite map_filter_lookup_Some.
    split;auto.
    iFrame "Φ".
    iIntros (v').
    case_decide.
    iIntros "Φ".
    rewrite map_filter_insert_True;auto.
    rewrite big_sepM_insert_delete.
    iFrame.
    rewrite map_filter_insert_False;auto.
    rewrite map_filter_delete.
    done.
  Qed.

  Lemma big_sepFM_delete_acc_True {m : gmap K A} {P : K * A -> Prop} `{∀ x, Decision (P x)}
        {Φ : K -> A -> PROP} {k : K} (v' :A):
    P (k,v') ->
    (big_sepFM (delete k m) P Φ) ⊢
    Φ k v' -∗ big_sepFM (<[k := v']>m) P Φ .
  Proof.
    intro HP.
    iIntros "delete Φ".
    rewrite /big_sepFM.
    rewrite map_filter_insert_True;auto.
    rewrite big_sepM_insert_delete.
    iFrame "Φ".
    rewrite map_filter_delete.
    done.
  Qed.

  Lemma big_sepFM_delete_acc_False {m : gmap K A} {P : K * A -> Prop} `{∀ x, Decision (P x)}
        {Φ : K -> A -> PROP} {k : K} (v' :A):
    ¬P (k,v') ->
    (big_sepFM (delete k m) P Φ) ⊢
    big_sepFM (<[k := v']>m) P Φ .
  Proof.
    intro HP.
    iIntros "delete".
    rewrite /big_sepFM.
    rewrite map_filter_insert_False;auto.
  Qed.

  Lemma big_sepFM_lookup_Some{m : gmap K A} {P : K * A -> Prop} `{∀ x, Decision (P x)}
        {Φ : K -> A -> PROP} {k : K} {v : A} :
    m !! k = Some v ->
    P (k,v) ->
    big_sepFM m P Φ ⊢ Φ k v ∗ (big_sepFM (delete k m) P Φ).
  Proof.
    iIntros (Hlk P_v) "fm".
    rewrite /big_sepFM.
    iDestruct (big_sepM_delete _ _ k v with "fm") as "[Φ Hacc]".
    rewrite map_filter_lookup_Some.
    split;auto.
    iFrame "Φ".
    rewrite map_filter_delete;auto.
  Qed.

  Lemma big_sepFM_lookup_None {m : gmap K A} {P : K * A -> Prop} `{∀ x, Decision (P x)}
        {Φ : K -> A -> PROP} (k : K) :
    m !! k = None ->
    big_sepFM m P Φ ⊢  (∀ v', if (decide (P (k,v'))) then (Φ k v' -∗ big_sepFM (<[k := v']>m) P Φ)
                                                                                  else big_sepFM (<[k := v']>m) P Φ).
  Proof.
    iIntros (Hlk) "fm".
    rewrite /big_sepFM.
    iIntros (v').
    case_decide.
    iIntros "Φ".
    rewrite map_filter_insert_True;auto.
    rewrite big_sepM_insert.
    iFrame.
    rewrite map_filter_lookup_None.
    eauto.
    rewrite map_filter_insert_False;auto.
    rewrite delete_notin; done.
  Qed.

  Lemma big_sepFM_lookup_None_True {m  : gmap K A} {P : K * A -> Prop} `{∀ x, Decision (P x)}
        {Φ : K -> A -> PROP} {k : K} (v' : A) :
    m !! k = None ->
    P (k,v') ->
    big_sepFM m P Φ ⊢  Φ k v' -∗ big_sepFM (<[k := v']>m) P Φ.
  Proof.
    iIntros (Hlk P_v') "fm".
    iIntros  "Φ".
    iDestruct (big_sepFM_lookup_None k with "fm") as "Hacc";auto.
    iDestruct ("Hacc" $! v') as "Hacc".
    case_decide.
    iApply ("Hacc" with "Φ").
    done.
  Qed.

  Lemma big_sepFM_lookup_None_False {m : gmap K A} {P : K * A -> Prop} `{∀ x, Decision (P x)}
        {Φ : K -> A -> PROP} {k : K} (v' : A) :
    m !! k = None ->
    ¬P (k,v') ->
    big_sepFM m P Φ ⊢  big_sepFM (<[k := v']>m) P Φ.
  Proof.
    iIntros (Hlk P_v') "fm".
    iDestruct (big_sepFM_lookup_None k with "fm") as "Hacc";auto.
    iDestruct ("Hacc" $! v') as "Hacc".
    case_decide.
    done.
    iApply "Hacc".
  Qed.

  Lemma big_sepFM_delete_False {m : gmap K A} {P : K * A -> Prop} `{∀ x, Decision (P x)}
        {Φ : K -> A -> PROP} {k : K} { v : A }  :
    m !! k = Some v ->
    ¬P (k,v) ->
    big_sepFM m P Φ ≡ big_sepFM (delete k m) P Φ.
  Proof.
    iIntros (Hlk P_not).
    rewrite /big_sepFM.
    rewrite map_filter_delete.
    rewrite delete_notin.
    done.
    rewrite map_filter_lookup_None_2 //.
    right.
    intros.
    rewrite Hlk in H1.
    inversion H1.
    subst v.
    done.
  Qed.

  Lemma big_sepFM_update_True{m : gmap K A} {P : K * A -> Prop} `{∀ x, Decision (P x)}
        {Φ : K -> A -> PROP} {k : K} {v : A} (v': A) :
    m !! k = Some v ->
    P (k,v) ->
    P (k,v') ->
    ⊢ (Φ k v -∗ Φ k v') -∗ big_sepFM m P Φ -∗ big_sepFM (<[k := v']>m) P Φ.
  Proof.
    iIntros (Hlk HP HP') "imp fm".
    rewrite /big_sepFM.
    iDestruct (big_sepM_delete _ _ k v with "fm") as "[Φ Hacc]".
    rewrite map_filter_lookup_Some.
    split;auto.
    iDestruct ("imp" with "Φ") as "Φ".
    rewrite map_filter_insert_True;auto.
    rewrite big_sepM_insert_delete.
    iFrame.
  Qed.

  Lemma big_sepFM_update_False{m : gmap K A} {P : K * A -> Prop} `{∀ x, Decision (P x)}
        {Φ : K -> A -> PROP} {k : K} {v : A} (v': A) :
    m !! k = Some v ->
    ¬P (k,v) ->
    ¬P (k,v') ->
    ⊢ big_sepFM m P Φ -∗ big_sepFM (<[k := v']>m) P Φ.
  Proof.
    iIntros (Hlk HP HP') "fm".
    rewrite big_sepFM_delete_False //.
    rewrite /big_sepFM.
    rewrite map_filter_insert_False //.
  Qed.

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
    pose proof(union_split_difference_intersection_subseteq_L s s' Hsubseteq) as [Heq Hdisj].
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

  Lemma ra_big_sepM_split_upd2' `{Countable K} { V :Type} (map : gmap K V) (k1 k2: K) (v1 v2:V)
        (f: K -> V -> iProp Σ):
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

  Lemma ra_big_sepM_split_upd4 `{Countable K} { V :Type} (map : gmap K V) (k1 k2 k3 k4: K) (v1 v2 v3 v4:V)
        (total:= (λ m, (∀ k, is_Some (m !! k))) : gmap K V -> Prop) (f: K -> V -> iProp Σ):
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
    iIntros (Hneq1 Hneq2 Hneq3 Hneq4 Hneq5 Hneq6 Hlookup1 Hlookup2 Hlookup3 Hlookup4) "[%Htotal Hmaps]".
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

  (** registers **)
  (* we provide lookup, so r and w can be implicit *)
  Lemma reg_big_sepM_split i {reg r w}:
    reg !! r = Some w ->
    (([∗ map] k↦y ∈ reg, k @@ i ->r y)%I
     ⊢  (r @@ i ->r w) ∗ ( r @@ i ->r w -∗ [∗ map] k↦y ∈ reg, k @@ i ->r y))%I.
  Proof.
    rewrite /reg_file.
    iIntros (Hlookup).
    iApply (ra_big_sepM_split reg r w (λ k v, k @@ i ->r v)%I Hlookup).
  Qed.


  Lemma reg_big_sepM_split_upd i {reg r w}:
    reg !! r = Some w ->
    ((⌜is_total_gmap (reg: gmap reg_name Addr)⌝ ∗ [∗ map] k↦y ∈ reg, k @@ i ->r y)%I
     ⊢  (r @@ i ->r w) ∗ (∀ w', r @@ i ->r w' -∗ ⌜is_total_gmap (<[r := w']>reg)⌝ ∗ [∗ map] k↦y ∈  <[r := w']>reg, k @@ i ->r y))%I.
  Proof.
    rewrite /reg_file /is_total_gmap.
    iIntros (Hlookup).
    iApply (ra_big_sepM_split_upd_with_total reg r w (λ k v, k @@ i ->r v)%I Hlookup).
  Qed.


  Lemma reg_big_sepM_split_upd2 i {reg r1 w1 r2 w2}:
    reg !! r1 = Some w1 ->
    reg !! r2 = Some w2 ->
    r1 ≠ r2 ->
    ((⌜is_total_gmap reg⌝ ∗ [∗ map] k↦y ∈ reg, k @@ i ->r y)%I
     ⊢  (r1 @@ i ->r w1) ∗ (r2 @@ i ->r w2) ∗
          (∀ w1' w2', r1 @@ i ->r w1' ∗ r2 @@ i ->r w2'-∗ ∃ reg', (⌜is_total_gmap reg'⌝ ∗ [∗ map] k↦y ∈ reg', k @@ i ->r y)))%I.
  Proof.
    iIntros ( Hlookup1 Hlookup2 Hneq) "[%Hfull Hregs]".
    iApply (ra_big_sepM_split_upd2 reg r1 r2 w1 w2 (λ k v, k @@ i ->r v)%I);eauto.
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
    iIntros (Hlookup1 Hlookup2 Hlookup3 Hneq1 Hneq2 Hneq3) "[%Hfull Hregs]".
    iApply (ra_big_sepM_split_upd3 reg r1 r2 r3 w1 w2 w3 (λ k v, k @@ i ->r v)%I);eauto.
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
    iIntros (Hlookup1 Hlookup2 Hlookup3 Hlookup4 Hneq1 Hneq2 Hneq3 ? ? ? ) "[%Hfull Hregs]".
    iApply (ra_big_sepM_split_upd4 reg r1 r2 r3 r4 w1 w2 w3 w4 (λ k v, k @@ i ->r v)%I);eauto.
  Qed.

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

  Lemma mem_big_sepM_split2 (mem: gmap Addr Word) {a1 a2 w1 w2} {f: _ -> _ -> iProp Σ}:
    a1 ≠ a2 ->
    mem !! a1 = Some w1->
    mem !! a2 = Some w2->
    (([∗ map] k↦y ∈ mem, f k y)
     ⊢  f a1 w1 ∗ f a2 w2 ∗ ((f a1 w1 ∗ f a2 w2) -∗
                            ( [∗ map] k↦y ∈ mem, f k y)))%I.
  Proof.
    iIntros (Hne Hlookup1 Hlookup2).
    iApply (ra_big_sepM_split2 mem a1 a2 w1 w2 f); auto.
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
    iApply (ra_big_sepM_split_upd2' mem a1 a2 w1 w2 f Hne Hlookup1 Hlookup2).
  Qed.

  (* TODO: For memory chunks *)

  (* lemmas about pages_in_trans *)
  Lemma elem_of_pages_in_trans p trans:
    p ∈ pages_in_trans trans <-> ∃h tran, trans !! h = Some tran ∧ p ∈ tran.1.1.2.
  Proof.
    rewrite /pages_in_trans.
    induction trans using map_ind.
    {
      rewrite map_fold_empty //.
      split;intros;first done.
      destruct H as [? [? [? ?]]].
      done.
    }
    {
      rewrite map_fold_insert_L.
      2:{
        intros w1 w2 trans1 trans2 y.
        intros Hneq Hlookup1 Hlookup2.
        set_solver +.
      }
      2: done.
      rewrite elem_of_union.
      split;intro Hin.
      destruct Hin as [Hin|Hin].
      exists i, x.
      split;auto.
      rewrite lookup_insert_Some;left;done.
      apply IHtrans in Hin as [h [x' [Hlookup Hin']]].
      exists h, x'.
      split;auto.
      rewrite lookup_insert_Some;right.
      split;auto.
      intro.
      subst i.
      rewrite H // in Hlookup.
      destruct (decide (p ∈ x.1.1.2)).
      left;done.
      right.
      apply IHtrans.
      destruct Hin as [h [x' [Hlookup Hin']]].
      destruct (decide (i = h)).
      subst i.
      rewrite lookup_insert_Some in Hlookup.
      destruct Hlookup as [? | [? ?]].
      destruct H0;subst.
      contradiction.
      contradiction.
      exists h, x'.
      split;last done.
      rewrite lookup_insert_ne in Hlookup.
      done.
      done.
    }
  Qed.


  Lemma subseteq_pages_in_trans h tran trans:
    trans !! h = Some tran ->
    tran.1.1.2 ⊆ pages_in_trans trans.
  Proof.
    intros Hlk.
    rewrite /pages_in_trans.
    induction trans using map_ind.
    {
      rewrite map_fold_empty //.
    }
    {
      rewrite map_fold_insert_L.
      2:{
        intros w1 w2 trans1 trans2 y.
        intros Hneq Hlookup1 Hlookup2.
        set_solver +.
      }
      2: done.
      destruct (decide (i = h)).
      {
        subst i.
        rewrite lookup_insert in Hlk.
        inversion Hlk.
        subst x.
        set_solver +.
      }
      {
        feed specialize IHtrans.
        rewrite lookup_insert_ne in Hlk;auto.
        set_solver + IHtrans.
      }
    }
  Qed.

  Lemma get_trans_ps_disj trans {Φ : _ -> iProp Σ}:
    (([∗ map] h ↦ tran ∈ trans , Φ tran) ∗
       (∀ v1 v2, Φ v1 ∗ Φ v2 -∗ ⌜v1.1.1.2 ## v2.1.1.2⌝)
     ⊢ ⌜trans_ps_disj trans⌝)%I.
  Proof.
    rewrite /trans_ps_disj.
    iIntros "[m Hfalse]".
    iIntros (k v Hlookup).
    rewrite elem_of_disjoint.
    iIntros (p Hin Hin').
    iDestruct (big_sepM_delete with "m") as "[Φ m]".
    exact Hlookup.
    apply elem_of_pages_in_trans in Hin' as [h [v' [Hlookup' Hin'']]].
    iDestruct (big_sepM_delete with "m") as "[Φ' m]".
    exact Hlookup'.
    iDestruct ("Hfalse" $! v v' with "[$ Φ $ Φ']") as %Hdisj.
    set_solver + Hdisj Hin Hin''.
  Qed.

  Lemma pages_in_trans_subseteq m m':
    m' ⊆ m -> pages_in_trans m' ⊆ pages_in_trans m.
  Proof.
    intros Hsub.
    rewrite /pages_in_trans.
    induction m' using map_ind.
    {
      rewrite map_fold_empty //.
    }
    {
      rewrite map_fold_insert_L.
      2:{
        intros w1 w2 trans1 trans2 y.
        intros Hneq Hlookup1 Hlookup2.
        set_solver +.
      }
      2: done.
      pose proof Hsub.
      rewrite map_subseteq_spec in Hsub.
      specialize (Hsub i x).
      feed specialize Hsub.
      rewrite lookup_insert //.
      apply union_least.
      {
        rewrite elem_of_subseteq.
        intros.
        rewrite elem_of_pages_in_trans.
        exists i, x.
        split;done.
      }
      apply IHm'.
      rewrite map_subseteq_spec.
      intros.
      rewrite map_subseteq_spec in H0.
      apply H0.
      rewrite lookup_insert_Some.
      right.
      split;last done.
      intro.
      subst.
      rewrite H1 in H.
      done.
    }
  Qed.

  Lemma pages_in_trans_insert{h tran trans}:
    trans !! h = None ->
    pages_in_trans (<[h := tran]> trans) =tran.1.1.2 ∪ pages_in_trans trans.
  Proof.
    intros Hlk.
    rewrite /pages_in_trans.
    rewrite map_fold_insert_L.
    2:{
      intros w1 w2 trans1 trans2 y.
      intros Hneq Hlookup1 Hlookup2.
      set_solver +.
    }
    2: done.
    done.
  Qed.

  Lemma pages_in_trans_insert'{h tran tran' trans}:
    trans !! h = Some tran ->
    tran.1 = tran'.1 ->
    pages_in_trans (<[h := tran']> trans) = pages_in_trans trans.
  Proof.
    intros Hlk.
    rewrite /pages_in_trans.
    induction trans using map_ind.
    {
      rewrite map_fold_empty //.
    }
    {
      intro Heq.
      destruct (decide (i = h)).

      subst i.
      rewrite insert_insert.

      rewrite lookup_insert_Some in Hlk.
      destruct Hlk as [[_ ->]|[? _]].
      2: done.
      rewrite map_fold_insert_L;auto.
      2:{
        intros w1 w2 trans1 trans2 y.
        intros Hneq Hlookup1 Hlookup2.
        set_solver +.
      }
      rewrite map_fold_insert_L;auto.
      2:{
        intros w1 w2 trans1 trans2 y.
        intros Hneq Hlookup1 Hlookup2.
        set_solver +.
      }
      rewrite Heq //.
      rewrite lookup_insert_Some in Hlk.
      destruct Hlk as [[? _]|[_ Hlk]].
      contradiction.
      rewrite map_insert_swap //.

      specialize (IHtrans Hlk Heq).
      rewrite (map_fold_insert_L _ _ _ _ (<[h:=tran']> m));auto.
      2:{
        intros w1 w2 trans1 trans2 y.
        intros Hneq Hlookup1 Hlookup2.
        set_solver +.
      }
      rewrite (map_fold_insert_L _ _ i _ );auto.
      2:{
        intros w1 w2 trans1 trans2 y.
        intros Hneq Hlookup1 Hlookup2.
        set_solver +.
      }
      2: rewrite lookup_insert_ne //.
      rewrite IHtrans //.
    }
Qed.

  Lemma trans_ps_disj_subseteq m m':
    trans_ps_disj m -> m' ⊆ m -> trans_ps_disj m'.
  Proof.
    intros Hdisj Hsub.
    intros k v Hlookup.
    rewrite map_subseteq_spec in Hsub.
    assert (delete k m' ⊆ delete k m).
    rewrite map_subseteq_spec.
    intros.
    destruct (decide (i = k)).
    {
      subst.
      rewrite lookup_delete_Some in H.
      destruct H;contradiction.
    }
    {
      rewrite lookup_delete_ne in H;auto.
      rewrite lookup_delete_ne;auto.
    }
    pose proof (pages_in_trans_subseteq _ _ H).
    specialize (Hdisj k v).
    simpl in Hdisj.
    feed specialize Hdisj.
    apply Hsub;eauto.
    set_solver + Hdisj H0.
  Qed.

  Lemma pages_in_trans_delete {h tran trans}:
    trans !! h = Some tran ->
    trans_ps_disj trans ->
    pages_in_trans (delete h trans) = pages_in_trans trans ∖ tran.1.1.2.
  Proof.
    intros Hlk Hdisj.
    specialize (Hdisj _ _ Hlk).
    rewrite /pages_in_trans.
    induction trans using map_ind.
    {
      rewrite map_fold_empty //.
    }
    {
      rewrite map_fold_insert_L.
      2:{
        intros w1 w2 trans1 trans2 y.
        intros Hneq Hlookup1 Hlookup2.
        set_solver +.
      }
      2: done.
      destruct (decide (i = h)).
      subst i.
      rewrite delete_insert. 2: done.
      {
        simpl in Hdisj.
        rewrite lookup_insert in Hlk.
        inversion Hlk.
        subst x.
        clear Hlk.
        rewrite delete_insert in Hdisj;auto.
        rewrite /pages_in_trans in Hdisj.
        set_solver + Hdisj.
      }
      {
        rewrite delete_insert_ne;auto.
        rewrite map_fold_insert_L.
        2:{
          intros w1 w2 trans1 trans2 y.
          intros Hneq Hlookup1 Hlookup2.
          set_solver +.
        }
        2: {
          rewrite lookup_delete_ne;auto.
        }
        rewrite lookup_insert_ne in Hlk.
        rewrite delete_insert_ne in Hdisj;auto.
        rewrite /pages_in_trans in Hdisj.
        rewrite map_fold_insert_L in Hdisj.
        2:{
          intros w1 w2 trans1 trans2 y.
          intros Hneq Hlookup1 Hlookup2.
          set_solver +.
        }
        2: {
          rewrite lookup_delete_ne;auto.
        }
        rewrite /pages_in_trans.
        rewrite IHtrans;auto.
        2: {
          set_solver + Hdisj. }
        2: done.
        set_solver + Hdisj.
      }
    }
  Qed.

  Lemma trans_ps_disj_insert h tran trans :
    trans_ps_disj trans ->
    trans !! h = None ->
    tran.1.1.2 ## pages_in_trans trans ->
    trans_ps_disj (<[h:=tran]> trans).
  Proof.
    intros Hdisj Hlk Hdisj'.
    intros k v Hlk'.
    destruct (decide (k = h)).
    {
      subst.
      rewrite delete_insert;auto.
      rewrite lookup_insert in Hlk'.
      inversion Hlk'.
      subst v.
      done.
    }
    {
      rewrite delete_insert_ne;auto.
      rewrite pages_in_trans_insert.
      rewrite lookup_insert_ne in Hlk';auto.

      rewrite (pages_in_trans_delete Hlk' );auto.
      pose proof (subseteq_pages_in_trans _ _ _ Hlk').
      set_solver + Hdisj' H.
      rewrite lookup_delete_ne;auto.
    }
  Qed.

  Lemma trans_ps_disj_update{trans h tran tran'}:
    trans_ps_disj trans ->
    trans !! h = Some tran->
    tran.1 = tran'.1 ->
    trans_ps_disj (<[h:=tran']> trans).
  Proof.
    intros Hdisj Hlk Heq.
    intros k v Hlk'.
    destruct (decide (k = h)).
    {
      subst.
      rewrite delete_insert_delete;auto.
      rewrite lookup_insert in Hlk'.
      inversion Hlk'.
      subst v.
      rewrite -Heq.
      apply Hdisj.
      done.
    }
    {
      rewrite delete_insert_ne;auto.
      rewrite (pages_in_trans_insert' (tran:=tran));auto.
      rewrite lookup_insert_ne in Hlk';auto.
      rewrite lookup_delete_ne //.
    }
  Qed.

End logrel_extra.
