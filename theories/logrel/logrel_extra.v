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
    iApply (ra_big_sepM_split_upd reg r w (λ k v, k @@ i ->r v)%I Hlookup).
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


Lemma memory_cells_disj s1 s2 : memory_cells s1 ∗ memory_cells s2 ⊢ ⌜s1 ## s2⌝.
Proof.
Admitted.


Lemma disj'' (p: PID) (s1 : gset PID) (s2: gset Addr) : p ∉ s1 ->
        (list_to_set (addr_of_page p)) ## s2 ->
       (list_to_set (addr_of_page p))  ## (set_fold (λ p acc, list_to_set (addr_of_page p) ∪ acc) s2 s1).
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
      apply IHs1.
      set_solver + H0.
      apply disjoint_union_r.
      split;last done.
      assert ( p ≠ x ).
      { intro. subst p. set_solver + H0. }
     admit.
    }
    {
      admit.
    }
    set_solver + H.

}
Admitted.

Lemma disj' (s1 s2 : gset PID) (s3 : gset Addr): s1 ## s2 ->
       s3 ## set_fold (λ (p : PID) (acc : gset Addr), list_to_set (addr_of_page p) ∪ acc) ∅ s2 ->
      (set_fold (λ p acc, list_to_set (addr_of_page p) ∪ acc) s3 s1) ##
      (set_fold (λ p acc, list_to_set (addr_of_page p) ∪ acc) ∅ s2).
Proof.
  revert s1 s2 s3.
  induction s1 using set_ind_L.
  {
    intros.
    rewrite set_fold_empty.
    done.
  }
  {
    intros ? ? Hdisj Hdisj'.
    rewrite (set_fold_disj_union_strong _ _ s3 {[x]} X).
    {
      rewrite set_fold_singleton.
      apply IHs1.
      set_solver + Hdisj.
      apply disjoint_union_l.
      split;last done.
      apply disj''.
      set_solver + Hdisj.
      apply disjoint_empty_r.
    }
    {
      admit.
    }
    set_solver + H.
  }
Admitted.

Lemma addr_of_page_disj (s1 s2 : gset PID) : s1 ## s2 ->
      (set_fold (λ p acc, list_to_set (addr_of_page p) ∪ acc) (∅: gset _) s1) ##
      (set_fold (λ p acc, list_to_set (addr_of_page p) ∪ acc) ∅ s2).
Proof.
  intros.
  apply disj';first done.
  apply disjoint_empty_l.
Qed.

Lemma memory_cell'_split (ps1 ps2 :gset PID) :
  ps1 ## ps2 ->
  memory_cell' ps1 ∗ memory_cell' ps2 ⊢ memory_cell' (ps1 ∪ ps2).
Proof.
  iIntros (Hdisj) "[[%m1 [%Hdom1 mem1]] [%m2 [%Hdom2 mem2]]]".
  iExists (m1 ∪ m2).
  iSplitL "".
  iPureIntro.
  rewrite dom_union_L.
  rewrite Hdom1 Hdom2.
  rewrite set_fold_disj_union_strong .
 admit.
admit.
done.
rewrite big_sepM_union.
  iFrame.
  apply map_disjoint_dom.
  rewrite Hdom1 Hdom2.
  apply addr_of_page_disj.
  done.
Admitted.


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
    admit.
    (* iApply (ra_big_sepM_split_upd mem a w f Hlookup). *)
Admitted.

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

End logrel_extra.
