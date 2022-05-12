From iris.proofmode Require Import tactics.
From machine_program_logic.program_logic Require Import weakestpre.
From HypVeri.lang Require Import lang.
From HypVeri.algebra Require Import base base_extra mem trans.
From HypVeri.logrel Require Import logrel.
From HypVeri Require Import proofmode stdpp_extra.
From stdpp Require fin_map_dom.
Import uPred.

Lemma half_of_half: (1/2/2)%Qp = (1/4)%Qp.
Proof.
  apply (bool_decide_unpack _).
  by compute.
Qed.

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

  Lemma difference_union_subseteq A B C :
    B ⊆ C ->
    A ∖ B ∪ C = A ∪ C.
  Proof.
    intro Hsub.
    apply (union_split_difference_intersection_subseteq_L C B) in Hsub.
    destruct Hsub as [Heq _].
    replace (A ∖ B ∪ C) with (A ∖ B ∪ (C ∖ B ∪ B)).
    rewrite (union_comm_L  _ B).
    rewrite union_assoc_L.
    rewrite difference_union_L.
    rewrite -(union_assoc_L _ B).
    rewrite (union_comm_L B).
    set_solver + Heq.
    set_solver + Heq.
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

  Lemma big_sepFM_update_True {m : gmap K A} {P : K * A -> Prop} `{∀ x, Decision (P x)}
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

  Lemma big_sepFM_update_False {m : gmap K A} {P : K * A -> Prop} `{∀ x, Decision (P x)}
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

  Lemma big_sepFM_empty {P: K * A -> Prop} `{∀ x, Decision (P x)} {Φ: K -> A -> PROP}:
    ⊢ big_sepFM ∅ P Φ.
  Proof.
    iIntros. rewrite /big_sepFM.
    rewrite big_sepM_empty //.
  Qed.


  Lemma big_sepFM_insert_True (k: K) (v: A) {m: gmap K A} {P: K * A -> Prop} `{∀ x, Decision (P x)} {Φ: K -> A -> PROP}:
    P (k,v) ->
    m !! k = None ->
    big_sepFM (<[k:=v]>m) P Φ ⊣⊢ (Φ k v) ∗ big_sepFM m P Φ.
  Proof.
    iIntros (HP Hlk). rewrite /big_sepFM.
    rewrite map_filter_insert_True //.
    rewrite big_sepM_insert //.
    rewrite map_filter_lookup_None. left;auto.
  Qed.

  Lemma big_sepFM_insert_False (k: K) (v: A) {m: gmap K A} {P: K * A -> Prop} `{∀ x, Decision (P x)} {Φ: K -> A -> PROP}:
    ¬P (k,v) ->
    m !! k = None ->
    big_sepFM (<[k:=v]>m) P Φ ⊣⊢ big_sepFM m P Φ.
  Proof.
    iIntros (HP Hlk). rewrite /big_sepFM.
    rewrite map_filter_insert_False //.
    rewrite delete_notin //.
  Qed.

  Lemma big_sepFM_iff {m: gmap K A} {P Q: K * A -> Prop} `{∀ x, Decision (P x)} `{∀ x, Decision (Q x)} {Φ: K -> A -> PROP}:
    (∀ kv, P kv <-> Q kv) ->
    big_sepFM m P Φ ⊣⊢ big_sepFM m Q Φ.
  Proof.
    intro equiv.
    iInduction m  as [| k v m Hlk] "IH" using map_ind.
    iSplit; iIntros "?";iApply big_sepFM_empty.
    destruct (decide (P(k,v))).
    rewrite 2?big_sepFM_insert_True //.
    iSplit; iIntros "[$ ?]";by iApply "IH".
    by apply equiv.
    rewrite 2?big_sepFM_insert_False //.
    intro Q'. by apply equiv in Q'.
  Qed.
  
  Lemma big_sepFM_split_decide {m: gmap K A} {P Q: K * A -> Prop} `{∀ x, Decision (P x)} `{∀ x, Decision (Q x)}
                       {Φ: K -> A -> PROP}:
    big_sepFM m P Φ ⊣⊢ (big_sepFM m (λ kv, ((P kv) ∧ Q kv):Prop) Φ)
                       ∗ big_sepFM m (λ kv, (P kv ∧ ¬(Q kv)):Prop) Φ.
  Proof.
    {
      iInduction m as [|k v m Hlk] "H" using map_ind.
      iSplit; iIntros "_";try iSplitL;iApply big_sepFM_empty.
      destruct (decide (P (k,v)));destruct (decide (Q (k,v))).
      {
        rewrite 2?big_sepFM_insert_True//.
        rewrite big_sepFM_insert_False//.
        2:{ intros [_ ?]. done. }
        iSplit. iIntros "[$ ?]".
        by iApply "H".
        iIntros "[[$ ?] ?]".
        iApply "H"; iFrame.
      }
      {
        rewrite big_sepFM_insert_True//.
        rewrite big_sepFM_insert_False//.
        2:{ intros [_ ?]. done. }
        rewrite big_sepFM_insert_True//.
        iSplit. iIntros "[$ ?]".
        by iApply "H".
        iIntros "[?  [$ ?]]".
        iApply "H"; iFrame.
      }
      {
        rewrite 3?big_sepFM_insert_False//.
        2:{ intros [? _]. done. }
        intros [? _]. done.
      }
      {
        rewrite 3?big_sepFM_insert_False//.
        2:{ intros [? _]. done. }
        intros [? _]. done.
      }
    }
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
         (f: K -> V -> iProp Σ) :
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
        (total:= (λ m, (∀ k,  is_Some (m !! k))) : gmap K V -> Prop) (f: K -> V -> iProp Σ) :
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
         (f: K -> V -> iProp Σ) :
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

  (* Lemma get_trans_ps_disj trans {Φ : _ -> iProp Σ}: *)
  (*   (([∗ map] h ↦ tran ∈ trans , Φ tran) ∗ *)
  (*      (∀ v1 v2, Φ v1 ∗ Φ v2 -∗ ⌜v1.1.1.2 ## v2.1.1.2⌝) *)
  (*    ⊢ ⌜trans_ps_disj trans⌝)%I. *)
  (* Proof. *)
  (* Admitted. *)
    (* rewrite /trans_ps_disj. *)
    (* iIntros "[m Hfalse]". *)
    (* iIntros (k v Hlookup). *)
    (* rewrite elem_of_disjoint. *)
    (* iIntros (p Hin Hin'). *)
    (* iDestruct (big_sepM_delete with "m") as "[Φ m]". *)
    (* exact Hlookup. *)
    (* apply elem_of_pages_in_trans in Hin' as [h [v' [Hlookup' Hin'']]]. *)
    (* iDestruct (big_sepM_delete with "m") as "[Φ' m]". *)
    (* exact Hlookup'. *)
    (* iDestruct ("Hfalse" $! v v' with "[$ Φ $ Φ']") as %Hdisj. *)
    (* set_solver + Hdisj Hin Hin''. *)
  (* Qed. *)

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
