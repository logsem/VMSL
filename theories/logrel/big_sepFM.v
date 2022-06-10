From iris.base_logic Require Import base_logic.
From stdpp Require fin_map_dom.
From iris.proofmode Require Export tactics.
Import uPred.

Section definition.
  Context `{Countable K}  {V: Type}.
  Context {PROP : bi}.

  Definition big_sepFM(m : gmap K V) (P : K * V-> Prop) `{∀ x, Decision (P x)} (Φ : K -> V -> PROP) : PROP:=
    [∗ map] k ↦ v ∈ (filter P m), Φ k v.
End definition.

Section lemmas.
  Context `{Countable K}  {A: Type}.
  Context {PROP : bi}.
  Implicit Types m : gmap K A.

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

  Lemma big_sepFM_lookup_Some'{m : gmap K A} {P : K * A -> Prop} `{∀ x, Decision (P x)}
        {Φ : K -> A -> PROP} {k : K} {v : A} :
    m !! k = Some v ->
    P (k,v) ->
     Φ k v ∗ (big_sepFM (delete k m) P Φ) ⊢ big_sepFM m P Φ.
  Proof.
    iIntros (Hlk P_v) "[Φ fm]".
    rewrite /big_sepFM.
    rewrite map_filter_delete;auto.
    iDestruct (big_sepM_delete _ _ k v with "[Φ $fm]") as "acc".
    rewrite map_filter_lookup_Some.
    split;auto.
    iFrame "Φ".
    done.
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
    iInduction m as [| k v m Hlk] "IH" using map_ind.
    iSplit; iIntros "?";iApply big_sepFM_empty.
    destruct (decide (P(k,v))).
    rewrite 2?big_sepFM_insert_True //.
    iSplit; iIntros "[$ ?]";by iApply "IH".
    by apply equiv.
    rewrite 2?big_sepFM_insert_False //.
    intro Q'. by apply equiv in Q'.
  Qed.

  Lemma big_sepFM_iff_weak {m: gmap K A} {P Q: K * A -> Prop} `{∀ x, Decision (P x)} `{∀ x, Decision (Q x)} {Φ: K -> A -> PROP}:
    map_Forall (λ k v, P (k, v) <-> Q (k, v)) m ->
    big_sepFM m P Φ ⊣⊢ big_sepFM m Q Φ.
  Proof.
    intro equiv.
    iInduction m as [| k v m Hlk] "IH" using map_ind.
    iSplit; iIntros "?";iApply big_sepFM_empty.
    rewrite map_Forall_insert in equiv.
    destruct equiv as [eq equiv].
    destruct (decide (P(k,v))).
    rewrite 2?big_sepFM_insert_True //.
    iSplit; iIntros "[$ ?]";by iApply ("IH" $! equiv).
    by apply eq.
    rewrite 2?big_sepFM_insert_False //.
    by iApply ("IH" $! equiv).
    intro Q'. by apply eq in Q'. done.
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

  Lemma big_sepFM_split_lor {m: gmap K A} {P Q: K * A -> Prop} `{∀ x, Decision (P x)} `{∀ x, Decision (Q x)}
                       {Φ: K -> A -> PROP}:
    (∀ kv, P kv ∧ Q kv -> False)
    ->
    big_sepFM m (λ kv, ((P kv) ∨ Q kv):Prop) Φ ⊣⊢ (big_sepFM m P Φ)
                       ∗ big_sepFM m Q Φ.
  Proof.
    intro Hfalse.
    {
      iInduction m as [|k v m Hlk] "H" using map_ind.
      iSplit; iIntros "_";try iSplitL;iApply big_sepFM_empty.
      destruct (decide (P (k,v)));destruct (decide (Q (k,v))).
      {
        exfalso.
        eapply Hfalse.
        split;done.
      }
      {
        rewrite big_sepFM_insert_True//.
        rewrite big_sepFM_insert_True//.
        rewrite big_sepFM_insert_False//.
        2:{ left;done. }
        iSplit. iIntros "[$ ?]".
        by iApply "H".
        iIntros "[[$ ?] ?]".
        iApply "H"; iFrame.
      }
      {
        rewrite big_sepFM_insert_True//.
        rewrite big_sepFM_insert_False//.
        rewrite big_sepFM_insert_True//.
        2:{ right;done. }
        iSplit. iIntros "[$ ?]".
        by iApply "H".
        iIntros "[? [$ ?]]".
        iApply "H"; iFrame.
      }
      {
        rewrite 3?big_sepFM_insert_False//.
        intros [? | ?]; done.
      }
    }
  Qed.


  Lemma big_sepFM_split_lor_weak {m: gmap K A} {P Q: K * A -> Prop} `{∀ x, Decision (P x)} `{∀ x, Decision (Q x)}
                       {Φ: K -> A -> PROP}:
    map_Forall (λ k v, P (k,v) ∧ Q (k,v) -> False) m
    ->
    (big_sepFM m (λ kv, ((P kv) ∨ Q kv):Prop) Φ ⊣⊢ (big_sepFM m P Φ)
                       ∗ big_sepFM m Q Φ).
  Proof.
    intro Hfalse.
    {
      iInduction m as [|k v m Hlk] "H" using map_ind.
      iSplit; iIntros "_";try iSplitL;iApply big_sepFM_empty.
      assert (Hfalse': map_Forall (λ (k0 : K) (v0 : A), P (k0, v0) ∧ Q (k0, v0) → False) m).
      {
        rewrite map_Forall_insert //in Hfalse.
        destruct Hfalse;done.
      }
      iSpecialize ("H" $! Hfalse').
      destruct (decide (P (k,v)));destruct (decide (Q (k,v))).
      {
        exfalso.
        eapply (Hfalse k v).
        rewrite lookup_insert //.
        split;done.
      }
      {
        rewrite big_sepFM_insert_True//.
        rewrite big_sepFM_insert_True//.
        rewrite big_sepFM_insert_False//.
        2:{ left;done. }
        iSplit. iIntros "[$ ?]".
        by iApply "H".
        iIntros "[[$ ?] ?]".
        iApply "H"; iFrame.
      }
      {
        rewrite big_sepFM_insert_True//.
        rewrite big_sepFM_insert_False//.
        rewrite big_sepFM_insert_True//.
        2:{ right;done. }
        iSplit. iIntros "[$ ?]".
        by iApply "H".
        iIntros "[? [$ ?]]".
        iApply "H"; iFrame.
      }
      {
        rewrite 3?big_sepFM_insert_False//.
        intros [? | ?]; done.
      }
    }
  Qed.

  Lemma big_sepFM_False {m: gmap K A} `{∀x, (Decision (P x))} {Φ: K -> A -> PROP}:
    (∀ x, P x -> False) ->
    ⊢ big_sepFM m P Φ.
  Proof.
    intro Hfalse.
    iIntros.
    iInduction m as [| k v m Hlk] "IH" using map_ind.
    iApply big_sepFM_empty.
    rewrite big_sepFM_insert_False //.
    intro. eapply Hfalse.  done.
  Qed.

  Lemma big_sepFM_False_weak{m: gmap K A} `{∀x, (Decision (P x))} {Φ: K -> A -> PROP}:
    map_Forall (λ k v, P(k,v) -> False) m->
    ⊢ big_sepFM m P Φ.
  Proof.
    intro Hfalse.
    iIntros.
    iInduction m as [| k v m Hlk] "IH" using map_ind.
    iApply big_sepFM_empty.
    rewrite big_sepFM_insert_False //.
    assert (Hfalse': map_Forall (λ (k0 : K) (v0 : A), P (k0, v0) → False) m).
    {
      rewrite map_Forall_insert //in Hfalse.
      destruct Hfalse;done.
    }
    iApply ("IH" $! Hfalse').
    rewrite map_Forall_insert //in Hfalse.
    destruct Hfalse;done.
  Qed.

  Lemma big_sepFM_filter{m : gmap K A} `{∀x, (Decision (P x))} `{∀x, (Decision (Q x))}
    {Φ: K -> A -> PROP}:
    big_sepFM (filter P m) Q Φ
    ⊣⊢ big_sepFM m (λ x, (Q x ∧ P x):Prop) Φ.
  Proof.
    iInduction m as [| k v m Hlk] "IH" using map_ind.
    iSplit;iIntros "_"; iApply big_sepFM_empty.
    rewrite map_filter_insert //.
    case_decide.
    destruct (decide (Q (k,v))).
    rewrite big_sepFM_insert_True //.
    rewrite big_sepFM_insert_True //.
    iSplit;iIntros "[$ ?]";iApply "IH";done.
    rewrite map_filter_lookup_None. left;done.
    rewrite big_sepFM_insert_False //.
    rewrite big_sepFM_insert_False //.
    intros [];done.
    rewrite map_filter_lookup_None. left;done.
    rewrite delete_notin //.
    rewrite big_sepFM_insert_False //.
    intros [];done.
  Qed.

End lemmas.
