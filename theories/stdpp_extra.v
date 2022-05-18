From Coq Require Import ssreflect.
Require Import stdpp.gmap.
From Coq Require Import Lia.

Lemma zip_length_le {A B} {l' : list A} {l1 l2 l3 : list B} :
  length l' <= length l1 -> l2 = l1 ++ l3 -> zip l1 l' = zip l2 l'.
Proof.
  simpl.
  generalize dependent l1.
  generalize dependent l2.
  generalize dependent l3.
  induction l'.
  - intros l3 l2 l1 H1 H2.
    rewrite /zip.
    destruct l2, l1; done.
  - intros l3 l2 l1 H1 H2.
    destruct l2, l1; try done.
    simpl in H2.
    inversion H2.
    simpl in H1.
    inversion H1.
    inversion H2; subst.
    simpl.
    f_equal.
    rewrite (IHl' l3 (l1 ++ l3) l1); try done.
    simpl in H1.
    lia.
Qed.

Lemma map_subseteq_delete `{Countable K}  {V: Type} (m :gmap K V) i : (delete i m) ⊆ m.
Proof.
  rewrite map_subseteq_spec.
  intros k v Hlk.
  destruct (decide (i = k)).
  subst.
  rewrite lookup_delete_Some in Hlk.
  destruct Hlk;done.
  rewrite lookup_delete_ne in Hlk;auto.
Qed.

Lemma map_insert_swap `{Countable K}  {V: Type} (m :gmap K V) k1 k2 v1 v2:
  k1 ≠ k2 ->
  (<[k1:=v1]> (<[k2:=v2]> m) = <[k2:=v2]> (<[k1:=v1]> m)).
Proof.
  intro Hneq.
  revert k1 k2 v1 v2 Hneq.
  induction m using map_ind.
  intros.
  apply map_eq.
  intro.
  destruct (decide (i = k1));
    destruct (decide (i = k2));simplify_map_eq /=;auto.
  intros.
  destruct (decide (i = k1));
    destruct (decide (i = k2));simplify_map_eq /=;auto.
  rewrite IHm. intro; done.
  rewrite 2!insert_insert.
  apply IHm.
  done.
  rewrite insert_insert.
  set X := (Y in Y = _).
  rewrite IHm. auto.
  rewrite insert_insert.
  rewrite /X IHm //.
  apply map_eq.
  intro.
  destruct (decide (i0 = k1));
    destruct (decide (i0 = k2));simplify_map_eq /=;auto.
  rewrite (lookup_insert_ne _ k2) //.
  rewrite (lookup_insert_ne _ k1) //.
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
    apply (union_split_difference_intersection_subseteq_L) in Hsub.
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

  Lemma intersection_subseteq_disjoint A B C:
    C ⊆ A -> C ⊆ B ->
    A ∖ C ## B ->
    A ∩ B = C.
  Proof.
    intros Hsub1 Hsub2 Hdisj.
    rewrite set_eq.
    intros. split.
    set_solver.
    set_solver.
  Qed.

  Lemma difference_difference_union A B C:
    C ⊆ A ->
    A ∖ (B ∖ C) = A ∖ B ∪ C.
  Proof.
    intro.
    rewrite set_eq.
    intros. split.
    intro.
    apply elem_of_difference in H1.
    destruct H1.
    destruct (decide (x ∈ B)).
    destruct (decide (x ∈ C)); set_solver.
    set_solver.
    intro.
    rewrite elem_of_union in H1.
    destruct H1; set_solver.
  Qed.

  Lemma intersection_difference A B:
    A ∖ B = A ∖ (A ∩ B).
  Proof.
    set_solver.
  Qed.

End sets.

Section filter.
  Context `{Countable K} {V: Type}.

  Implicit Type m : gmap K V.

  Lemma map_filter_imp m P `{∀ x, Decision (P x)} Q `{∀ x, Decision (Q x)}:
    (∀ x, P x -> Q x) ->
    filter P m ⊆ filter Q m.
  Proof.
    intros Himp.
    induction m using map_ind. done.
    rewrite 2?map_filter_insert.
    case_decide;case_decide.
    {
      apply map_subseteq_spec.
      intros.
      rewrite lookup_insert_Some in H5.
      destruct H5 as [[-> ->]|[Hneq Hlk]].
      {
        rewrite lookup_insert //.
      }
      {
        rewrite lookup_insert_ne //.
        rewrite map_subseteq_spec in IHm.
        by apply IHm.
      }
      }
      by apply Himp in H3.
    rewrite delete_notin //.
    apply map_subseteq_spec.
    intros.
    destruct (decide (i = i0)).
    {
      subst.
      rewrite map_filter_lookup_Some in H5.
      destruct H5;auto.
      rewrite H5 in H2. inversion H2.
    }
    {
      rewrite lookup_insert_ne //.
      rewrite map_subseteq_spec in IHm.
      by apply IHm.
    }
    rewrite 2?delete_notin //.
  Qed.

End filter.
