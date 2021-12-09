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

  Lemma big_sepM_union_acc Φ m m' m'' :
    m' ⊆ m ->
    (dom (gset K) m') = (dom (gset K) m'') ->
    ([∗ map] k↦y ∈ m, Φ k y) ⊢ ([∗ map] k↦y ∈ m', Φ k y) ∗ (([∗ map] k↦y ∈ m'', Φ k y) -∗ [∗ map] k↦y ∈ (m'' ∪  m) , Φ k y).
  Proof.
    iIntros (Hsubseteq Hdomeq) "Hmap".
    pose proof (map_difference_union m' m Hsubseteq) as Hrewrite.
    rewrite <-Hrewrite.
    iDestruct (big_sepM_union with "Hmap") as "[Hmap1 Hmap2]".
    apply map_disjoint_difference_r; auto.
    iSplitL "Hmap1"; first iFrame.
    iIntros "Hmap1".
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
(*
For memory chunks
TODO: move to iris.algebra.big_op
*)

  Lemma reg_bigM_split reg i r w w':
    ((full_reg_map reg ∗ [∗ map] k↦y ∈ reg, k @@ i ->r y)%I
     ⊢ (r @@ i ->r w) ∗ (r @@ i ->r w' -∗ ∃ reg', (full_reg_map reg' ∗ [∗ map] k↦y ∈ reg', k @@ i ->r y)))%I.
  Proof.
    Admitted.

End logrel_extra.
