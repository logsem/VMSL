From iris.base_logic Require Import base_logic.
From stdpp Require fin_map_dom.
From iris.proofmode Require Export tactics.
Import uPred.

Section definition.
  Context `{Countable K}.
  Context {PROP : bi}.

  Definition big_sepSS(s : gset K) (Φ : K -> K -> PROP) : PROP:=
    [∗ set] x1 ∈ s, [∗ set] x2 ∈ s, Φ x1 x2.

  Definition big_sepSS_singleton(s : gset K) (x0: K) (Φ : K -> K -> PROP) : PROP:=
    if decide (x0 ∈ s) then
    (Φ x0 x0 ∗ ([∗ set] x ∈ (s∖ {[x0]}), Φ x0 x ∗ Φ x x0))%I
    else ([∗ set] x ∈ (s∖ {[x0]}), Φ x0 x ∗ Φ x x0)%I.

  Definition big_sepSS_except(s : gset K) (x0: K) (Φ : K -> K -> PROP) : PROP:=
    big_sepSS (s ∖ {[x0]}) Φ.

End definition.

Section lemmas.
  Context `{Countable K}.
  Context {PROP : bi}.
  Implicit Types s : gset K.
  Implicit Type Φ : (K -> K -> PROP).

  Lemma big_sepSS_union_singleton s (x:K) Φ:
    x ∉ s ->
    big_sepSS s Φ ∗ big_sepSS_singleton (s ∪ {[x]}) x Φ ⊢ big_sepSS (s ∪ {[x]}) Φ.
  Proof.
    iIntros (Hnin) "[SS single]".
    rewrite /big_sepSS.
    rewrite big_sepS_union.
    rewrite big_sepS_singleton.
    rewrite (big_sepS_proper (λ y, [∗ set] x2 ∈ (s ∪ {[x]}), Φ y x2)%I).
    2:{
      intros.
      iApply big_sepS_union.
      set_solver.
    }
    rewrite big_sepS_sep.
    iFrame "SS".
    rewrite /big_sepSS_singleton.
    rewrite 2?big_sepS_union.
    rewrite 2?big_sepS_singleton.
    rewrite (big_sepS_proper (λ y, [∗ set] y0 ∈ {[x]}, Φ y y0)%I).
    2:{
      intros.
      iApply big_sepS_singleton.
    }
    assert ((s ∪ {[x]}) ∖ {[x]} = s) as ->. set_solver.
    case_decide.
    rewrite big_sepS_sep.
    iDestruct ("single") as "[$ [$ $]]".
    set_solver.
    set_solver.
    set_solver.
  Qed.

  Lemma big_sepSS_difference_singleton s (x0:K) Φ:
    x0 ∈ s ->
    big_sepSS s Φ ⊢ big_sepSS_except s x0 Φ ∗ big_sepSS_singleton s x0 Φ.
  Proof.
    iIntros (Hin) "SS".
    rewrite /big_sepSS_except /big_sepSS.
    rewrite /big_sepSS_singleton.
    assert (s = s ∖ {[x0]} ∪ {[x0]}). rewrite difference_union_L. set_solver + Hin.
    rewrite H0 in Hin.
    rewrite H0.
    assert ((s ∖ {[x0]} ∪ {[x0]}) ∖ {[x0]} = s ∖ {[x0]}) as ->.
    set_solver +.
    rewrite big_sepS_union.
    rewrite big_sepS_singleton.
    rewrite big_sepS_union.
    rewrite big_sepS_singleton.
    rewrite (big_sepS_proper (λ y, [∗ set] x2 ∈ (s ∖ {[x0]} ∪ {[x0]}), Φ y x2)%I).
    2:{
      intros.
      iApply big_sepS_union.
      set_solver.
    }
    rewrite big_sepS_sep.
    rewrite (big_sepS_proper (λ y, [∗ set] y0 ∈ {[x0]}, Φ y y0)%I).
    2:{
      intros.
      iApply big_sepS_singleton.
    }
    case_decide.
    rewrite big_sepS_sep.
    iDestruct ("SS") as "(($&$)&$&$)".
    done.
    set_solver.
    set_solver.
  Qed.

  Lemma big_sepSS_sep s Φ Φ1 Φ2 :
    (∀ x y, Φ x y ⊣⊢ Φ1 x y ∗ Φ2 x y) ->
    big_sepSS s Φ ⊣⊢ big_sepSS s Φ1 ∗ big_sepSS s Φ2.
  Proof.
    intros.
    rewrite /big_sepSS.
    rewrite (big_sepS_proper (λ x1, [∗ set] x2 ∈ s, Φ x1 x2)%I).
    2:{
      intros.
      rewrite (big_sepS_proper (λ x2, Φ x x2)%I).
      2:{
        intros.
        apply H0.
      }
      iApply big_sepS_sep.
    }
    rewrite big_sepS_sep.
    done.
  Qed.

  Lemma big_sepSS_singletion_union s v v' Φ :
    v ∈ s ->
    big_sepSS_singleton (s ∖ {[v]}) v' Φ ∗ big_sepSS_singleton {[v]} v' Φ
    ⊣⊢ big_sepSS_singleton s v' Φ.
  Proof.
    intro.
    rewrite /big_sepSS_singleton.
    case_decide.
    case_decide;first set_solver.
    case_decide;last set_solver.
    rewrite -sep_assoc.
    rewrite -big_sepS_union.
    rewrite -difference_union_distr_l_L.
    assert ((s ∖ {[v]} ∪ {[v]}) = s) as ->.
    rewrite difference_union_L. set_solver.
    done.
    set_solver.
    case_decide.
    case_decide;last set_solver.
    rewrite sep_comm .
    rewrite -sep_assoc.
    rewrite -big_sepS_union.
    rewrite -difference_union_distr_l_L.
    assert (({[v]} ∪ s ∖ {[v]}) = s) as ->.
    rewrite union_comm_L. rewrite difference_union_L. set_solver.
    done.
    set_solver.
    case_decide. set_solver.
    rewrite -big_sepS_union.
    rewrite -difference_union_distr_l_L.
    assert ((s ∖ {[v]} ∪ {[v]}) = s) as ->.
    rewrite difference_union_L. set_solver.
    done.
    set_solver.
  Qed.

End lemmas.
