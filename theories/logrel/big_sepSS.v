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
    [∗ set] x∈ s, Φ x0 x ∗ Φ x x0.

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
  Admitted.

  Lemma big_sepSS_difference_singleton s (x0:K) Φ:
    x0 ∈ s ->
    big_sepSS s Φ ⊢ big_sepSS_except s x0 Φ ∗ big_sepSS_singleton s x0 Φ.
  Proof.
  Admitted.

  Lemma big_sepSS_sep s Φ Φ1 Φ2 :
    (∀ x y, Φ x y⊣⊢ Φ1 x y ∗ Φ2 x y) ->
    big_sepSS s Φ ⊣⊢ big_sepSS s Φ1 ∗ big_sepSS s Φ2.
  Proof.
  Admitted.

End lemmas.
