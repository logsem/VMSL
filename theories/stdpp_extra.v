From Coq Require Import ssreflect ssrfun ssrbool.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import stdpp.base.
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
