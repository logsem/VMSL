From stdpp Require Import fin_maps.
From stdpp Require Import gmap.

Section gmap_map_zip.
  Context  {K V: Type}.
  Context `{Countable K}.
  Implicit Type m : gmap K V.

  Lemma map_zip_empty_r{V':Type} m:
    map_zip m (∅: gmap _ V') = ∅.
  Proof.
    unfold map_zip_with.
    induction m using map_ind.
    {
      simpl. apply merge_empty.
    }
    {
      rewrite merge_empty_r.
      rewrite merge_empty_r in IHm.
      rewrite omap_insert_None.
      rewrite IHm.
      rewrite delete_empty. auto.
      done.
    }
  Qed.

  Lemma map_zip_empty_l{V':Type} m:
    map_zip (∅: gmap _ V') m = ∅.
  Proof.
    unfold map_zip_with.
    rewrite merge_empty_l.
    induction m using map_ind.
    {
      rewrite omap_empty. done.
    }
    {
      rewrite omap_insert_None.
      rewrite IHm.
      rewrite delete_empty. auto.
      done.
    }
  Qed.

End gmap_map_zip.
