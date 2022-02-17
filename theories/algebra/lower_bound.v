From HypVeri.algebra Require Import base.

Section lower_bound_rules.

  Context `{vmG :gen_VMG Σ}.

  Implicit Type σ : state.
  Implicit Type i : VMID.
  Implicit Type s : gset PID.

  Lemma lb_agree {m} i s:
    LB_auth m -∗
    LB@ i := [s] -∗
    ⌜m !! i = Some s⌝.
  Proof.
    iIntros "auth frag".
    rewrite lower_bound_frag_mapsto_eq /lower_bound_frag_mapsto_def.
    rewrite lower_bound_auth_mapsto_eq /lower_bound_auth_mapsto_def.
    iDestruct (own_valid_2 with "auth frag") as "%Hvalid".
    setoid_rewrite auth_both_valid_discrete in Hvalid.
    destruct Hvalid as [Hvalid1 Hvalid2].
    apply singleton_included_exclusive_l in Hvalid1.
    {
      fold_leibniz.
      rewrite lookup_fmap_Some in Hvalid1.
      destruct Hvalid1 as [x [Heq Hlookup]].
      inversion Heq.
      subst x.
      done.
    }
    apply excl_exclusive.
    done.
  Qed.

  Lemma lb_update_alloc {m} i s:
    m !! i = None ->
    LB_auth m ==∗
    LB_auth <[i := s]>m ∗ LB@ i := [s].
  Proof.
    iIntros (Hnone) "auth".
    rewrite lower_bound_frag_mapsto_eq /lower_bound_frag_mapsto_def.
    rewrite lower_bound_auth_mapsto_eq /lower_bound_auth_mapsto_def.
    rewrite -own_op.
    iApply (own_update with "auth").
    apply auth_update_alloc.
    rewrite fmap_insert.
    apply alloc_local_update.
    rewrite lookup_fmap Hnone //.
    done.
  Qed.

End lower_bound_rules.
