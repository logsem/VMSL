From HypVeri.algebra Require Import base.

Section predicates.

  Context `{hypconst : !HypervisorConstants}.

  Definition is_total_gmap `{Countable K} {V: Type} (m : gmap K V) : Prop := ∀ (k : K), is_Some (m !! k).

End predicates.

Section preservation.
  Context `{hypconst : !HypervisorConstants}.

  Implicit Type σ: state.

  Lemma preserve_get_reg_gmap σ' σ :
    get_reg_files σ = get_reg_files σ' -> get_reg_gmap σ = get_reg_gmap σ'.
  Proof.
    intro Heq_proj.
    rewrite /get_reg_gmap Heq_proj //.
  Qed.

  Lemma preserve_get_mb_gmap σ' σ :
    get_mail_boxes σ = get_mail_boxes σ' -> get_mb_gmap σ = get_mb_gmap σ'.
  Proof.
    intro Heq_proj.
    rewrite /get_mb_gmap Heq_proj //.
  Qed.

  Lemma preserve_get_rx_gmap σ' σ :
    get_mail_boxes σ = get_mail_boxes σ' -> get_rx_gmap σ = get_rx_gmap σ'.
  Proof.
    intro Heq_proj.
    rewrite /get_rx_gmap Heq_proj //.
  Qed.

  Lemma preserve_get_own_gmap σ' σ :
    get_page_table σ = get_page_table σ' -> get_own_gmap σ = get_own_gmap σ'.
  Proof.
    intro Heq_proj.
    rewrite /get_own_gmap Heq_proj //.
  Qed.

  Lemma preserve_get_access_gmap σ' σ :
    get_page_table σ = get_page_table σ' -> get_access_gmap σ = get_access_gmap σ'.
  Proof.
    intro Heq_proj.
    rewrite /get_access_gmap Heq_proj //.
  Qed.

  Lemma preserve_get_excl_gmap σ' σ :
    get_page_table σ = get_page_table σ' -> get_excl_gmap σ = get_excl_gmap σ'.
  Proof.
    intro Heq_proj.
    rewrite /get_excl_gmap Heq_proj //.
  Qed.

  Lemma preserve_get_trans_gmap σ' σ :
    (get_transactions σ) = (get_transactions σ') -> get_trans_gmap σ = get_trans_gmap σ'.
  Proof.
    intro Heq_proj.
    rewrite /get_trans_gmap /get_transactions_gmap Heq_proj //.
  Qed.

  Lemma preserve_get_hpool_gset σ' σ :
    (get_transactions σ) = (get_transactions σ') -> get_hpool_gset σ = get_hpool_gset σ'.
  Proof.
    intro Heq_proj.
    rewrite /get_hpool_gset /get_transactions_gmap Heq_proj //.
  Qed.

  Lemma preserve_get_retri_gmap σ' σ :
    (get_transactions σ) = (get_transactions σ') -> get_retri_gmap σ = get_retri_gmap σ'.
  Proof.
    intro Heq_proj.
    rewrite /get_retri_gmap /get_transactions_gmap Heq_proj //.
  Qed.

  Lemma preserve_inv_trans_wellformed σ' σ :
    (get_transactions σ) = (get_transactions σ') -> inv_trans_wellformed σ = inv_trans_wellformed σ'.
  Proof.
    intro Heq_proj.
    rewrite /inv_trans_wellformed Heq_proj //.
  Qed.

  Lemma preserve_inv_trans_pgt_consistent σ' σ :
    (get_transactions σ) = (get_transactions σ') ->
    (get_page_table σ) = (get_page_table σ') ->
    inv_trans_pgt_consistent σ = inv_trans_pgt_consistent σ'.
  Proof.
    intros Heq_proj_trans Heq_proj_pgt.
    rewrite /inv_trans_pgt_consistent Heq_proj_trans Heq_proj_pgt //.
  Qed.

End preservation.

Section helper.

  Context `{hypconst : !HypervisorConstants}.

  Definition  update_acc_gmap upd (gm:gmap PID (frac * (gset_disj VMID)))  (v: VMID) (sps: gset PID):=
    (set_fold (λ p acc, upd acc v p) gm sps).

  Definition revoke_acc_gmap :=
    update_acc_gmap (λ (gm: gmap _ (frac * (gset_disj VMID))) (v:VMID) (p:PID),  match (gm !! p) with
                                | Some (q, GSet s) => <[p:= (q, GSet (s ∖ {[v]}))]>gm
                                | _ => gm
                                end
                    ).

End helper.


From iris.algebra.lib Require Import gmap_view.

Section ghost_map_extra.

  Context `{ghost_mapG Σ K V}.

  Lemma ghost_map_elem_split (k :K) γ q (v:V) :
    k ↪[γ]{#q} v ⊣⊢ k ↪[γ]{#q / 2} v ∗ k ↪[γ]{#q / 2} v.
  Proof.
    iSplit.
    iIntros "elem".
    rewrite ghost_map_elem_eq /ghost_map_elem_def.
    rewrite -own_op.
    rewrite -gmap_view_frag_op.
    rewrite dfrac_op_own.
    rewrite (Qp_div_2 q).
    done.
    iIntros "[elem1 elem2]".
    iDestruct (ghost_map_elem_combine with "elem1 elem2") as "[elem _]".
    rewrite dfrac_op_own.
    rewrite (Qp_div_2 q).
    done.
  Qed.

  End ghost_map_extra.
