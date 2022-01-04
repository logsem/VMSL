From HypVeri.algebra Require Import base.

Section predicates.

  Context `{hypconst : !HypervisorConstants}.

  Definition is_total_gmap `{Countable K} {V: Type} (m : gmap K V) : Prop := ∀ (k : K), is_Some (m !! k).

  (* Definition is_checkb (checkb: permission -> VMID -> Prop) (pgt:page_table) p i := *)
  (*   match pgt !! p with *)
  (*   | Some perm => checkb perm i *)
  (*   (* assume pgt is total *) *)
  (*   | None => False *)
  (*   end. *)

  (* Definition is_accessible pgt p i := is_checkb (λ perm i, i ∈ perm.2) pgt p i. *)

  (* Lemma is_accessible_check_true σ p i: *)
  (*   let pgt := (get_page_table σ) in *)
  (*   is_total_gmap pgt -> is_accessible pgt p i -> check_access_page σ i p = true. *)
  (* Proof. *)
  (*   intros pgt Htotal Hcheckb. *)
  (*   rewrite /check_access_page. *)
  (*   rewrite /is_accessible /is_checkb in Hcheckb. *)
  (*   destruct (pgt !! p) eqn:Heqn. *)
  (*   - rewrite Heqn in Hcheckb. *)
  (*     rewrite Heqn. *)
  (*     destruct p0. *)
  (*     case_match;first done. *)
  (*     simpl in Heqn. *)
  (*     done. *)
  (*   - rewrite /is_total_gmap in Htotal. *)
  (*     specialize (Htotal p) as [? Hsome]. *)
  (*     rewrite Heqn in Hsome. *)
  (*     done. *)
  (* Qed. *)

  (* Definition is_owned pgt p i := is_checkb (λ perm i, Some i = perm.1.1) pgt p i. *)

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
    (get_transactions σ).1 = (get_transactions σ').1 -> get_trans_gmap σ = get_trans_gmap σ'.
  Proof.
    intro Heq_proj.
    rewrite /get_trans_gmap /get_transactions_gmap Heq_proj //.
  Qed.

  Lemma preserve_get_hpool_gset σ' σ :
    (get_transactions σ).2 = (get_transactions σ').2 -> get_hpool_gset σ = get_hpool_gset σ'.
  Proof.
    intro Heq_proj.
    rewrite /get_hpool_gset /get_transactions_gmap Heq_proj //.
  Qed.

  Lemma preserve_get_retri_gmap σ' σ :
    (get_transactions σ).1 = (get_transactions σ').1 -> get_retri_gmap σ = get_retri_gmap σ'.
  Proof.
    intro Heq_proj.
    rewrite /get_retri_gmap /get_transactions_gmap Heq_proj //.
  Qed.

  Lemma preserve_inv_trans_hpool_consistent σ' σ :
    (get_transactions σ) = (get_transactions σ') -> inv_trans_hpool_consistent σ = inv_trans_hpool_consistent σ'.
  Proof.
    intro Heq_proj.
    rewrite /inv_trans_hpool_consistent.
    rewrite /inv_trans_hpool_disj /inv_finite_handles.
    destruct (get_transactions σ), (get_transactions σ').
    inversion Heq_proj;subst.
    done.
  Qed.

  Lemma preserve_inv_trans_wellformed σ' σ :
    (get_transactions σ).1 = (get_transactions σ').1 -> inv_trans_wellformed σ = inv_trans_wellformed σ'.
  Proof.
    intro Heq_proj.
    rewrite /inv_trans_wellformed Heq_proj //.
  Qed.

  Lemma preserve_inv_trans_pgt_consistent σ' σ :
    (get_transactions σ).1 = (get_transactions σ').1 ->
    (get_page_table σ) = (get_page_table σ') ->
    inv_trans_pgt_consistent σ = inv_trans_pgt_consistent σ'.
  Proof.
    intros Heq_proj_trans Heq_proj_pgt.
    rewrite /inv_trans_pgt_consistent Heq_proj_trans Heq_proj_pgt //.
  Qed.

  Lemma preserve_inv_pgt_mb_consistent σ' σ:
    (get_page_table σ) = (get_page_table σ') ->
    (get_mail_boxes σ) = (get_mail_boxes σ') ->
    inv_pgt_mb_consistent σ = inv_pgt_mb_consistent σ'.
  Proof.
    intros Heq_pgt Heq_mb.
    rewrite /inv_pgt_mb_consistent Heq_pgt Heq_mb //.
  Qed.

  Lemma preserve_inv_mb_wellformed σ' σ:
    (get_mail_boxes σ) = (get_mail_boxes σ') ->
    inv_mb_wellformed σ = inv_mb_wellformed σ'.
  Proof.
    intros Heq_mb.
    rewrite /inv_mb_wellformed (preserve_get_mb_gmap σ' σ) //.
  Qed.

End preservation.

Section helper.

  Context `{hypconst : !HypervisorConstants}.

  Definition  update_acc_gmap upd  (gm:gmap PID (frac * (gset_disj VMID)))  (v: VMID) (sps: gset PID):=
    (set_fold (λ p acc, upd acc v p) gm sps).

  Definition revoke_acc_gmap :=
    update_acc_gmap (λ (gm: gmap _ (frac * (gset_disj VMID))) (v:VMID) (p:PID),  match (gm !! p) with
                                | Some (q, GSet s) => <[p:= (q, GSet (s ∖ {[v]}))]>gm
                                | _ => gm
                                end
                    ).

End helper.
