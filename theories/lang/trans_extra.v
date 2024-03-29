From HypVeri Require Import machine machine_extra tactics.
From HypVeri.algebra Require Import base base_extra.

Section trans_extra.

Context `{HyperConst : HypervisorConstants}.
Implicit Type σ : state.
Implicit Type h : Word.

Lemma validate_descriptor i tran:
  validate_transaction_descriptor i tran = true ->
  ∃ j ps, tran = (i,None,j,ps) ∧ j ≠ i.
Proof.
  intro Hvalid.
  rewrite /validate_transaction_descriptor in Hvalid.
  destruct tran as  [[[v wh] r]  ps'].
  exists r, ps'.
  case_bool_decide;last done.
  destruct H as [? [? ?]].
  subst.
  split.
  destruct wh.
  rewrite is_Some_alt // in H1.
  done.
  done.
Qed.

Lemma p_alloc_tran_current_vm σ h trans:
  get_current_vm (alloc_transaction σ h trans) = get_current_vm σ.
Proof. f_equal. Qed.

Lemma p_alloc_tran_regs σ h trans:
  get_reg_files (alloc_transaction σ h trans) = get_reg_files σ.
Proof. f_equal. Qed.

Lemma p_alloc_tran_mem σ h trans:
  get_mem (alloc_transaction σ h trans) = get_mem σ.
Proof. f_equal. Qed.

Lemma p_alloc_tran_mb σ h trans:
  get_mail_boxes (alloc_transaction σ h trans) = get_mail_boxes σ.
Proof. f_equal. Qed.

Lemma p_alloc_tran_pgt σ h trans:
  get_page_table (alloc_transaction σ h trans) = get_page_table σ.
Proof. f_equal. Qed.

Lemma insert_transaction_update_transactions{Info:Type} {σ} (proj: transaction -> Info) h tran:
  (get_transactions_gmap (insert_transaction σ h tran) proj)
  = <[h:= Some (proj tran)]>(get_transactions_gmap σ proj).
Proof.
  rewrite /get_transactions_gmap //=.
  apply map_eq.
  intro.
  destruct (decide (h=i)).
  - subst i;rewrite lookup_insert.
    apply lookup_fmap_Some.
    exists (Some tran).
    split;first auto.
    rewrite lookup_insert_Some.
    left.
    done.
  - rewrite lookup_insert_ne;eauto.
    rewrite fmap_insert.
    rewrite lookup_insert_ne;eauto.
Qed.

Lemma alloc_transaction_update_transactions{Info:Type}{σ} (proj: transaction -> Info) h tran:
  (get_transactions_gmap (alloc_transaction σ h tran) proj)
  = <[h:= Some (proj tran)]>(get_transactions_gmap σ proj).
Proof.
  apply insert_transaction_update_transactions.
Qed.

Lemma insert_transaction_update_hpool {σ} h tran:
   (get_hpool_gset (insert_transaction σ h tran)) = (get_hpool_gset σ) ∖ {[h]}.
Proof.
  rewrite /get_hpool_gset.
  rewrite /get_fresh_handles /insert_transaction /=.
  rewrite map_filter_insert_False.
  rewrite map_filter_delete.
  rewrite dom_delete_L. set_solver.
  done.
Qed.

Lemma update_transaction_update_hpool {σ} h tran:
   (get_hpool_gset (update_transaction σ h tran))
   = (get_hpool_gset σ) ∖ {[h]}.
Proof.
  apply insert_transaction_update_hpool.
Qed.

Lemma update_transaction_preserve_trans {meta} σ wh b b' :
  (get_transactions σ) !! wh = Some (Some (meta, b)) ->
   (get_trans_gmap (update_transaction σ wh (meta, b')))
  = get_trans_gmap σ.
Proof.
  intros H.
  rewrite /get_trans_gmap /get_transactions_gmap //=.
  apply map_eq.
  intros i.
  rewrite fmap_insert.
  destruct (decide (wh=i)).
  - subst i.
    rewrite lookup_insert.
    symmetry.
    apply lookup_fmap_Some.
    exists (Some (meta, b)).
    split;auto.
  - rewrite lookup_insert_ne;eauto.
Qed.

Lemma get_retri_gmap_to_get_transaction σ wh {meta b}:
  (<[wh:= Some b]> (get_retri_gmap σ)) =
  (get_retri_gmap
     (get_reg_files σ, get_mail_boxes σ, get_page_table σ,
      get_current_vm σ, get_mem σ,
      (<[wh := Some (meta, b)]> (get_transactions σ)))).
Proof.
  rewrite /get_retri_gmap.
  rewrite /get_transactions_gmap.
  apply map_eq.
  intros i.
  rewrite fmap_insert //=.
Qed.

Lemma p_alloc_tran_inv_wf {σ} h tran:
  inv_trans_wellformed σ ->
  ((size tran.1.1.2 + 4)%nat <=? 1000)%Z = true ->
  tran.1.1.1.1 ≠ tran.1.1.1.2 ->
  is_Some (σ.2 !! h) ->
  inv_trans_wellformed (alloc_transaction σ h tran).
  Proof.
    rewrite /inv_trans_wellformed /inv_trans_wellformed'.
    intros.
    rewrite /alloc_transaction.
    rewrite /insert_transaction /=.
    destruct H.
    split.
    rewrite /inv_trans_pg_num_ub.
    apply (map_Forall_insert_2 _ σ.2).
    done.
    done.
    destruct H3.
    split.
    rewrite /inv_trans_sndr_rcvr_neq.
    apply (map_Forall_insert_2 _ σ.2).
    done.
    done.
    rewrite /inv_finite_handles.
    rewrite dom_insert_L.
    rewrite /inv_finite_handles in H1.
    rewrite -elem_of_dom in H2.
    rewrite /inv_finite_handles in H4.
    rewrite H4.
    set_solver + H2.
  Qed.

Lemma u_alloc_tran_trans σ h tran:
  (get_trans_gmap (alloc_transaction σ h tran))
  = <[h:= Some (tran.1)]>(get_trans_gmap σ).
Proof.
  unfold get_trans_gmap.
  apply (alloc_transaction_update_transactions (λ tran, (tran.1))).
Qed.

Lemma u_alloc_tran_retri σ h tran:
  (get_retri_gmap (alloc_transaction σ h tran)) = <[h:= Some tran.2]>(get_retri_gmap σ).
Proof. apply (alloc_transaction_update_transactions (λ tran, tran.2)). Qed.

Lemma u_alloc_tran_hpool σ h tran:
(get_hpool_gset (alloc_transaction σ h tran)) = (get_hpool_gset σ) ∖ {[h]}.
Proof. apply update_transaction_update_hpool. Qed.

Lemma p_alloc_tran_inv_disj σ h tran:
  inv_trans_ps_disj σ ->
  σ.2 !! h = Some None ->
  tran.1.1.2 ## pages_in_trans' σ.2->
  inv_trans_ps_disj (alloc_transaction σ h tran).
Proof.
  rewrite /inv_trans_ps_disj /alloc_transaction /=.
  intros.
  apply trans_ps_disj_update_None';auto.
Qed.

Lemma p_upd_tran_current_vm σ h trans:
  get_current_vm (update_transaction σ h trans) = get_current_vm σ.
Proof. f_equal. Qed.

Lemma p_upd_tran_regs σ h trans:
  get_reg_files (update_transaction σ h trans) = get_reg_files σ.
Proof. f_equal. Qed.

Lemma p_upd_tran_mem σ h trans:
  get_mem (update_transaction σ h trans) = get_mem σ.
Proof. f_equal. Qed.

Lemma p_upd_tran_mb σ h trans:
  get_mail_boxes (update_transaction σ h trans) = get_mail_boxes σ.
Proof. f_equal. Qed.

Lemma p_upd_tran_pgt σ h trans:
  get_page_table (update_transaction σ h trans) = get_page_table σ.
Proof. f_equal. Qed.

Lemma update_transaction_update_transactions{Info:Type}{σ} (proj: transaction -> Info) h tran:
  (get_transactions_gmap (update_transaction σ h tran) proj)
  = <[h:= Some (proj tran)]>(get_transactions_gmap σ proj).
Proof. apply insert_transaction_update_transactions. Qed.

Lemma u_upd_tran_trans σ h tran:
  (get_trans_gmap (update_transaction σ h tran)) = <[h:= Some tran.1]>(get_trans_gmap σ).
Proof. apply (update_transaction_update_transactions (λ tran, tran.1)). Qed.

Lemma u_upd_tran_retri σ h tran:
  (get_retri_gmap (update_transaction σ h tran)) = <[h:= Some tran.2]>(get_retri_gmap σ).
Proof. apply (update_transaction_update_transactions (λ tran, tran.2)). Qed.

Lemma p_upd_tran_hp {σ} h tran:
  (∃ tran, σ.2 !! h = Some tran ∧ is_Some tran) ->
  (get_hpool_gset (update_transaction σ h tran)) = ((get_hpool_gset σ)).
Proof.
  intro.
  rewrite /get_hpool_gset /=.
  rewrite /get_fresh_handles.
  rewrite map_filter_insert_False; last done.
  rewrite map_filter_delete.
  f_equal.
  rewrite delete_notin //.
  rewrite map_filter_lookup_None.
  right.
  destruct H as [? [? ?]].
  intros.
  rewrite H1 in H.
  inversion H. subst x0.
  simpl. destruct H0.
  subst x. done.
Qed.

Lemma p_upd_tran_inv_wf σ h tran:
  inv_trans_wellformed σ ->
  (∃t, σ.2 !! h = Some (Some t) ∧ t.1 = tran.1) ->
  inv_trans_wellformed (update_transaction σ h tran).
Proof.
  intros Hinv Hlk.
  destruct Hlk as [? [Hlk Heq]].
  rewrite /inv_trans_wellformed /inv_trans_wellformed' /update_transaction /insert_transaction /=.
  destruct Hinv as [Hub [Hneq Hfin]].
  split.
  apply (map_Forall_insert_2 _ σ.2).
  specialize (Hub h _ Hlk).
  simpl in Hub.
  rewrite -Heq //.
  done.
  split.
  apply (map_Forall_insert_2 _ σ.2).
  specialize (Hneq h _ Hlk).
  simpl in Hneq.
  rewrite -Heq //.
  done.
  rewrite /inv_finite_handles.
  rewrite dom_insert_L.
  rewrite /inv_finite_handles in Hfin.
  assert (is_Some (σ.2 !! h)).
  exists (Some x).
  done.
  rewrite -elem_of_dom in H.
  rewrite Hfin.
  set_solver + H.
Qed.

Lemma p_upd_tran_inv_disj σ h (tran tran': transaction):
  inv_trans_ps_disj σ ->
  σ.2 !! h = Some (Some tran) ->
  tran.1 = tran'.1 ->
  inv_trans_ps_disj (update_transaction σ h tran').
Proof.
  rewrite /inv_trans_ps_disj /update_transaction /=.
  intros.
  eapply trans_ps_disj_update'.
  done. exact H0. done.
Qed.

Lemma p_rm_tran_current_vm σ h:
  get_current_vm (remove_transaction σ h) = get_current_vm σ.
Proof. f_equal. Qed.

Lemma p_rm_tran_regs σ h :
  get_reg_files (remove_transaction σ h ) = get_reg_files σ.
Proof. f_equal. Qed.

Lemma p_rm_tran_mem σ h :
  get_mem (remove_transaction σ h ) = get_mem σ.
Proof. f_equal. Qed.

Lemma p_rm_tran_mb σ h :
 get_mail_boxes (remove_transaction σ h ) = get_mail_boxes σ.
Proof. f_equal. Qed.

Lemma p_rm_tran_pgt σ h :
  get_page_table (remove_transaction σ h ) = get_page_table σ.
Proof. f_equal. Qed.

Lemma p_rm_tran_inv_wf σ h :
  inv_trans_wellformed σ ->
  is_Some(σ.2 !! h) ->
  inv_trans_wellformed (remove_transaction σ h).
Proof.
   rewrite /inv_trans_wellformed /inv_trans_wellformed'.
    intros.
    rewrite /remove_transaction /=.
    destruct H.
    split.
    rewrite /inv_trans_pg_num_ub.
    apply (map_Forall_insert_2 _ σ.2).
    done.
    done.
    destruct H1.
    split.
    rewrite /inv_trans_sndr_rcvr_neq.
    apply (map_Forall_insert_2 _ σ.2).
    done.
    done.
    rewrite /inv_finite_handles.
    rewrite dom_insert_L.
    rewrite /inv_finite_handles in H2.
    rewrite -elem_of_dom in H0.
    rewrite H2.
    set_solver + H0.
  Qed.

Lemma u_rm_tran_tran' {Info:Type}{σ} (proj: transaction -> Info) h :
  (get_transactions_gmap (remove_transaction σ h) proj)
  = (<[h:= None]> (get_transactions_gmap σ proj)).
Proof.
  rewrite /get_transactions_gmap //=.
  apply map_eq.
  intro.
  rewrite fmap_insert //.
Qed.

Lemma u_rm_tran_hp {σ} h :
  h ∈ valid_handles ->
  (get_hpool_gset (remove_transaction σ h)) = ({[h]} ∪ (get_hpool_gset σ) ).
Proof.
  intro Hvalid.
  rewrite /get_hpool_gset /=.
  rewrite /get_fresh_handles.
  rewrite map_filter_insert_True;last done.
  rewrite dom_insert_L. set_solver.
Qed.

Lemma u_rm_tran_tran σ h :
  (get_trans_gmap (remove_transaction σ h ))
  = (<[h:= None]>(get_trans_gmap σ)).
Proof.
  apply (u_rm_tran_tran' (λ tran, tran.1)).
Qed.

Lemma u_rm_tran_retri σ h :
  (get_retri_gmap (remove_transaction σ h )) = (<[h := None]> (get_retri_gmap σ)).
Proof.
  apply (u_rm_tran_tran' (λ tran, tran.2)).
Qed.

Lemma p_rm_tran_inv_disj σ h :
  inv_trans_ps_disj σ ->
  inv_trans_ps_disj (remove_transaction σ h).
Proof.
  rewrite /inv_trans_ps_disj /remove_transaction /=.
  intro.
  by apply trans_ps_disj_delete'.
Qed.

End trans_extra.
