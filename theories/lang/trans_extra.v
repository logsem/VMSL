From HypVeri Require Import machine machine_extra tactics.
From HypVeri.algebra Require Import base.

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
  symmetry in Hvalid.
  repeat (apply andb_true_eq in Hvalid;destruct Hvalid as [? Hvalid]).
  symmetry in H.
  rewrite Nat.eqb_eq in H.
  apply fin_to_nat_inj in H.
  subst.
  symmetry in H0.
  rewrite negb_true_iff in H0.
  rewrite Nat.eqb_neq in H0.
  split.
  2: {intro H'; apply H0; symmetry in H'.  rewrite H'. done. }
  destruct wh.
  inversion Hvalid.
  done.
Qed.

Lemma p_alloc_trans_current_vm σ h trans:
  get_current_vm (alloc_transaction σ h trans) = get_current_vm σ.
Proof. f_equal. Qed.

Lemma p_alloc_trans_regs σ h trans:
  get_reg_files (alloc_transaction σ h trans) = get_reg_files σ.
Proof. f_equal. Qed.

Lemma p_alloc_trans_mem σ h trans:
  get_mem (alloc_transaction σ h trans) = get_mem σ.
Proof. f_equal. Qed.

Lemma p_alloc_trans_mb σ h trans:
  get_mail_boxes (alloc_transaction σ h trans) = get_mail_boxes σ.
Proof. f_equal. Qed.

Lemma p_alloc_trans_pgt σ h trans:
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
   (get_hpool_gset (insert_transaction σ h tran))
   = (get_hpool_gset σ) ∖ {[h]}.
Proof.
  rewrite /get_hpool_gset.
  rewrite /get_fresh_handles /insert_transaction /=.
  rewrite map_filter_insert_False.
  rewrite map_filter_delete.
  rewrite dom_delete_L //.
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

Lemma u_alloc_trans_trans σ h tran:
  (get_trans_gmap (alloc_transaction σ h tran))
  = <[h:= Some (tran.1)]>(get_trans_gmap σ).
Proof.
  unfold get_trans_gmap.
  apply (alloc_transaction_update_transactions (λ tran, (tran.1))).
Qed.

Lemma u_alloc_trans_retri σ h tran:
  (get_retri_gmap (alloc_transaction σ h tran)) = <[h:= Some tran.2]>(get_retri_gmap σ).
Proof.
  apply (alloc_transaction_update_transactions (λ tran, tran.2)).
Qed.

(* TODO *)
Lemma update_transaction_preserve_current_vm σ h trans:
  get_current_vm (update_transaction σ h trans) = get_current_vm σ.
Proof. f_equal. Qed.

Lemma update_transaction_preserve_regs σ h trans:
  get_reg_gmap (update_transaction σ h trans) = get_reg_gmap σ.
Proof. f_equal. Qed.

Lemma update_transaction_preserve_mem σ h trans:
  get_mem (update_transaction σ h trans) = get_mem σ.
Proof. f_equal. Qed.

Lemma update_transaction_preserve_mb σ h trans:
  get_mb_gmap (update_transaction σ h trans) = get_mb_gmap σ.
Proof. f_equal. Qed.

Lemma update_transaction_preserve_rx σ h trans:
  get_rx_gmap (update_transaction σ h trans) = get_rx_gmap σ.
Proof. f_equal. Qed.

Lemma update_transaction_preserve_owned σ h trans:
  get_own_gmap (update_transaction σ h trans) = get_own_gmap σ.
Proof. f_equal. Qed.

Lemma update_transaction_update_transactions{Info:Type}{σ} (proj: transaction -> Info) h tran:
  (get_transactions_gmap (update_transaction σ h tran) proj)
  = <[h:= Some (proj tran)]>(get_transactions_gmap σ proj).
Proof.
  apply insert_transaction_update_transactions.
Qed.

Lemma update_transaction_update_trans σ h tran:
  (get_trans_gmap (update_transaction σ h tran))
  = <[h:= Some tran.1]>(get_trans_gmap σ).
Proof.
  apply (update_transaction_update_transactions (λ tran, tran.1)).
Qed.

Lemma update_transaction_update_retri σ h tran:
  (get_retri_gmap (update_transaction σ h tran)) = <[h:= Some tran.2]>(get_retri_gmap σ).
Proof.
  apply (update_transaction_update_transactions (λ tran, tran.2)).
Qed.

(* Lemma get_transactions_gmap_preserve_dom {Info:Type} {σ} (proj : transaction->Info): *)
(*   dom (gset Word) (get_transactions_gmap σ proj) = dom (gset Word) (get_transactions σ). *)
(* Proof. *)
(*   rewrite /get_transactions_gmap. *)
(*   rewrite dom_fmap_L //. *)
(* Qed. *)

(* Lemma get_trans_gmap_preserve_dom {σ}: *)
(*   dom (gset Word) (get_trans_gmap σ) = dom (gset Word) (get_transactions σ). *)
(* Proof. *)
(*   apply get_transactions_gmap_preserve_dom. *)
(* Qed. *)

(* Lemma get_retri_gmap_preserve_dom {σ}: *)
(*   dom (gset Word) (get_retri_gmap σ) = dom (gset Word) (get_transactions σ). *)
(* Proof. *)
(*   apply get_transactions_gmap_preserve_dom. *)
(* Qed. *)

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
  inv_trans_wellformed σ -> inv_trans_wellformed (remove_transaction σ h).
Proof.
  Admitted.

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
  (get_hpool_gset (remove_transaction σ h))
  = ({[h]} ∪ (get_hpool_gset σ) ).
Proof.
  rewrite /get_hpool_gset /=.
  rewrite /get_fresh_handles.
  rewrite map_filter_insert_True;last done.
  rewrite dom_insert_L //.
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


(* Lemma get_retri_gmap_lookup {σ meta} wh b: *)
(* (get_transactions σ) !! wh = Some (Some (meta,b))-> *)
(* get_retri_gmap σ !! wh = Some (Some b). *)
(* Proof. *)
(*   intros Hlk. *)
(*   rewrite /get_retri_gmap /get_transactions_gmap. *)
(*   rewrite lookup_fmap_Some. *)
(*   exists (Some (meta,b)). *)
(*   split;auto. *)
(* Qed. *)

End trans_extra.
