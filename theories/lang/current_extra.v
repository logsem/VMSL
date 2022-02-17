From HypVeri Require Import machine machine_extra.
From HypVeri.algebra Require Import base.

Section current_extra.

Context `{HyperConst : HypervisorConstants}.

Lemma p_upd_id_reg σ i :
  get_reg_files (update_current_vmid σ i) = get_reg_files σ.
Proof. f_equal. Qed.

Lemma p_upd_id_mem σ i :
  get_mem (update_current_vmid σ i) = get_mem σ.
Proof. f_equal. Qed.

Lemma p_upd_id_mb σ i :
  get_mail_boxes (update_current_vmid σ i) = (get_mail_boxes σ).
Proof. f_equal. Qed.

Lemma p_upd_id_pgt σ i :
  get_page_table (update_current_vmid σ i) = get_page_table σ.
Proof. f_equal. Qed.

Lemma p_upd_id_trans σ i :
  get_transactions (update_current_vmid σ i) = (get_transactions σ).
Proof. f_equal. Qed.

End current_extra.
