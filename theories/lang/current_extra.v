From HypVeri Require Import machine machine_extra.
From HypVeri.algebra Require Import base.

Section current_extra.

Context `{HyperConst : HypervisorConstants}.

Lemma update_current_vmid_preserve_reg σ i :
  get_reg_gmap (update_current_vmid σ i) = get_reg_gmap σ.
Proof. f_equal. Qed.

Lemma update_current_vmid_preserve_mem σ i :
  get_mem (update_current_vmid σ i) = get_mem σ.
Proof. f_equal. Qed.


Lemma update_current_vmid_preserve_tx σ i :
  get_tx_agree (update_current_vmid σ i) = (get_tx_agree σ).
Proof. f_equal. Qed.

Lemma update_current_vmid_preserve_rx1 σ i :
  get_rx_agree (update_current_vmid σ i) = (get_rx_agree σ).
Proof. f_equal. Qed.


Lemma update_current_vmid_preserve_rx2 σ i :
  get_rx_gmap (update_current_vmid σ i) = (get_rx_gmap σ).
Proof. f_equal. Qed.

Lemma update_current_vmid_preserve_pt σ i i':
  get_vm_page_table (update_current_vmid σ i) i' = get_vm_page_table σ i'.
Proof. f_equal. Qed.

Lemma update_current_vmid_preserve_owned σ i :
  get_owned_gmap (update_current_vmid σ i) = (get_owned_gmap σ).
Proof. f_equal. Qed.

Lemma update_current_vmid_preserve_access σ i :
  get_access_gmap (update_current_vmid σ i) = (get_access_gmap σ).
Proof. f_equal. Qed.

Lemma update_current_vmid_preserve_excl σ i :
  get_excl_gmap (update_current_vmid σ i) = (get_excl_gmap σ).
Proof. f_equal. Qed.

Lemma update_current_vmid_preserve_trans σ i :
  get_trans_gmap (update_current_vmid σ i) = (get_trans_gmap σ).
Proof. f_equal. Qed.

Lemma update_current_vmid_preserve_trans' σ i :
  get_transactions (update_current_vmid σ i) = (get_transactions σ).
Proof. f_equal. Qed.

Lemma update_current_vmid_preserve_hpool σ i :
  get_hpool_gset (update_current_vmid σ i) = (get_hpool_gset σ).
Proof. f_equal. Qed.

Lemma update_current_vmid_preserve_retri σ i :
  get_retri_gmap (update_current_vmid σ i) = (get_retri_gmap σ).
Proof. f_equal. Qed.

End current_extra.

Ltac rewrite_vmid_all :=
  match goal with
  | |- _ =>
    try rewrite -> update_current_vmid_preserve_reg;
    try rewrite -> update_current_vmid_preserve_mem;
    try rewrite -> update_current_vmid_preserve_tx;
    try rewrite -> update_current_vmid_preserve_rx1;
    try rewrite -> update_current_vmid_preserve_rx2;
    try rewrite -> update_current_vmid_preserve_owned;
    try rewrite -> update_current_vmid_preserve_access;
    try rewrite -> update_current_vmid_preserve_excl;
    try rewrite -> update_current_vmid_preserve_trans;
    try rewrite -> update_current_vmid_preserve_trans';
    try rewrite -> update_current_vmid_preserve_hpool;
    try rewrite -> update_current_vmid_preserve_retri
  end.
