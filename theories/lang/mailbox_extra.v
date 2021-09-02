From HypVeri Require Import machine.
From HypVeri.algebra Require Import base.

Lemma empty_rx_global_preserve_current_vm σ i :
  (get_current_vm (empty_rx_global σ i)) = (get_current_vm σ).
Proof.
  rewrite /empty_rx_global.
  rewrite (surjective_pairing (get_vm_mail_box σ i)).
  by rewrite (surjective_pairing (get_vm_mail_box σ i).2).
Qed.

Lemma empty_rx_global_preserve_mem σ i :
  get_mem (empty_rx_global σ i) = get_mem σ.
Proof.
  rewrite /empty_rx_global.
  rewrite (surjective_pairing (get_vm_mail_box σ i)).
  by rewrite (surjective_pairing (get_vm_mail_box σ i).2).
Qed.

Lemma empty_rx_global_preserve_regs σ i :
 get_reg_gmap (empty_rx_global σ i) = get_reg_gmap σ.
Proof.
  rewrite /empty_rx_global.
  rewrite (surjective_pairing (get_vm_mail_box σ i)).
  by rewrite (surjective_pairing (get_vm_mail_box σ i).2).
Qed.

Lemma empty_rx_global_preserve_tx σ i :
  get_tx_agree (empty_rx_global σ i) = (get_tx_agree σ).
Proof.
  rewrite /empty_rx_global.
  rewrite (surjective_pairing (get_vm_mail_box σ i)).
  rewrite (surjective_pairing (get_vm_mail_box σ i).2).
  rewrite /get_tx_agree /get_txrx_auth_agree.
  f_equal.
  simplify_list_eq.
  apply (list_eq_same_length _ _ vm_count).
  rewrite fmap_length.
  apply length_list_of_vmids.
  rewrite fmap_length.
  apply length_list_of_vmids.
  intros.
  apply list_lookup_fmap_inv in H0, H1.
  destruct H0, H1.
  destruct H0, H1.
  rewrite H3 in H2.
  inversion H2;subst x1.
  clear H2.
  rewrite H0 H1.
  do 2 f_equal.
  rewrite /get_vm_mail_box /get_mail_boxes /=.
  destruct (decide (i = x0)).
  subst x0.
  by rewrite vlookup_insert //.
  by rewrite vlookup_insert_ne //.
Qed.

Lemma empty_rx_global_preserve_rx1 σ i :
  get_rx_agree (empty_rx_global σ i) = (get_rx_agree σ).
Proof.
  rewrite /empty_rx_global.
  rewrite (surjective_pairing (get_vm_mail_box σ i)).
  rewrite (surjective_pairing (get_vm_mail_box σ i).2).
  rewrite /get_rx_agree /get_txrx_auth_agree.
  f_equal.
  simplify_list_eq.
  apply (list_eq_same_length _ _ vm_count).
  rewrite fmap_length.
  apply length_list_of_vmids.
  rewrite fmap_length.
  apply length_list_of_vmids.
  intros.
  apply list_lookup_fmap_inv in H0, H1.
  destruct H0, H1.
  destruct H0, H1.
  rewrite H3 in H2.
  inversion H2;subst x1.
  clear H2.
  rewrite H0 H1.
  do 2 f_equal.
  rewrite /get_vm_mail_box /get_mail_boxes /=.
  destruct (decide (i = x0)).
  subst x0.
  by rewrite vlookup_insert //.
  by rewrite vlookup_insert_ne //.
Qed.

Lemma empty_rx_global_preserve_pt σ i i':
  get_vm_page_table (empty_rx_global σ i) i' = get_vm_page_table σ i'.
Proof.
  rewrite /empty_rx_global.
  rewrite (surjective_pairing (get_vm_mail_box σ i)).
  by rewrite (surjective_pairing (get_vm_mail_box σ i).2).
Qed.

Lemma empty_rx_global_preserve_owned σ i :
  get_owned_gmap (empty_rx_global σ i) = (get_owned_gmap σ).
Proof.
  rewrite /empty_rx_global.
  rewrite (surjective_pairing (get_vm_mail_box σ i)).
  by rewrite (surjective_pairing (get_vm_mail_box σ i).2).
Qed.

Lemma empty_rx_global_preserve_access σ i :
  get_access_gmap (empty_rx_global σ i) = (get_access_gmap σ).
Proof.
  rewrite /empty_rx_global.
  rewrite (surjective_pairing (get_vm_mail_box σ i)).
  by rewrite (surjective_pairing (get_vm_mail_box σ i).2).
Qed.

Lemma empty_rx_global_preserve_excl σ i :
  get_excl_gmap (empty_rx_global σ i) = (get_excl_gmap σ).
Proof.
  rewrite /empty_rx_global.
  rewrite (surjective_pairing (get_vm_mail_box σ i)).
  by rewrite (surjective_pairing (get_vm_mail_box σ i).2).
Qed.

Lemma empty_rx_global_preserve_trans σ i :
  get_trans_gmap (empty_rx_global σ i) = (get_trans_gmap σ).
Proof.
  rewrite /empty_rx_global.
  rewrite (surjective_pairing (get_vm_mail_box σ i)).
  by rewrite (surjective_pairing (get_vm_mail_box σ i).2).
Qed.

Lemma empty_rx_global_preserve_trans' σ i :
  get_transactions (empty_rx_global σ i) = (get_transactions σ).
Proof.
  rewrite /empty_rx_global.
  rewrite (surjective_pairing (get_vm_mail_box σ i)).
  by rewrite (surjective_pairing (get_vm_mail_box σ i).2).
Qed.

Lemma empty_rx_global_preserve_hpool σ i :
  get_hpool_gset (empty_rx_global σ i) = (get_hpool_gset σ).
Proof.
  rewrite /empty_rx_global.
  rewrite (surjective_pairing (get_vm_mail_box σ i)).
  by rewrite (surjective_pairing (get_vm_mail_box σ i).2).
Qed.

Lemma empty_rx_global_preserve_retri σ i :
  get_retri_gmap (empty_rx_global σ i) = (get_retri_gmap σ).
Proof.
  rewrite /empty_rx_global.
  rewrite (surjective_pairing (get_vm_mail_box σ i)).
  by rewrite (surjective_pairing (get_vm_mail_box σ i).2).
Qed.

Ltac rewrite_empty_rx_global :=
  match goal with
  | |- _ =>
    try rewrite -> empty_rx_global_preserve_current_vm;
    try rewrite -> empty_rx_global_preserve_regs;
    try rewrite -> empty_rx_global_preserve_mem;
    try rewrite -> empty_rx_global_preserve_tx;
    try rewrite  -> empty_rx_global_preserve_rx1;
    try rewrite -> empty_rx_global_preserve_owned;
    try rewrite -> empty_rx_global_preserve_access;
    try rewrite -> empty_rx_global_preserve_excl;
    try rewrite -> empty_rx_global_preserve_trans;
    try rewrite -> empty_rx_global_preserve_trans';
    try rewrite -> empty_rx_global_preserve_hpool;
    try rewrite -> empty_rx_global_preserve_retri
  end.

(* TODO simplify *)
Lemma empty_rx_global_update_mailbox σ l :
  get_rx_gmap (empty_rx_global σ l) = <[l := None]>(get_rx_gmap σ).
Proof.
  rewrite /get_rx_gmap.
  apply map_eq.
  intros i.
  destruct (list_to_map
              (map
                 (λ v0 : VMID,
                         match (get_vm_mail_box (empty_rx_global σ l) v0).2.2 with
                         | Some (l0, j) => (v0, Some (l0, j))
                         | None => (v0, None)
                         end
                 )
                 list_of_vmids) !! i) eqn:Heqn.
  - apply elem_of_list_to_map_2 in Heqn.
    apply elem_of_list_In in Heqn.
    apply in_map_iff in Heqn.
    destruct Heqn as [y [Heqn1 Heqn2]].
    apply elem_of_list_In in Heqn2.
    rewrite /empty_rx_global //= in Heqn1.
    rewrite (surjective_pairing (get_vm_mail_box σ l)) in Heqn1.
    rewrite (surjective_pairing (get_vm_mail_box σ l).2) in Heqn1.
    rewrite /get_vm_mail_box /get_mail_boxes in Heqn1.
    simpl in Heqn1.
    destruct (decide (l = y)).
    + subst.
      rewrite vlookup_insert in Heqn1.
      simpl in Heqn1.
      inversion Heqn1; subst; clear Heqn1.
      rewrite lookup_insert.
      reflexivity.
    + symmetry.
      rewrite lookup_insert_Some.
      rewrite /get_vm_mail_box /get_mail_boxes //= in Heqn1.
      rewrite vlookup_insert_ne in Heqn1; auto.
      destruct (σ.1.1.1.1.2 !!! y) as [a b] eqn:Heqn3.
      destruct b as [c d] eqn:Heqn4.
      simpl in Heqn1.
      destruct d as [e|] eqn:Heqn5.
      * destruct e as [f g] eqn:Heqn6.
        inversion Heqn1; subst; clear Heqn1.
        rewrite /get_vm_mail_box /get_mail_boxes.
        right.
        split; auto.
        apply elem_of_list_to_map_1'.
        -- intros y H.
           apply elem_of_list_In in H.
           apply in_map_iff in H.
           destruct H as [x [H1 H2]].
           destruct (decide (x = i)).
           ++ subst.
              rewrite Heqn3 //= in H1.
              inversion H1; subst; reflexivity.
           ++ destruct (σ.1.1.1.1.2 !!! x) as [a' b'] eqn:Heqn3'.
              destruct b' as [c' d'] eqn:Heqn4'.
              simpl in H1.
              destruct d' as [e'|] eqn:Heqn5'.
              ** destruct e' as [f' g'] eqn:Heqn6'.
                 simplify_eq.
              ** simplify_eq.
        -- apply elem_of_list_In.
           apply in_map_iff.
           exists i.
           rewrite Heqn3 //=.
           apply elem_of_list_In in Heqn2.
           split; auto.
      * simplify_eq.
        rewrite /get_vm_mail_box /get_mail_boxes //=.
        right.
        split; auto.
        apply elem_of_list_to_map_1'.
        -- intros y H.
           apply elem_of_list_In in H.
           apply in_map_iff in H.
           destruct H as [x [H1 H2]].
           destruct (decide (x = i)).
           ++ subst.
              rewrite Heqn3 //= in H1.
              inversion H1; subst; reflexivity.
           ++ destruct (σ.1.1.1.1.2 !!! x) as [a' b'] eqn:Heqn3'.
              destruct b' as [c' d'] eqn:Heqn4'.
              simpl in H1.
              destruct d' as [e'|] eqn:Heqn5'.
              ** destruct e' as [f' g'] eqn:Heqn6'.
                 simplify_eq.
              ** simplify_eq.
        -- apply elem_of_list_In.
           apply in_map_iff.
           exists i.
           rewrite Heqn3 //=.
           apply elem_of_list_In in Heqn2.
           split; auto.
  - symmetry.
    rewrite <-not_elem_of_list_to_map in Heqn.
    rewrite /empty_rx_global //= in Heqn.
    rewrite (surjective_pairing (get_vm_mail_box σ l)) in Heqn.
    rewrite (surjective_pairing (get_vm_mail_box σ l).2) in Heqn.
    rewrite /get_vm_mail_box /get_mail_boxes in Heqn.
    simpl in Heqn.
    destruct (decide (l = i)).
    + subst.
      exfalso.
      apply Heqn.
      rewrite <-list_fmap_compose.
      rewrite /compose.
      rewrite /get_vm_mail_box /fill_rx_unsafe /get_mail_boxes //=.
      apply elem_of_list_In.
      apply in_map_iff.
      exists i.
      split; auto using in_list_of_vmids.
      rewrite vlookup_insert //=.
    + rewrite /get_vm_mail_box /fill_rx_unsafe /get_mail_boxes //=.
      rewrite lookup_insert_None.
      split; auto.
      rewrite <-not_elem_of_list_to_map.
      rewrite /get_vm_mail_box /fill_rx_unsafe /get_mail_boxes //= in Heqn.
      intros H.
      apply Heqn.
      apply elem_of_list_In.
      apply in_map_iff.
      apply elem_of_list_In in H.
      apply in_map_iff in H.
      destruct H as [x [H1 H2]]; subst.
      apply in_map_iff in H2.
      destruct H2 as [x' [H1 H2]].
      destruct (σ.1.1.1.1.2 !!! x') as [a b] eqn:Heqn3.
      destruct b as [c d] eqn:Heqn4.
      simpl in H1.
      destruct d as [e|] eqn:Heqn5.
      * destruct e as [f g] eqn:Heqn6.
        exists (x.1, Some (f, g)).
        split; auto.
        apply in_map_iff.
        exists x.1.
        rewrite vlookup_insert_ne //=; auto.
        split; auto using in_list_of_vmids.
        simplify_eq.
        rewrite // Heqn3 //=.
      * simplify_eq.
        exists (x', None).
        split; auto.
        apply in_map_iff.
        exists x'.
        simpl in n.
        rewrite vlookup_insert_ne //=; auto.
        split; auto using in_list_of_vmids.
        rewrite Heqn3 //=.
Qed.
