From HypVeri Require Import machine machine_extra.
From HypVeri.algebra Require Import base.

(* lemmas about update_mem_unsafe *)
Lemma update_memory_unsafe_preserve_current_vm σ a w :
  (get_current_vm (update_memory_unsafe σ a w)) = (get_current_vm σ).
Proof. f_equal. Qed.

Lemma update_memory_unsafe_preserve_reg σ a w:
  get_reg_gmap (update_memory_unsafe σ a w) = get_reg_gmap σ.
Proof. f_equal. Qed.

Lemma update_memory_unsafe_preserve_tx σ a w :
  get_tx_agree (update_memory_unsafe σ a w) = get_tx_agree σ.
Proof. f_equal. Qed.

Lemma update_memory_unsafe_preserve_rx1 σ a w :
  get_rx_agree (update_memory_unsafe σ a w) = (get_rx_agree σ).
Proof. f_equal. Qed.

Lemma update_memory_unsafe_preserve_rx2 σ a w :
  get_rx_gmap (update_memory_unsafe σ a w) = (get_rx_gmap σ).
Proof. f_equal. Qed.

Lemma update_memory_unsafe_preserve_owned σ a w :
  get_owned_gmap (update_memory_unsafe σ a w) = (get_owned_gmap σ).
Proof. f_equal. Qed.

Lemma update_memory_unsafe_preserve_access σ a w :
  get_access_gmap (update_memory_unsafe σ a w) = (get_access_gmap σ).
Proof. f_equal. Qed.

Lemma update_memory_unsafe_preserve_excl σ a w :
  get_excl_gmap (update_memory_unsafe σ a w) = (get_excl_gmap σ).
Proof. f_equal. Qed.

Lemma update_memory_unsafe_preserve_trans σ a w :
  get_trans_gmap (update_memory_unsafe σ a w) = (get_trans_gmap σ).
Proof. f_equal. Qed.

Lemma update_memory_unsafe_preserve_trans' σ a w :
  get_transactions (update_memory_unsafe σ a w) = (get_transactions σ).
Proof. f_equal. Qed.

Lemma update_memory_unsafe_preserve_hpool σ a w :
  get_hpool_gset (update_memory_unsafe σ a w) = (get_hpool_gset σ).
Proof. f_equal. Qed.

Lemma update_memory_unsafe_preserve_retri σ a w :
  get_retri_gmap (update_memory_unsafe σ a w) = (get_retri_gmap σ).
Proof. f_equal. Qed.

Ltac rewrite_mem_unsafe :=
  match goal with
  | |- _ =>
    try rewrite -> update_memory_unsafe_preserve_current_vm;
    try rewrite -> update_memory_unsafe_preserve_reg;
    try rewrite -> update_memory_unsafe_preserve_tx;
    try rewrite -> update_memory_unsafe_preserve_rx1;
    try rewrite -> update_memory_unsafe_preserve_rx2;
    try rewrite -> update_memory_unsafe_preserve_owned;
    try rewrite -> update_memory_unsafe_preserve_access;
    try rewrite -> update_memory_unsafe_preserve_excl;
    try rewrite -> update_memory_unsafe_preserve_trans;
    try rewrite -> update_memory_unsafe_preserve_trans';
    try rewrite -> update_memory_unsafe_preserve_hpool;
    try rewrite -> update_memory_unsafe_preserve_retri
  end.

Lemma update_memory_unsafe_update_mem σ a w :
  is_Some((get_mem σ) !! a) ->
  get_mem (update_memory_unsafe σ a w) = <[a := w]>(get_mem σ).
Proof. intros. rewrite  /update_memory_unsafe //. Qed.

(* lemmas about zero_pages *)
Lemma zero_pages_preserve_current_vm σ ps:
  (get_current_vm (zero_pages σ ps)) = (get_current_vm σ).
Proof.
  rewrite /get_current_vm /zero_pages.
  cbn.
  generalize σ.
  induction ps.
  done.
  intro.
  cbn.
  induction (finz.seq a (Z.to_nat page_size)).
  cbn.
  apply IHps.
  cbn.
  rewrite /get_current_vm.
  apply IHl.
Qed.

Lemma zero_pages_preserve_reg σ ps:
  (get_reg_gmap (zero_pages σ ps)) = (get_reg_gmap σ).
Proof.
  rewrite /zero_pages.
  cbn.
  generalize σ.
  induction ps.
  done.
  intro.
  cbn.
  induction (finz.seq a (Z.to_nat page_size)).
  cbn.
  apply IHps.
  cbn.
  apply IHl.
Qed.

Lemma zero_pages_preserve_tx σ ps:
  (get_tx_agree (zero_pages σ ps)) = (get_tx_agree σ).
Proof.
  rewrite /zero_pages.
  cbn.
  generalize σ.
  induction ps.
  done.
  intro.
  cbn.
  induction (finz.seq a (Z.to_nat page_size)).
  cbn.
  apply IHps.
  cbn.
  apply IHl.
Qed.

Lemma zero_pages_preserve_rx1 σ ps:
  (get_rx_agree (zero_pages σ ps)) = (get_rx_agree σ).
Proof.
  rewrite /zero_pages.
  cbn.
  generalize σ.
  induction ps.
  done.
  intro.
  cbn.
  induction (finz.seq a (Z.to_nat page_size)).
  cbn.
  apply IHps.
  cbn.
  apply IHl.
Qed.

Lemma zero_pages_preserve_rx2 σ ps:
  (get_rx_gmap (zero_pages σ ps)) = (get_rx_gmap σ).
Proof.
  rewrite /zero_pages.
  cbn.
  generalize σ.
  induction ps.
  done.
  intro.
  cbn.
  induction (finz.seq a (Z.to_nat page_size)).
  cbn.
  apply IHps.
  cbn.
  apply IHl.
Qed.

Lemma zero_pages_preserve_owned σ ps :
  get_owned_gmap (zero_pages σ ps) = (get_owned_gmap σ).
Proof.
  rewrite /zero_pages.
  cbn.
  generalize σ.
  induction ps.
  done.
  intro.
  cbn.
  induction (finz.seq a (Z.to_nat page_size)).
  cbn.
  apply IHps.
  cbn.
  apply IHl.
Qed.

Lemma zero_pages_preserve_access σ ps :
  get_access_gmap (zero_pages σ ps) = (get_access_gmap σ).
Proof.
  rewrite /zero_pages.
  cbn.
  generalize σ.
  induction ps.
  done.
  intro.
  cbn.
  induction (finz.seq a (Z.to_nat page_size)).
  cbn.
  apply IHps.
  cbn.
  apply IHl.
Qed.

Lemma zero_pages_preserve_excl σ ps :
  get_excl_gmap (zero_pages σ ps) = (get_excl_gmap σ).
Proof.
  rewrite /zero_pages.
  cbn.
  generalize σ.
  induction ps.
  done.
  intro.
  cbn.
  induction (finz.seq a (Z.to_nat page_size)).
  cbn.
  apply IHps.
  cbn.
  apply IHl.
Qed.

Lemma zero_pages_preserve_trans σ ps :
  get_trans_gmap (zero_pages σ ps) = (get_trans_gmap σ).
Proof.
  rewrite /zero_pages.
  cbn.
  generalize σ.
  induction ps.
  done.
  intro.
  cbn.
  induction (finz.seq a (Z.to_nat page_size)).
  cbn.
  apply IHps.
  cbn.
  apply IHl.
Qed.

Lemma zero_pages_preserve_trans' σ ps :
  get_transactions (zero_pages σ ps) = (get_transactions σ).
Proof.
  rewrite /zero_pages.
  cbn.
  generalize σ.
  induction ps.
  done.
  intro.
  cbn.
  induction (finz.seq a (Z.to_nat page_size)).
  cbn.
  apply IHps.
  cbn.
  apply IHl.
Qed.

Lemma zero_pages_preserve_hpool σ ps :
  get_hpool_gset (zero_pages σ ps) = (get_hpool_gset σ).
Proof.
  rewrite /zero_pages.
  cbn.
  generalize σ.
  induction ps.
  done.
  intro.
  cbn.
  induction (finz.seq a (Z.to_nat page_size)).
  cbn.
  apply IHps.
  cbn.
  apply IHl.
Qed.

Lemma zero_pages_preserve_retri σ ps :
  get_retri_gmap (zero_pages σ ps) = (get_retri_gmap σ).
Proof.
  rewrite /zero_pages.
  cbn.
  generalize σ.
  induction ps.
  done.
  intro.
  cbn.
  induction (finz.seq a (Z.to_nat page_size)).
  cbn.
  apply IHps.
  cbn.
  apply IHl.
Qed.

Lemma zero_pages_update_mem σ ps:
  (list_to_map (zip (list_pid_to_addr ps) (flat_list_list_word (pages_of_W0 (length ps))))
               ∪ get_mem σ) =  get_mem (zero_pages σ ps).
Proof.
  f_equal.
Qed.

Ltac rewrite_mem_zero :=
  match goal with
  | |- _ =>
    try rewrite -> zero_pages_preserve_current_vm;
    try rewrite -> zero_pages_preserve_reg;
    try rewrite -> zero_pages_preserve_tx;
    try rewrite -> zero_pages_preserve_rx1;
    try rewrite -> zero_pages_preserve_rx2;
    try rewrite -> zero_pages_preserve_owned;
    try rewrite -> zero_pages_preserve_access;
    try rewrite -> zero_pages_preserve_excl;
    try rewrite -> zero_pages_preserve_trans;
    try rewrite -> zero_pages_preserve_trans';
    try rewrite -> zero_pages_preserve_hpool;
    try rewrite -> zero_pages_preserve_retri
  end.

Lemma copy_page_segment_unsafe_preserve_current_vm σ src dst l:
  get_current_vm (copy_page_segment_unsafe σ src dst l) = get_current_vm σ.
Proof. f_equal. Qed.

Lemma copy_page_segment_unsafe_preserve_regs σ src dst l:
  get_reg_gmap (copy_page_segment_unsafe σ src dst l) = get_reg_gmap σ.
Proof. f_equal. Qed.

Lemma copy_page_segment_unsafe_preserve_tx σ src dst l:
  get_tx_agree (copy_page_segment_unsafe σ src dst l) = get_tx_agree σ.
Proof. f_equal. Qed.

Lemma copy_page_segment_unsafe_preserve_rx1 σ src dst l:
  get_rx_agree (copy_page_segment_unsafe σ src dst l) = get_rx_agree σ.
Proof. f_equal. Qed.

Lemma copy_page_segment_unsafe_preserve_rx2 σ src dst l:
  get_rx_gmap (copy_page_segment_unsafe σ src dst l) = get_rx_gmap σ.
Proof. f_equal. Qed.

Lemma copy_page_segment_unsafe_preserve_rx σ src dst l:
  (get_rx_agree (copy_page_segment_unsafe σ src dst l),
   get_rx_gmap (copy_page_segment_unsafe σ src dst l)) =
  (get_rx_agree σ, get_rx_gmap σ).
Proof. by rewrite copy_page_segment_unsafe_preserve_rx1
                  copy_page_segment_unsafe_preserve_rx2 . Qed.

Lemma copy_page_segment_unsafe_preserve_owned σ src dst l:
  get_owned_gmap (copy_page_segment_unsafe σ src dst l) = get_owned_gmap σ.
Proof. f_equal. Qed.

Lemma copy_page_segment_unsafe_preserve_access σ src dst l:
  get_access_gmap (copy_page_segment_unsafe σ src dst l) = get_access_gmap σ.
Proof. f_equal. Qed.

Lemma copy_page_segment_unsafe_preserve_excl σ src dst l:
  get_excl_gmap (copy_page_segment_unsafe σ src dst l) = get_excl_gmap σ.
Proof. f_equal. Qed.

Lemma copy_page_segment_unsafe_preserve_trans σ src dst l:
  (get_trans_gmap (copy_page_segment_unsafe σ src dst l))
  = get_trans_gmap σ.
Proof. f_equal. Qed.

Lemma copy_page_segment_unsafe_preserve_hpool σ src dst l:
  get_hpool_gset (copy_page_segment_unsafe σ src dst l) = get_hpool_gset σ.
Proof. f_equal. Qed.

Lemma copy_page_segment_unsafe_preserve_receivers σ src dst l:
  get_retri_gmap (copy_page_segment_unsafe σ src dst l) = get_retri_gmap σ.
Proof. f_equal. Qed.

Lemma write_mem_segment_unsafe_preserve_current_vm σ dst ws:
  get_current_vm (write_mem_segment_unsafe σ dst ws) = get_current_vm σ.
Proof. f_equal. Qed.

Lemma write_mem_segment_unsafe_preserve_regs σ dst ws:
  get_reg_gmap (write_mem_segment_unsafe σ dst ws) = get_reg_gmap σ.
Proof. f_equal. Qed.

Lemma write_mem_segment_unsafe_preserve_tx σ dst ws:
  get_tx_agree (write_mem_segment_unsafe σ dst ws) = get_tx_agree σ.
Proof. f_equal. Qed.

Lemma write_mem_segment_unsafe_preserve_rx1 σ dst ws:
  get_rx_agree (write_mem_segment_unsafe σ dst ws) = get_rx_agree σ.
Proof. f_equal. Qed.

Lemma write_mem_segment_unsafe_preserve_rx2 σ dst ws:
  get_rx_gmap (write_mem_segment_unsafe σ dst ws) = get_rx_gmap σ.
Proof. f_equal. Qed.

Lemma write_mem_segment_unsafe_preserve_rx σ dst ws:
  (get_rx_agree (write_mem_segment_unsafe σ dst ws),
   get_rx_gmap (write_mem_segment_unsafe σ dst ws)) =
  (get_rx_agree σ, get_rx_gmap σ).
Proof. by rewrite write_mem_segment_unsafe_preserve_rx1
                  write_mem_segment_unsafe_preserve_rx2 . Qed.

Lemma write_mem_segment_unsafe_preserve_owned σ dst ws:
  get_owned_gmap (write_mem_segment_unsafe σ dst ws) = get_owned_gmap σ.
Proof. f_equal. Qed.

Lemma write_mem_segment_unsafe_preserve_access σ dst ws:
  get_access_gmap (write_mem_segment_unsafe σ dst ws) = get_access_gmap σ.
Proof. f_equal. Qed.

Lemma write_mem_segment_unsafe_preserve_excl σ dst ws:
  get_excl_gmap (write_mem_segment_unsafe σ dst ws) = get_excl_gmap σ.
Proof. f_equal. Qed.

Lemma write_mem_segment_unsafe_preserve_trans σ dst ws:
  (get_trans_gmap (write_mem_segment_unsafe σ dst ws))
  = get_trans_gmap σ.
Proof. f_equal. Qed.

Lemma write_mem_segment_unsafe_preserve_hpool σ dst ws:
  get_hpool_gset (write_mem_segment_unsafe σ dst ws) = get_hpool_gset σ.
Proof. f_equal. Qed.

Lemma write_mem_segment_unsafe_preserve_receivers σ dst ws:
  get_retri_gmap (write_mem_segment_unsafe σ dst ws) = get_retri_gmap σ.
Proof. f_equal. Qed.



Lemma fill_rx_unsafe_preserve_current_vm σ l v r tx rx :
  get_current_vm (fill_rx_unsafe σ l v r tx rx) = get_current_vm σ.
Proof. f_equal. Qed.

Lemma fill_rx_unsafe_preserve_mem σ l v r tx rx :
  get_mem (fill_rx_unsafe σ l v r tx rx) = get_mem σ.
Proof. f_equal. Qed.

Lemma fill_rx_unsafe_preserve_regs σ l v r tx rx :
  get_reg_gmap (fill_rx_unsafe σ l v r tx rx) = get_reg_gmap σ.
Proof. f_equal. Qed.

Lemma fill_rx_unsafe_preserve_tx σ l v r tx rx :
  tx = get_tx_pid_global σ r ->
  get_tx_agree (fill_rx_unsafe σ l v r tx rx) = get_tx_agree σ.
Proof.
  intros H.
  rewrite /fill_rx_unsafe /get_tx_agree /get_txrx_auth_agree H
          /get_tx_pid_global /get_vm_mail_box /get_mail_boxes.
  simpl.
  f_equal.
  induction list_of_vmids as [|? ? IH].
  - reflexivity.
  - simpl.
    f_equal.
    + f_equal.
      f_equal.
      destruct (decide (a = r)) as [p|p].
      * rewrite p.
        rewrite vlookup_insert.
        reflexivity.
      * rewrite vlookup_insert_ne; auto.
    + rewrite IH.
      reflexivity.
Qed.

Lemma fill_rx_unsafe_preserve_rx1 σ l v r tx rx :
  rx = get_rx_pid_global σ r ->
  get_rx_agree (fill_rx_unsafe σ l v r tx rx) = get_rx_agree σ.
Proof.
  intros H.
  rewrite /fill_rx_unsafe /get_rx_agree /get_txrx_auth_agree H
          /get_rx_pid_global /get_vm_mail_box /get_mail_boxes.
  simpl.
  f_equal.
  induction list_of_vmids as [|? ? IH].
  - reflexivity.
  - simpl.
    f_equal.
    + f_equal.
      f_equal.
      destruct (decide (a = r)) as [p|p].
      * rewrite p.
        rewrite vlookup_insert.
        reflexivity.
      * rewrite vlookup_insert_ne; auto.
    + rewrite IH.
      reflexivity.
Qed.

Lemma fill_rx_unsafe_preserve_owned σ l v r tx rx :
  get_owned_gmap (fill_rx_unsafe σ l v r tx rx) = get_owned_gmap σ.
Proof. f_equal. Qed.

Lemma fill_rx_unsafe_preserve_access σ l v r tx rx :
  get_access_gmap (fill_rx_unsafe σ l v r tx rx) = get_access_gmap σ.
Proof. f_equal. Qed.

Lemma fill_rx_unsafe_preserve_excl σ l v r tx rx :
  get_excl_gmap (fill_rx_unsafe σ l v r tx rx) = get_excl_gmap σ.
Proof. f_equal. Qed.

Lemma fill_rx_unsafe_preserve_trans σ l v r tx rx :
  (get_trans_gmap (fill_rx_unsafe σ l v r tx rx))
  = get_trans_gmap σ.
Proof. f_equal. Qed.

Lemma fill_rx_unsafe_preserve_hpool σ l v r tx rx :
  get_hpool_gset (fill_rx_unsafe σ l v r tx rx) = get_hpool_gset σ.
Proof. f_equal. Qed.

Lemma fill_rx_unsafe_preserve_receivers σ l v r tx rx :
  get_retri_gmap (fill_rx_unsafe σ l v r tx rx) = get_retri_gmap σ.
Proof. f_equal. Qed.

Lemma fill_rx_unsafe_update_mailbox σ l v r tx rx :
  get_rx_gmap (fill_rx_unsafe σ l v r tx rx) = <[r := Some (l, v)]>(get_rx_gmap σ).
Proof.
  rewrite /get_rx_gmap.
  apply map_eq.
  intros i.
  destruct (list_to_map
              (map
                 (λ v0 : VMID,
                         match (get_vm_mail_box (fill_rx_unsafe σ l v r tx rx) v0).2.2 with
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
    rewrite /fill_rx_unsafe //= in Heqn1.
    destruct (decide (r = y)).
    + subst.
      rewrite /get_vm_mail_box /get_mail_boxes //= in Heqn1.
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
    destruct (decide (r = i)).
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
