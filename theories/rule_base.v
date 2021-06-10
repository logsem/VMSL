From iris.algebra Require Import gmap gset.
From HypVeri Require Import RAs.

  Lemma get_reg_gmap_lookup_Some σ i r w : (get_reg_gmap σ) !! (r,i)= Some w <->  get_vm_reg_file σ i !! r = Some w.
    Proof.
      split.
      - unfold get_reg_gmap.
        intro HSome.
        apply elem_of_list_to_map_2 in HSome.
        apply elem_of_list_In in HSome.
        apply in_flat_map in HSome.
        destruct HSome  as [i'] .
        destruct H as [HiIn].
        apply in_map_iff in H.
        destruct H as [p].
        destruct H as [Heqn].
        inversion Heqn ;subst;clear Heqn.
        apply elem_of_list_In in H.
        by apply elem_of_map_to_list' in H.
      - intro HSome.
        apply  elem_of_list_to_map_1'.
        + intros.
          apply elem_of_list_In in H.
          apply in_flat_map in H.
          destruct H as [i'].
          destruct H as [Hi'In H].
          apply in_map_iff in H.
          destruct H as [p].
          destruct H as [Heqn H].
          apply elem_of_list_In in H.
          apply elem_of_map_to_list' in H.
          inversion Heqn;subst;clear Heqn.
          rewrite H in HSome.
          by inversion HSome.
        + apply elem_of_list_In.
          apply in_flat_map.
          exists i.
          split;[apply in_list_of_vmids|].
          apply in_map_iff.
          exists (r,w).
          split;[done|].
          apply elem_of_list_In.
          apply elem_of_map_to_list'.
          done.
    Qed.

  Lemma get_reg_gmap_lookup_None σ i r : (get_reg_gmap σ) !! (r,i)= None <->  get_vm_reg_file σ i !! r = None.
    Proof.
      split.
      - destruct (get_vm_reg_file σ i !! r) eqn:Heqn;[|done].
        intro HNone.
        apply not_elem_of_list_to_map_2 in HNone.
        exfalso.
        apply HNone.
        apply elem_of_list_In.
        apply in_map_iff.
        exists (r,i,w).
        split;[done|].
        apply in_flat_map.
        exists i.
        split;[apply in_list_of_vmids|].
        apply in_map_iff.
        exists (r,w).
        split;[done|].
        apply elem_of_list_In.
        apply elem_of_map_to_list'.
        by simplify_eq /=.
      - intro HNone.
        apply  not_elem_of_list_to_map_1.
        intro.
        apply elem_of_list_In in H.
          apply in_map_iff in H.
          destruct H as [p].
          destruct H as [Heqn H].
          apply elem_of_list_In in H.
          apply elem_of_list_In in H.
          apply in_flat_map in H.
          inversion Heqn;subst;clear Heqn.
          destruct H as [i'].
          destruct H as [HIn H].
           apply in_map_iff in H.
          destruct H as [p2].
          destruct H as [Heqn H].
          apply elem_of_list_In in H.
          apply elem_of_map_to_list' in H.
          inversion Heqn;subst;clear H0.
          inversion H1;subst;clear H1.
          rewrite H in HNone.
          by inversion HNone.
    Qed.


  Lemma get_reg_gmap_get_vm_reg_file σ (r:reg_name) (i:vmid) :
   (get_reg_gmap σ) !! (r,i) = (get_vm_reg_file σ i) !! r.
    Proof.
      destruct (get_reg_gmap σ !! (r, i)) eqn:Heqn.
      apply get_reg_gmap_lookup_Some in Heqn;done.
      apply get_reg_gmap_lookup_None in Heqn;done.
    Qed.


  Lemma get_reg_gmap_get_reg_Some σ (r:reg_name) (w:word) (i:vmid) : i= (get_current_vm σ)->
                                                                   (get_reg_gmap σ) !! (r,i) = Some w <->
                                                                   ((get_reg σ r) = Some w).
  Proof.
    intros.
    rewrite get_reg_gmap_get_vm_reg_file.
    unfold get_reg,get_reg_global;subst;done.
  Qed.


  Lemma update_reg_global_update_reg σ i r w : is_Some((get_reg_gmap σ) !! (r,i)) -> get_reg_gmap (update_reg_global σ i r w) =
                                             <[(r,i) := w]>(get_reg_gmap σ).
  Proof.
    intros.
    rewrite  /update_reg_global.
    apply map_eq.
    intro j.
    destruct( decide (j=(r,i)) ).
    - subst j.

      rewrite lookup_insert.
      rewrite get_reg_gmap_get_vm_reg_file.
      rewrite /get_vm_reg_file /get_reg_files.
        simpl.
        rewrite -> (vlookup_insert i _  _).
        by rewrite lookup_insert.
    - destruct ((get_reg_gmap σ) !! j) eqn:Heqn;
        rewrite lookup_insert_ne;[|done | |done];
        rewrite -> Heqn;
        destruct j as [r' i'];
        rewrite ->get_reg_gmap_get_vm_reg_file in Heqn;
        rewrite ->get_reg_gmap_get_vm_reg_file;
        destruct (decide (i=i'));
        destruct (decide (r=r'));
        subst;
        try contradiction;
        rewrite - Heqn;
        rewrite /get_vm_reg_file /get_reg_files;simpl.
       + rewrite -> (vlookup_insert i' _ _).
         by rewrite lookup_insert_ne ;[|done].
       + by rewrite vlookup_insert_ne.
       + by rewrite vlookup_insert_ne.
       + rewrite -> (vlookup_insert i' _ _).
         by rewrite lookup_insert_ne ;[|done].
       + by rewrite vlookup_insert_ne ;[|done].
       + by rewrite vlookup_insert_ne ;[|done].
  Qed.

  Lemma update_offset_PC_update_PC1 σ i (w:word) (o:nat):
   i=get_current_vm σ -> ((get_reg_gmap σ) !! (PC,i) = Some w)
   ->get_reg_gmap (update_offset_PC σ true o) = <[(PC,i) := (w +w o)]>(get_reg_gmap σ).
  Proof.
    intros.
    rewrite /update_offset_PC.
    remember H0.
    clear Heqe.
    rewrite /get_reg_gmap /update_reg_global in H0.
    apply elem_of_list_to_map_2 in H0.
    apply elem_of_list_In in H0.
    apply in_flat_map in H0.
    destruct H0.
    destruct H0.
    apply in_map_iff in H1.
    destruct H1.
    destruct H1.
    inversion H1;subst;clear H1.
    apply elem_of_list_In in H2.
    apply elem_of_map_to_list' in H2.
    rewrite H2.
    rewrite /update_reg.
    apply update_reg_global_update_reg.
    exists x0.2.
    by rewrite H4.
  Qed.

   Lemma update_reg_global_preserve_tx σ i r w : get_tx_agree (update_reg_global σ i r w) =
                                               (get_tx_agree σ).
  Proof.
    rewrite /get_tx_agree /get_txrx_auth_agree.
    f_equal.
  Qed.

  Lemma update_offset_PC_preserve_tx σ d o : get_tx_agree (update_offset_PC σ d o) = get_tx_agree σ.
  Proof.
    unfold update_offset_PC.
    destruct (get_vm_reg_file σ (get_current_vm σ) !! PC).
    destruct d; rewrite /update_reg update_reg_global_preserve_tx;done.
    done.
  Qed.

 Lemma update_reg_global_preserve_rx1 σ i r w : get_rx_agree (update_reg_global σ i r w) =
                                               (get_rx_agree σ).
  Proof.
    rewrite /get_rx_agree /get_txrx_auth_agree.
    f_equal.
  Qed.

  Lemma update_offset_PC_preserve_rx1 σ d o : get_rx_agree (update_offset_PC σ d o) = get_rx_agree σ.
  Proof.
    unfold update_offset_PC.
    destruct (get_vm_reg_file σ (get_current_vm σ) !! PC).
    destruct d; rewrite /update_reg update_reg_global_preserve_rx1;done.
    done.
  Qed.


   Lemma update_reg_global_preserve_rx2 σ i r w : get_rx_gmap (update_reg_global σ i r w) =
                                               (get_rx_gmap σ).
  Proof.
    rewrite /get_rx_gmap /get_txrx_auth_agree.
    f_equal.
  Qed.

  Lemma update_offset_PC_preserve_rx2 σ d o : get_rx_gmap (update_offset_PC σ d o) = get_rx_gmap σ.
  Proof.
    unfold update_offset_PC.
    destruct (get_vm_reg_file σ (get_current_vm σ) !! PC).
    destruct d; rewrite /update_reg update_reg_global_preserve_rx2;done.
    done.
  Qed.


  (* TODO: the proofs above are identical *)

  Lemma update_reg_global_preserve_rx σ i r w : (get_rx_agree (update_reg_global σ i r w), get_rx_gmap (update_reg_global σ i r w)) =
                                               (get_rx_agree σ, get_rx_gmap σ).
  Proof.
    by rewrite update_reg_global_preserve_rx1 update_reg_global_preserve_rx2.
  Qed.

  Lemma update_offset_PC_preserve_rx  σ d o : (get_rx_agree (update_offset_PC σ d o), get_rx_gmap (update_offset_PC σ d o) ) =
                                               (get_rx_agree σ, get_rx_gmap σ).
  Proof.
    by rewrite update_offset_PC_preserve_rx1 update_offset_PC_preserve_rx2 .
  Qed.


  Lemma update_reg_global_preserve_owned σ i r w : get_owned_gmap (update_reg_global σ i r w) =
                                               (get_owned_gmap σ).
  Proof.
    rewrite /get_owned_gmap.
    f_equal.
    Qed.

  Lemma update_offset_PC_preserve_owned σ d o : get_owned_gmap (update_offset_PC σ d o) = get_owned_gmap σ.
  Proof.
    unfold update_offset_PC.
    destruct (get_vm_reg_file σ (get_current_vm σ) !! PC).
    destruct d; rewrite /update_reg update_reg_global_preserve_owned;done.
    done.
  Qed.

  Lemma update_reg_global_preserve_access σ i r w : get_access_gmap (update_reg_global σ i r w) =
                                               (get_access_gmap σ).
  Proof.
    rewrite /get_access_gmap.
    f_equal.
    Qed.

  Lemma update_offset_PC_preserve_access σ d o : get_access_gmap (update_offset_PC σ d o) = get_access_gmap σ.
  Proof.
    unfold update_offset_PC.
    destruct (get_vm_reg_file σ (get_current_vm σ) !! PC).
    destruct d; rewrite /update_reg update_reg_global_preserve_access;done.
    done.
  Qed.

  Lemma update_reg_global_preserve_trans σ i r w : get_trans_gmap (update_reg_global σ i r w) =
                                               (get_trans_gmap σ).
  Proof.
    rewrite /get_trans_gmap.
    f_equal.
  Qed.

  Lemma update_offset_PC_preserve_trans σ d o : get_trans_gmap (update_offset_PC σ d o) = get_trans_gmap σ.
  Proof.
    unfold update_offset_PC.
    destruct (get_vm_reg_file σ (get_current_vm σ) !! PC).
    destruct d; rewrite /update_reg update_reg_global_preserve_trans;done.
    done.
  Qed.

  Lemma update_reg_global_preserve_receivers σ i r w : get_receivers_gmap (update_reg_global σ i r w) =
                                               (get_receivers_gmap σ).
  Proof.
    rewrite /get_receivers_gmap.
    f_equal.
  Qed.

  Lemma update_offset_PC_preserve_receivers σ d o : get_receivers_gmap (update_offset_PC σ d o) = get_receivers_gmap σ.
  Proof.
    unfold update_offset_PC.
    destruct (get_vm_reg_file σ (get_current_vm σ) !! PC).
    destruct d; rewrite /update_reg update_reg_global_preserve_receivers;done.
    done.
  Qed.
