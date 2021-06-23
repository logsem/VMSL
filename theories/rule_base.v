From iris.algebra Require Import gmap gset.
From HypVeri Require Import RAs.



  Lemma update_reg_global_preserve_current_vm σ r w :(get_current_vm (update_reg_global σ (get_current_vm σ) r w)) = (get_current_vm σ).
  Proof.
    unfold get_current_vm ,update_reg_global.
    simpl.
    unfold get_current_vm.
    reflexivity.
  Qed.

  Lemma update_offset_PC_preserve_current_vm σ d o :(get_current_vm (update_offset_PC σ d o )) = (get_current_vm σ).
  Proof.
    unfold get_current_vm ,update_offset_PC.
    unfold get_current_vm.
    destruct (get_vm_reg_file σ σ.1.1.2 !! PC),d;eauto.
  Qed.

  Lemma update_memory_unsafe_preserve_current_vm σ a w :(get_current_vm (update_memory_unsafe σ a w)) = (get_current_vm σ).
  Proof.
    unfold get_current_vm ,update_memory_unsafe.
    simpl.
    unfold get_current_vm.
    reflexivity.
  Qed.


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


  Lemma update_memory_unsafe_preserve_reg σ a w:
   get_reg_gmap (update_memory_unsafe σ a w) = get_reg_gmap σ.
  Proof.
    rewrite /get_reg_gmap /update_memory_unsafe //.
  Qed.

  Lemma update_reg_global_preserve_mem σ i r w : get_mem (update_reg_global σ i r w) = get_mem σ.
  Proof.
    unfold update_reg_global, get_mem.
    simpl.
    reflexivity.
  Qed.

  Lemma update_reg_preserve_mem σ r w : get_mem (update_reg σ r w) = get_mem σ.
  Proof.
    unfold update_reg.
    apply update_reg_global_preserve_mem.
  Qed.

  Lemma update_offset_PC_preserve_mem σ d o : get_mem (update_offset_PC σ d o) = get_mem σ.
  Proof.
    unfold update_offset_PC.
    destruct (get_vm_reg_file σ (get_current_vm σ) !! PC).
    destruct d; rewrite -> update_reg_preserve_mem;done.
    done.
  Qed.

  Lemma update_memory_unsafe_update_mem σ a w : is_Some((get_mem σ) !! a) -> get_mem (update_memory_unsafe σ a w) =
                                             <[a := w]>(get_mem σ).
  Proof.
    intros.
    rewrite  /update_memory_unsafe //.
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

  Lemma update_memory_unsafe_preserve_tx σ a w : get_tx_agree (update_memory_unsafe σ a w) = get_tx_agree σ.
  Proof.
    rewrite /get_tx_agree /get_txrx_auth_agree.
    f_equal.
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

 Lemma update_memory_unsafe_preserve_rx1 σ a w : get_rx_agree (update_memory_unsafe σ a w) =
                                               (get_rx_agree σ).
  Proof.
    rewrite /get_rx_agree /get_txrx_auth_agree.
    f_equal.
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

   Lemma update_memory_unsafe_preserve_rx2 σ a w : get_rx_gmap (update_memory_unsafe σ a w) =
                                               (get_rx_gmap σ).
  Proof.
    rewrite /get_rx_gmap /get_txrx_auth_agree.
    f_equal.
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


  Lemma update_memory_unsafe_preserve_rx  σ a w : (get_rx_agree (update_memory_unsafe σ a w), get_rx_gmap (update_memory_unsafe σ a w) ) =
                                               (get_rx_agree σ, get_rx_gmap σ).
  Proof.
    by rewrite update_memory_unsafe_preserve_rx1 update_memory_unsafe_preserve_rx2 .
  Qed.

  Lemma update_reg_global_preserve_pt σ i i' r w:
   get_vm_page_table (update_reg_global σ i r w) i' = get_vm_page_table σ i'.
  Proof.
    rewrite /update_reg_global /get_vm_page_table /get_page_tables.
    done.
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

  Lemma update_memory_unsafe_preserve_owned σ a w : get_owned_gmap (update_memory_unsafe σ a w) =
                                               (get_owned_gmap σ).
  Proof.
    rewrite /get_owned_gmap.
    f_equal.
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

  Lemma update_offset_PC_preserve_check_access σ d o a:
  check_access_addr (update_offset_PC σ d o) (get_current_vm σ) a = check_access_addr  σ (get_current_vm σ) a.
  Proof.
    rewrite /update_offset_PC /check_access_addr /check_access_page.
    simpl.
    destruct (get_vm_reg_file σ (get_current_vm σ) !! PC);eauto.
    destruct d;
    by rewrite /update_reg  update_reg_global_preserve_pt.
  Qed.

  Lemma update_memory_unsafe_preserve_access σ a w : get_access_gmap (update_memory_unsafe σ a w) =
                                               (get_access_gmap σ).
  Proof.
    rewrite /get_access_gmap.
    f_equal.
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

  Lemma update_memory_unsafe_preserve_trans σ a w : get_trans_gmap (update_memory_unsafe σ a w) =
                                               (get_trans_gmap σ).
  Proof.
    rewrite /get_trans_gmap.
    f_equal.
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

 Lemma update_memory_unsafe_preserve_receivers σ a w : get_receivers_gmap (update_memory_unsafe σ a w) =
                                               (get_receivers_gmap σ).
  Proof.
    rewrite /get_receivers_gmap.
    f_equal.
  Qed.

  Lemma reducible_normal{σ} i instr ai wi :
   (get_current_vm σ) = i ->
   check_access_addr σ i ai = true ->
   get_reg σ PC = Some ai ->
   get_mem σ !! ai = Some wi ->
   decode_instruction wi = Some (instr) ->
   ∃ m' σ', step ExecI σ m' σ'.
  Proof.
    intros.
    remember (exec instr σ) as ex.
    exists ex.1 ,ex.2 .
    apply step_exec_normal with ai wi instr;subst i ;eauto.
    + by rewrite /is_valid_PC H1 /= H0.
    + by rewrite /get_memory H0.
   Qed.

  Lemma step_ExecI_normal {σ m' σ' } i instr ai wi  :
   step ExecI σ m' σ'->
   (get_current_vm σ) = i ->
   check_access_addr σ i ai = true ->
   get_reg σ PC = Some ai ->
   get_mem σ !! ai = Some wi ->
   decode_instruction wi = Some (instr) ->
   (exec instr σ).1 = m' ∧ (exec instr σ).2 = σ'.
  Proof.
    intros HstepP Heqi Hacc HPC Hmem Hdecode.
  inversion HstepP as
        [ σ1' Hnotvalid
        | σ1'  ? ? ? ? Hvalid Hreg2 Hmem2 Hdecode2 Hexec Hcontrol];
      simplify_eq /=.
    + (*Fail*)
      by rewrite /is_valid_PC //= HPC Hacc in  Hnotvalid.
    + (* Normal. *)
      (* eliminate Hmem2 *)
      rewrite /get_memory  Hacc /get_memory_unsafe Hmem in Hmem2 .
      inversion Hmem2;subst wi; clear Hmem2.
      (* eliminate Hdecode2 *)
      by rewrite Hdecode in Hdecode2;inversion Hdecode2;subst i0.
  Qed.

 Lemma option_state_unpack_preserve_state_Some σ1 σ2 σ2' :
   σ2' = Some σ2 ->  (ExecI, σ2) = (option_state_unpack σ1 σ2').
  Proof.
    intros.
    destruct σ2' eqn:Heqn.
    inversion H; subst.
    done.
    done.
  Qed.


  Lemma mov_word_ExecI σ1 r w :
   PC ≠ r ->  NZ ≠ r -> (mov_word σ1 r w)= (ExecI, (update_incr_PC (update_reg σ1 r w))).
  Proof.
    intros.
    unfold mov_word .
    destruct r;[contradiction|contradiction|].
    rewrite <- (option_state_unpack_preserve_state_Some σ1
                                                        (update_incr_PC (update_reg σ1 (R n fin) w)) (Some (update_incr_PC (update_reg σ1 (R n fin) w))));eauto.
  Qed.



  Lemma mov_reg_ExecI σ1 r1 r2 w:
   PC ≠ r1 ->  NZ ≠ r1 ->
   PC ≠ r2 -> NZ ≠ r2 ->
   (get_reg σ1 r2) = Some w ->
   (mov_reg σ1 r1 r2)= (ExecI, (update_incr_PC (update_reg σ1 r1 w))).
  Proof.
    intros.
    unfold mov_reg.
    destruct r1 eqn:Heqn1,r2 eqn:Heqn2 ;try contradiction.
    unfold bind.
    simpl.
    rewrite H3.
    rewrite <- (option_state_unpack_preserve_state_Some σ1
                                                        (update_incr_PC (update_reg σ1 (R n fin) w)) (Some (update_incr_PC (update_reg σ1 (R n fin) w))));eauto.
  Qed.



  Lemma ldr_ExecI σ1 r1 r2 a w:
   PC ≠ r1 ->  NZ ≠ r1 ->
   PC ≠ r2 -> NZ ≠ r2 ->
   (get_mail_boxes σ1 !!! get_current_vm σ1).1 ≠ (mm_translation a) ->
   (get_reg σ1 r2) = Some a ->
   get_memory σ1 a = Some w ->
   (ldr σ1 r1 r2)= (ExecI, (update_incr_PC (update_reg σ1 r1 w))).
  Proof.
    intros.
    unfold ldr.
    destruct r1 eqn:Heqn1,r2 eqn:Heqn2 ;try contradiction.
    unfold bind.
    simpl.
    rewrite H4 H5.
    destruct (get_mail_boxes σ1 !!! get_current_vm σ1).
    simpl in H3.
    destruct (decide (mm_translation a =t)).
    done.
    done.
  Qed.


   Lemma str_ExecI σ1 r1 r2 w a:
   PC ≠ r1 ->  NZ ≠ r1 ->
   PC ≠ r2 -> NZ ≠ r2 ->
   (get_mail_boxes σ1 !!! get_current_vm σ1).2.1 ≠ (mm_translation a) ->
   (get_reg σ1 r1) = Some w ->
   (get_reg σ1 r2) = Some a ->
   check_access_addr σ1 (get_current_vm σ1) a = true ->
   (str σ1 r1 r2)= (ExecI, (update_memory_unsafe (update_incr_PC σ1) a w)).
  Proof.
    intros.
    unfold str.
    destruct r1 eqn:Heqn1,r2 eqn:Heqn2 ;try contradiction.
    unfold bind.
    simpl.
    rewrite H4 H5.
    destruct ((get_mail_boxes σ1 !!! get_current_vm σ1)).
    destruct p.
    simpl in H3.
    destruct (decide(mm_translation a = t0)).
    done.
    rewrite /update_memory /update_incr_PC update_offset_PC_preserve_current_vm.
    rewrite update_offset_PC_preserve_check_access H6 //.
  Qed.
