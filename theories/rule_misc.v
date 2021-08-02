From iris.algebra Require Import gmap gset dfrac agree.
From HypVeri Require Import RAs.

(* some preservation properties of the opsem*)
  Lemma update_reg_global_preserve_current_vm σ i r w :(get_current_vm (update_reg_global σ i r w)) = (get_current_vm σ).
  Proof.
    unfold get_current_vm ,update_reg_global.
    simpl.
    unfold get_current_vm.
    reflexivity.
  Qed.

  Lemma update_offset_PC_preserve_current_vm σ o :(get_current_vm (update_offset_PC σ o )) = (get_current_vm σ).
  Proof.
    unfold get_current_vm ,update_offset_PC.
    unfold get_current_vm.
    destruct (get_vm_reg_file σ σ.1.1.2 !! PC);eauto.
  Qed.

  Lemma update_memory_unsafe_preserve_current_vm σ a w :(get_current_vm (update_memory_unsafe σ a w)) = (get_current_vm σ).
  Proof.
    unfold get_current_vm ,update_memory_unsafe.
    simpl.
    unfold get_current_vm.
    reflexivity.
  Qed.

  Lemma get_reg_global_update_reg_global_ne_vmid {σ i j R1 R2 A B} :
    i ≠ j ->
    get_reg_global σ j R2 = Some B ->
    get_reg_global (update_reg_global σ i R1 A) j R2 = Some B.
  Proof.
    intros Hne Hlk.
    rewrite /get_reg_global /get_vm_reg_file /get_reg_files /update_reg_global.
    simpl.
    rewrite vlookup_insert_ne; auto.
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
      - destruct (get_vm_reg_file σ i !! r) as [w|]  eqn:Heqn;[|done].
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


  Lemma get_reg_gmap_get_vm_reg_file σ (r:reg_name) (i:VMID) :
   (get_reg_gmap σ) !! (r,i) = (get_vm_reg_file σ i) !! r.
    Proof.
      destruct (get_reg_gmap σ !! (r, i)) eqn:Heqn.
      apply get_reg_gmap_lookup_Some in Heqn;done.
      apply get_reg_gmap_lookup_None in Heqn;done.
    Qed.


  Lemma get_reg_gmap_get_reg_Some σ (r:reg_name) (w:Word) (i:VMID) : i= (get_current_vm σ)->
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

  Lemma update_offset_PC_update_PC1 σ i (w:Word) (o:Z):
   i=get_current_vm σ -> ((get_reg_gmap σ) !! (PC,i) = Some w)
   ->get_reg_gmap (update_offset_PC σ o) = <[(PC,i) := (w ^+ o)%f]>(get_reg_gmap σ).
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


  Lemma update_current_vmid_preserve_reg σ i :
    get_reg_gmap (update_current_vmid σ i) = get_reg_gmap σ.
  Proof.
    rewrite /get_reg_gmap /update_memory_unsafe //.
  Qed.

  Lemma update_memory_unsafe_preserve_reg σ a w:
   get_reg_gmap (update_memory_unsafe σ a w) = get_reg_gmap σ.
  Proof.
    rewrite /get_reg_gmap /update_memory_unsafe //.
  Qed.

  Lemma update_current_vmid_preserve_mem σ i : get_mem (update_current_vmid σ i) = get_mem σ.
  Proof.
    unfold update_reg_global, get_mem.
    simpl.
    reflexivity.
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

  Lemma update_offset_PC_preserve_mem σ o : get_mem (update_offset_PC σ o) = get_mem σ.
  Proof.
    unfold update_offset_PC.
    destruct (get_vm_reg_file σ (get_current_vm σ) !! PC).
    rewrite -> update_reg_preserve_mem;done.
    done.
  Qed.

  Lemma update_memory_unsafe_update_mem σ a w : is_Some((get_mem σ) !! a) -> get_mem (update_memory_unsafe σ a w) =
                                             <[a := w]>(get_mem σ).
  Proof.
    intros.
    rewrite  /update_memory_unsafe //.
  Qed.


  Lemma update_current_vmid_preserve_tx σ i : get_tx_agree (update_current_vmid σ i) =
                                               (get_tx_agree σ).
  Proof.
    rewrite /get_tx_agree /get_txrx_auth_agree.
    f_equal.
  Qed.

  Lemma update_reg_global_preserve_tx σ i r w : get_tx_agree (update_reg_global σ i r w) =
                                               (get_tx_agree σ).
  Proof.
    rewrite /get_tx_agree /get_txrx_auth_agree.
    f_equal.
  Qed.

  Lemma update_offset_PC_preserve_tx σ o : get_tx_agree (update_offset_PC σ o) = get_tx_agree σ.
  Proof.
    unfold update_offset_PC.
    destruct (get_vm_reg_file σ (get_current_vm σ) !! PC).
    rewrite /update_reg update_reg_global_preserve_tx;done.
    done.
  Qed.

  Lemma update_memory_unsafe_preserve_tx σ a w : get_tx_agree (update_memory_unsafe σ a w) = get_tx_agree σ.
  Proof.
    rewrite /get_tx_agree /get_txrx_auth_agree.
    f_equal.
  Qed.

  Lemma update_current_vmid_preserve_rx1 σ i : get_rx_agree (update_current_vmid σ i) =
                                               (get_rx_agree σ).
  Proof.
    rewrite /get_rx_agree /get_txrx_auth_agree.
    f_equal.
  Qed.

 Lemma update_reg_global_preserve_rx1 σ i r w : get_rx_agree (update_reg_global σ i r w) =
                                               (get_rx_agree σ).
  Proof.
    rewrite /get_rx_agree /get_txrx_auth_agree.
    f_equal.
  Qed.

  Lemma update_offset_PC_preserve_rx1 σ o : get_rx_agree (update_offset_PC σ o) = get_rx_agree σ.
  Proof.
    unfold update_offset_PC.
    destruct (get_vm_reg_file σ (get_current_vm σ) !! PC).
    rewrite /update_reg update_reg_global_preserve_rx1;done.
    done.
  Qed.

 Lemma update_memory_unsafe_preserve_rx1 σ a w : get_rx_agree (update_memory_unsafe σ a w) =
                                               (get_rx_agree σ).
  Proof.
    rewrite /get_rx_agree /get_txrx_auth_agree.
    f_equal.
  Qed.

  Lemma update_current_vmid_preserve_rx2 σ i : get_rx_gmap (update_current_vmid σ i) =
                                                 (get_rx_gmap σ).
  Proof.
    rewrite /get_rx_gmap /get_txrx_auth_agree.
    f_equal.
  Qed.

   Lemma update_reg_global_preserve_rx2 σ i r w : get_rx_gmap (update_reg_global σ i r w) =
                                               (get_rx_gmap σ).
  Proof.
    rewrite /get_rx_gmap /get_txrx_auth_agree.
    f_equal.
  Qed.

  Lemma update_offset_PC_preserve_rx2 σ o : get_rx_gmap (update_offset_PC σ o) = get_rx_gmap σ.
  Proof.
    unfold update_offset_PC.
    destruct (get_vm_reg_file σ (get_current_vm σ) !! PC).
    rewrite /update_reg update_reg_global_preserve_rx2;done.
    done.
  Qed.

   Lemma update_memory_unsafe_preserve_rx2 σ a w : get_rx_gmap (update_memory_unsafe σ a w) =
                                               (get_rx_gmap σ).
  Proof.
    rewrite /get_rx_gmap /get_txrx_auth_agree.
    f_equal.
  Qed.


  (* TODO: the proofs above are identical *)

  Lemma update_current_vmid_preserve_rx σ i : (get_rx_agree (update_current_vmid σ i), get_rx_gmap (update_current_vmid σ i)) =
                                               (get_rx_agree σ, get_rx_gmap σ).
  Proof.
    by rewrite update_current_vmid_preserve_rx1 update_current_vmid_preserve_rx2.
  Qed.

  Lemma update_reg_global_preserve_rx σ i r w : (get_rx_agree (update_reg_global σ i r w), get_rx_gmap (update_reg_global σ i r w)) =
                                               (get_rx_agree σ, get_rx_gmap σ).
  Proof.
    by rewrite update_reg_global_preserve_rx1 update_reg_global_preserve_rx2.
  Qed.

  Lemma update_offset_PC_preserve_rx  σ o : (get_rx_agree (update_offset_PC σ o), get_rx_gmap (update_offset_PC σ o) ) =
                                               (get_rx_agree σ, get_rx_gmap σ).
  Proof.
    by rewrite update_offset_PC_preserve_rx1 update_offset_PC_preserve_rx2 .
  Qed.


  Lemma update_memory_unsafe_preserve_rx  σ a w : (get_rx_agree (update_memory_unsafe σ a w), get_rx_gmap (update_memory_unsafe σ a w) ) =
                                               (get_rx_agree σ, get_rx_gmap σ).
  Proof.
    by rewrite update_memory_unsafe_preserve_rx1 update_memory_unsafe_preserve_rx2 .
  Qed.

  Lemma update_current_vmid_preserve_pt σ i i':
   get_vm_page_table (update_current_vmid σ i) i' = get_vm_page_table σ i'.
  Proof.
    rewrite /update_reg_global /get_vm_page_table /get_page_tables.
    done.
  Qed.

  Lemma update_reg_global_preserve_pt σ i i' r w:
   get_vm_page_table (update_reg_global σ i r w) i' = get_vm_page_table σ i'.
  Proof.
    rewrite /update_reg_global /get_vm_page_table /get_page_tables.
    done.
  Qed.

  Lemma update_current_vmid_preserve_owned σ i : get_owned_gmap (update_current_vmid σ i) =
                                               (get_owned_gmap σ).
  Proof.
    rewrite /get_owned_gmap.
    f_equal.
  Qed.

  Lemma update_reg_global_preserve_owned σ i r w : get_owned_gmap (update_reg_global σ i r w) =
                                               (get_owned_gmap σ).
  Proof.
    rewrite /get_owned_gmap.
    f_equal.
  Qed.

  Lemma update_offset_PC_preserve_owned σ o : get_owned_gmap (update_offset_PC σ o) = get_owned_gmap σ.
  Proof.
    unfold update_offset_PC.
    destruct (get_vm_reg_file σ (get_current_vm σ) !! PC).
    rewrite /update_reg update_reg_global_preserve_owned;done.
    done.
  Qed.

  Lemma update_memory_unsafe_preserve_owned σ a w : get_owned_gmap (update_memory_unsafe σ a w) =
                                               (get_owned_gmap σ).
  Proof.
    rewrite /get_owned_gmap.
    f_equal.
  Qed.

  Lemma update_current_vmid_preserve_access σ i : get_access_gmap (update_current_vmid σ i) =
                                               (get_access_gmap σ).
  Proof.
    rewrite /get_access_gmap.
    f_equal.
  Qed.

  Lemma update_reg_global_preserve_access σ i r w : get_access_gmap (update_reg_global σ i r w) =
                                               (get_access_gmap σ).
  Proof.
    rewrite /get_access_gmap.
    f_equal.
  Qed.

  Lemma update_offset_PC_preserve_access σ o : get_access_gmap (update_offset_PC σ o) = get_access_gmap σ.
  Proof.
    unfold update_offset_PC.
    destruct (get_vm_reg_file σ (get_current_vm σ) !! PC).
    rewrite /update_reg update_reg_global_preserve_access;done.
    done.
  Qed.

  Lemma update_offset_PC_preserve_check_access σ o a:
  check_access_addr (update_offset_PC σ o) (get_current_vm σ) a = check_access_addr  σ (get_current_vm σ) a.
  Proof.
    rewrite /update_offset_PC /check_access_addr /check_access_page.
    simpl.
    destruct (get_vm_reg_file σ (get_current_vm σ) !! PC);eauto.
  Qed.

  Lemma update_memory_unsafe_preserve_access σ a w : get_access_gmap (update_memory_unsafe σ a w) =
                                               (get_access_gmap σ).
  Proof.
    rewrite /get_access_gmap.
    f_equal.
  Qed.

  Lemma update_current_vmid_preserve_excl σ i : get_excl_gmap (update_current_vmid σ i) =
                                               (get_excl_gmap σ).
  Proof.
    rewrite /get_excl_gmap.
    f_equal.
  Qed.

  Lemma update_reg_global_preserve_excl σ i r w : get_excl_gmap (update_reg_global σ i r w) =
                                               (get_excl_gmap σ).
  Proof.
    rewrite /get_excl_gmap.
    f_equal.
  Qed.

  Lemma update_offset_PC_preserve_excl σ o : get_excl_gmap (update_offset_PC σ o) = get_excl_gmap σ.
  Proof.
    unfold update_offset_PC.
    destruct (get_vm_reg_file σ (get_current_vm σ) !! PC).
    rewrite /update_reg update_reg_global_preserve_excl;done.
    done.
  Qed.


  Lemma update_memory_unsafe_preserve_excl σ a w : get_excl_gmap (update_memory_unsafe σ a w) =
                                               (get_excl_gmap σ).
  Proof.
    rewrite /get_excl_gmap.
    f_equal.
  Qed.


  Lemma update_current_vmid_preserve_trans σ i : get_trans_gmap (update_current_vmid σ i) =
                                               (get_trans_gmap σ).
  Proof.
    rewrite /get_trans_gmap.
    f_equal.
  Qed.

  Lemma update_reg_global_preserve_trans σ i r w : get_trans_gmap (update_reg_global σ i r w) =
                                               (get_trans_gmap σ).
  Proof.
    rewrite /get_trans_gmap.
    f_equal.
  Qed.

  Lemma update_offset_PC_preserve_trans σ o : get_trans_gmap (update_offset_PC σ o) = get_trans_gmap σ.
  Proof.
    unfold update_offset_PC.
    destruct (get_vm_reg_file σ (get_current_vm σ) !! PC).
     rewrite /update_reg update_reg_global_preserve_trans;done.
    done.
  Qed.

  Lemma update_memory_unsafe_preserve_trans σ a w : get_trans_gmap (update_memory_unsafe σ a w) =
                                               (get_trans_gmap σ).
  Proof.
    rewrite /get_trans_gmap.
    f_equal.
  Qed.

  Lemma update_current_vmid_preserve_hpool σ i : get_hpool_gset (update_current_vmid σ i) =
                                               (get_hpool_gset σ).
  Proof.
    rewrite /get_hpool_gset.
    f_equal.
  Qed.


  Lemma update_reg_global_preserve_hpool σ i r w : get_hpool_gset (update_reg_global σ i r w) =
                                               (get_hpool_gset σ).
  Proof.
    rewrite /get_hpool_gset.
    f_equal.
  Qed.

  Lemma update_offset_PC_preserve_hpool σ o : get_hpool_gset (update_offset_PC σ o) = get_hpool_gset σ.
  Proof.
    unfold update_offset_PC.
    destruct (get_vm_reg_file σ (get_current_vm σ) !! PC).
     rewrite /update_reg update_reg_global_preserve_hpool;done.
    done.
  Qed.

  Lemma update_memory_unsafe_preserve_hpool σ a w : get_hpool_gset (update_memory_unsafe σ a w) =
                                               (get_hpool_gset σ).
  Proof.
    rewrite /get_hpool_gset.
    f_equal.
  Qed.


  Lemma update_current_vmid_preserve_receivers σ i : get_receivers_gmap (update_current_vmid σ i) =
                                               (get_receivers_gmap σ).
  Proof.
    rewrite /get_receivers_gmap.
    f_equal.
  Qed.

  Lemma update_reg_global_preserve_receivers σ i r w : get_receivers_gmap (update_reg_global σ i r w) =
                                               (get_receivers_gmap σ).
  Proof.
    rewrite /get_receivers_gmap.
    f_equal.
  Qed.

  Lemma update_offset_PC_preserve_receivers σ o : get_receivers_gmap (update_offset_PC σ o) = get_receivers_gmap σ.
  Proof.
    unfold update_offset_PC.
    destruct (get_vm_reg_file σ (get_current_vm σ) !! PC).
    rewrite /update_reg update_reg_global_preserve_receivers;done.
    done.
  Qed.

 Lemma update_memory_unsafe_preserve_receivers σ a w : get_receivers_gmap (update_memory_unsafe σ a w) =
                                               (get_receivers_gmap σ).
  Proof.
    rewrite /get_receivers_gmap.
    f_equal.
  Qed.

  (* Lemma update_page_table_foldr σ i (psd: list PID) perm: *)
  (*  i = (get_current_vm σ) -> *)
  (*  (foldr (λ (v' : PID) (acc' : state), update_page_table acc' v' perm) σ psd) *)
  (*  = ((get_reg_files σ), (get_mail_boxes σ), *)
  (*         (foldr (λ (p:PID) acc, vinsert i (<[p:=perm]>(get_vm_page_table σ i)) acc) (get_page_tables σ) psd), *)
  (*                             (get_current_vm σ), (get_mem σ), (get_transactions σ)). *)
  (*   Proof. *)
  (*     intros ->. *)
  (*     induction psd. *)
  (*     simpl. *)
  (*     repeat destruct σ as [σ ?]. *)
  (*     done. *)
  (*     simpl. *)
  (*     simpl in IHpsd. *)
  (*     rewrite -> IHpsd. *)
  (*     rewrite /update_page_table //= /get_current_vm //=  /update_page_table_global  /get_reg_files //=. *)
  (*     rewrite /get_mail_boxes /get_mem /get_transactions /get_current_vm  //=  /get_page_tables //=. *)
  (*     f_equal. *)
  (*     f_equal. *)
  (*     f_equal. *)
  (*     f_equal /=. *)
  (*     (* TODO, seems like we need a lemma: ∀ i, vec1 !!! i = vec2 !!! i -> vec1=vec2 *) *)
  (*         Admitted. *)

  Lemma update_page_table_batch_preserve_current_vm σ (ps: list PID) perm:
   get_current_vm (update_page_table_batch σ ps perm) = get_current_vm σ.
    Proof.
      rewrite /get_current_vm.
      f_equal.
Qed.

  Lemma update_page_table_batch_preserve_regs σ (ps: list PID) perm:
   get_reg_gmap (update_page_table_batch σ ps perm) = get_reg_gmap σ.
    Proof.
      rewrite /get_reg_gmap.
      f_equal.
Qed.
   Lemma update_page_table_batch_preserve_mem σ (ps: list PID) perm:
   get_mem (update_page_table_batch σ ps perm) = get_mem σ.
    Proof.
      rewrite /get_mem.
      f_equal.
Qed.
   Lemma update_page_table_batch_preserve_tx σ (ps: list PID) perm:
   get_tx_agree (update_page_table_batch σ ps perm) = get_tx_agree σ.
    Proof.
      rewrite /get_tx_agree.
      f_equal.
Qed.
       Lemma update_page_table_batch_preserve_rx1 σ (ps: list PID) perm:
   get_rx_agree (update_page_table_batch σ ps perm) = get_rx_agree σ.
    Proof.
      rewrite /get_rx_agree.
      f_equal.
Qed.
   Lemma update_page_table_batch_preserve_rx2 σ (ps: list PID) perm:
   get_rx_gmap (update_page_table_batch σ ps perm) = get_rx_gmap σ.
    Proof.
      rewrite /get_rx_gmap.
      f_equal.
Qed.
      Lemma update_page_table_batch_preserve_rx σ (ps: list PID) perm:
       (get_rx_agree (update_page_table_batch σ ps perm), get_rx_gmap (update_page_table_batch σ ps perm) ) =
                                               (get_rx_agree σ, get_rx_gmap σ).
  Proof.
    by rewrite update_page_table_batch_preserve_rx1 update_page_table_batch_preserve_rx2 .
  Qed.

   Lemma update_page_table_batch_preserve_trans σ (ps: list PID) perm:
   get_trans_gmap (update_page_table_batch σ ps perm) = get_trans_gmap σ.
    Proof.
      rewrite /get_trans_gmap.
      f_equal.
Qed.
   Lemma update_page_table_batch_preserve_hpool σ (ps: list PID) perm:
   get_hpool_gset (update_page_table_batch σ ps perm) = get_hpool_gset σ.
    Proof.
      rewrite /get_hpool_gset.
      f_equal.
Qed.
   Lemma update_page_table_batch_preserve_receivers σ (ps: list PID) perm:
   get_receivers_gmap (update_page_table_batch σ ps perm) = get_receivers_gmap σ.
    Proof.
      rewrite /get_receivers_gmap.
      f_equal.
Qed.

    Lemma update_page_table_batch_preserve_other_page_tables σ ps perm i:
     i ≠ (get_current_vm σ) ->
    (get_page_tables (update_page_table_batch σ ps perm)) !!! i =
    (get_page_tables σ) !!! i.
      Proof.
        intros.
        rewrite /get_page_tables /update_page_table_batch /update_page_table_global_batch /=.
       rewrite vlookup_insert_ne.
       rewrite /get_page_tables //.
       done.
       Qed.

  Ltac inv_map_in :=
       match goal with
         | H : (?i, ?y) ∈ map ?f ?l |- _ => apply elem_of_list_In in H;
             apply in_map_iff in H;
             destruct H;
             destruct H
         |  |- (?i, ?y) ∈ map ?f ?l => apply elem_of_list_In;
             apply in_map_iff;
             try split;eauto
         | H : (?x) ∈ map ?f ?l |- _ => apply elem_of_list_In in H;
             apply in_map_iff in H;
             destruct H;
             destruct H
         |  |- (?x) ∈ map ?f ?l => apply elem_of_list_In;
             apply in_map_iff;
             try split;eauto
       end.

      Lemma get_access_gmap_is_accessible_true {σ i sacc} p:
            (get_access_gmap σ) !! i = Some (DfracOwn 1, to_agree (GSet sacc))->
            (p ∈ sacc <->
            ∃ perm, (get_vm_page_table σ i) !! p =Some perm ∧ is_accessible perm = true).
        Proof.
          intros.
          rewrite /get_access_gmap in H.
          apply (elem_of_list_to_map_2 _ i (DfracOwn 1, to_agree (GSet sacc))) in H.
          inv_map_in. clear H0.
          inversion H.
          subst.
          clear H.
          split.
          - intro H. apply elem_of_list_to_set in H.
            inv_map_in.
          apply elem_of_list_In in H0.
          apply elem_of_map_to_list' in H0.
          apply map_filter_lookup_Some in H0.
          destruct H0.
          exists x.2.
          split;eauto.
          by subst p.
          - intros H.
            destruct H.
            apply elem_of_list_to_set.
            apply elem_of_list_In.
            apply in_map_iff.
            exists (p,x).
            split;eauto.
            apply elem_of_list_In.
            apply elem_of_map_to_list'.
            apply map_filter_lookup_Some.
            done.
        Qed.

    Lemma update_page_table_batch_update_access_noaccess{ σ i sacc} {sps:gset PID} (ps: list PID) o :
     sps = (list_to_set ps)->
     i = (get_current_vm σ) ->
     (get_access_gmap σ) !! i = Some (DfracOwn 1, to_agree (GSet sacc)) ->
     get_access_gmap (update_page_table_batch σ ps (o,NoAccess)) =
     <[(get_current_vm σ):= (DfracOwn 1, to_agree (GSet (sacc ∖ sps ) ))]>(get_access_gmap σ).
      Proof.
        intros.
        rewrite /get_access_gmap.
        apply (@map_eq VMID (gmap VMID) _ _ _ _ _ _ _ _ gmap_finmap);eauto.
        intro.
        rewrite -H0.
        destruct(decide (i0 = i)).
        - subst i0. rewrite lookup_insert.
          apply (@elem_of_list_to_map_1' VMID (gmap VMID) _ _ _ _ _ _ _ _ gmap_finmap).
          + intros.
            inv_map_in.
             inversion H2.
             do 3 f_equal.
             clear H6 H3 H2.
             subst x.
             symmetry.
             apply set_eq.
             intro.
             rewrite  elem_of_list_to_set.
             split.
            * intros.
              inv_map_in.
              apply elem_of_list_In in H3.
              apply (elem_of_map_to_list' _ x0) in H3.
              apply map_filter_lookup_Some in H3.
              destruct H3.
              simplify_eq /=.
              rewrite /get_vm_page_table /get_page_tables /update_page_table_batch /update_page_table_global_batch //= in H3.
              rewrite vlookup_insert in H3.
              apply elem_of_difference.
              induction ps; simpl in *.
              -- split;[|set_solver].
                 apply (get_access_gmap_is_accessible_true x0.1 H1).
                 exists (x0.2).
                 split;eauto.
              -- assert (Hneq: a ≠ x0.1).
                 { destruct (decide (a=x0.1));eauto.
                   subst a.
                   rewrite lookup_insert in H3.
                   inversion H3.
                   rewrite -H0 in H4.
                   rewrite /is_accessible //=.
                 }
                 rewrite not_elem_of_union.
                 assert (Himp : x0.1 ∈ sacc ∧ x0.1 ∉ ((list_to_set ps):gset PID) ->(x0.1 ∈ sacc ∧ (x0.1 ∉ ({[a]}:gset PID)) ∧ x0.1 ∉ ((list_to_set ps):gset PID))).
                 { intros. destruct H; split;eauto. split. set_solver. done. }
                 apply Himp.
                 apply IHps;eauto.
                 rewrite lookup_insert_ne in H3;done.
            * intros.
              apply elem_of_difference in H2.
              destruct H2.
              apply (get_access_gmap_is_accessible_true x H1) in H2;eauto.
              destruct H2.
              destruct H2.
              inv_map_in.
              exists (x,x0).
              split;eauto.
              apply elem_of_list_In .
              apply  elem_of_map_to_list.
              apply map_filter_lookup_Some.
              rewrite /get_vm_page_table /get_page_tables /update_page_table_batch /update_page_table_global_batch /=.
              rewrite -H0 vlookup_insert.
              destruct H1;split;eauto.
              generalize dependent sps.
              induction ps;simpl.
              done.
              intros.
              rewrite H //= in H3.
              assert (Hneq: a ≠ x).
              { set_solver. }
              rewrite lookup_insert_ne;eauto.
              apply (IHps (list_to_set ps));eauto.
              set_solver.
          + inv_map_in.
            exists i.
            split;[|apply in_list_of_vmids].
            do 4 f_equal.
            apply set_eq.
            intro.
            rewrite  elem_of_list_to_set.
            split.
            -- intros.
               inv_map_in.
               subst x.
               apply elem_of_list_In in H3.
               apply (elem_of_map_to_list' _ x0) in H3.
               apply map_filter_lookup_Some in H3.
               destruct H3.
               rewrite /get_vm_page_table /get_page_tables /update_page_table_batch /update_page_table_global_batch //= in H2.
               rewrite -H0 vlookup_insert in H2.
               apply elem_of_difference.
               generalize dependent sps.
               induction ps; simpl in *.
               ++ intros.
                 split;[|set_solver].
                 apply (get_access_gmap_is_accessible_true x0.1 H1).
                 exists x0.2.
                 split;eauto.
               ++ intros.
                 assert (Hneq: a ≠ x0.1).
                 { destruct (decide (a=x0.1));eauto.
                   subst a.
                   rewrite lookup_insert in H2.
                   inversion H2.
                   rewrite -H5 in H3.
                   rewrite /is_accessible //=.
                 }
                 rewrite H.
                 rewrite not_elem_of_union.
                 assert (Himp : x0.1 ∈ sacc ∧ x0.1 ∉ ((list_to_set ps):gset PID) ->(x0.1 ∈ sacc ∧ (x0.1 ∉ ({[a]}:gset PID)) ∧ x0.1 ∉ ((list_to_set ps):gset PID))).
                 {  intros. destruct H4; split;eauto. split. set_solver. done. }
                 apply Himp.
                 apply IHps;eauto.
                 rewrite lookup_insert_ne //= in H2.
            -- intros.
               apply elem_of_difference in H2.
               destruct H2.
               apply (get_access_gmap_is_accessible_true x H1) in H2;eauto.
               destruct H2.
               destruct H2.
               inv_map_in.
               exists (x,x0).
               split;eauto.
                 apply elem_of_list_In .
                 apply  elem_of_map_to_list.
                 apply map_filter_lookup_Some.
                 rewrite /get_vm_page_table /get_page_tables /update_page_table_batch /update_page_table_global_batch /=.
                 rewrite -H0 vlookup_insert.
                 destruct H1;split;eauto.
                 generalize dependent sps.
                 induction ps;simpl.
                 done.
                 intros.
                 rewrite H in H3.
                 simpl in H3.
                 assert (Hneq: a ≠ x).
                 { set_solver. }
                 rewrite lookup_insert_ne;eauto.
                 apply (IHps (list_to_set ps));eauto.
                 set_solver.
        - rewrite (lookup_insert_ne _ i i0 _);eauto.
          set (l:= (map
                      (λ v : VMID,
                             (v,
                              (DfracOwn 1,
                               to_agree
                                 (GSet
                                    (list_to_set
                                       (map (λ p : PID * permission, p.1)
                                            (map_to_list
                                               (filter (λ p : PID * permission, is_accessible p.2 = true) (get_vm_page_table σ v)))))))))
                      list_of_vmids)) in *.
          destruct (list_to_map l !! i0) eqn:Heqn.
          + apply (elem_of_list_to_map_2 l i0 c) in Heqn.
            apply elem_of_list_In in Heqn.
            apply in_map_iff in Heqn.
            inversion Heqn;clear Heqn.
            destruct H2 as [H3 HIn];inversion H3;subst;clear H3.
            apply (@elem_of_list_to_map_1' VMID (gmap VMID) _ _ _ _ _ _ _ _ gmap_finmap).
            *  intros.
               inv_map_in.
               inversion H.
               do 7 f_equal.
               rewrite /get_vm_page_table update_page_table_batch_preserve_other_page_tables //.
            * inv_map_in.
              exists i0.
              split;eauto.
              do 8 f_equal.
              rewrite /get_vm_page_table update_page_table_batch_preserve_other_page_tables //.
          + apply (@not_elem_of_list_to_map_2 VMID (gmap VMID) _ _ _ _ _ _ _ _ gmap_finmap) in Heqn.
            apply (@not_elem_of_list_to_map_1 VMID (gmap VMID) _ _ _ _ _ _ _ _ gmap_finmap).
            intro P.
            apply Heqn.
            apply elem_of_list_In.
            apply in_map_iff.
            apply elem_of_list_In in P.
            apply in_map_iff in P.
            destruct P.
            exists x.
            destruct H2.
            split;eauto.
            apply in_map_iff.
            apply in_map_iff in H3.
            destruct H3.
            exists x0.
            destruct H3.
            split;eauto.
            rewrite -H3.
            do 8 f_equal.
            rewrite /get_vm_page_table update_page_table_batch_preserve_other_page_tables //.
            destruct x.
            simpl in H2;inversion H3.
            by subst.
      Qed.

      Lemma get_owned_gmap_is_owned_true {σ i sown} p:
            (get_owned_gmap σ) !! i = Some (DfracOwn 1, to_agree (GSet sown))->
            (p ∈ sown <->
            ∃ perm, (get_vm_page_table σ i) !! p =Some perm ∧ is_owned perm = true).
        Proof.
          intros.
          rewrite /get_owned_gmap in H.
          apply (elem_of_list_to_map_2 _ i (DfracOwn 1, to_agree (GSet sown))) in H.
          inv_map_in. clear H0.
          inversion H.
          subst.
          clear H.
          split.
          - intro H. apply elem_of_list_to_set in H.
            inv_map_in.
          apply elem_of_list_In in H0.
          apply elem_of_map_to_list' in H0.
          apply map_filter_lookup_Some in H0.
          destruct H0.
          exists x.2.
          split;eauto.
          by subst p.
          - intros H.
            destruct H.
            apply elem_of_list_to_set.
            apply elem_of_list_In.
            apply in_map_iff.
            exists (p,x).
            split;eauto.
            apply elem_of_list_In.
            apply elem_of_map_to_list'.
            apply map_filter_lookup_Some.
            done.
        Qed.


    Lemma update_page_table_batch_update_own_owned{ σ i sown} {sps:gset PID} (ps: list PID) a :
     sps = (list_to_set ps)->
     i = (get_current_vm σ) ->
     (get_owned_gmap σ) !! i = Some (DfracOwn 1, to_agree (GSet sown)) ->
     get_owned_gmap (update_page_table_batch σ ps (Owned,a)) =
     <[i:= (DfracOwn 1, to_agree (GSet (sown ∪ sps ) ))]>(get_owned_gmap σ).
      Proof.
        intros.
        rewrite /get_owned_gmap.
        apply (@map_eq VMID (gmap VMID) _ _ _ _ _ _ _ _ gmap_finmap);eauto.
        intro.
        destruct(decide (i0 = i)).
        - subst i0. rewrite lookup_insert.
          apply (@elem_of_list_to_map_1' VMID (gmap VMID) _ _ _ _ _ _ _ _ gmap_finmap).
          + intros.
            inv_map_in.
             inversion H2.
             do 3 f_equal.
             clear H6 H3 H2.
             subst x.
             symmetry.
             apply set_eq.
             intro.
             rewrite  elem_of_list_to_set.
             split.
            * intros.
              inv_map_in.
              apply elem_of_list_In in H3.
              apply (elem_of_map_to_list' _ x0) in H3.
              apply map_filter_lookup_Some in H3.
              destruct H3.
              simplify_eq /=.
              rewrite /get_vm_page_table /get_page_tables /update_page_table_batch /update_page_table_global_batch //= in H3.
              rewrite vlookup_insert in H3.
              apply elem_of_union.
              induction ps; simpl in *.
              -- left.
                 apply (get_owned_gmap_is_owned_true x0.1 H1).
                 exists (x0.2).
                 split;eauto.
              -- destruct (decide (a0=x0.1)).
                 right;set_solver.
                 assert (Himp :(x0.1 ∈ sown ∨ x0.1 ∈ ((list_to_set ps):gset PID))
                                ->(x0.1 ∈ sown ∨ x0.1 ∈ {[a0]} ∪ ((list_to_set ps):gset PID))).
                 { intros. destruct H. left;done. right; set_solver. }
                 apply Himp.
                 apply IHps;eauto.
                 rewrite lookup_insert_ne in H3;done.
            * intros.
              apply elem_of_union in H2.
              destruct H2.
              apply (get_owned_gmap_is_owned_true x H1) in H2;eauto.
              destruct H2.
              destruct H2.
              inv_map_in.
              exists (x,x0).
              split;eauto.
              apply elem_of_list_In .
              apply elem_of_map_to_list.
              apply map_filter_lookup_Some.
              rewrite /get_vm_page_table /get_page_tables /update_page_table_batch /update_page_table_global_batch /=.
              rewrite -H0 vlookup_insert.
              destruct H1;split;eauto.
              generalize dependent sps.
              induction ps;simpl.
              done.
              intros.
              (* rewrite H //= in H3. *)
              destruct (decide (x=a0)).
              subst a0.
              rewrite lookup_insert.
              Admitted.
              (* TODO: this lemma is not provable if we update ownership and accessiblity at the same time *)
      (*         assert (Hneq: a ≠ x). *)
      (*         { set_solver. } *)
      (*         rewrite lookup_insert_ne;eauto. *)
      (*         apply (IHps (list_to_set ps));eauto. *)
      (*         set_solver. *)
      (*     + inv_map_in. *)
      (*       exists i. *)
      (*       split;[|apply in_list_of_vmids]. *)
      (*       do 4 f_equal. *)
      (*       apply set_eq. *)
      (*       intro. *)
      (*       rewrite  elem_of_list_to_set. *)
      (*       split. *)
      (*       -- intros. *)
      (*          inv_map_in. *)
      (*          subst x. *)
      (*          apply elem_of_list_In in H3. *)
      (*          apply (elem_of_map_to_list' _ x0) in H3. *)
      (*          apply map_filter_lookup_Some in H3. *)
      (*          destruct H3. *)
      (*          rewrite /get_vm_page_table /get_page_tables /update_page_table_batch /update_page_table_global_batch //= in H2. *)
      (*          rewrite -H0 vlookup_insert in H2. *)
      (*          apply elem_of_difference. *)
      (*          generalize dependent sps. *)
      (*          induction ps; simpl in *. *)
      (*          ++ intros. *)
      (*            split;[|set_solver]. *)
      (*            apply (get_access_gmap_is_accessible_true x0.1 H1). *)
      (*            exists x0.2. *)
      (*            split;eauto. *)
      (*          ++ intros. *)
      (*            assert (Hneq: a ≠ x0.1). *)
      (*            { destruct (decide (a=x0.1));eauto. *)
      (*              subst a. *)
      (*              rewrite lookup_insert in H2. *)
      (*              inversion H2. *)
      (*              rewrite -H5 in H3. *)
      (*              rewrite /is_accessible //=. *)
      (*            } *)
      (*            rewrite H. *)
      (*            rewrite not_elem_of_union. *)
      (*            assert (Himp : x0.1 ∈ sacc ∧ x0.1 ∉ ((list_to_set ps):gset PID) ->(x0.1 ∈ sacc ∧ (x0.1 ∉ ({[a]}:gset PID)) ∧ x0.1 ∉ ((list_to_set ps):gset PID))). *)
      (*            {  intros. destruct H4; split;eauto. split. set_solver. done. } *)
      (*            apply Himp. *)
      (*            apply IHps;eauto. *)
      (*            rewrite lookup_insert_ne //= in H2. *)
      (*       -- intros. *)
      (*          apply elem_of_difference in H2. *)
      (*          destruct H2. *)
      (*          apply (get_access_gmap_is_accessible_true x H1) in H2;eauto. *)
      (*          destruct H2. *)
      (*          destruct H2. *)
      (*          inv_map_in. *)
      (*          exists (x,x0). *)
      (*          split;eauto. *)
      (*            apply elem_of_list_In . *)
      (*            apply  elem_of_map_to_list. *)
      (*            apply map_filter_lookup_Some. *)
      (*            rewrite /get_vm_page_table /get_page_tables /update_page_table_batch /update_page_table_global_batch /=. *)
      (*            rewrite -H0 vlookup_insert. *)
      (*            destruct H1;split;eauto. *)
      (*            generalize dependent sps. *)
      (*            induction ps;simpl. *)
      (*            done. *)
      (*            intros. *)
      (*            rewrite H in H3. *)
      (*            simpl in H3. *)
      (*            assert (Hneq: a ≠ x). *)
      (*            { set_solver. } *)
      (*            rewrite lookup_insert_ne;eauto. *)
      (*            apply (IHps (list_to_set ps));eauto. *)
      (*            set_solver. *)
      (*   - rewrite (lookup_insert_ne _ i i0 _);eauto. *)
      (*     set (l:= (map *)
      (*                 (λ v : VMID, *)
      (*                        (v, *)
      (*                         (DfracOwn 1, *)
      (*                          to_agree *)
      (*                            (GSet *)
      (*                               (list_to_set *)
      (*                                  (map (λ p : PID * permission, p.1) *)
      (*                                       (map_to_list *)
      (*                                          (filter (λ p : PID * permission, is_accessible p.2 = true) (get_vm_page_table σ v))))))))) *)
      (*                 list_of_vmids)) in *. *)
      (*     destruct (list_to_map l !! i0) eqn:Heqn. *)
      (*     + apply (elem_of_list_to_map_2 l i0 c) in Heqn. *)
      (*       apply elem_of_list_In in Heqn. *)
      (*       apply in_map_iff in Heqn. *)
      (*       inversion Heqn;clear Heqn. *)
      (*       destruct H2 as [H3 HIn];inversion H3;subst;clear H3. *)
      (*       apply (@elem_of_list_to_map_1' VMID (gmap VMID) _ _ _ _ _ _ _ _ gmap_finmap). *)
      (*       *  intros. *)
      (*          inv_map_in. *)
      (*          inversion H. *)
      (*          do 7 f_equal. *)
      (*          rewrite /get_vm_page_table update_page_table_batch_preserve_other_page_tables //. *)
      (*       * inv_map_in. *)
      (*         exists i0. *)
      (*         split;eauto. *)
      (*         do 8 f_equal. *)
      (*         rewrite /get_vm_page_table update_page_table_batch_preserve_other_page_tables //. *)
      (*     + apply (@not_elem_of_list_to_map_2 VMID (gmap VMID) _ _ _ _ _ _ _ _ gmap_finmap) in Heqn. *)
      (*       apply (@not_elem_of_list_to_map_1 VMID (gmap VMID) _ _ _ _ _ _ _ _ gmap_finmap). *)
      (*       intro P. *)
      (*       apply Heqn. *)
      (*       apply elem_of_list_In. *)
      (*       apply in_map_iff. *)
      (*       apply elem_of_list_In in P. *)
      (*       apply in_map_iff in P. *)
      (*       destruct P. *)
      (*       exists x. *)
      (*       destruct H2. *)
      (*       split;eauto. *)
      (*       apply in_map_iff. *)
      (*       apply in_map_iff in H3. *)
      (*       destruct H3. *)
      (*       exists x0. *)
      (*       destruct H3. *)
      (*       split;eauto. *)
      (*       rewrite -H3. *)
      (*       do 8 f_equal. *)
      (*       rewrite /get_vm_page_table update_page_table_batch_preserve_other_page_tables //. *)
      (*       destruct x. *)
      (*       simpl in H2;inversion H3. *)
      (*       by subst. *)
      (* Qed. *)

  Lemma insert_transaction_preserve_current_vm σ h trans:
   get_current_vm (insert_transaction σ h trans) = get_current_vm σ.
    Proof.
      rewrite /get_current_vm.
      f_equal.
Qed.

      Lemma insert_transaction_preserve_regs σ h trans:
   get_reg_gmap (insert_transaction σ h trans) = get_reg_gmap σ.
    Proof.
      rewrite /get_reg_gmap.
      f_equal.
Qed.
  Lemma insert_transaction_preserve_mem σ h trans:
   get_mem (insert_transaction σ h trans) = get_mem σ.
    Proof.
      rewrite /get_mem.
      f_equal.
Qed.
  Lemma insert_transaction_preserve_tx σ h trans:
   get_tx_agree (insert_transaction σ h trans) = get_tx_agree σ.
    Proof.
      rewrite /get_tx_agree.
      f_equal.
Qed.
  Lemma insert_transaction_preserve_rx1 σ h trans:
   get_rx_agree (insert_transaction σ h trans) = get_rx_agree σ.
    Proof.
      rewrite /get_rx_agree.
      f_equal.
Qed.
  Lemma insert_transaction_preserve_rx2 σ h trans:
   get_rx_gmap(insert_transaction σ h trans) = get_rx_gmap σ.
    Proof.
      rewrite /get_rx_gmap.
      f_equal.
Qed.
  Lemma insert_transaction_preserve_rx  σ h trans:
       (get_rx_agree (insert_transaction σ h trans), get_rx_gmap (insert_transaction σ h trans) ) =
                                               (get_rx_agree σ, get_rx_gmap σ).
  Proof.
    by rewrite insert_transaction_preserve_rx1 insert_transaction_preserve_rx2 .
  Qed.
  Lemma insert_transaction_preserve_owned σ h trans:
   get_owned_gmap (insert_transaction σ h trans) = get_owned_gmap σ.
    Proof.
      rewrite /get_owned_gmap.
      f_equal.
Qed.
   Lemma insert_transaction_preserve_access σ h trans:
   get_access_gmap (insert_transaction σ h trans) = get_access_gmap σ.
    Proof.
      rewrite /get_access_gmap.
      f_equal.
Qed.
     Lemma insert_transaction_preserve_excl σ h trans:
   get_excl_gmap (insert_transaction σ h trans) = get_excl_gmap σ.
    Proof.
      rewrite /get_excl_gmap.
      f_equal.
Qed.



 (* TODO more preserving rules. *)


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
   (get_mail_boxes σ1 !!! get_current_vm σ1).1 ≠ (to_pid_aligned a) ->
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
    destruct (decide (to_pid_aligned a = p)).
    done.
    done.
  Qed.


   Lemma str_ExecI σ1 r1 r2 w a:
   PC ≠ r1 ->  NZ ≠ r1 ->
   PC ≠ r2 -> NZ ≠ r2 ->
   (get_mail_boxes σ1 !!! get_current_vm σ1).2.1 ≠ (to_pid_aligned a) ->
   (get_reg σ1 r1) = Some w ->
   (get_reg σ1 r2) = Some a ->
   check_access_addr σ1 (get_current_vm σ1) a = true ->
   (str σ1 r1 r2)= (ExecI, (update_offset_PC (update_memory_unsafe σ1 a w) 1)).
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
    destruct (decide(to_pid_aligned a = p)).
    done.
    rewrite /update_memory /update_incr_PC /update_memory H6.
    done.
  Qed.

  Lemma cmp_word_ExecI  σ1 r w1 w2:
   PC ≠ r ->  NZ ≠ r ->
   (get_reg σ1 r) = Some w1 ->
   (cmp_word σ1 r w2)= (ExecI, (update_incr_PC (update_reg σ1 NZ
            (if (w1 <? w2)%f then W2 else if (w2 <? w1)%f then W0 else W1)))).
  Proof.
    intros.
    unfold cmp_word .
    destruct r;[contradiction|contradiction|].
    rewrite H1.
    simpl.
    destruct ((w1 <? w2)%f).
    rewrite <- (option_state_unpack_preserve_state_Some σ1
             (update_incr_PC (update_reg σ1 NZ W2)));eauto.
    destruct (w2 <? w1)%f.
    rewrite <- (option_state_unpack_preserve_state_Some σ1
             (update_incr_PC (update_reg σ1 NZ W0)));eauto.
    done.
  Qed.


   Lemma cmp_reg_ExecI  σ1 r1 w1 r2 w2:
   PC ≠ r1 ->  NZ ≠ r1 ->
   PC ≠ r2 ->  NZ ≠ r2 ->
   (get_reg σ1 r1) = Some w1 ->
   (get_reg σ1 r2) = Some w2 ->
   (cmp_reg σ1 r1 r2)= (ExecI, (update_incr_PC (update_reg σ1 NZ
            (if (w1 <? w2)%f then W2 else if (w2 <? w1)%f then W0 else W1)))).
  Proof.
    intros.
    unfold cmp_reg.
    destruct r1;[contradiction|contradiction|].
    destruct r2; [contradiction|contradiction|].
    rewrite H3 H4.
    simpl.
    destruct ((w1 <? w2)%f).
    rewrite <- (option_state_unpack_preserve_state_Some σ1
             (update_incr_PC (update_reg σ1 NZ W2)));eauto.
    destruct (w2 <? w1)%f.
    rewrite <- (option_state_unpack_preserve_state_Some σ1
             (update_incr_PC (update_reg σ1 NZ W0)));eauto.
    done.
  Qed.

  Lemma bne_ExecI  σ1 w1 r w2:
   PC ≠ r ->  NZ ≠ r ->
   (get_reg σ1 r) = Some w2 ->
   (get_reg σ1 NZ) = Some w1 ->
   (bne σ1 r)= (ExecI, if (w1 =? W1)%f then (update_incr_PC σ1) else (update_reg σ1 PC w2)).
  Proof.
    intros.
    unfold bne .
    destruct r;[contradiction|contradiction|].
    rewrite H1 H2.
    simpl.
    destruct (w1 =? W1)%f;eauto.
  Qed.

  Lemma br_ExecI  σ1 r w1:
   PC ≠ r ->  NZ ≠ r ->
   (get_reg σ1 r) = Some w1 ->
   (br σ1 r)= (ExecI,  (update_reg σ1 PC w1)).
  Proof.
    intros.
    unfold br.
    destruct r;[contradiction|contradiction|].
    rewrite H1 //.
  Qed.

