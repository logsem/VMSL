From HypVeri Require Import machine machine_extra tactics.
From HypVeri.algebra Require Import base.

Lemma update_ownership_batch_preserve_current_vm σ (ps: list PID) perm:
 get_current_vm (update_ownership_batch σ ps perm) = get_current_vm σ.
Proof. f_equal. Qed.

Lemma update_ownership_batch_preserve_regs σ (ps: list PID) perm:
 get_reg_gmap (update_ownership_batch σ ps perm) = get_reg_gmap σ.
Proof. f_equal. Qed.

Lemma update_ownership_batch_preserve_mem σ (ps: list PID) perm:
 get_mem (update_ownership_batch σ ps perm) = get_mem σ.
Proof. f_equal. Qed.

Lemma update_ownership_batch_preserve_tx σ (ps: list PID) perm:
 get_tx_agree (update_ownership_batch σ ps perm) = get_tx_agree σ.
Proof. f_equal. Qed.

Lemma update_ownership_batch_preserve_rx1 σ (ps: list PID) perm:
 get_rx_agree (update_ownership_batch σ ps perm) = get_rx_agree σ.
Proof. f_equal. Qed.

Lemma update_ownership_batch_preserve_rx2 σ (ps: list PID) perm:
 get_rx_gmap (update_ownership_batch σ ps perm) = get_rx_gmap σ.
Proof. f_equal. Qed.

Lemma update_ownership_batch_preserve_rx σ (ps: list PID) perm:
 (get_rx_agree (update_ownership_batch σ ps perm), get_rx_gmap (update_ownership_batch σ ps perm) ) =
 (get_rx_agree σ, get_rx_gmap σ).
Proof. by rewrite update_ownership_batch_preserve_rx1 update_ownership_batch_preserve_rx2 . Qed.

Lemma update_ownership_batch_preserve_trans σ (ps: list PID) perm:
 get_trans_gmap (update_ownership_batch σ ps perm) = get_trans_gmap σ.
Proof. f_equal. Qed.

Lemma update_ownership_batch_preserve_trans' σ (ps: list PID) perm:
 get_transactions (update_ownership_batch σ ps perm) = get_transactions σ.
Proof. f_equal. Qed.

Lemma update_ownership_batch_preserve_hpool σ (ps: list PID) perm:
 get_hpool_gset (update_ownership_batch σ ps perm) = get_hpool_gset σ.
Proof. f_equal. Qed.

Lemma update_ownership_batch_preserve_retri σ (ps: list PID) perm:
 get_retri_gmap (update_ownership_batch σ ps perm) = get_retri_gmap σ.
Proof. f_equal. Qed.

Lemma update_ownership_batch_preserve_other_page_tables σ ps perm i:
 i ≠ (get_current_vm σ) ->
 (get_page_tables (update_ownership_batch σ ps perm)) !!! i =
 (get_page_tables σ) !!! i.
Proof.
  intros.
  rewrite /get_page_tables /update_ownership_batch /update_ownership_global_batch /=.
  rewrite vlookup_insert_ne.
  rewrite /get_page_tables //.
  done.
Qed.

Lemma update_ownership_batch_preserve_access σ ps perm : get_access_gmap (update_ownership_batch σ ps perm) = (get_access_gmap σ).
Proof.
  rewrite /get_access_gmap /get_pagetable_gmap /update_ownership_batch /update_ownership_global_batch /=.
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
  rewrite H0 H1 /get_pagetable_gset.
  do 5 f_equal.
  rewrite /get_vm_page_table /get_page_tables /=.
  destruct (decide (get_current_vm σ = x0)).
  subst x0.
  rewrite vlookup_insert //.
  rewrite vlookup_insert_ne //.
Qed.

Lemma update_ownership_batch_preserve_excl σ ps perm : get_excl_gmap (update_ownership_batch σ ps perm) = (get_excl_gmap σ).
Proof.
  rewrite /get_excl_gmap /get_pagetable_gmap /update_ownership_batch /update_ownership_global_batch /=.
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
  rewrite H0 H1 /get_pagetable_gset.
  do 5 f_equal.
  rewrite /get_vm_page_table /get_page_tables /=.
  destruct (decide (get_current_vm σ = x0)).
  subst x0.
  rewrite vlookup_insert //.
  rewrite vlookup_insert_ne //.
Qed.


Ltac rewrite_ownership_all :=
  match goal with
  | |- _ =>
    try rewrite -> update_ownership_batch_preserve_current_vm;
    try rewrite -> update_ownership_batch_preserve_regs;
    try rewrite -> update_ownership_batch_preserve_mem;
    try rewrite -> update_ownership_batch_preserve_tx;
    try rewrite -> update_ownership_batch_preserve_rx1;
    try rewrite -> update_ownership_batch_preserve_rx2;
    try rewrite -> update_ownership_batch_preserve_trans;
    try rewrite -> update_ownership_batch_preserve_trans';
    try rewrite -> update_ownership_batch_preserve_hpool;
    try rewrite -> update_ownership_batch_preserve_retri
  end.


Lemma update_access_batch_preserve_current_vm σ (ps: list PID) perm:
 get_current_vm (update_access_batch σ ps perm) = get_current_vm σ.
Proof. f_equal. Qed.

Lemma update_access_batch_preserve_regs σ (ps: list PID) perm:
 get_reg_gmap (update_access_batch σ ps perm) = get_reg_gmap σ.
Proof. f_equal. Qed.

Lemma update_access_batch_preserve_mem σ (ps: list PID) perm:
 get_mem (update_access_batch σ ps perm) = get_mem σ.
Proof. f_equal. Qed.

Lemma update_access_batch_preserve_tx σ (ps: list PID) perm:
 get_tx_agree (update_access_batch σ ps perm) = get_tx_agree σ.
Proof. f_equal. Qed.

Lemma update_access_batch_preserve_rx1 σ (ps: list PID) perm:
 get_rx_agree (update_access_batch σ ps perm) = get_rx_agree σ.
Proof. f_equal. Qed.

Lemma update_access_batch_preserve_rx2 σ (ps: list PID) perm:
 get_rx_gmap (update_access_batch σ ps perm) = get_rx_gmap σ.
Proof. f_equal. Qed.

Lemma update_access_batch_preserve_rx σ (ps: list PID) perm:
 (get_rx_agree (update_access_batch σ ps perm), get_rx_gmap (update_access_batch σ ps perm) ) =
 (get_rx_agree σ, get_rx_gmap σ).
Proof. by rewrite update_access_batch_preserve_rx1 update_access_batch_preserve_rx2. Qed.

Lemma update_access_batch_preserve_trans σ (ps: list PID) perm:
 get_trans_gmap (update_access_batch σ ps perm) = get_trans_gmap σ.
Proof. f_equal. Qed.

Lemma update_access_batch_preserve_trans' σ (ps: list PID) perm:
 get_transactions (update_access_batch σ ps perm) = get_transactions σ.
Proof. f_equal. Qed.

Lemma update_access_batch_preserve_hpool σ (ps: list PID) perm:
 get_hpool_gset (update_access_batch σ ps perm) = get_hpool_gset σ.
Proof. f_equal. Qed.

Lemma update_access_batch_preserve_retri σ (ps: list PID) perm:
 get_retri_gmap (update_access_batch σ ps perm) = get_retri_gmap σ.
Proof. f_equal. Qed.

Lemma update_access_batch_preserve_other_page_tables σ ps perm i:
 i ≠ (get_current_vm σ) ->
 (get_page_tables (update_access_batch σ ps perm)) !!! i =
 (get_page_tables σ) !!! i.
Proof.
  intros.
  rewrite /get_page_tables /update_access_batch /update_access_global_batch /=.
  rewrite vlookup_insert_ne.
  rewrite /get_page_tables //.
  done.
Qed.

Lemma update_access_batch_preserve_ownerships σ ps perm :
 (get_owned_gmap (update_access_batch σ ps perm)) = (get_owned_gmap σ).
Proof.
  rewrite /get_owned_gmap /get_pagetable_gmap /update_access_batch /update_access_global_batch /=.
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
  rewrite H0 H1 /get_pagetable_gset.
  do 5 f_equal.
  rewrite /get_vm_page_table /get_page_tables /=.
  destruct (decide (get_current_vm σ = x0)).
  subst x0.
  rewrite vlookup_insert //.
  rewrite vlookup_insert_ne //.
Qed.


(* TODO rename hypotheses. *)
Lemma update_access_batch_preserve_excl {sps sexcl:gset _} σ ps:
 sps = (list_to_set ps)->
 get_excl_gmap σ !! (get_current_vm σ) = Some sexcl ->
 sps ## sexcl ->
 (get_excl_gmap (update_access_batch σ ps SharedAccess)) = (get_excl_gmap σ).
Proof.
  rewrite /get_excl_gmap /get_pagetable_gmap.
  intros.
  f_equal.
  apply (list_eq_same_length _ _ vm_count).
  - rewrite map_length.
    apply length_list_of_vmids.
  - rewrite map_length.
    apply length_list_of_vmids.
  - intros ? ? ? Hlt Hl1 Hl2.
    rewrite list_lookup_fmap /=in Hl1.
    pose proof (lookup_list_of_vmids i Hlt) as Hv.
    rewrite Hv /=in Hl1.
    inversion Hl1.
    rewrite list_lookup_fmap /=in Hl2.
    rewrite Hv /= in Hl2.
    inversion Hl2.
    f_equal.
    apply elem_of_list_to_map_2 in H0.
    apply elem_of_list_In in H0.
    apply in_map_iff in H0.
    destruct H0 as [?[Heq _]].
    inversion Heq.
    subst x0.
    set (v:= (nat_to_fin Hlt)) in *.
    clear Hl1 Hl2 H3 H4 Heq.
    destruct (decide ((get_current_vm σ) = v)).
    + rewrite e in H5. rewrite H5.
      rewrite /get_pagetable_gset /=.
      apply set_eq.
      intros.
      split.
      *  rewrite elem_of_list_to_set.
         intro.
         apply elem_of_list_In in H0.
         apply in_map_iff in H0.
         destruct H0 as [? [<- Hin]].
         apply elem_of_list_In in Hin.
         destruct x1.
         apply elem_of_map_to_list in Hin.
         apply map_filter_lookup_Some in Hin.
         destruct Hin.
         rewrite -H5 /get_pagetable_gset /=.
         rewrite elem_of_list_to_set.
         apply elem_of_list_In.
         apply in_map_iff.
         exists (p,a).
         split;auto.
         apply elem_of_list_In.
         apply elem_of_map_to_list.
         apply map_filter_lookup_Some.
         split;auto.
         rewrite /get_vm_page_table /get_page_tables /= in H0.
         rewrite -e in H0.
         rewrite vlookup_insert /=in H0.
         generalize dependent  sps.
         induction ps.
         cbn in H0.
         rewrite -e //.
         intros.
         cbn in H0.
         destruct (decide (a0 = p)).
         subst a0.
         rewrite lookup_insert in H0.
         inversion H0.
         subst a.
         cbn in H2.
         done.
         rewrite lookup_insert_ne in H0.
         apply (IHps H0 (list_to_set ps));auto.
         cbn in H.
         subst sps.
         apply disjoint_union_l  in H1.
         destruct H1.
         assumption.
         done.
      *  rewrite elem_of_list_to_set.
         intro.
         rewrite -H5 in H0.
         rewrite /get_pagetable_gset /get_vm_page_table /get_page_tables /= in H0.
         apply elem_of_list_to_set in H0.
         apply elem_of_list_In in H0.
         apply in_map_iff in H0.
         destruct H0 as [? [<- Hin]].
         apply elem_of_list_In in Hin.
         destruct x1.
         apply elem_of_map_to_list in Hin.
         apply map_filter_lookup_Some in Hin.
         destruct Hin.
         apply elem_of_list_In.
         apply in_map_iff.
         exists (p,a).
         split;auto.
         apply elem_of_list_In.
         apply elem_of_map_to_list.
         apply map_filter_lookup_Some.
         split;auto.
         rewrite /get_vm_page_table /get_page_tables /=.
         rewrite -e.
         rewrite vlookup_insert /=.
         generalize dependent  sps.
         induction ps.
         intros.
         cbn.
         rewrite e //.
         intros.
         cbn.
         destruct (decide (a0 = p)).
         -- assert (Hpin: p ∈ sexcl ).
            {
              rewrite -H5.
              rewrite /get_pagetable_gset /get_vm_page_table /get_page_tables /=.
              apply elem_of_list_to_set.
              apply elem_of_list_In.
              apply in_map_iff.
              exists (p,a).
              split;auto.
              apply elem_of_list_In.
              apply elem_of_map_to_list.
              apply map_filter_lookup_Some.
              split;done.
            }
            subst a0.
            assert (Hpin': p ∈ sps).
            {
              set_solver.
            }
            set_solver.
         --
         rewrite lookup_insert_ne;auto.
         apply (IHps (list_to_set ps));auto.
         cbn in H.
         subst sps.
         apply disjoint_union_l  in H1.
         destruct H1.
         assumption.
    + rewrite /get_pagetable_gset /=.
      do 3 f_equal.
      rewrite /get_vm_page_table /get_page_tables /update_access_batch /update_access_global_batch /=.
      rewrite vlookup_insert_ne;auto.
    Qed.



Ltac rewrite_access_all :=
  match goal with
  | |- _ =>
    try rewrite -> update_access_batch_preserve_current_vm;
    try rewrite -> update_access_batch_preserve_regs;
    try rewrite -> update_access_batch_preserve_mem;
    try rewrite -> update_access_batch_preserve_tx;
    try rewrite -> update_access_batch_preserve_rx1;
    try rewrite -> update_access_batch_preserve_rx2;
    try rewrite -> update_access_batch_preserve_trans;
    try rewrite -> update_access_batch_preserve_trans';
    try rewrite -> update_access_batch_preserve_hpool;
    try rewrite -> update_access_batch_preserve_retri
  end.



Lemma get_pagetable_gmap_checkb {Perm:Type} {σ i s} proj (checkb: Perm -> bool) p:
 (get_pagetable_gmap σ proj checkb) !! i = Some  s->
 (p ∈ s <->
  ∃ perm, (proj (get_vm_page_table σ i)) !! p =Some perm ∧ checkb perm = true).
Proof.
  intros.
  rewrite /get_access_gmap in H.
  apply (elem_of_list_to_map_2 _ i s) in H.
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

Lemma get_owned_gmap_is_owned {σ i sown} p:
 (get_owned_gmap σ) !! i = Some sown->
 (p ∈ sown <->
  ∃ perm, (get_vm_page_table σ i).1 !! p =Some perm ∧ is_owned perm = true).
Proof.
  intros.
  rewrite /get_owned_gmap in H.
    by apply get_pagetable_gmap_checkb.
Qed.

Lemma get_access_gmap_is_accessible {σ i sacc} p:
 (get_access_gmap σ) !! i = Some  sacc->
 (p ∈ sacc <->
  ∃ perm, (get_vm_page_table σ i).2 !! p =Some perm ∧ is_accessible perm = true).
Proof.
  intros.
  rewrite /get_access_gmap in H.
    by apply get_pagetable_gmap_checkb.
Qed.

Lemma get_excl_gmap_is_exclusive_true {σ i sexcl} p:
 (get_excl_gmap σ) !! i = Some  sexcl->
 (p ∈ sexcl<->
  ∃ perm, (get_vm_page_table σ i).2 !! p =Some perm ∧ is_exclusive perm = true).
Proof.
  intros.
  rewrite /get_excl_gmap in H.
    by apply get_pagetable_gmap_checkb.
Qed.

Lemma update_access_batch_update_pagetable_diff {σ i s} {sps:gset PID}
      (checkb: access->bool) (ps: list PID):
 sps = (list_to_set ps)->
 i = (get_current_vm σ) ->
 checkb NoAccess = false ->
 (get_pagetable_gmap σ (λ pt,pt.2) checkb) !! i = Some s ->
 (get_pagetable_gmap (update_access_batch σ ps NoAccess)  (λ pt,pt.2) checkb) =
 <[(get_current_vm σ):= s ∖ sps]>(get_pagetable_gmap σ (λ pt,pt.2) checkb).
Proof.
  intros Hsps Hi Hcheckb Hlookup.
  rewrite /get_pagetable_gmap.
  apply (@map_eq VMID (gmap VMID) _ _ _ _ _ _ _ _ gmap_finmap);eauto.
  intro.
  rewrite -Hi.
  destruct(decide (i0 = i)).
  - subst i0. rewrite lookup_insert.
    assert(Hgoal : list_to_set
                     (map (λ p : PID * access, p.1)
                          (map_to_list (filter (λ p : PID * access, checkb p.2 = true)
                                               (get_vm_page_table (update_access_batch σ ps NoAccess) i).2))) = s ∖ sps).
    { apply set_eq.
      intro.
      rewrite elem_of_list_to_set.
      split.
      * intros.
        inv_map_in.
        apply elem_of_list_In in H0.
        apply (elem_of_map_to_list' _ x0) in H0.
        apply map_filter_lookup_Some in H0.
        destruct H0 as [Hlookup' Hcheckbtrue].
        simplify_eq /=.
        rewrite /get_vm_page_table /get_page_tables /update_access_batch
                /update_access_global_batch //= in Hlookup'.
        rewrite vlookup_insert in Hlookup'.
        apply elem_of_difference.
        induction ps; simpl in *.
        -- split;[|set_solver].
           apply ((get_pagetable_gmap_checkb (λ pt,pt.2) checkb) x0.1 Hlookup).
           exists (x0.2).
           split;eauto.
        -- assert (Hneq: a ≠ x0.1).
           { destruct (decide (a=x0.1));eauto.
             subst a.
             rewrite lookup_insert in Hlookup'.
             inversion Hlookup'.
             rewrite -H0  Hcheckb // in Hcheckbtrue.
           }
           rewrite not_elem_of_union.
           assert (Himp : x0.1 ∈ s ∧ x0.1 ∉ ((list_to_set ps):gset PID)
                          ->(x0.1 ∈ s ∧ (x0.1 ∉ ({[a]}:gset PID)) ∧ x0.1 ∉ ((list_to_set ps):gset PID))).
           { intros. destruct H; split;eauto. split. set_solver. done. }
           apply Himp.
           apply IHps;eauto.
           rewrite lookup_insert_ne in Hlookup';done.
      * intros Hin.
        apply elem_of_difference in Hin.
        destruct Hin as [Hin Hnotin].
        apply ((get_pagetable_gmap_checkb (λ pt,pt.2) checkb) x Hlookup) in Hin;eauto.
        destruct Hin.
        destruct H.
        inv_map_in.
        exists (x,x0).
        split;eauto.
        apply elem_of_list_In .
        apply  elem_of_map_to_list.
        apply map_filter_lookup_Some.
        rewrite /get_vm_page_table /get_page_tables /update_access_batch
                /update_access_global_batch /=.
        rewrite -Hi vlookup_insert.
        split;eauto.
        generalize dependent sps.
        induction ps;simpl.
        done.
        intros.
        assert (Hneq: a ≠ x).
        { set_solver. }
        rewrite lookup_insert_ne;eauto.
        apply (IHps (list_to_set ps));eauto.
        set_solver.
    }
    apply (@elem_of_list_to_map_1' VMID (gmap VMID) _ _ _ _ _ _ _ _ gmap_finmap).
    + intros.
      inv_map_in.
      inversion H.
      do 3 f_equal.
      clear H3 H0 H.
      subst x.
      symmetry.
      apply Hgoal.
    + inv_map_in.
      exists i.
      split;[|apply in_list_of_vmids].
      do 4 f_equal.
      apply Hgoal.
  - rewrite (lookup_insert_ne _ i i0 _);eauto.
    set (l:= (map (λ v,  (v, get_pagetable_gset (update_access_batch σ ps NoAccess) v (λ pt : page_table, pt.2) checkb)) list_of_vmids)) in *.
    destruct (list_to_map l !! i0) eqn:Heqn.
    + apply (elem_of_list_to_map_2 l i0 g) in Heqn.
      apply elem_of_list_In in Heqn.
      apply in_map_iff in Heqn.
      inversion Heqn;clear Heqn.
      destruct H as [H HIn];inversion H;subst;clear H.
      symmetry.
      eapply elem_of_list_to_map_1'.
      * intros.
        inv_map_in.
        inversion H.
        rewrite /get_pagetable_gset.
        do 4 f_equal.
        rewrite /get_vm_page_table update_access_batch_preserve_other_page_tables //.
      * inv_map_in.
        exists i0.
        split;eauto.
        rewrite /get_pagetable_gset.
        do 6 f_equal.
        rewrite /get_vm_page_table update_access_batch_preserve_other_page_tables //.
    + apply (@not_elem_of_list_to_map_2 VMID (gmap VMID) _ _ _ _ _ _ _ _ gmap_finmap) in Heqn.
      symmetry.
      apply not_elem_of_list_to_map_1.
      intro P.
      apply Heqn.
      apply elem_of_list_In.
      apply in_map_iff.
      apply elem_of_list_In in P.
      apply in_map_iff in P.
      destruct P.
      exists x.
      destruct H.
      split;eauto.
      apply in_map_iff.
      apply in_map_iff in H0.
      destruct H0.
      exists x0.
      destruct H0.
      split;eauto.
      rewrite -H0 /get_pagetable_gset.
      do 6 f_equal.
      rewrite /get_vm_page_table update_access_batch_preserve_other_page_tables //.
      destruct x.
      inversion H0.
        by subst.
Qed.

Lemma update_access_batch_update_access_diff{σ i sacc} {sps:gset PID} (ps: list PID):
 sps = (list_to_set ps)->
 i = (get_current_vm σ) ->
 (get_access_gmap σ) !! i = Some sacc ->
 get_access_gmap (update_access_batch σ ps NoAccess) =
 <[(get_current_vm σ):= (sacc∖ sps)]>(get_access_gmap σ).
Proof.
  intros.
  apply (@update_access_batch_update_pagetable_diff _ i);eauto.
Qed.

Lemma update_access_batch_update_excl_diff{σ i sexcl} {sps:gset PID} (ps: list PID):
 sps = (list_to_set ps)->
 i = (get_current_vm σ) ->
 (get_excl_gmap σ) !! i = Some sexcl ->
 get_excl_gmap (update_access_batch σ ps NoAccess) =
 <[(get_current_vm σ):= (sexcl ∖ sps)]>(get_excl_gmap σ).
Proof.
  intros.
  apply (@update_access_batch_update_pagetable_diff _ i);eauto.
Qed.

Lemma update_ownership_batch_update_pagetable_union {σ i sown} {sps:gset PID} (ps: list PID):
 sps = (list_to_set ps)->
 i = (get_current_vm σ)->
 (get_owned_gmap σ) !! i = Some sown ->
 get_owned_gmap (update_ownership_batch σ ps Owned) =
 <[i:= sown ∪ sps]>(get_owned_gmap σ).
Proof.
  intros.
  rewrite /get_owned_gmap /get_pagetable_gmap.
  apply (@map_eq VMID (gmap VMID) _ _ _ _ _ _ _ _ gmap_finmap);eauto.
  intro.
  destruct(decide (i0 = i)).
  - subst i0. rewrite lookup_insert.
    assert(Hgoal: get_pagetable_gset (update_ownership_batch σ ps Owned) i (λ pt : page_table, pt.1) is_owned
                  = sown ∪ sps).
    {
      apply set_eq.
      intro.
      rewrite elem_of_list_to_set.
      split.
      * intros.
        inv_map_in.
        apply elem_of_list_In in H3.
        apply (elem_of_map_to_list' _ x0) in H3.
        apply map_filter_lookup_Some in H3.
        destruct H3.
        simplify_eq /=.
        rewrite /get_vm_page_table /get_page_tables /update_ownership_batch
                /update_ownership_global_batch //= in H3.
        rewrite vlookup_insert in H3.
        apply elem_of_union.
        induction ps; simpl in *.
        -- left.
           apply (get_owned_gmap_is_owned x0.1 H1).
           exists (x0.2).
           split;eauto.
        -- destruct (decide (a=x0.1)).
           right;set_solver.
           assert (Himp :(x0.1 ∈ sown ∨ x0.1 ∈ ((list_to_set ps):gset PID))
                         ->(x0.1 ∈ sown ∨ x0.1 ∈ {[a]} ∪ ((list_to_set ps):gset PID))).
           { intros. destruct H. left;done. right; set_solver. }
           apply Himp.
           apply IHps;eauto.
           rewrite lookup_insert_ne in H3;done.
      * intros.
        apply elem_of_union in H2.
        destruct H2.
        apply (get_owned_gmap_is_owned x H1) in H2;eauto.
        destruct H2.
        destruct H2.
        inv_map_in.
        exists (x,x0).
        split;eauto.
        apply elem_of_list_In .
        apply elem_of_map_to_list.
        apply map_filter_lookup_Some.
        rewrite /get_vm_page_table /get_page_tables /update_ownership_batch
                /update_ownership_global_batch /=.
        rewrite -H0 vlookup_insert.
        destruct H1;split;eauto.
        generalize dependent sps.
        induction ps;simpl in *.
        done.
        intros.
        destruct (decide (x=a)).
        subst a.
        rewrite lookup_insert.
        rewrite /is_owned in H3.
        destruct x0;eauto.
        done.
        rewrite lookup_insert_ne;eauto.
        inv_map_in.
        exists (x,Owned).
        split;eauto.
        apply elem_of_list_In .
        apply elem_of_map_to_list.
        apply map_filter_lookup_Some.
        rewrite /get_vm_page_table /get_page_tables /update_ownership_batch
                /update_ownership_global_batch /=.
        split;eauto.
        rewrite -H0 vlookup_insert //=.
        generalize dependent sps.
        induction ps;simpl in *.
        intros.
        set_solver.
        intros.
        destruct (decide (x=a)).
        subst a.
        rewrite lookup_insert //.
        rewrite lookup_insert_ne;eauto.
        apply (IHps (list_to_set ps));eauto.
        set_solver.
    }
    apply (@elem_of_list_to_map_1' VMID (gmap VMID) _ _ _ _ _ _ _ _ gmap_finmap).
    + intros.
      inv_map_in.
      inversion H2.
      do 3 f_equal.
      clear H6 H3 H2.
      subst x.
      symmetry.
      apply Hgoal.
    + inv_map_in.
      exists i.
      split;[|apply in_list_of_vmids].
      do 4 f_equal.
      apply Hgoal.
  - rewrite (lookup_insert_ne _ i i0 _);eauto.
    set (l:= (map
                (λ v,
                 (v, get_pagetable_gset (update_ownership_batch σ ps Owned) v (λ pt : page_table, pt.1) is_owned))
                list_of_vmids)) in *.
    destruct (list_to_map l !! i0) eqn:Heqn.
    + apply (elem_of_list_to_map_2 l i0 g) in Heqn.
      apply elem_of_list_In in Heqn.
      apply in_map_iff in Heqn.
      inversion Heqn;clear Heqn.
      destruct H2 as [H3 HIn];inversion H3;subst;clear H3.
      symmetry.
      apply elem_of_list_to_map_1'.
      *  intros.
         inv_map_in.
         inversion H.
         rewrite /get_pagetable_gset.
         do 5 f_equal.
         rewrite /get_vm_page_table update_ownership_batch_preserve_other_page_tables //.
      * inv_map_in.
        exists i0.
        split;eauto.
        rewrite /get_pagetable_gset.
        do 6 f_equal.
        rewrite /get_vm_page_table update_ownership_batch_preserve_other_page_tables //.
    + apply (@not_elem_of_list_to_map_2 VMID (gmap VMID) _ _ _ _ _ _ _ _ gmap_finmap) in Heqn.
      symmetry.
      apply not_elem_of_list_to_map_1.
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
      rewrite -H3 /get_pagetable_gset.
      do 6 f_equal.
      rewrite /get_vm_page_table update_ownership_batch_preserve_other_page_tables //.
      destruct x.
      simpl in H2;inversion H3.
        by subst.
Qed.

Lemma update_exclusive_batch_update_pagetable_union {σ i sexcl} {sps:gset PID} (ps: list PID):
 sps = (list_to_set ps) ->
 i = (get_current_vm σ) ->
 (get_excl_gmap σ) !! i = Some (sexcl) ->
 get_excl_gmap (update_access_batch σ ps ExclusiveAccess) =
 <[i:= (sexcl ∪ sps)]>(get_excl_gmap σ).
Proof.
  intros.
  rewrite /get_excl_gmap /get_pagetable_gmap.
  apply (@map_eq VMID (gmap VMID) _ _ _ _ _ _ _ _ gmap_finmap); eauto.
  intro.
  destruct(decide (i0 = i)).
  - subst i0. rewrite lookup_insert.
    assert(Hgoal: get_pagetable_gset (update_access_batch σ ps ExclusiveAccess) i (λ pt : page_table, pt.2) is_exclusive
                  = sexcl ∪ sps).
    {
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
        rewrite /get_vm_page_table /get_page_tables /update_access_batch
                /update_access_global_batch //= in H3.
        rewrite vlookup_insert in H3.
        apply elem_of_union.
        induction ps; simpl in *.
        -- left.
           apply (get_excl_gmap_is_exclusive_true x0.1 H1).
           exists (x0.2).
           split;eauto.
        -- destruct (decide (a=x0.1)).
           right;set_solver.
           assert (Himp :(x0.1 ∈ sexcl ∨ x0.1 ∈ ((list_to_set ps):gset PID))
                         ->(x0.1 ∈ sexcl ∨ x0.1 ∈ {[a]} ∪ ((list_to_set ps):gset PID))).
           { intros. destruct H. left;done. right; set_solver. }
           apply Himp.
           apply IHps;eauto.
           rewrite lookup_insert_ne in H3;done.
      * intros.
        apply elem_of_union in H2.
        destruct H2.
        apply (get_excl_gmap_is_exclusive_true x H1) in H2;eauto.
        destruct H2.
        destruct H2.
        inv_map_in.
        exists (x,x0).
        split;eauto.
        apply elem_of_list_In .
        apply elem_of_map_to_list.
        apply map_filter_lookup_Some.
        rewrite /get_vm_page_table /get_page_tables /update_access_batch
                /update_access_global_batch /=.
        rewrite -H0 vlookup_insert.
        destruct H1;split;eauto.
        generalize dependent sps.
        induction ps;simpl in *.
        done.
        intros.
        destruct (decide (x=a)).
        subst a.
        rewrite lookup_insert.
        rewrite /is_exclusive in H3.
        destruct x0;try done.
        rewrite lookup_insert_ne;eauto.
        inv_map_in.
        exists (x, ExclusiveAccess).
        split;eauto.
        apply elem_of_list_In .
        apply elem_of_map_to_list.
        apply map_filter_lookup_Some.
        rewrite /get_vm_page_table /get_page_tables /update_access_batch
                /update_access_global_batch /=.
        split;eauto.
        rewrite -H0 vlookup_insert //=.
        generalize dependent sps.
        induction ps;simpl in *.
        intros.
        set_solver.
        intros.
        destruct (decide (x=a)).
        subst a.
        rewrite lookup_insert //.
        rewrite lookup_insert_ne;eauto.
        apply (IHps (list_to_set ps));eauto.
        set_solver.
    }
    apply (@elem_of_list_to_map_1' VMID (gmap VMID) _ _ _ _ _ _ _ _ gmap_finmap).
    + intros.
      inv_map_in.
      inversion H2.
      do 3 f_equal.
      clear H6 H3 H2.
      subst x.
      symmetry.
      apply Hgoal.
    + inv_map_in.
      exists i.
      split;[|apply in_list_of_vmids].
      do 4 f_equal.
      apply Hgoal.
  - rewrite (lookup_insert_ne _ i i0 _);eauto.
    set (l:= (map (λ v, (v,
                         get_pagetable_gset (update_access_batch σ ps ExclusiveAccess) v (λ pt : page_table, pt.2) is_exclusive))
                  list_of_vmids)) in *.
    destruct (list_to_map l !! i0) eqn:Heqn.
    + apply (elem_of_list_to_map_2 l i0 g) in Heqn.
      apply elem_of_list_In in Heqn.
      apply in_map_iff in Heqn.
      inversion Heqn;clear Heqn.
      destruct H2 as [H3 HIn];inversion H3;subst;clear H3.
      symmetry.
      apply elem_of_list_to_map_1'.
      *  intros.
         inv_map_in.
         inversion H.
         rewrite /get_pagetable_gset.
         do 5 f_equal.
         rewrite /get_vm_page_table update_access_batch_preserve_other_page_tables //.
      * inv_map_in.
        exists i0.
        split;eauto.
        rewrite /get_pagetable_gset.
        do 6 f_equal.
        rewrite /get_vm_page_table update_access_batch_preserve_other_page_tables //.
    + apply (@not_elem_of_list_to_map_2 VMID (gmap VMID) _ _ _ _ _ _ _ _ gmap_finmap) in Heqn.
      symmetry.
      apply not_elem_of_list_to_map_1.
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
      rewrite -H3 /get_pagetable_gset.
      do 6 f_equal.
      rewrite /get_vm_page_table update_access_batch_preserve_other_page_tables //.
      destruct x.
      simpl in H2;inversion H3.
        by subst.
Qed.

Lemma update_access_batch_update_pagetable_union {σ i sacc a'} {sps:gset PID} (ps: list PID):
 sps = (list_to_set ps) ->
 i = (get_current_vm σ) ->
 (get_access_gmap σ) !! i = Some (sacc) ->
 sps ## sacc ->
 is_accessible a' = true ->
 get_access_gmap (update_access_batch σ ps a') =
 <[i:= (sacc ∪ sps)]>(get_access_gmap σ).
Proof.
  intros H H0 H1 P Q.
  rewrite /get_access_gmap /get_pagetable_gmap.
  apply (@map_eq VMID (gmap VMID) _ _ _ _ _ _ _ _ gmap_finmap); eauto.
  intro.
  destruct(decide (i0 = i)).
  - subst i0. rewrite lookup_insert.
    assert(Hgoal: get_pagetable_gset (update_access_batch σ ps a') i (λ pt : page_table, pt.2) is_accessible
                  = sacc ∪ sps).
    {
      apply set_eq.
      intro.
      rewrite elem_of_list_to_set.
      split.
      * intros.
        inv_map_in.
        apply elem_of_list_In in H3.
        apply (elem_of_map_to_list' _ x0) in H3.
        apply map_filter_lookup_Some in H3.
        destruct H3.
        simplify_eq /=.
        rewrite /get_vm_page_table /get_page_tables /update_access_batch
                /update_access_global_batch //= in H3.
        rewrite vlookup_insert in H3.
        apply elem_of_union.
        induction ps; simpl in *.
        -- left.
           apply (get_access_gmap_is_accessible x0.1 H1).
           exists (x0.2).
           split;eauto.
        -- destruct (decide (a=x0.1)).
           right;set_solver.
           assert (Himp :(x0.1 ∈ sacc ∨ x0.1 ∈ ((list_to_set ps):gset PID))
                         ->(x0.1 ∈ sacc ∨ x0.1 ∈ {[a]} ∪ ((list_to_set ps):gset PID))).
           { intros. destruct H. left;done. right; set_solver. }
           apply Himp.
           apply IHps;eauto.
           rewrite ->disjoint_union_l in P.
           destruct P; done.
           rewrite lookup_insert_ne in H3;done.
      * intros.
        apply elem_of_union in H2.
        destruct H2.
        pose proof H2 as H2'.
        apply (get_access_gmap_is_accessible x H1) in H2;eauto.
        destruct H2.
        destruct H2.
        inv_map_in.
        exists (x,x0).
        split;eauto.
        apply elem_of_list_In .
        apply elem_of_map_to_list.
        apply map_filter_lookup_Some.
        rewrite /get_vm_page_table /get_page_tables /update_access_batch
                /update_access_global_batch /=.
        rewrite -H0 vlookup_insert.
        destruct H1;split;eauto.
        simpl.
        generalize dependent sps.
        induction ps;simpl in *.
        done.
        intros.
        destruct (decide (x=a)).
        subst a.
        rewrite lookup_insert.
        rewrite /is_accessible in H3.
        destruct x0;try done.
        rewrite ->elem_of_disjoint in P.
        exfalso.
        apply P with x; set_solver.
        rewrite ->elem_of_disjoint in P.
        exfalso.
        apply P with x; set_solver.
        rewrite lookup_insert_ne; eauto.
        apply IHps with (list_to_set ps); auto.
        apply disjoint_union_l with {[a]}.
        rewrite H in P; auto.
        inv_map_in.
        exists (x, a').
        split;eauto.
        apply elem_of_list_In .
        apply elem_of_map_to_list.
        apply map_filter_lookup_Some.
        rewrite /get_vm_page_table /get_page_tables /update_access_batch
                /update_access_global_batch /=.
        split;eauto.
        rewrite -H0 vlookup_insert //=.
        generalize dependent sps.
        induction ps;simpl in *.
        intros.
        set_solver.
        intros.
        destruct (decide (x=a)).
        subst a.
        rewrite lookup_insert //.
        rewrite lookup_insert_ne;eauto.
        apply (IHps (list_to_set ps));eauto.
        set_solver.
        set_solver.
    }
    apply (@elem_of_list_to_map_1' VMID (gmap VMID) _ _ _ _ _ _ _ _ gmap_finmap).
    + intros.
      inv_map_in.
      inversion H2.
      do 3 f_equal.
      clear H6 H3 H2.
      subst x.
      symmetry.
      apply Hgoal.
    + inv_map_in.
      exists i.
      split;[|apply in_list_of_vmids].
      do 4 f_equal.
      apply Hgoal.
  - rewrite (lookup_insert_ne _ i i0 _);eauto.
    set (l:= (map (λ v,
                   (v, get_pagetable_gset (update_access_batch σ ps a') v (λ pt : page_table, pt.2) is_accessible))
                  list_of_vmids)) in *.
    destruct (list_to_map l !! i0) eqn:Heqn.
    + apply (elem_of_list_to_map_2 l i0 g) in Heqn.
      apply elem_of_list_In in Heqn.
      apply in_map_iff in Heqn.
      inversion Heqn;clear Heqn.
      destruct H2 as [H3 HIn];inversion H3;subst;clear H3.
      symmetry.
      apply elem_of_list_to_map_1'.
      *  intros.
         inv_map_in.
         inversion H.
         rewrite /get_pagetable_gset.
         do 5 f_equal.
         rewrite /get_vm_page_table update_access_batch_preserve_other_page_tables //.
      * inv_map_in.
        exists i0.
        split;eauto.
        rewrite /get_pagetable_gset.
        do 6 f_equal.
        rewrite /get_vm_page_table update_access_batch_preserve_other_page_tables //.
    + apply (@not_elem_of_list_to_map_2 VMID (gmap VMID) _ _ _ _ _ _ _ _ gmap_finmap) in Heqn.
      symmetry.
      apply not_elem_of_list_to_map_1.
      intro R.
      apply Heqn.
      apply elem_of_list_In.
      apply in_map_iff.
      apply elem_of_list_In in R.
      apply in_map_iff in R.
      destruct R.
      exists x.
      destruct H2.
      split;eauto.
      apply in_map_iff.
      apply in_map_iff in H3.
      destruct H3.
      exists x0.
      destruct H3.
      split;eauto.
      rewrite -H3 /get_pagetable_gset.
      do 6 f_equal.
      rewrite /get_vm_page_table update_access_batch_preserve_other_page_tables //.
      destruct x.
      simpl in H2;inversion H3.
        by subst.
Qed.
