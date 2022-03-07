From HypVeri Require Import machine machine_extra tactics.
From HypVeri.algebra Require Import base base_extra pagetable.

Section pagetable_extra.

Context `{HyperConst : HypervisorConstants}.

Implicit Type σ : state.

Lemma upd_is_strong_assoc_comm (X Y:gset PID) upd (i:VMID):
∀ (x1 x2 : PID) (b' : page_table),
    x1 ∈ X ∪ Y
    → x2 ∈ X ∪ Y
      → x1 ≠ x2
        → match match b' !! x2 with
                | Some perm0 => <[x2:=upd perm0 i]> b'
                | None => b'
                end !! x1 with
          | Some perm0 => <[x1:=upd perm0 i]> match b' !! x2 with
                                              | Some perm1 => <[x2:=upd perm1 i]> b'
                                              | None => b'
                                              end
          | None => match b' !! x2 with
                    | Some perm0 => <[x2:=upd perm0 i]> b'
                    | None => b'
                    end
          end =
          match match b' !! x1 with
                | Some perm0 => <[x1:=upd perm0 i]> b'
                | None => b'
                end !! x2 with
          | Some perm0 => <[x2:=upd perm0 i]> match b' !! x1 with
                                              | Some perm1 => <[x1:=upd perm1 i]> b'
                                              | None => b'
                                              end
          | None => match b' !! x1 with
                    | Some perm0 => <[x1:=upd perm0 i]> b'
                    | None => b'
                    end
          end.
Proof.
  intros.
  destruct (b' !! x2) as [p2|] eqn: Hlookup2, (b' !! x1) as [p1|] eqn:Hlookup1;
    try destruct p1; try destruct p2 ; rewrite ?lookup_insert_ne ?Hlookup1 ?Hlookup2 //;last eauto.
  apply (insert_commute b').
  done.
Qed.

Lemma p_upd_own_current_vm σ i (ps: gset PID):
 get_current_vm (update_page_table_global update_ownership σ i ps) = get_current_vm σ.
Proof. f_equal. Qed.

Lemma p_upd_own_regs σ i (ps: gset PID):
 get_reg_files (update_page_table_global update_ownership σ i ps) = get_reg_files σ.
Proof. f_equal. Qed.

Lemma p_upd_own_mem σ i (ps: gset PID):
 get_mem (update_page_table_global update_ownership σ i ps) = get_mem σ.
Proof. f_equal. Qed.

Lemma p_upd_pgt_mb σ i (ps: gset PID):
 get_mail_boxes (update_page_table_global update_ownership σ i ps) = get_mail_boxes σ.
Proof. f_equal. Qed.

Lemma p_upd_own_trans σ i (ps: gset PID):
 get_transactions (update_page_table_global update_ownership σ i ps) = get_transactions σ.
Proof. f_equal. Qed.

Lemma p_upd_own_acc σ i ps:
((get_access_gmap (update_page_table_global update_ownership σ i ps)):gmap _ _) = ((get_access_gmap σ): gmap _ _).
Proof.
  rewrite /get_access_gmap  /=.
  generalize dependent σ.1.1.1.2.
  induction ps as [|p ps] using set_ind_L.
  done.
  intro.
  rewrite set_fold_disj_union_strong.
  {
    rewrite set_fold_singleton /=.
  set pgt' := (X in X !! p).
  destruct (pgt' !! p) eqn:Hlookup.
  { destruct p1.
    rewrite IHps /=.
    f_equal.
    apply (list_eq_same_length _ _ vm_count).
    rewrite fmap_length.
    apply length_list_of_vmids.
    rewrite fmap_length.
    apply length_list_of_vmids.
    intros ? ? ? ? H0 H1.
    apply list_lookup_fmap_inv in H0, H1.
    destruct H0, H1.
    destruct H0, H1.
    rewrite H3 in H4.
    inversion H4. subst x1.
    clear H4.
    rewrite H0 H1.
    do 4 f_equal.
    destruct p1.
    destruct o;
    rewrite fmap_insert insert_id //.
    all: rewrite /= lookup_fmap Hlookup //.
  }
  rewrite IHps //.
  }
  apply upd_is_strong_assoc_comm.
  { set_solver + H. }
Qed.

Lemma p_grnt_acc_current_vm σ i (ps: gset PID) :
 get_current_vm (update_page_table_global grant_access σ i ps) = get_current_vm σ.
Proof. f_equal. Qed.

Lemma p_grnt_acc_regs σ i (ps: gset PID):
 get_reg_files (update_page_table_global grant_access σ i ps) = get_reg_files σ.
Proof. f_equal. Qed.

Lemma p_grnt_acc_mem σ i (ps: gset PID):
 get_mem (update_page_table_global grant_access σ i ps) = get_mem σ.
Proof. f_equal. Qed.

Lemma p_grnt_acc_mb σ i (ps: gset PID):
 get_mail_boxes (update_page_table_global grant_access σ i ps) = get_mail_boxes σ.
Proof. f_equal. Qed.

Lemma p_grnt_acc_trans σ i (ps: gset PID):
 get_transactions (update_page_table_global grant_access σ i ps) = get_transactions σ.
Proof. f_equal. Qed.

Lemma p_grnt_acc_own σ i ps:
 (get_own_gmap (update_page_table_global grant_access σ i ps)) = (get_own_gmap σ).
Proof.
  rewrite /get_own_gmap /=.
  generalize dependent σ.1.1.1.2.
  induction ps as [|p ps] using set_ind_L.
  done.
  intro.
  rewrite set_fold_disj_union_strong.
  {
    rewrite set_fold_singleton /=.
  set pgt' := (X in X !! p).
  destruct (pgt' !! p) eqn:Hlookup.
  { destruct p1.
    rewrite IHps /=.
    rewrite fmap_insert /=.
    apply map_eq.
    intro.
    destruct (decide (i0=p)).
    rewrite e.
    rewrite lookup_insert.
    rewrite lookup_fmap  Hlookup //.
    rewrite lookup_insert_ne;[done|eauto].
  }
  rewrite IHps //.
  }
  apply upd_is_strong_assoc_comm.
  { set_solver + H. }
Qed.

Lemma p_grnt_acc_excl σ i ps:
  set_Forall (λ p, ∃ e, (get_page_table σ) !! p = Some e ∧ (e.2 = ∅ ∨ e.1.2 = false)) ps ->
 (get_excl_gmap (update_page_table_global grant_access σ i ps)) = (get_excl_gmap σ).
Proof.
  rewrite /get_excl_gmap /=.
  generalize dependent σ.1.1.1.2.
  induction ps as [|p ps] using set_ind_L.
  done.
  intros ? Hforall.
  rewrite set_fold_disj_union_strong.
  {
    rewrite set_fold_singleton /=.
    set pgt' := (X in X !! p).
    destruct (pgt' !! p) eqn:Hlookup.
    { destruct p1.
      rewrite IHps /=.
      rewrite fmap_insert /=.
      apply map_eq.
      intro.
      destruct (decide (i0=p)).
      rewrite e.
      rewrite lookup_insert.
      rewrite lookup_fmap Hlookup /=.
      specialize (Hforall p).
      feed specialize Hforall. set_solver +.
      destruct Hforall as [? [? ?]].
      rewrite /pgt' in Hlookup.
      rewrite H0 in Hlookup.
      inversion Hlookup. subst x. simpl in H1.
      destruct H1.
      do 2 f_equal.
      subst g.
      rewrite union_empty_r_L.
      rewrite size_singleton size_empty.
      case_bool_decide;done.
      rewrite H1 //.
      rewrite lookup_insert_ne;[done|eauto].
      intros p2 Hin.
      specialize (Hforall p2).
      feed specialize Hforall.
      set_solver + Hin.
      destruct Hforall.
      exists x.
      assert (p ≠ p2). set_solver + H Hin.
      rewrite lookup_insert_ne //.
    }
    rewrite IHps //.
    intros p2 Hin.
    specialize (Hforall p2).
    feed specialize Hforall.
    set_solver + Hin.
    apply Hforall.
  }
  apply upd_is_strong_assoc_comm.
  { set_solver + H. }
Qed.

Lemma u_grnt_acc_acc σ ps v sacc:
  set_Forall (λ p, is_Some ((get_page_table σ) !! p)) ps ->
  get_access_gmap σ !! v = Some (to_dfrac_agree (DfracOwn 1) sacc) ->
  get_access_gmap (update_page_table_global grant_access σ v ps)
  =  <[v := to_dfrac_agree (DfracOwn 1) (ps ∪ sacc)]>(get_access_gmap σ).
Proof.
  rewrite /grant_access /update_page_table_global /=.
  repeat destruct σ as [σ ?].
  simpl.
  intros Hforall Hlk.
  apply map_eq.
  intro.
  destruct (decide (i = v)).
  { subst.
    rewrite lookup_insert.
    revert Hforall Hlk.
    generalize p.
    generalize sacc.
    induction ps as [|p' ps] using set_ind_L.
    intros ? ? Hlk.
    rewrite !set_fold_empty //.
    rewrite union_empty_l_L //.
    intros ? ?  Hlk.
    rewrite !set_fold_disj_union_strong /=.
    rewrite !set_fold_singleton.
    destruct (p0 !! p') eqn: Hlk_p'.
    2:{
      specialize (Hlk p'). feed specialize Hlk.
      set_solver.
      simpl in Hlk.
      rewrite Hlk_p' in Hlk.
      inversion Hlk. done.
    }
    intro Hlookup.
    rewrite (IHps ({[p']} ∪ sacc0)).
    assert (ps ∪ ({[p']} ∪ sacc0) = {[p']} ∪ ps ∪ sacc0) as ->.
    set_solver +.
    done.
    rewrite /get_access_gmap.
    destruct p1.
    intros p2 Hin_p2.
    destruct (decide (p2 = p')).
    { subst p2. rewrite lookup_insert. done. }
    { rewrite lookup_insert_ne //. apply Hlk. set_solver + Hin_p2. }
    rewrite /get_access_gmap /=.
    rewrite fmap_insert /=.
    destruct p1.
    simpl.
    rewrite -elem_of_list_to_map.
    2:{
      rewrite -list_fmap_compose.
      simpl.
      rewrite NoDup_fmap.
      apply NoDup_list_of_vmids.
    }
    apply elem_of_list_In.
    apply in_map_iff.
    exists v.
    split;auto.
    2: apply in_list_of_vmids.
    f_equal.
    f_equal.
    rewrite (map_filter_insert_True _ _ p').
    2: { set_solver. }
    rewrite dom_insert_L.
    f_equal.
    rewrite /get_access_gmap in Hlookup.
    rewrite -elem_of_list_to_map in Hlookup.
    2:{
      rewrite -list_fmap_compose.
      simpl.
      rewrite NoDup_fmap.
      apply NoDup_list_of_vmids.
    }
    apply elem_of_list_In in Hlookup.
    apply in_map_iff in Hlookup.
    destruct Hlookup as [? [Heq _]].
    inversion Heq.
    done.
    2: set_solver + H.
    {
      intros.
      destruct (b' !! x2) as [p2|] eqn: Hlookup2, (b' !! x1) as [p1|] eqn:Hlookup1;
        rewrite ?lookup_insert_ne ?Hlookup1 ?Hlookup2 //;last eauto.
      rewrite insert_commute //.
    }
  }
  { rewrite lookup_insert_ne //.
    destruct (get_access_gmap (σ, t0, p, v0, m, t) !! i) eqn: Hlookup.
    {
    revert Hforall Hlookup.
    generalize p.
    generalize sacc.
    induction ps as [|p' ps] using set_ind_L.
    intros ? ? Hforall.
    rewrite !set_fold_empty //.
    intros ? ?  Hforall Hlookup.
    rewrite !set_fold_disj_union_strong /=.
    rewrite !set_fold_singleton.
    destruct (p0 !! p') eqn: Hlk_p'.
    2:{
      specialize (Hforall p'). feed specialize Hforall.
      set_solver.
      simpl in Hforall.
      rewrite Hlk_p' in Hforall.
      inversion Hforall. done.
    }
    rewrite (IHps ({[p']} ∪ sacc0)) //.
    destruct p1.
    intros p2 Hin_p2.
    destruct (decide (p2 = p')).
    { subst p2. rewrite lookup_insert. done. }
    { rewrite lookup_insert_ne //. apply Hforall. set_solver + Hin_p2. }
    rewrite /get_access_gmap /=.
    rewrite fmap_insert /=.
    destruct p1.
    simpl.
    rewrite -elem_of_list_to_map.
    2:{
      rewrite -list_fmap_compose.
      simpl.
      rewrite NoDup_fmap.
      apply NoDup_list_of_vmids.
    }
    apply elem_of_list_In.
    apply in_map_iff.
    exists i.
    split;auto.
    2: apply in_list_of_vmids.
    f_equal.
    rewrite /get_access_gmap in Hlookup.
    rewrite -elem_of_list_to_map in Hlookup.
    2:{
      rewrite -list_fmap_compose.
      simpl.
      rewrite NoDup_fmap.
      apply NoDup_list_of_vmids.
    }
    apply elem_of_list_In in Hlookup.
    apply in_map_iff in Hlookup.
    destruct Hlookup as [? [Heq _]].
    inversion Heq.
    subst x.
    f_equal.
    destruct (decide (i ∈ g)).
    rewrite (map_filter_insert_True _ _ p').
    2: { set_solver + e. }
    rewrite dom_insert_L.
    assert (p' ∈ dom (gset PID) (filter (λ kv : PID * gset VMID, i ∈ kv.2) ((λ p2 : option VMID * bool * gset VMID, p2.2) <$> p0))).
    {
      rewrite elem_of_dom.
      exists g.
      rewrite map_filter_lookup_Some.
      split;auto.
      rewrite lookup_fmap_Some.
      exists (p1,g).
      split;done.
    }
    set_solver + H0.
    rewrite (map_filter_insert_False _ _ p').
    2: { set_solver + n0 n. }
    rewrite map_filter_delete.
    rewrite dom_delete_L.
    assert (p' ∉ dom (gset PID) (filter (λ kv : PID * gset VMID, i ∈ kv.2) ((λ p2 : option VMID * bool * gset VMID, p2.2) <$> p0))).
    {
      rewrite elem_of_dom.
      intro.
      destruct H0.
      rewrite map_filter_lookup_Some in H0.
      destruct H0.
      rewrite lookup_fmap_Some in H0.
      destruct H0.
      destruct H0.
      subst x.
      rewrite H3 in Hlk_p'.
      inversion Hlk_p'.
      subst x0.
      set_solver + H1 n0.
    }
    set_solver + H0.
    2: set_solver + H.
    {
      intros.
      destruct (b' !! x2) as [p2|] eqn: Hlookup2, (b' !! x1) as [p1|] eqn:Hlookup1;
        rewrite ?lookup_insert_ne ?Hlookup1 ?Hlookup2 //;last eauto.
      rewrite insert_commute //.
    }
    }
    rewrite /get_access_gmap in Hlookup.
    rewrite -not_elem_of_list_to_map in Hlookup.
    exfalso.
    apply Hlookup.
    rewrite -list_fmap_compose.
    rewrite /fst.
    cbn.
    apply <- (elem_of_list_fmap (A:= fin vm_count) (B:= VMID)).
    exists i.
    split. done.
    rewrite elem_of_list_In.
    apply in_list_of_vmids.
  }
Qed.

Lemma p_rvk_acc_current_vm σ i l:
  get_current_vm (update_page_table_global revoke_access σ i l) = get_current_vm σ.
Proof. f_equal. Qed.

Lemma p_rvk_acc_regs σ i l:
  get_reg_files (update_page_table_global revoke_access σ i l) = get_reg_files σ.
Proof. f_equal. Qed.

Lemma p_rvk_acc_mem σ i l:
  get_mem (update_page_table_global revoke_access σ i l) = get_mem σ.
Proof. f_equal. Qed.

Lemma p_rvk_acc_mb σ i l:
  get_mail_boxes (update_page_table_global revoke_access σ i l) = get_mail_boxes σ.
Proof. f_equal. Qed.

Lemma p_rvk_acc_trans σ i l:
  get_transactions (update_page_table_global revoke_access σ i l) = get_transactions σ.
Proof. f_equal. Qed.

Lemma p_rvk_acc_own σ i ps:
 (get_own_gmap (update_page_table_global revoke_access σ i ps)) = (get_own_gmap σ).
Proof.
  rewrite /get_own_gmap /=.
  generalize dependent σ.1.1.1.2.
  induction ps as [|p ps] using set_ind_L.
  done.
  intro.
  rewrite set_fold_disj_union_strong.
  {
    rewrite set_fold_singleton /=.
  set pgt' := (X in X !! p).
  destruct (pgt' !! p) eqn:Hlookup.
  { destruct p1.
    rewrite IHps /=.
    rewrite fmap_insert /=.
    apply map_eq.
    intro.
    destruct (decide (i0=p)).
    rewrite e.
    rewrite lookup_insert.
    rewrite lookup_fmap  Hlookup //.
    rewrite lookup_insert_ne;[done|eauto].
  }
  rewrite IHps //.
  }
  apply upd_is_strong_assoc_comm.
  { set_solver + H. }
Qed.

Lemma u_rvk_acc_acc σ ps v sacc:
  set_Forall (λ p, is_Some ((get_page_table σ) !! p)) ps ->
  get_access_gmap σ !! v = Some (to_dfrac_agree (DfracOwn 1) sacc) ->
  get_access_gmap (update_page_table_global revoke_access σ v ps)
  = <[v := to_dfrac_agree (DfracOwn 1) (sacc ∖ ps)]>(get_access_gmap σ).
Proof.
  rewrite /revoke_access /update_page_table_global /=.
  repeat destruct σ as [σ ?].
  simpl.
  intros Hforall Hlk.
  apply map_eq.
  intro.
  destruct (decide (i = v)).
  { subst.
    rewrite lookup_insert.
    revert Hforall Hlk.
    generalize p.
    generalize sacc.
    induction ps as [|p' ps] using set_ind_L.
    intros ? ? Hlk.
    rewrite !set_fold_empty //.
    rewrite difference_empty_L //.
    intros ? ? Hlk.
    rewrite !set_fold_disj_union_strong /=.
    rewrite !set_fold_singleton.
    destruct (p0 !! p') eqn: Hlk_p'.
    2:{
      specialize (Hlk p'). feed specialize Hlk.
      set_solver.
      simpl in Hlk.
      rewrite Hlk_p' in Hlk.
      inversion Hlk. done.
    }
    intro Hlookup.
    rewrite (IHps ( sacc0 ∖ {[p']})).
    assert (sacc0 ∖ ({[p']} ∪ ps) = sacc0 ∖ {[p']} ∖ ps) as ->.
    set_solver +. done.
    rewrite /get_access_gmap.
    destruct p1.
    intros p2 Hin_p2.
    destruct (decide (p2 = p')).
    { subst p2. rewrite lookup_insert. done. }
    { rewrite lookup_insert_ne //. apply Hlk. set_solver + Hin_p2. }
    rewrite /get_access_gmap /=.
    rewrite fmap_insert /=.
    destruct p1.
    rewrite /= -elem_of_list_to_map.
    2:{
      rewrite -list_fmap_compose.
      simpl.
      rewrite NoDup_fmap.
      apply NoDup_list_of_vmids.
    }
    apply elem_of_list_In.
    apply in_map_iff.
    exists v.
    split;auto.
    2: apply in_list_of_vmids.
    f_equal.
    f_equal.
    rewrite (map_filter_insert_False _ _ p').
    2: { set_solver. }
    rewrite map_filter_delete.
    rewrite dom_delete_L.
    f_equal.
    rewrite /get_access_gmap in Hlookup.
    rewrite -elem_of_list_to_map in Hlookup.
    2:{
      rewrite -list_fmap_compose.
      simpl.
      rewrite NoDup_fmap.
      apply NoDup_list_of_vmids.
    }
    apply elem_of_list_In in Hlookup.
    apply in_map_iff in Hlookup.
    destruct Hlookup as [? [Heq _]].
    inversion Heq.
    done.
    2: set_solver + H.
    {
      intros.
      destruct (b' !! x2) as [p2|] eqn: Hlookup2, (b' !! x1) as [p1|] eqn:Hlookup1;
        rewrite ?lookup_insert_ne ?Hlookup1 ?Hlookup2 //;last eauto.
      rewrite insert_commute //.
    }
  }
  { rewrite lookup_insert_ne //.
    destruct (get_access_gmap (σ, t0, p, v0, m, t) !! i) eqn: Hlookup.
    {
    revert Hforall Hlookup.
    generalize p.
    generalize sacc.
    induction ps as [|p' ps] using set_ind_L.
    intros ? ? Hforall.
    rewrite !set_fold_empty //.
    intros ? ?  Hforall Hlookup.
    rewrite !set_fold_disj_union_strong /=.
    rewrite !set_fold_singleton.
    destruct (p0 !! p') eqn: Hlk_p'.
    2:{
      specialize (Hforall p'). feed specialize Hforall.
      set_solver.
      simpl in Hforall.
      rewrite Hlk_p' in Hforall.
      inversion Hforall. done.
    }
    rewrite (IHps (sacc0 ∖ {[p']})) //.
    destruct p1.
    intros p2 Hin_p2.
    destruct (decide (p2 = p')).
    { subst p2. rewrite lookup_insert //. }
    { rewrite lookup_insert_ne //. apply Hforall. set_solver + Hin_p2. }
    rewrite /get_access_gmap /=.
    rewrite fmap_insert /=.
    destruct p1. simpl.
    rewrite -elem_of_list_to_map.
    2:{
      rewrite -list_fmap_compose.
      simpl.
      rewrite NoDup_fmap.
      apply NoDup_list_of_vmids.
    }
    apply elem_of_list_In.
    apply in_map_iff.
    exists i.
    split;auto.
    2: apply in_list_of_vmids.
    f_equal.
    rewrite /get_access_gmap in Hlookup.
    rewrite -elem_of_list_to_map in Hlookup.
    2:{
      rewrite -list_fmap_compose.
      simpl.
      rewrite NoDup_fmap.
      apply NoDup_list_of_vmids.
    }
    apply elem_of_list_In in Hlookup.
    apply in_map_iff in Hlookup.
    destruct Hlookup as [? [Heq _]].
    inversion Heq.
    subst x.
    f_equal.
    destruct (decide (i ∈ g)).
    rewrite (map_filter_insert_True _ _ p').
    2: { set_solver + e n. }
    rewrite dom_insert_L.
    assert (p' ∈ dom (gset PID) (filter (λ kv : PID * gset VMID, i ∈ kv.2) ((λ p2 : option VMID * bool * gset VMID, p2.2) <$> p0))).
    {
      rewrite elem_of_dom.
      exists g.
      rewrite map_filter_lookup_Some.
      split;auto.
      rewrite lookup_fmap_Some.
      exists (p1,g).
      split;done.
    }
    set_solver + H0.
    rewrite (map_filter_insert_False _ _ p').
    2: { set_solver + n0 n. }
    rewrite map_filter_delete.
    rewrite dom_delete_L.
    assert (p' ∉ dom (gset PID) (filter (λ kv : PID * gset VMID, i ∈ kv.2) ((λ p2 : option VMID * bool * gset VMID, p2.2) <$> p0))).
    {
      rewrite elem_of_dom.
      intro.
      destruct H0.
      rewrite map_filter_lookup_Some in H0.
      destruct H0.
      rewrite lookup_fmap_Some in H0.
      destruct H0.
      destruct H0.
      subst x.
      rewrite H3 in Hlk_p'.
      inversion Hlk_p'.
      subst x0.
      set_solver + H1 n0.
    }
    set_solver + H0.
    2: set_solver + H.
    {
      intros.
      destruct (b' !! x2) as [p2|] eqn: Hlookup2, (b' !! x1) as [p1|] eqn:Hlookup1;
        rewrite ?lookup_insert_ne ?Hlookup1 ?Hlookup2 //;last eauto.
      rewrite insert_commute //.
    }
    }
    rewrite /get_access_gmap in Hlookup.
    rewrite -not_elem_of_list_to_map in Hlookup.
    exfalso.
    apply Hlookup.
    rewrite -list_fmap_compose.
    rewrite /fst.
    cbn.
    apply <- (elem_of_list_fmap (A:= fin vm_count) (B:= VMID)).
    exists i.
    split. done.
    rewrite elem_of_list_In.
    apply in_list_of_vmids.
  }
Qed.

Lemma p_rvk_acc_excl σ i j tt ps:
 set_Forall (λ p, match tt with
                | Donation => False
                | Sharing => σ.1.1.1.2 !! p = Some (Some j, false, {[j; i]})
                | Lending => σ.1.1.1.2 !! p = Some (Some j, true, {[i]})
                end) ps ->
 (get_excl_gmap (update_page_table_global revoke_access σ i ps)) = (get_excl_gmap σ).
Proof.
  rewrite /get_excl_gmap /=.
  generalize dependent σ.1.1.1.2.
  induction ps as [|p ps] using set_ind_L.
  done.
  intros ? Hforall.
  rewrite set_fold_disj_union_strong.
  {
    rewrite set_fold_singleton /=.
    set pgt' := (X in X !! p).
    destruct (pgt' !! p) eqn:Hlookup.
    { destruct p1.
      rewrite IHps /=.
      rewrite fmap_insert /=.
      apply map_eq.
      intro.
      destruct (decide (i0=p)).
      subst i0.
      rewrite lookup_insert.
      rewrite lookup_fmap Hlookup /=.
      specialize (Hforall p).
      feed specialize Hforall.
      set_solver +.
      destruct tt.
      done.
      rewrite Hlookup in Hforall.
      inversion Hforall.
      done.
      rewrite Hlookup in Hforall.
      inversion Hforall.
      assert ({[i]}∖ {[i]} = ∅) as ->. set_solver +.
      case_bool_decide;case_bool_decide;eauto.
      exfalso.
      apply H3.
      rewrite size_singleton //.
      exfalso.
      apply H0.
      rewrite size_empty //. lia.
      rewrite lookup_insert_ne;[done|eauto].
      intros p' Hin'.
      specialize (Hforall p').
      feed specialize Hforall.
      set_solver + Hin'.
      simpl in Hforall.
      assert ( p ≠ p' ).
      set_solver + Hin' H.
      destruct tt;auto.
      rewrite lookup_insert_ne //.
      rewrite lookup_insert_ne //.
    }
    rewrite IHps //.
    intros p' Hin'.
    specialize (Hforall p').
    feed specialize Hforall.
    set_solver + Hin'.
    done.
  }
  apply upd_is_strong_assoc_comm.
  { set_solver + H. }
Qed.

Lemma p_flip_excl_current_vm σ i (ps: gset PID) :
 get_current_vm (update_page_table_global flip_excl σ i ps) = get_current_vm σ.
Proof. f_equal. Qed.

Lemma p_flip_excl_regs σ i (ps: gset PID):
 get_reg_files (update_page_table_global flip_excl σ i ps) = get_reg_files σ.
Proof. f_equal. Qed.

Lemma p_flip_excl_mem σ i (ps: gset PID):
 get_mem (update_page_table_global flip_excl σ i ps) = get_mem σ.
Proof. f_equal. Qed.

Lemma p_flip_excl_mb σ i (ps: gset PID):
 get_mail_boxes (update_page_table_global flip_excl σ i ps) = get_mail_boxes σ.
Proof. f_equal. Qed.

Lemma p_flip_excl_trans σ i (ps: gset PID):
 get_transactions (update_page_table_global flip_excl σ i ps) = get_transactions σ.
Proof. f_equal. Qed.

Lemma p_flip_excl_own σ i ps:
 (get_own_gmap (update_page_table_global flip_excl σ i ps)) = (get_own_gmap σ).
Proof.
  rewrite /get_own_gmap /=.
  generalize dependent σ.1.1.1.2.
  induction ps as [|p ps] using set_ind_L.
  done.
  intro.
  rewrite set_fold_disj_union_strong.
  {
    rewrite set_fold_singleton /=.
  set pgt' := (X in X !! p).
  destruct (pgt' !! p) eqn:Hlookup.
  { destruct p1.
    rewrite IHps /=.
    rewrite fmap_insert /=.
    apply map_eq.
    intro.
    destruct (decide (i0=p)).
    rewrite e.
    rewrite lookup_insert.
    destruct p1.
    rewrite lookup_fmap Hlookup //.
    rewrite lookup_insert_ne;[done|eauto].
  }
  rewrite IHps //.
  }
  apply upd_is_strong_assoc_comm.
  { set_solver + H. }
  Qed.

Lemma p_flip_excl_acc σ i ps:
 (get_access_gmap (update_page_table_global flip_excl σ i ps)) = (get_access_gmap σ).
Proof.
  rewrite /get_access_gmap  /=.
  generalize dependent σ.1.1.1.2.
  induction ps as [|p ps] using set_ind_L.
  done.
  intro.
  rewrite set_fold_disj_union_strong.
  {
    rewrite set_fold_singleton /=.
  set pgt' := (X in X !! p).
  destruct (pgt' !! p) eqn:Hlookup.
  { destruct p1.
    rewrite IHps /=.
    f_equal.
    apply (list_eq_same_length _ _ vm_count).
    rewrite fmap_length.
    apply length_list_of_vmids.
    rewrite fmap_length.
    apply length_list_of_vmids.
    intros ? ? ? ? H0 H1.
    apply list_lookup_fmap_inv in H0, H1.
    destruct H0, H1.
    destruct H0, H1.
    rewrite H3 in H4.
    inversion H4. subst x1.
    clear H4.
    rewrite H0 H1.
    do 4 f_equal.
    destruct p1.
    destruct o;
    rewrite fmap_insert insert_id //.
    all: rewrite /= lookup_fmap Hlookup //.
  }
  rewrite IHps //.
  }
  apply upd_is_strong_assoc_comm.
  { set_solver + H. }
Qed.

Lemma u_flip_excl_excl σ ps v :
  set_Forall (λ p, ∃ e, (get_page_table σ) !! p = Some e ∧ e.2 = {[v]}) ps ->
 (get_excl_gmap (update_page_table_global flip_excl σ v ps)) = flip_excl_gmap (get_excl_gmap σ) ps.
Proof.
  rewrite /get_excl_gmap.
  rewrite /update_page_table_global /=.
  rewrite /flip_excl_gmap /update_pgt_gmap /=.
  generalize σ.1.1.1.2.
  induction ps as [|p ps] using set_ind_L.
  intros.
  rewrite !set_fold_empty //.
  intros pgt Hforall.
  rewrite !set_fold_disj_union_strong /=.
  rewrite !set_fold_singleton.
  rewrite IHps.
  rewrite lookup_fmap.
  destruct (pgt!! p) eqn:Hlookup.
  { rewrite Hlookup /=.
    destruct p0.
    simpl.
    f_equal.
    destruct p0.
    rewrite fmap_insert //=.
    assert (bool_decide (size g ≤ 1) = true) as ->.
    {
      specialize (Hforall p).
      feed specialize Hforall. set_solver +.
      destruct Hforall as [? [? ?]].
      rewrite H0 in Hlookup.
      inversion Hlookup. subst x. simpl in H1. subst g.
      rewrite size_singleton.
      case_bool_decide;done.
    }
    rewrite 2!andb_true_r //.
  }
  { rewrite Hlookup //=. }
  {
    intros p1 Hin.
    specialize (Hforall p1).
    feed specialize Hforall. set_solver + Hin.
    destruct Hforall as [? [? ?]].
    destruct (pgt !! p).
    exists x.
    assert (p ≠ p1). set_solver + Hin H.
    rewrite lookup_insert_ne //.
    exists x. done.
  }
  2,4 : set_solver + H.
  {
    intros.
    destruct (b' !! x2) as [p2|] eqn: Hlookup2, (b' !! x1) as [p1|] eqn:Hlookup1;
      try destruct p1 as [q1 []]; try destruct p2 as [q2 []]; rewrite ?lookup_insert_ne ?Hlookup1 ?Hlookup2 //;last eauto.
    apply insert_commute.
    done.
  }
  apply upd_is_strong_assoc_comm.
Qed.

Lemma p_upd_pgt_pgt_not_elem {i:VMID} {perm : permission} pgt upd (sps: gset PID) (p:PID) :
  p ∉ sps ->
  pgt !! p = Some perm ->
  set_fold (λ (p0 : PID) (acc : page_table), match acc !! p0 with
                                             | Some perm => <[p0:= upd perm i]> acc
                                             | None => acc
                                             end) pgt sps !! p = Some perm.
Proof.
  generalize pgt.
  clear pgt.
  induction sps as [|p' sps] using set_ind_L.
  intros pgt Hnotin Hlookup.
  rewrite set_fold_empty //.
  intros pgt Hnotin Hlookup.
  rewrite set_fold_disj_union_strong.
  {
    apply IHsps.
    set_solver + Hnotin.
    rewrite set_fold_singleton.
    assert ( p ≠ p' ) as Hneq.
    {
      intro.
      subst p'.
      set_solver + Hnotin.
    }
    destruct (pgt !! p').
    rewrite lookup_insert_ne;last eauto.
    all : done.
  }
  apply upd_is_strong_assoc_comm.
  set_solver + H.
Qed.

Lemma  u_upd_pgt_elem_of {σ} {i:VMID} {perm : permission} upd (sps: gset PID) (p:PID) :
  p ∈ sps ->
  (get_page_table σ) !! p = Some perm ->
  set_fold (λ (p0 : PID) (acc : page_table), match acc !! p0 with
                                             | Some perm => <[p0:= upd perm i]> acc
                                             | None => acc
                                             end) (get_page_table σ) sps !! p = Some (upd perm i).
Proof.
  generalize σ.1.1.1.2.
  induction sps as [|p' sps] using set_ind_L.
  intros pgt Hin Hlookup.
  rewrite set_fold_empty //.
  intros pgt Hin Hlookup.
  rewrite set_fold_disj_union_strong.
  {
    destruct (decide (p = p')).
    subst p'.
    rewrite set_fold_singleton.
    apply p_upd_pgt_pgt_not_elem.
    done.
    rewrite  Hlookup lookup_insert //.
    apply IHsps.
    set_solver + Hin n.
    rewrite set_fold_singleton.
    destruct (pgt !! p').
    rewrite lookup_insert_ne //.
    done.
  }
  apply upd_is_strong_assoc_comm.
  set_solver + H.
Qed.

End pagetable_extra.
