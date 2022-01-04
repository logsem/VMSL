From HypVeri Require Import machine machine_extra tactics.
From HypVeri.algebra Require Import base base_extra.

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

Lemma p_upd_own_access σ i ps:
((get_access_gmap (update_page_table_global update_ownership σ i ps)):gmap _ _) = ((get_access_gmap σ): gmap _ _).
Proof.
  rewrite /get_access_gmap  /=.
  generalize dependent σ.1.1.1.2.
  induction ps as [|p ps] using set_ind_L.
  done.
  intro.
  (* rewrite /update_ownership /=. *)
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

Lemma p_grnt_acc_ownerships σ i ps:
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

Lemma p_rvk_acc_ownerships σ i ps:
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

(*--- prove having mappings in gmap implies owership/access to pages in opsem ---*)

(* TODO *)
(* Lemma u_rvk_acc_acc σ ps v : *)
(*   get_access_gmap (revoke_access_global σ v ps) = revoke_acc_gmap (get_access_gmap σ) v ps. *)
(* Proof. *)
(*   rewrite /get_access_gmap. *)
(*   rewrite /revoke_access_global /update_page_table_global /=. *)
(*   rewrite /revoke_acc_gmap /update_acc_gmap /=. *)
(*   generalize  σ.1.1.1.2. *)
(*   induction ps as [|p ps] using set_ind_L. *)
(*   intros. *)
(*   rewrite !set_fold_empty //. *)
(*   intro pgt. *)
(*   rewrite !set_fold_disj_union_strong /=. *)
(*   rewrite !set_fold_singleton. *)
(*   rewrite IHps. *)
(*   rewrite lookup_fmap. *)
(*   destruct (pgt!! p) eqn:Hlookup. *)
(*   { rewrite Hlookup /=. *)
(*     destruct p0. *)
(*     simpl. *)
(*     f_equal. *)
(*     rewrite fmap_insert //=. *)
(*   } *)
(*   { rewrite Hlookup //=. } *)
(*   2,4 : set_solver + H. *)
(*   { *)
(*     intros. *)
(*     destruct (b' !! x2) as [p2|] eqn: Hlookup2, (b' !! x1) as [p1|] eqn:Hlookup1; *)
(*       try destruct p1 as [q1 []]; try destruct p2 as [q2 []]; rewrite ?lookup_insert_ne ?Hlookup1 ?Hlookup2 //;last eauto. *)
(*     apply insert_commute. *)
(*     done. *)
(*   } *)
(*   apply upd_is_strong_assoc_comm. *)
(* Qed. *)

Lemma update_page_table_lookup_not_elem_of {i:VMID} {perm : permission} pgt upd (sps: gset PID) (p:PID) :
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

Lemma update_page_table_lookup_elem_of {σ} {i:VMID} {perm : permission} upd (sps: gset PID) (p:PID) :
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
    apply update_page_table_lookup_not_elem_of.
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
