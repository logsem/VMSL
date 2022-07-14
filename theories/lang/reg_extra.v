From HypVeri Require Import machine.
From HypVeri.lang Require lang.
From HypVeri.algebra Require Import base base_extra.

Section reg_extra.

Context `{HyperConst : HypervisorConstants}.

Implicit Type σ : state.
Implicit Type i : VMID.

Lemma p_upd_reg_current_vm σ i r w :
  get_current_vm (update_reg_global σ i r w) = get_current_vm σ.
Proof. f_equal. Qed.

Lemma p_upd_reg_mem σ i r w :
  get_mem (update_reg_global σ i r w) = get_mem σ.
Proof. f_equal. Qed.

Lemma p_upd_reg_mb σ i r w :
  get_mail_boxes (update_reg_global σ i r w) = (get_mail_boxes σ).
Proof. f_equal. Qed.

Lemma p_upd_reg_pgt σ i r w:
  get_page_table (update_reg_global σ i r w) = get_page_table σ.
Proof. f_equal. Qed.

Lemma p_upd_reg_trans σ i r w :
  get_transactions (update_reg_global σ i r w) = (get_transactions σ).
Proof. f_equal. Qed.

Lemma p_upd_pc_current_vm σ o :
  (get_current_vm (update_offset_PC σ o)) = (get_current_vm σ).
Proof.
  rewrite /update_offset_PC.
  destruct (get_reg_file σ @ σ.1.1.2 !! PC);eauto.
Qed.

Lemma p_upd_pc_mem σ o :
  get_mem (update_offset_PC σ o) = get_mem σ.
Proof.
  unfold update_offset_PC.
  destruct (get_reg_file σ @ (get_current_vm σ) !! PC).
  f_equal.
  done.
Qed.

Lemma p_upd_pc_mb σ o :
  get_mail_boxes (update_offset_PC σ o) = get_mail_boxes σ.
Proof.
  unfold update_offset_PC.
  destruct (get_reg_file σ @ (get_current_vm σ) !! PC).
  rewrite /update_reg p_upd_reg_mb;done.
  done.
Qed.

Lemma p_upd_pc_pgt σ o :
  get_page_table (update_offset_PC σ o) = get_page_table σ.
Proof.
  unfold update_offset_PC.
  destruct (get_reg_file σ @ (get_current_vm σ) !! PC).
  rewrite /update_reg  p_upd_reg_pgt;done.
  done.
Qed.

Lemma p_upd_pc_trans σ o :
  get_transactions (update_offset_PC σ o) = get_transactions σ.
Proof.
  unfold update_offset_PC.
  destruct (get_reg_file σ @ (get_current_vm σ) !! PC).
  rewrite /update_reg p_upd_reg_trans;done.
  done.
Qed.

Lemma get_reg_global_update_reg_global_ne_vmid {σ i j R1 R2 A B} :
  i ≠ j ->
  get_reg_global σ j R2 = Some B ->
  get_reg_global (update_reg_global σ i R1 A) j R2 = Some B.
Proof.
  intros Hne Hlk.
  rewrite /get_reg_global /update_reg_global.
  simpl.
  rewrite vlookup_insert_ne; auto.
Qed.

Lemma get_reg_gmap_lookup_Some σ i r w :
  (get_reg_gmap σ) !! (r,i)= Some w <->  get_reg_file σ @ i !! r = Some w.
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

Lemma get_reg_gmap_lookup_None σ i r :
  (get_reg_gmap σ) !! (r,i)= None <->  get_reg_file σ @ i !! r = None.
Proof.
  split.
  - destruct (get_reg_file σ @ i !! r) as [w|]  eqn:Heqn;[|done].
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

Lemma get_reg_gmap_get_reg_file σ (r:reg_name) (i:VMID) :
  (get_reg_gmap σ) !! (r,i) = (get_reg_file σ @ i) !! r.
Proof.
  destruct (get_reg_gmap σ !! (r, i)) eqn:Heqn.
  apply get_reg_gmap_lookup_Some in Heqn;done.
  apply get_reg_gmap_lookup_None in Heqn;done.
Qed.

Lemma get_reg_gmap_get_reg_Some σ (r:reg_name) (w:Word) (i:VMID) :
  i= (get_current_vm σ)->
  (get_reg_gmap σ) !! (r,i) = Some w <-> ((get_reg σ r) = Some w).
Proof.
  intros.
  rewrite get_reg_gmap_get_reg_file.
  unfold get_reg,get_reg_global;subst;done.
Qed.

Lemma u_upd_reg_regs σ i r w :
  get_reg_gmap (update_reg_global σ i r w) = <[(r,i) := w]>(get_reg_gmap σ).
Proof.
  intros.
  rewrite /update_reg_global.
  apply map_eq.
  intro j.
  destruct( decide (j=(r,i)) ).
  - subst j.
    rewrite lookup_insert.
    rewrite get_reg_gmap_get_reg_file /=.
    rewrite -> (vlookup_insert i _  _).
    by rewrite lookup_insert.
  - destruct ((get_reg_gmap σ) !! j) eqn:Heqn;
        rewrite lookup_insert_ne;[|done | |done];
        rewrite -> Heqn;
        destruct j as [r' i'];
        rewrite ->get_reg_gmap_get_reg_file in Heqn;
        rewrite ->get_reg_gmap_get_reg_file;
        destruct (decide (i=i'));
        destruct (decide (r=r'));
        subst;
        try contradiction;
        rewrite -Heqn /=.
    + rewrite -> (vlookup_insert i' _ _).
      by rewrite lookup_insert_ne ;[|done].
    + by rewrite vlookup_insert_ne.
    + by rewrite vlookup_insert_ne.
    + rewrite -> (vlookup_insert i' _ _).
      by rewrite lookup_insert_ne ;[|done].
    + by rewrite vlookup_insert_ne ;[|done].
    + by rewrite vlookup_insert_ne ;[|done].
Qed.

Lemma u_upd_pc_regs σ i (w:Word) (o:Z):
  (i= get_current_vm σ) -> ((get_reg_gmap σ) !! (PC,i) = Some w) ->
  get_reg_gmap (update_offset_PC σ o) = <[(PC,i) := (w ^+ o)%f]>(get_reg_gmap σ).
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
  apply u_upd_reg_regs.
Qed.

End reg_extra.

Ltac solve_reg_lookup :=
  match goal with
  | _ : get_reg ?σ ?r = Some ?w |- get_reg_gmap ?σ !! (?r, ?i) = Some ?w => rewrite get_reg_gmap_get_reg_Some;eauto
  | _ : get_reg ?σ ?r = Some ?w |- is_Some (get_reg_gmap ?σ !! (?r, ?i)) => eexists;rewrite get_reg_gmap_get_reg_Some;eauto
  | _ : get_reg ?σ ?r1 = Some ?w, _ : ?r1 ≠ ?r2 |- <[(?r2, ?i):= ?w2]>(get_reg_gmap ?σ) !! (?r1, ?i) = Some ?w =>
    rewrite lookup_insert_ne; eauto
  end.
