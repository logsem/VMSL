From HypVeri Require Import machine machine_extra.
From HypVeri.algebra Require Import base.
From HypVeri.lang Require Import lang_extra.

Section mem_extra.

Context `{HyperConst : HypervisorConstants}.

(* TODO *)
Lemma update_memory_preserve_current_vm σ a w :
  (get_current_vm (update_memory σ a w)) = (get_current_vm σ).
Proof. f_equal. Qed.

Lemma update_memory_preserve_reg σ a w:
  get_reg_gmap (update_memory σ a w) = get_reg_gmap σ.
Proof. f_equal. Qed.

Lemma update_memory_preserve_mb σ a w :
  get_mb_gmap (update_memory σ a w) = get_mb_gmap σ.
Proof. f_equal. Qed.

Lemma update_memory_preserve_rx σ a w :
  get_rx_gmap (update_memory σ a w) = (get_rx_gmap σ).
Proof. f_equal. Qed.

Lemma update_memory_preserve_owned σ a w :
  get_own_gmap (update_memory σ a w) = (get_own_gmap σ).
Proof. f_equal. Qed.

Lemma update_memory_preserve_access σ a w :
  get_access_gmap (update_memory σ a w) = (get_access_gmap σ).
Proof. f_equal. Qed.

Lemma update_memory_preserve_trans σ a w :
  get_trans_gmap (update_memory σ a w) = (get_trans_gmap σ).
Proof. f_equal. Qed.

Lemma update_memory_preserve_trans' σ a w:
  get_transactions (update_memory σ a w) = (get_transactions σ).
Proof. f_equal. Qed.

Lemma update_memory_preserve_retri σ a w :
  get_retri_gmap (update_memory σ a w) = (get_retri_gmap σ).
Proof. f_equal. Qed.

Lemma update_memory_update_mem σ a w :
  is_Some((get_mem σ) !! a) ->
  get_mem (update_memory σ a w) = <[a := w]>(get_mem σ).
Proof. intros. rewrite  /update_memory //. Qed.

Lemma p_wr_mem_current_vm σ dst ws:
  get_current_vm (write_mem_segment σ dst ws) = get_current_vm σ.
Proof. f_equal. Qed.

Lemma p_wr_mem_regs σ dst ws:
  get_reg_files (write_mem_segment σ dst ws) = get_reg_files σ.
Proof. f_equal. Qed.

Lemma p_wr_mem_mb σ dst ws:
  get_mail_boxes (write_mem_segment σ dst ws) = get_mail_boxes σ.
Proof. f_equal. Qed.

Lemma p_wr_mem_pgt σ dst ws:
  get_page_table (write_mem_segment σ dst ws) = get_page_table σ.
Proof. f_equal. Qed.

Lemma p_wr_mem_trans σ dst ws:
  get_transactions (write_mem_segment σ dst ws) = get_transactions σ.
Proof. f_equal. Qed.

Lemma u_wr_mem_mem σ dst ws:
  get_mem (write_mem_segment σ dst ws) = list_to_map (zip (finz.seq dst (length ws)) ws) ∪ get_mem σ.
Proof. done. Qed.

Lemma p_cp_mem_current_vm σ src dst l:
  get_current_vm (copy_page_segment σ src dst l) = get_current_vm σ.
Proof. rewrite /copy_page_segment. destruct (read_mem_segment σ.1.2 src l). f_equal. done. Qed.

Lemma p_cp_mem_regs σ src dst l:
  get_reg_files (copy_page_segment σ src dst l) = get_reg_files σ.
Proof. rewrite /copy_page_segment. destruct (read_mem_segment σ.1.2 src l). f_equal. done. Qed.

Lemma p_cp_mem_mb σ src dst l:
  get_mail_boxes (copy_page_segment σ src dst l) = get_mail_boxes σ.
Proof. rewrite /copy_page_segment. destruct (read_mem_segment σ.1.2 src l). f_equal. done. Qed.

Lemma p_cp_mem_pgt σ src dst l:
  get_page_table (copy_page_segment σ src dst l) = get_page_table σ.
Proof. rewrite /copy_page_segment. destruct (read_mem_segment σ.1.2 src l). f_equal. done. Qed.

Lemma p_cp_mem_trans σ src dst l:
  (get_transactions (copy_page_segment σ src dst l)) = get_transactions σ.
Proof. rewrite /copy_page_segment. destruct (read_mem_segment σ.1.2 src l). f_equal. done. Qed.

Lemma u_cp_mem_mem {σ} des (src dst: PID) l:
  read_mem_segment (get_mem σ) src l = Some des ->
  get_mem (copy_page_segment σ src dst l) = (list_to_map (zip (finz.seq dst (length des)) des)) ∪ get_mem σ.
Proof.
  intros.
  rewrite /copy_page_segment H u_wr_mem_mem //.
Qed.

Lemma rd_mem_mem_Some (m1 m2 : mem) (src:PID) (l:Word) :
  (l <= page_size)%Z ->
  dom m1 = list_to_set (addr_of_page src) ->
  m1 ⊆ m2 ->
  ∃ wl, read_mem_segment m2 src (Z.to_nat l) = Some wl ∧ length wl = (Z.to_nat l).
Proof.
  intros Hle Hdom Hsub.
  feed pose proof (sequence_a_map_Forall_Some (Z.to_nat l) src m1).
  rewrite Hdom.
  apply addr_of_page_subseteq. lia.
  destruct H as [ws [Hseq Hlen]].
  rewrite /read_mem_segment.
  exists ws.
  split.
  apply (sequence_a_map_subseteq _ _ _ m1). done. done.
  done.
Qed.

Lemma rd_mem_mem_Some' (m1 m2 : mem) (src:PID) (l:Word) wl :
  (l <= page_size)%Z ->
  dom m1 = list_to_set (addr_of_page src) ->
  read_mem_segment m2 src (Z.to_nat l) = Some wl ->
  m1 ⊆ m2 ->
  read_mem_segment m1 src (Z.to_nat l) = Some wl.
Proof.
  intros Hle Hdom Hrd Hsub.
  feed pose proof (rd_mem_mem_Some m1 m1 src l).
  done.
  done.
  rewrite map_subseteq_spec.
  intros. done.
  destruct H as [? [Hrd' ?]].
  feed pose proof (sequence_a_map_subseteq x (Z.to_nat l) src m1 m2).
  apply Hrd'.
  done.
  rewrite /read_mem_segment H0 in Hrd.
  inversion Hrd.
  subst x. done.
Qed.

Lemma rd_mem_mem_subseteq m src l wl:
  l = length wl ->
  read_mem_segment m src l = Some wl ->
  (list_to_map (zip (finz.seq src (length wl)) wl)) ⊆ m.
Proof.
  intros Hlen Hsome.
  rewrite /read_mem_segment in Hsome.
  generalize dependent l.
  generalize dependent src.
  induction wl.
  intros.
  simpl.
  rewrite map_subseteq_spec.
  intros. done.
  simpl.
  intros.
  subst l.
  simpl in Hsome.
  rewrite /monad.List.sequence_a_list /= in Hsome.
  destruct (m !! src) eqn:Hlk.
  { simpl in Hsome.
    destruct (list.foldr _ _) eqn:Hfold.
    inversion Hsome.
    2: inversion Hsome.
    subst f l.
    specialize (IHwl (src ^+ 1)%f (length wl)).
    feed specialize IHwl.
    done.
    rewrite /sequence_a /= /monad.List.sequence_a_list //= .
    {
      rewrite map_subseteq_spec.
      intros.
      destruct (decide (i = src)).
      subst i.
      rewrite lookup_insert in H.
      inversion H.
      subst a.
      done.
      rewrite lookup_insert_ne in H.
      rewrite map_subseteq_spec in IHwl.
      apply IHwl.
      done.
      done.
    }
  }
  inversion Hsome.
Qed.

Lemma dom_wr_mem_subseteq (mem: gmap Addr Word) (dst: PID) ws:
  (length ws) <= (Z.to_nat page_size) ->
  dom mem = list_to_set (addr_of_page dst) ->
  dom (list_to_map (zip (finz.seq dst (length ws)) ws) ∪ mem) = dom mem.
Proof.
  intros Hle Hdom.
  destruct ws.
  rewrite /= dom_union_L dom_empty_L.
  set_solver +.
  rewrite dom_union_L.
  apply subseteq_union_1_L.
  rewrite dom_list_to_map_L.
  rewrite fst_zip.
  2:{
    rewrite finz_seq_length. lia.
  }
  rewrite Hdom.
  intros a.
  rewrite 2!elem_of_list_to_set.
  intro Hin.
  rewrite /addr_of_page.
  rewrite elem_of_addr_of_page_iff.
  symmetry.
  apply to_pid_aligned_in_page.
  rewrite /addr_in_page.
  pose proof (finz_seq_in1 _ _ _ Hin).
  pose proof (finz_seq_in2 _ _ _ Hin).
  split.
  rewrite /finz.leb /Is_true.
  destruct (dst <=? a)%Z eqn:Heqn;first done.
  solve_finz.
  rewrite /finz.leb /Is_true.
  destruct (a <=? (dst ^+ (1000 - 1))%f)%Z eqn:Heqn;first done.
  rewrite Z.leb_gt in Heqn.
  solve_finz.
Qed.

End mem_extra.
