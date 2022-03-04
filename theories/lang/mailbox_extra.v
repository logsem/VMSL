From HypVeri Require Import machine machine_extra.
From HypVeri.algebra Require Import base.


Section mailbox_extra.

Context {HyperConst : HypervisorConstants}.
Implicit Type σ : state.
Implicit Type i : VMID.

Lemma empty_rx_preserve_current_vm σ :
  get_current_vm (empty_rx σ) = get_current_vm σ.
Proof.
  rewrite /empty_rx.
  destruct (σ.1.1.1.1.2 !!! σ.1.1.2).
  destruct p.
  done.
Qed.

Lemma empty_rx_preserve_mem σ:
  get_mem (empty_rx σ) = get_mem σ.
Proof.
  rewrite /empty_rx.
  destruct (σ.1.1.1.1.2 !!! σ.1.1.2).
  destruct p.
  done.
Qed.

Lemma empty_rx_preserve_regs σ:
 get_reg_gmap (empty_rx σ) = get_reg_gmap σ.
Proof.
  rewrite /empty_rx.
  destruct (σ.1.1.1.1.2 !!! σ.1.1.2).
  destruct p.
  done.
Qed.

Lemma empty_rx_preserve_mb σ:
  get_mb_gmap (empty_rx σ) = (get_mb_gmap σ).
Proof.
  rewrite /empty_rx.
(* XXX: couldn't find useful lemmas about flat_map, maybe redefine get_mb_gmap? *)
Admitted.

Lemma empty_rx_preserve_pagetable σ:
  get_page_table (empty_rx σ)  = get_page_table σ.
Proof.
  rewrite /empty_rx.
  destruct (σ.1.1.1.1.2 !!! σ.1.1.2).
  destruct p.
  done.
Qed.

Lemma empty_rx_preserve_trans σ :
  get_transactions (empty_rx σ) = (get_transactions σ).
Proof.
  rewrite /empty_rx.
  destruct (σ.1.1.1.1.2 !!! σ.1.1.2).
  destruct p.
  done.
Qed.

(* TODO simplify *)
Lemma empty_rx_update_mailbox σ:
  get_rx_gmap (empty_rx σ) = <[(get_current_vm σ) := None]>(get_rx_gmap σ).
Proof.
  rewrite /get_rx_gmap.
  apply map_eq.
  intros i.
  destruct (list_to_map
    (map
       (λ v : VMID,
          match get_transactions (get_transactions get_mail_boxes empty_rx σ !!! v) with
          | Some (l0, j) => (v, Some (l0, j))
          | None => (v, None)
          end) list_of_vmids) !! i) eqn:Heqn.
  - apply elem_of_list_to_map_2 in Heqn.
    apply elem_of_list_In in Heqn.
    apply in_map_iff in Heqn.
    destruct Heqn as [y [Heqn1 Heqn2]].
    apply elem_of_list_In in Heqn2.
    rewrite /empty_rx //= in Heqn1.
    destruct (σ.1.1.1.1.2 !!! σ.1.1.2).
    destruct p.
    simpl in Heqn1.
    destruct (decide ((get_current_vm σ) = y)).
    + subst.
      rewrite vlookup_insert in Heqn1.
      simpl in Heqn1.
      inversion Heqn1; subst; clear Heqn1.
      rewrite lookup_insert.
      reflexivity.
    + symmetry.
      rewrite lookup_insert_Some.
      rewrite vlookup_insert_ne in Heqn1; auto.
      destruct (σ.1.1.1.1.2 !!! y) as [a b] eqn:Heqn3.
      destruct b as [c d] eqn:Heqn4.
      simpl in Heqn1.
      destruct d as [e|] eqn:Heqn5.
      * destruct e as [f g] eqn:Heqn6.
        inversion Heqn1; subst; clear Heqn1.
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
    rewrite /empty_rx //= in Heqn.
    destruct (σ.1.1.1.1.2 !!! σ.1.1.2).
    destruct p.
    simpl in Heqn.
    destruct (decide ((get_current_vm σ) = i)).
    + subst.
      exfalso.
      apply Heqn.
      rewrite <-list_fmap_compose.
      rewrite /compose.
      rewrite /fill_rx_unsafe //=.
      apply elem_of_list_In.
      apply in_map_iff.
      exists (get_current_vm σ).
      split; auto using in_list_of_vmids.
      rewrite vlookup_insert //=.
    + rewrite /fill_rx_unsafe //=.
      rewrite lookup_insert_None.
      split; auto.
      rewrite <-not_elem_of_list_to_map.
      rewrite /fill_rx_unsafe //= in Heqn.
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

Lemma p_fill_rx_current_vm σ v r l tx rx :
  get_current_vm (fill_rx_unsafe σ l v r tx rx) = get_current_vm σ.
Proof. f_equal. Qed.

Lemma p_fill_rx_mem σ l v r tx rx :
  get_mem (fill_rx_unsafe σ l v r tx rx) = get_mem σ.
Proof. f_equal. Qed.

Lemma p_fill_rx_regs σ l v r tx rx :
  get_reg_files (fill_rx_unsafe σ l v r tx rx) = get_reg_files σ.
Proof. f_equal. Qed.

Lemma p_fill_rx_mb σ l v r tx rx :
  tx = (get_mail_box σ @ r).1 ->
  rx = (get_mail_box σ @ r).2.1 ->
  get_mb_gmap (fill_rx_unsafe σ l v r tx rx) = get_mb_gmap σ.
Proof.
  intros Htx Hrx.
  rewrite /fill_rx_unsafe /get_mb_gmap /=.
  f_equal.
  induction list_of_vmids as [|? ? IH].
  - reflexivity.
  - simpl.
    f_equal.
    + f_equal.
      destruct (decide (a = r)) as [p|p].
      * rewrite p.
        rewrite vlookup_insert //.
      * rewrite vlookup_insert_ne; auto.
    + rewrite IH /=.
      f_equal.
      destruct (decide (a = r)) as [p|p].
      * rewrite p.
        rewrite vlookup_insert Hrx //.
      * rewrite vlookup_insert_ne; auto.
Qed.

Lemma p_fill_rx_pgt σ l v r tx rx :
  get_page_table (fill_rx_unsafe σ l v r tx rx) = get_page_table σ.
Proof. f_equal. Qed.

Lemma p_fill_rx_trans σ l v r tx rx :
  (get_transactions (fill_rx_unsafe σ l v r tx rx)) = get_transactions σ.
Proof. f_equal. Qed.

Lemma u_fill_rx_rx_state σ l v r tx rx :
  get_rx_gmap (fill_rx_unsafe σ l v r tx rx) = <[r := Some (l, v)]>(get_rx_gmap σ).
Proof.
  rewrite /get_rx_gmap.
  apply map_eq.
  intros i.
  destruct (list_to_map
    (map
       (λ v0 : VMID,
          match get_transactions (get_transactions get_mail_boxes fill_rx_unsafe σ l v r tx rx !!! v0) with
          | Some (l0, j) => (v0, Some (l0, j))
          | None => (v0, None)
          end) list_of_vmids) !! i) eqn:Heqn.
  - apply elem_of_list_to_map_2 in Heqn.
    apply elem_of_list_In in Heqn.
    apply in_map_iff in Heqn.
    destruct Heqn as [y [Heqn1 Heqn2]].
    apply elem_of_list_In in Heqn2.
    rewrite /fill_rx_unsafe //= in Heqn1.
    destruct (decide (r = y)).
    + subst.
      rewrite vlookup_insert in Heqn1.
      simpl in Heqn1.
      inversion Heqn1; subst; clear Heqn1.
      rewrite lookup_insert.
      reflexivity.
    + symmetry.
      rewrite lookup_insert_Some.
      rewrite vlookup_insert_ne in Heqn1; auto.
      destruct (σ.1.1.1.1.2 !!! y) as [a b] eqn:Heqn3.
      destruct b as [c d] eqn:Heqn4.
      simpl in Heqn1.
      destruct d as [e|] eqn:Heqn5.
      * destruct e as [f g] eqn:Heqn6.
        inversion Heqn1; subst; clear Heqn1.
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
      rewrite /fill_rx_unsafe //=.
      apply elem_of_list_In.
      apply in_map_iff.
      exists i.
      split; auto using in_list_of_vmids.
      rewrite vlookup_insert //=.
    + rewrite /fill_rx_unsafe //=.
      rewrite lookup_insert_None.
      split; auto.
      rewrite <-not_elem_of_list_to_map.
      rewrite  /fill_rx_unsafe //= in Heqn.
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
End mailbox_extra.
