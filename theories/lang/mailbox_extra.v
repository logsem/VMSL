From HypVeri Require Import machine machine_extra.
From HypVeri.algebra Require Import base.


Section mailbox_extra.

Context {HyperConst : HypervisorConstants}.
Implicit Type σ : state.
Implicit Type i : VMID.

Lemma p_empty_rx_current_vm σ :
  get_current_vm (empty_rx σ) = get_current_vm σ.
Proof.
  rewrite /empty_rx.
  destruct (σ.1.1.1.1.2 !!! σ.1.1.2).
  destruct p.
  done.
Qed.

Lemma p_empty_rx_mem σ:
  get_mem (empty_rx σ) = get_mem σ.
Proof.
  rewrite /empty_rx.
  destruct (σ.1.1.1.1.2 !!! σ.1.1.2).
  destruct p.
  done.
Qed.

Lemma p_empty_rx_regs σ:
 get_reg_files (empty_rx σ) = get_reg_files σ.
Proof.
  rewrite /empty_rx.
  destruct (σ.1.1.1.1.2 !!! σ.1.1.2).
  destruct p.
  done.
Qed.

Lemma p_empty_rx_mb σ:
  get_mb_gmap (empty_rx σ) = (get_mb_gmap σ).
Proof.
  rewrite /empty_rx.
  destruct (σ.1.1.1.1.2 !!! σ.1.1.2) eqn:Heqn_mb.
  destruct p.
  rewrite /get_mb_gmap /=.
  set i := (σ.1.1.2).
  apply map_eq.
  intros [j RT].
  destruct (list_to_map (flat_map (λ v : VMID, [(v, TX, (σ.1.1.1.1.2 !!! v).1); (v, RX, (σ.1.1.1.1.2 !!! v).2.1)]) list_of_vmids) !! (j, RT)) eqn:Heqn.
  rewrite -elem_of_list_to_map'.
  rewrite elem_of_list_In.
  rewrite in_flat_map.
  exists j.
  split. apply in_list_of_vmids.
  apply elem_of_list_to_map_2 in Heqn.
  rewrite elem_of_list_In in Heqn.
  rewrite in_flat_map in Heqn.
  rewrite -elem_of_list_In.
  destruct Heqn as [? [_ ?]].
  apply in_inv in H.
  destruct H.
  inversion H.
  subst x RT.
  assert (p0 = (vinsert i (t, (p, None)) σ.1.1.1.1.2 !!! j).1).
  {
    destruct (decide (i = j)).
    subst j.
    rewrite vlookup_insert /=.
    rewrite Heqn_mb in H3.
    simpl in H3.
    done.
    rewrite vlookup_insert_ne;last done.
    done.
  }
  rewrite -H0 H.
  apply elem_of_list_here.
  apply elem_of_list_further.
  apply in_inv in H.
  destruct H.
  2:{
    apply in_nil in H.
    done.
  }
  inversion H.
  subst x RT.
  assert (p0 = (vinsert i (t, (p, None)) σ.1.1.1.1.2 !!! j).2.1).
  {
    simpl in H3.
    destruct (decide (i = j)).
    subst j.
    rewrite vlookup_insert /=.
    rewrite Heqn_mb in H.
    inversion H.
    done.
    rewrite vlookup_insert_ne;last done.
    done.
  }
  rewrite H H0.
  apply elem_of_list_here.
  {
    intros.
    rewrite elem_of_list_In in H.
    rewrite elem_of_list_In in H0.
    rewrite in_flat_map in H.
    rewrite in_flat_map in H0.
    destruct H as [? [_ ?]].
    destruct H0 as [? [_ ?]].
    apply in_inv in H.
    destruct H.
    inversion H.
    subst x RT.
    apply in_inv in H0.
    destruct H0.
    2: {
      apply in_inv in H0.
      destruct H0;last done.
      inversion H0.
    }
    inversion H0.
    done.
    apply in_inv in H.
    destruct H;last done.
    inversion H.
    subst x RT.
    apply in_inv in H0.
    destruct H0.
    inversion H0.
    apply in_inv in H0.
    destruct H0;last done.
    inversion H0.
    done.
  }
  apply not_elem_of_list_to_map in Heqn.
  exfalso.
  apply Heqn.
  rewrite elem_of_list_fmap.
  destruct RT.
  {
    exists (j,RX, (σ.1.1.1.1.2 !!! j).2.1).
    split;first done.
    rewrite elem_of_list_In.
    rewrite in_flat_map.
    exists j.
    split;first apply in_list_of_vmids.
    rewrite -elem_of_list_In.
    apply elem_of_list_further.
    apply elem_of_list_here.
  }
  {
    exists (j,TX, (σ.1.1.1.1.2 !!! j).1).
    split;first done.
    rewrite elem_of_list_In.
    rewrite in_flat_map.
    exists j.
    split;first apply in_list_of_vmids.
    rewrite -elem_of_list_In.
    apply elem_of_list_here.
  }
Qed.

Lemma p_empty_rx_pgt σ:
  get_page_table (empty_rx σ)  = get_page_table σ.
Proof.
  rewrite /empty_rx.
  destruct (σ.1.1.1.1.2 !!! σ.1.1.2).
  destruct p.
  done.
Qed.

Lemma p_empty_rx_trans σ :
  get_transactions (empty_rx σ) = (get_transactions σ).
Proof.
  rewrite /empty_rx.
  destruct (σ.1.1.1.1.2 !!! σ.1.1.2).
  destruct p.
  done.
Qed.

Lemma u_empty_rx_mb σ:
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
