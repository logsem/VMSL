From HypVeri Require Import machine machine_extra tactics.
From HypVeri.algebra Require Import base.

Section trans_extra.

Context `{HyperConst : HypervisorConstants}.

Lemma alloc_transaction_preserve_current_vm σ h trans:
  get_current_vm (alloc_transaction σ h trans) = get_current_vm σ.
Proof. f_equal. Qed.

Lemma alloc_transaction_preserve_regs σ h trans:
  get_reg_gmap (alloc_transaction σ h trans) = get_reg_gmap σ.
Proof. f_equal. Qed.

Lemma alloc_transaction_preserve_mem σ h trans:
  get_mem (alloc_transaction σ h trans) = get_mem σ.
Proof. f_equal. Qed.

Lemma alloc_transaction_preserve_tx σ h trans:
  get_tx_agree (alloc_transaction σ h trans) = get_tx_agree σ.
Proof. f_equal. Qed.

Lemma alloc_transaction_preserve_rx1 σ h trans:
  get_rx_agree (alloc_transaction σ h trans) = get_rx_agree σ.
Proof. f_equal. Qed.

Lemma alloc_transaction_preserve_rx2 σ h trans:
  get_rx_gmap(alloc_transaction σ h trans) = get_rx_gmap σ.
Proof. f_equal. Qed.

Lemma alloc_transaction_preserve_rx  σ h trans:
  (get_rx_agree (alloc_transaction σ h trans), get_rx_gmap (alloc_transaction σ h trans) ) =
  (get_rx_agree σ, get_rx_gmap σ).
Proof. by rewrite alloc_transaction_preserve_rx1 alloc_transaction_preserve_rx2 . Qed.

Lemma alloc_transaction_preserve_owned σ h trans:
  get_owned_gmap (alloc_transaction σ h trans) = get_owned_gmap σ.
Proof. f_equal. Qed.
Lemma alloc_transaction_preserve_access σ h trans:
  get_access_gmap (alloc_transaction σ h trans) = get_access_gmap σ.
Proof. f_equal. Qed.

Lemma alloc_transaction_preserve_excl σ h trans:
  get_excl_gmap (alloc_transaction σ h trans) = get_excl_gmap σ.
Proof. f_equal. Qed.



Lemma insert_transaction_update_transactions{Info:Type}{σ} (proj: transaction -> Info) h tran shp:
  (get_transactions_gmap (insert_transaction σ h tran shp) proj)
  = <[h:= (proj tran)]>(get_transactions_gmap σ proj).
Proof.
  rewrite /get_transactions_gmap //=.
  apply map_eq.
  intro.
  destruct (decide (h=i)).
  - subst i;rewrite lookup_insert.
    apply elem_of_list_to_map_1'.
    + intros.
      inv_map_in.
      inversion H.
      subst h.
      destruct x;simpl.
      apply elem_of_list_In in H0.
      apply elem_of_map_to_list' in H0.
      simpl in H0.
      rewrite lookup_insert in H0.
      inversion H0;subst t.
      done.
    + inv_map_in.
      exists (h, tran).
      split.
      done.
      apply elem_of_list_In.
      apply elem_of_map_to_list'.
      apply lookup_insert.
  - rewrite lookup_insert_ne;eauto.
    destruct (list_to_map (map (λ p : Addr * transaction, (p.1, (proj p.2) )) (map_to_list (get_transactions σ).1)) !! i) eqn:Heqn.
    + apply elem_of_list_to_map_2 in Heqn.
      apply elem_of_list_In in Heqn.
      apply in_map_iff in Heqn.
      destruct Heqn.
      destruct H.
      inversion H.
      subst i.
      destruct x;simpl in *.
      apply elem_of_list_In in H0.
      apply elem_of_map_to_list' in H0.
      simpl in H0.
      apply elem_of_list_to_map_1'.
      * intros.
        inv_map_in.
        inversion H1.
        subst f.
        destruct x;simpl in *.
        apply elem_of_list_In in H2.
        apply elem_of_map_to_list' in H2.
        simpl in H2.
        rewrite lookup_insert_ne in H2;eauto.
        rewrite H2 in H0.
        inversion H0;subst t.
        done.
      * inv_map_in.
        exists (f, t).
        split.
        done.
        apply elem_of_list_In.
        apply elem_of_map_to_list'.
        simpl.
        rewrite lookup_insert_ne;eauto.
    + apply not_elem_of_list_to_map_1.
      apply not_elem_of_list_to_map_2 in Heqn.
      intro.
      apply Heqn.
      apply elem_of_list_In in H.
      apply in_map_iff in H.
      destruct H.
      destruct H.
      destruct H.
      apply elem_of_list_In in H0.
      apply elem_of_list_In in H0.
      apply in_map_iff in H0.
      destruct H0.
      destruct H.
      destruct x;inversion H.
      apply elem_of_list_In in H0.
      apply elem_of_map_to_list' in H0.
      simpl in *.
      subst f.
      rewrite lookup_insert_ne in H0;eauto.
      apply elem_of_list_In.
      apply in_map_iff.
      exists (x0.1,i).
      split;[done|].
      apply in_map_iff.
      exists (x0.1,x0.2).
      subst i;split;[done|].
      apply elem_of_list_In.
      apply elem_of_map_to_list'.
      apply H0.
Qed.


Lemma alloc_transaction_update_transactions{Info:Type}{σ} (proj: transaction -> Info) h tran:
  (get_transactions_gmap (alloc_transaction σ h tran) proj)
  = <[h:= (proj tran)]>(get_transactions_gmap σ proj).
Proof.
  apply insert_transaction_update_transactions.
Qed.

Lemma update_transaction_preserve_trans {j wf i psd tt} σ wh b b' :
  (get_transactions σ).1 !! wh = Some (j, wf, b, i, psd, tt) ->
   (get_trans_gmap (update_transaction σ wh (j, wf, b', i, psd, tt)))
  = get_trans_gmap σ.
Proof.
  intros H.
  rewrite /get_trans_gmap /get_transactions_gmap //=.
  apply map_eq.
  intros x.
  assert (HlkSome : ∀  m k v,
               m !! k = Some v ->
               ((list_to_map
    (map (λ p : handle * transaction, (p.1, (p.2.1.1.1.1.1, p.2.1.1.1.1.2, p.2.1.1.2, p.2.1.2, p.2.2)))
       (map_to_list m))): gmap _ _) !! k =
            Some (v.1.1.1.1.1, v.1.1.1.1.2, v.1.1.2, v.1.2, v.2)).
    {
      intros.
    apply elem_of_list_to_map_1'.
    - intros t P.
      apply elem_of_list_In in P.
      apply in_map_iff in P.
      destruct P as [r [P1 P2]].
      apply elem_of_list_In in P2.
      apply elem_of_map_to_list' in P2.
      inversion P1; subst; clear P1.
      rewrite H0 in P2.
      inversion P2.
      done.
    - apply elem_of_list_In.
      apply in_map_iff.
      exists (k,v).
      split; auto.
      apply elem_of_list_In.
      apply elem_of_map_to_list'.
      rewrite //=.
    }
  destruct (((list_to_map
    (map (λ p : handle * transaction, (p.1, (p.2.1.1.1.1.1, p.2.1.1.1.1.2, p.2.1.1.2, p.2.1.2, p.2.2)))
       (map_to_list (<[wh:= (j, wf, b', i, psd, tt)]> (get_transactions σ).1)))):gmap _ _) !! x) eqn:Heqn.
  - apply elem_of_list_to_map_2 in Heqn.
    apply elem_of_list_In in Heqn.
    apply in_map_iff in Heqn.
    destruct Heqn as [y [Heqn1 Heqn2]].
    apply elem_of_list_In in Heqn2.
    apply elem_of_map_to_list' in Heqn2.
    inversion Heqn1; subst; clear Heqn1.
    rewrite (HlkSome  (<[wh:= (j, wf, b', i, psd, tt)]> (get_transactions σ).1) y.1 y.2);auto.
    symmetry.
    apply elem_of_list_to_map_1'.
    + intros t P.
      apply elem_of_list_In in P.
      apply in_map_iff in P.
      destruct P as [r [P1 P2]].
      apply elem_of_list_In in P2.
      apply elem_of_map_to_list' in P2.
      inversion P1; subst; clear P1.
      destruct (decide (wh = y.1)).
      * simplify_eq.
        rewrite lookup_insert in Heqn2.
        inversion Heqn2; subst; clear Heqn2.
        simpl.
        rewrite H1 in P2.
        rewrite H in P2.
        inversion P2.
        reflexivity.
      * rewrite H1 in P2.
        rewrite lookup_insert_ne in Heqn2; auto.
        rewrite P2 in Heqn2.
        inversion Heqn2; subst; clear Heqn2; reflexivity.
    + apply elem_of_list_In.
      apply in_map_iff.
      destruct (decide (wh = y.1)).
      * simplify_eq.
        rewrite lookup_insert in Heqn2.
        inversion Heqn2; subst; clear Heqn2.
        simpl.
        exists (y.1, ((j, wf, b, i, psd, tt))).
        split; auto.
        apply elem_of_list_In.
        apply elem_of_map_to_list'.
        rewrite //=.
      * rewrite lookup_insert_ne in Heqn2; auto.
        exists (y.1, y.2).
        split; auto.
        apply elem_of_list_In.
        apply elem_of_map_to_list'.
        rewrite //=.
  - rewrite Heqn.
    destruct (decide (wh = x)).
    + subst wh.
      symmetry.
      apply not_elem_of_list_to_map_1.
      intros P.
      apply not_elem_of_list_to_map_2 in Heqn.
      apply Heqn.
      rewrite <-list_fmap_compose.
      rewrite <-list_fmap_compose in P.
      rewrite /compose.
      rewrite /compose in P.
      simpl in *.
      apply elem_of_list_In.
      apply in_map_iff.
      apply elem_of_list_In in P.
      apply in_map_iff in P.
      destruct P as [t [P1 P2]].
      exists (t.1, (j, wf, b', i, psd, tt)).
      split; auto.
      apply elem_of_list_In.
      apply elem_of_map_to_list'.
      simpl.
      subst x.
      apply lookup_insert.
    + symmetry.
      apply not_elem_of_list_to_map_1.
      intros P.
      apply not_elem_of_list_to_map_2 in Heqn.
      apply Heqn.
      rewrite <-list_fmap_compose.
      rewrite <-list_fmap_compose in P.
      rewrite /compose.
      rewrite /compose in P.
      simpl in *.
      apply elem_of_list_In.
      apply in_map_iff.
      apply elem_of_list_In in P.
      apply in_map_iff in P.
      destruct P as [t [P1 P2]].
      apply elem_of_list_In in P2.
      destruct t as [t1 t2].
      apply elem_of_map_to_list in P2.
      exists (t1, t2).
      split; auto.
      apply elem_of_list_In.
      apply elem_of_map_to_list'.
      simpl.
      subst x.
      simpl in n.
      rewrite lookup_insert_ne; auto.
Qed.

Lemma get_retri_gmap_to_get_transaction σ wh {j wf b i psd tt}:
  (<[wh:=b]> (get_retri_gmap σ)) =
  (get_retri_gmap
     (get_reg_files σ, get_mail_boxes σ, get_page_tables σ,
      get_current_vm σ, get_mem σ,
      (<[wh := (j, wf, b, i, psd, tt)]>
       (get_transactions σ).1, (get_transactions σ).2))).
Proof.
  rewrite /get_retri_gmap.
  rewrite /get_transactions_gmap.
  apply map_eq.
  intros x.
  destruct (list_to_map
              (map (λ p : Addr * transaction, (p.1, p.2.1.1.1.2))
                   (map_to_list
                      (get_transactions
                         (get_reg_files σ, get_mail_boxes σ, get_page_tables σ,
                          get_current_vm σ, get_mem σ,
                          (<[wh := (j, wf, b, i, psd, tt)]> (get_transactions σ).1, (get_transactions σ).2))).1))
              !! x) eqn:Heqn.
  - apply elem_of_list_to_map_2 in Heqn.
    apply elem_of_list_In in Heqn.
    apply in_map_iff in Heqn.
    destruct Heqn as [y [Heqn1 Heqn2]].
    apply elem_of_list_In in Heqn2.
    apply elem_of_map_to_list' in Heqn2.
    inversion Heqn1; subst; clear Heqn1.
    destruct (decide (wh = y.1)).
    + subst.
      rewrite /get_transactions in Heqn2.
      simpl in Heqn2.
      apply lookup_insert_rev in Heqn2.
      inversion Heqn2; subst; clear Heqn2.
      simpl.
      apply lookup_insert.
    + rewrite /get_transactions in Heqn2.
      simpl in Heqn2.
      rewrite ->lookup_insert_Some in Heqn2.
      destruct Heqn2 as [H | H].
      destruct H; done.
      destruct H as [_ H].
      rewrite ->lookup_insert_Some.
      right.
      split; auto.
      apply elem_of_list_to_map_1'.
      intros y' Q.
      apply elem_of_list_In in Q.
      apply in_map_iff in Q.
      destruct Q as [r [Q1 Q2]].
      inversion Q1; subst; clear Q1.
      rewrite (surjective_pairing r) in Q2.
      apply elem_of_list_In in Q2.
      apply elem_of_map_to_list' in Q2.
      simpl in Q2.
      rewrite /get_transactions in Q2.
      rewrite H1 in Q2.
      rewrite Q2 in H.
      inversion H; subst; clear H.
      f_equal.
      apply elem_of_list_In.
      apply in_map_iff.
      exists (y.1, y.2).
      split; auto.
      rewrite /get_transactions.
      apply elem_of_list_In.
      apply elem_of_map_to_list.
      assumption.
  - rewrite <-not_elem_of_list_to_map in Heqn.
    simpl in Heqn.
    destruct (decide (wh = x)).
    + subst.
      exfalso.
      apply Heqn.
      rewrite <-list_fmap_compose.
      rewrite /compose.
      simpl.
      apply elem_of_list_In.
      apply in_map_iff.
      exists (x, (j, wf, b, i, psd, tt)).
      split; auto.
      apply elem_of_list_In.
      apply elem_of_map_to_list'.
      simpl.
      rewrite lookup_insert; auto.
    + rewrite lookup_insert_ne; auto.
      rewrite <-not_elem_of_list_to_map.
      intros H.
      apply Heqn.
      rewrite ->elem_of_list_In in H.
      apply in_map_iff in H.
      destruct H as [x' [H1 H2]]; subst.
      apply in_map_iff in H2.
      destruct H2 as [x'' [H2 H3]].
      inversion H2; subst.
      rewrite elem_of_list_In.
      apply in_map_iff.
      exists (x''.1, x''.2.1.1.1.2).
      split; auto.
      apply in_map_iff.
      exists (x''.1, x''.2).
      split; auto.
      rewrite <-elem_of_list_In.
      apply elem_of_map_to_list'.
      simpl.
      rewrite lookup_insert_ne; auto.
      rewrite <-elem_of_map_to_list.
      rewrite elem_of_list_In.
      rewrite <-surjective_pairing.
      assumption.
Qed.

Lemma alloc_transaction_update_trans σ h tran:
  (get_trans_gmap (alloc_transaction σ h tran))
  = <[h:= (tran.1.1.1.1.1,tran.1.1.1.1.2,tran.1.1.2,tran.1.2, tran.2)]>(get_trans_gmap σ).
Proof.
  apply (alloc_transaction_update_transactions
           (λ tran, (tran.1.1.1.1.1,tran.1.1.1.1.2,tran.1.1.2,tran.1.2, tran.2))).
Qed.

Lemma alloc_transaction_update_hpool σ h tran:
  (get_hpool_gset (alloc_transaction σ h tran)) = ((get_hpool_gset σ) ∖ {[h]}).
Proof. rewrite /alloc_transaction /get_hpool_gset /= //. Qed.

Lemma alloc_transaction_update_retri σ h tran:
  (get_retri_gmap (alloc_transaction σ h tran)) = <[h:=tran.1.1.1.2]>(get_retri_gmap σ).
Proof.
  apply (alloc_transaction_update_transactions (λ tran, tran.1.1.1.2)).
Qed.

Lemma update_transaction_preserve_current_vm σ h trans:
  get_current_vm (update_transaction σ h trans) = get_current_vm σ.
Proof. f_equal. Qed.

Lemma update_transaction_preserve_regs σ h trans:
  get_reg_gmap (update_transaction σ h trans) = get_reg_gmap σ.
Proof. f_equal. Qed.

Lemma update_transaction_preserve_mem σ h trans:
  get_mem (update_transaction σ h trans) = get_mem σ.
Proof. f_equal. Qed.

Lemma update_transaction_preserve_tx σ h trans:
  get_tx_agree (update_transaction σ h trans) = get_tx_agree σ.
Proof. f_equal. Qed.

Lemma update_transaction_preserve_rx1 σ h trans:
  get_rx_agree (update_transaction σ h trans) = get_rx_agree σ.
Proof. f_equal. Qed.

Lemma update_transaction_preserve_rx2 σ h trans:
  get_rx_gmap(update_transaction σ h trans) = get_rx_gmap σ.
Proof. f_equal. Qed.

Lemma update_transaction_preserve_rx  σ h trans:
  (get_rx_agree (update_transaction σ h trans), get_rx_gmap (update_transaction σ h trans) ) =
  (get_rx_agree σ, get_rx_gmap σ).
Proof. by rewrite update_transaction_preserve_rx1 update_transaction_preserve_rx2 . Qed.

Lemma update_transaction_preserve_owned σ h trans:
  get_owned_gmap (update_transaction σ h trans) = get_owned_gmap σ.
Proof. f_equal. Qed.
Lemma update_transaction_preserve_access σ h trans:
  get_access_gmap (update_transaction σ h trans) = get_access_gmap σ.
Proof. f_equal. Qed.

Lemma update_transaction_preserve_excl σ h trans:
  get_excl_gmap (update_transaction σ h trans) = get_excl_gmap σ.
Proof. f_equal. Qed.

Lemma update_transaction_preserve_hpool σ h tran:
  (get_hpool_gset (update_transaction σ h tran)) = (get_hpool_gset σ).
Proof. f_equal. Qed.


Lemma update_transaction_update_transactions{Info:Type}{σ} (proj: transaction -> Info) h tran:
  (get_transactions_gmap (update_transaction σ h tran) proj)
  = <[h:= (proj tran)]>(get_transactions_gmap σ proj).
Proof.
  apply insert_transaction_update_transactions.
Qed.

Lemma update_transaction_update_trans σ h tran:
  (get_trans_gmap (update_transaction σ h tran))
  = <[h:= (tran.1.1.1.1.1,tran.1.1.1.1.2,tran.1.1.2,tran.1.2, tran.2)]>(get_trans_gmap σ).
Proof.
  apply (update_transaction_update_transactions
           (λ tran, (tran.1.1.1.1.1,tran.1.1.1.1.2,tran.1.1.2,tran.1.2, tran.2))).
Qed.

Lemma update_transaction_update_retri σ h tran:
  (get_retri_gmap (update_transaction σ h tran)) = <[h:=tran.1.1.1.2]>(get_retri_gmap σ).
Proof.
  apply (update_transaction_update_transactions (λ tran, tran.1.1.1.2)).
Qed.

Lemma get_transactions_gmap_preserve_dom {Info:Type} {σ} (proj : transaction->Info):
  dom (gset handle) (get_transactions_gmap σ proj) = dom (gset handle) (get_transactions σ).1.
Proof.
  apply set_eq.
  split.
  - intros.
    apply elem_of_dom.
    apply elem_of_dom in H.
    destruct H.
    rewrite /get_trans_gmap in H.
    apply  elem_of_list_to_map_2 in H.
    inv_map_in.
    apply elem_of_list_In in H0.
    destruct x1.
    apply (elem_of_map_to_list) in H0.
    inversion H;subst f.
    eexists.
    done.
  - intros.
    apply elem_of_dom.
    apply elem_of_dom in H.
    destruct H.
    rewrite /get_trans_gmap.
    exists (proj x0).
    apply elem_of_list_to_map'.
    intros.
    inv_map_in.
    inversion H1;subst x.
    clear H5 H1.
    apply elem_of_list_In in H2.
    destruct x1.
    apply (elem_of_map_to_list) in H2.
    simpl in *.
    rewrite H2 in H.
    inversion H;subst t.
    done.
    inv_map_in.
    exists (x,x0).
    split;[done|].
    apply elem_of_list_In.
      by apply (elem_of_map_to_list).
Qed.

Lemma get_trans_gmap_preserve_dom {σ}:
  dom (gset handle) (get_trans_gmap σ) = dom (gset handle) (get_transactions σ).1.
Proof.
  apply get_transactions_gmap_preserve_dom.
Qed.

Lemma get_retri_gmap_preserve_dom {σ}:
  dom (gset handle) (get_retri_gmap σ) = dom (gset handle) (get_transactions σ).1.
Proof.
  apply get_transactions_gmap_preserve_dom.
Qed.

Lemma remove_transaction_preserve_current_vm σ h:
  get_current_vm (remove_transaction σ h) = get_current_vm σ.
Proof. f_equal. Qed.

Lemma remove_transaction_preserve_regs σ h :
  get_reg_gmap (remove_transaction σ h ) = get_reg_gmap σ.
Proof. f_equal. Qed.

Lemma remove_transaction_preserve_mem σ h :
  get_mem (remove_transaction σ h ) = get_mem σ.
Proof. f_equal. Qed.

Lemma remove_transaction_preserve_tx σ h :
  get_tx_agree (remove_transaction σ h ) = get_tx_agree σ.
Proof. f_equal. Qed.

Lemma remove_transaction_preserve_rx1 σ h :
  get_rx_agree (remove_transaction σ h ) = get_rx_agree σ.
Proof. f_equal. Qed.

Lemma remove_transaction_preserve_rx2 σ h :
  get_rx_gmap(remove_transaction σ h ) = get_rx_gmap σ.
Proof. f_equal. Qed.

Lemma remove_transaction_preserve_rx  σ h :
  (get_rx_agree (remove_transaction σ h ), get_rx_gmap (remove_transaction σ h ) ) =
  (get_rx_agree σ, get_rx_gmap σ).
Proof. by rewrite remove_transaction_preserve_rx1 remove_transaction_preserve_rx2 . Qed.

Lemma remove_transaction_preserve_owned σ h :
  get_owned_gmap (remove_transaction σ h ) = get_owned_gmap σ.
Proof. f_equal. Qed.
Lemma remove_transaction_preserve_access σ h :
  get_access_gmap (remove_transaction σ h ) = get_access_gmap σ.
Proof. f_equal. Qed.

Lemma remove_transaction_preserve_excl σ h :
  get_excl_gmap (remove_transaction σ h ) = get_excl_gmap σ.
Proof. f_equal. Qed.


Lemma remove_transaction_update_transactions{Info:Type}{σ} (proj: transaction -> Info) h :
  (get_transactions_gmap (remove_transaction σ h) proj)
  = (delete h (get_transactions_gmap σ proj)).
Proof.
  rewrite /get_transactions_gmap //=.
  apply map_eq.
  intro.
  destruct (decide (h=i)).
  - subst i;rewrite lookup_delete.
    apply not_elem_of_list_to_map_1.
    rewrite <-list_fmap_compose.
    rewrite /compose.
    cbn.
    intro HIn.
    apply elem_of_list_In in HIn.
    apply in_map_iff in HIn.
    destruct HIn as [? [Heqh HIn]].
    subst h.
    destruct x;cbn in HIn.
    apply elem_of_list_In in HIn.
    apply elem_of_map_to_list' in HIn.
    cbn in HIn.
    rewrite lookup_delete  //in HIn.
  - rewrite lookup_delete_ne;eauto.
    destruct (list_to_map (map (λ p : Addr * transaction, (p.1, (proj p.2) )) (map_to_list (get_transactions σ).1)) !! i) eqn:Heqn.
    + apply elem_of_list_to_map_2 in Heqn.
      apply elem_of_list_In in Heqn.
      apply in_map_iff in Heqn.
      destruct Heqn.
      destruct H.
      inversion H.
      subst i.
      destruct x;simpl in *.
      apply elem_of_list_In in H0.
      apply elem_of_map_to_list' in H0.
      simpl in H0.
      apply elem_of_list_to_map_1'.
      * intros.
        inv_map_in.
        inversion H1.
        subst f.
        destruct x;simpl in *.
        apply elem_of_list_In in H2.
        apply elem_of_map_to_list' in H2.
        simpl in H2.
        rewrite lookup_delete_ne in H2;eauto.
        rewrite H2 in H0.
        inversion H0;subst t.
        done.
      * inv_map_in.
        exists (f, t).
        split.
        done.
        apply elem_of_list_In.
        apply elem_of_map_to_list'.
        simpl.
        rewrite lookup_delete_ne;eauto.
    + apply not_elem_of_list_to_map_1.
      apply not_elem_of_list_to_map_2 in Heqn.
      intro.
      apply Heqn.
      apply elem_of_list_In in H.
      apply in_map_iff in H.
      destruct H.
      destruct H.
      destruct H.
      apply elem_of_list_In in H0.
      apply elem_of_list_In in H0.
      apply in_map_iff in H0.
      destruct H0.
      destruct H.
      destruct x;inversion H.
      apply elem_of_list_In in H0.
      apply elem_of_map_to_list' in H0.
      simpl in *.
      subst f.
      rewrite lookup_delete_ne in H0;eauto.
      apply elem_of_list_In.
      apply in_map_iff.
      exists (x0.1,i).
      split;[done|].
      apply in_map_iff.
      exists (x0.1,x0.2).
      subst i;split;[done|].
      apply elem_of_list_In.
      apply elem_of_map_to_list'.
      apply H0.
Qed.

Lemma remove_transaction_update_trans σ h :
  (get_trans_gmap (remove_transaction σ h ))
  = (delete h (get_trans_gmap σ)).
Proof.
  apply (remove_transaction_update_transactions
           (λ tran, (tran.1.1.1.1.1,tran.1.1.1.1.2,tran.1.1.2,tran.1.2, tran.2))).
Qed.

Lemma remove_transaction_update_hpool σ h :
  (get_hpool_gset (remove_transaction σ h )) = ((get_hpool_gset σ) ∪ {[h]}).
Proof. rewrite /remove_transaction /get_hpool_gset /= //. Qed.

Lemma remove_transaction_update_retri σ h :
  (get_retri_gmap (remove_transaction σ h )) = (delete h (get_retri_gmap σ)).
Proof.
  apply (remove_transaction_update_transactions (λ tran, tran.1.1.1.2)).
Qed.

Lemma get_retri_gmap_lookup {σ i j wf psd tt} wh b:
(get_transactions σ).1 !! wh = Some (i, wf, b, j, psd, tt)->
get_retri_gmap σ !! wh = Some b.
Proof.
  intros Hlk.
  rewrite /get_retri_gmap /get_transactions_gmap.
  apply elem_of_list_to_map_1'.
  intros y Hy.
  apply elem_of_list_In in Hy.
  apply in_map_iff in Hy.
  destruct Hy as [y' [Hy1 Hy2]].
  inversion Hy1; subst; clear Hy1.
  apply elem_of_list_In in Hy2.
  apply elem_of_map_to_list' in Hy2.
  rewrite Hlk in Hy2.
  inversion Hy2; subst; clear Hy2.
  reflexivity.
  apply elem_of_list_In.
  apply in_map_iff.
  exists (wh,(i, wf, b, j, psd, tt)).
  split.
  reflexivity.
  apply elem_of_list_In.
  apply elem_of_map_to_list'.
  simpl.
  assumption.
Qed.

End trans_extra.


Ltac rewrite_trans_alloc :=
  match goal with
  | |- _ =>
    try rewrite -> alloc_transaction_preserve_current_vm;
    try rewrite -> alloc_transaction_preserve_regs;
    try rewrite -> alloc_transaction_preserve_mem;
    try rewrite -> alloc_transaction_preserve_tx;
    try rewrite -> alloc_transaction_preserve_rx1;
    try rewrite -> alloc_transaction_preserve_rx2;
    try rewrite -> alloc_transaction_preserve_owned;
    try rewrite -> alloc_transaction_preserve_access;
    try rewrite -> alloc_transaction_preserve_excl
  end.

Ltac rewrite_trans_update :=
  match goal with
  | |- _ =>
    try rewrite -> update_transaction_preserve_current_vm;
    try rewrite -> update_transaction_preserve_regs;
    try rewrite -> update_transaction_preserve_mem;
    try rewrite -> update_transaction_preserve_tx;
    try rewrite -> update_transaction_preserve_rx1;
    try rewrite -> update_transaction_preserve_rx2;
    try rewrite -> update_transaction_preserve_owned;
    try rewrite -> update_transaction_preserve_access;
    try rewrite -> update_transaction_preserve_excl;
    try rewrite -> update_transaction_preserve_hpool
  end.

Ltac rewrite_trans_remove :=
  match goal with
  | |- _ =>
    try rewrite -> remove_transaction_preserve_current_vm;
    try rewrite -> remove_transaction_preserve_regs;
    try rewrite -> remove_transaction_preserve_mem;
    try rewrite -> remove_transaction_preserve_tx;
    try rewrite -> remove_transaction_preserve_rx1;
    try rewrite -> remove_transaction_preserve_rx2;
    try rewrite -> remove_transaction_preserve_owned;
    try rewrite -> remove_transaction_preserve_access;
    try rewrite -> remove_transaction_preserve_excl
  end.
