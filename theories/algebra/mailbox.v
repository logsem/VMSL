From HypVeri.algebra Require Import base.

Section mailbox_rules.

  Context `{vmG :gen_VMG Σ}.
  Implicit Type σ : state.
  Implicit Type i : VMID.

  Lemma rx_owned_dupl_false i j w :
    RX@ i := w -∗ RX@ j := w -∗ False.
  Proof.
    rewrite owned_mb_mapsto_eq /owned_mb_mapsto_def.
    iIntros "Ha1 Ha2".
    iDestruct (ghost_map_elem_valid_2 with "Ha1 Ha2") as %Hvalid.
    destruct Hvalid as [Hvalid _].
    apply dfrac_valid_own_r in Hvalid.
    inversion Hvalid.
  Qed.

  Lemma rx_state_dupl_false i x x' :
    rx_state_mapsto i x -∗ rx_state_mapsto i x' -∗ False.
  Proof.
    rewrite rx_state_mapsto_eq /rx_state_mapsto_def.
    iIntros "Ha1 Ha2".
    iDestruct (ghost_map_elem_valid_2 with "Ha1 Ha2") as %Hvalid.
    destruct Hvalid as [Hvalid _].
    apply dfrac_valid_own_r in Hvalid.
    inversion Hvalid.
  Qed.

  Lemma rx_owned_valid {σ} i p :
    (RX@ i := p) -∗
    ghost_map_auth (gen_owned_mb_name vmG) 1 (get_owned_gmap σ) -∗
    ⌜(get_mail_box σ @ i).2.1 = p⌝.
  Proof.
    iIntros "Hrx Hrxown".
    rewrite owned_mb_mapsto_eq /owned_mb_mapsto_def.
    iDestruct (ghost_map_lookup with "Hrxown Hrx") as "%Hsome".
    iPureIntro.
    rewrite /get_owned_gmap in Hsome.
    set l := map_to_list ((λ p : VMID * gset VMID, (p.1, Owned)) <$> get_page_table σ).
    apply (elem_of_list_to_map_2 l p (i, Rx)) in Hsome.
    subst l.
    apply elem_of_map_to_list in Hsome.
    apply lookup_fmap_Some in Hsome.
    destruct Hsome as [x [Hsome1 Hsome2]].
    simplify_eq.
  Qed.

  Lemma rx_state_valid {σ} i x :
    (rx_state_mapsto i x) -∗
    ghost_map_auth (gen_rx_state_name vmG) 1 (get_rx_gmap σ) -∗
    ⌜(get_mail_box σ @ i).2.2 = x⌝.
  Proof.
    iIntros "Hrx Hrxown".
    rewrite rx_state_mapsto_eq /rx_state_mapsto_def.
    iDestruct (ghost_map_lookup with "Hrxown Hrx") as "%Hsome".
    iPureIntro.
    rewrite /get_rx_gmap /=in Hsome.
    set l := (map
               (λ v : fin vm_count,
                  match get_transactions (get_transactions get_mail_boxes σ !!! v) with
                  | Some (l, j) => (v, Some (l, j))
                  | None => (v, None)
                  end) list_of_vmids).
    apply (elem_of_list_to_map_2 l i x) in Hsome.
    subst l.
    rewrite ->elem_of_list_In in Hsome.
    rewrite ->in_map_iff in Hsome.
    destruct Hsome as [y [Hsome1 Hsome2]].
    destruct ((σ.1.1.1.1.2 !!! y).2.2) eqn:Heq; simplify_eq.
    - destruct p.
      inversion Hsome1.
      simplify_eq /=.
      done.
    - done.
  Qed.

  Lemma rx_state_valid_None {σ} i :
    (RX@i :=()) -∗
    ghost_map_auth (gen_rx_state_name vmG) 1 (get_rx_gmap σ) -∗
    ⌜(get_mail_box σ @ i).2.2 = None⌝.
  Proof.
    iIntros "H1 H2".
    by iApply (rx_state_valid with "H1 H2").
  Qed.

  Lemma rx_state_valid_Some {σ} i a b :
    (RX@i :=(a, b)) -∗
    ghost_map_auth (gen_rx_state_name vmG) 1 (get_rx_gmap σ) -∗
    ⌜(get_mail_box σ @ i).2.2 = Some (a, b)⌝.
  Proof.
    iIntros "H1 H2".
    by iApply (rx_state_valid with "H1 H2").
  Qed.

  Lemma gen_rx_gmap_update_global {σ} i x x' :
    ghost_map_auth (gen_rx_state_name vmG) 1 (get_rx_gmap σ) -∗
    (rx_state_mapsto i x) ==∗
    ghost_map_auth (gen_rx_state_name vmG) 1 (<[i:=x']>(get_rx_gmap σ)) ∗
    rx_state_mapsto i x'.
  Proof.
    iIntros "Hσ Hrx".
    rewrite rx_state_mapsto_eq /rx_state_mapsto_def.
    iDestruct (ghost_map_update (x') with "Hσ Hrx") as ">[Hσ2 Hrx]".
    iFrame.
    done.
  Qed.
  
  Lemma gen_rx_gmap_update_global_None {σ} i l x:
     ghost_map_auth (gen_rx_state_name vmG) 1 (get_rx_gmap σ) -∗
     RX@i:=() ==∗
     ghost_map_auth (gen_rx_state_name vmG) 1 (<[i:=Some (l, x)]>(get_rx_gmap σ)) ∗
     RX@i:=(l,x).
  Proof.
    iIntros "Hσ Hrx".
    by iApply (gen_rx_gmap_update_global with "Hσ Hrx").
  Qed.

  Lemma gen_rx_gmap_update_empty_global_Some {_l _a σ} i:
     ghost_map_auth (gen_rx_state_name vmG) 1 (get_rx_gmap σ) -∗
     RX@i:=(_l,_a) ==∗
     ghost_map_auth (gen_rx_state_name vmG) 1 (<[i:=None]>(get_rx_gmap σ)) ∗
     RX@i:=().
  Proof.
    iIntros "Hσ Hrx".
    by iApply (gen_rx_gmap_update_global with "Hσ Hrx").
  Qed.


  Lemma gen_tx_valid {σ} i p:
   TX@ i := p -∗ ghost_map_auth (gen_owned_mb_name vmG) 1 (get_mb_gmap σ)  -∗ ⌜ (get_mail_box σ @ i ).1 = p ⌝.
  Proof.
    iIntros "Htx Hσ".
    rewrite owned_mb_mapsto_eq /owned_mb_mapsto_def.
    destruct σ as [[[[[? mb] ?] ?] ?] ?].
    rewrite /get_mb_gmap.
    simpl.
    iDestruct (ghost_map_lookup with "Hσ Htx") as %Hlookup.
    apply elem_of_list_to_map_2 in Hlookup.
    apply elem_of_list_In in Hlookup.
    apply in_flat_map in Hlookup.
    destruct Hlookup as [? [? Hin]].
    apply elem_of_list_In in Hin.
    inversion Hin.
    subst.
    done.
    subst.
    set_solver + H2.
  Qed.

  Lemma gen_rx_valid {σ} i p:
   RX@ i := p -∗ ghost_map_auth (gen_owned_mb_name vmG) 1 (get_mb_gmap σ)  -∗ ⌜ (get_mail_box σ @ i ).2.1 = p ⌝.
  Proof.
    iIntros "Htx Hσ".
    rewrite owned_mb_mapsto_eq /owned_mb_mapsto_def.
    destruct σ as [[[[[? mb] ?] ?] ?] ?].
    rewrite /get_mb_gmap.
    simpl.
    iDestruct (ghost_map_lookup with "Hσ Htx") as %Hlookup.
    apply elem_of_list_to_map_2 in Hlookup.
    apply elem_of_list_In in Hlookup.
    apply in_flat_map in Hlookup.
    destruct Hlookup as [? [? Hin]].
    apply elem_of_list_In in Hin.
    inversion Hin.
    subst.
    inversion H2.
    subst.
    done.
    subst.
    set_solver + H3.
  Qed.


End mailbox_rules.
