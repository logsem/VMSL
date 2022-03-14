From HypVeri.algebra Require Import base base_extra.

Section mailbox_rules.

  Context `{vmG :gen_VMG Σ}.
  Implicit Type σ : state.
  Implicit Type i : VMID.

  Lemma rx_state_dupl_false i x x' :
    RX_state@i := x -∗  RX_state@i := x' -∗ False.
  Proof.
    rewrite rx_state_mapsto_eq /rx_state_mapsto_def.
    iIntros "Ha1 Ha2".
    iDestruct (ghost_map_elem_valid_2 with "Ha1 Ha2") as %Hvalid.
    destruct Hvalid as [Hvalid _].
    apply dfrac_valid_own_r in Hvalid.
    inversion Hvalid.
  Qed.

  Lemma rx_state_split i q x:
    RX_state{q}@i := x ⊣⊢ RX_state{q/2}@i := x ∗ RX_state{q/2}@i := x.
  Proof.
    rewrite rx_state_mapsto_eq /rx_state_mapsto_def.
    iApply (ghost_map_elem_split i _ q x).
  Qed.

  Lemma rx_state_agree i q1 q2 x x':
     RX_state{q1}@i := x -∗ RX_state{q2}@i := x' -∗ ⌜x = x'⌝.
  Proof.
    rewrite rx_state_mapsto_eq /rx_state_mapsto_def.
    iIntros "Ha1 Ha2".
    iDestruct (ghost_map_elem_valid_2 with "Ha1 Ha2") as %Hvalid.
    destruct Hvalid as [_ Hvalid].
    done.
  Qed.

  Lemma rx_state_valid {σ q} i x :
    ghost_map_auth gen_rx_state_name 1 (get_rx_gmap σ) -∗
    RX_state{q}@i := x-∗
    ⌜(get_mail_box σ @ i).2.2 = x⌝.
  Proof.
    iIntros "Hrxown Hrx".
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

  Lemma rx_state_valid_None {σ q} i :
    ghost_map_auth gen_rx_state_name 1 (get_rx_gmap σ) -∗
    (RX_state{q}@i := None) -∗
    ⌜(get_mail_box σ @ i).2.2 = None⌝.
  Proof.
    iIntros "H1 H2".
    by iApply (rx_state_valid with "H1 H2").
  Qed.

  Lemma rx_state_valid_Some {σ q} i a b :
    ghost_map_auth gen_rx_state_name 1 (get_rx_gmap σ) -∗
    (RX_state{q}@i := Some (a, b)) -∗
    ⌜(get_mail_box σ @ i).2.2 = Some (a, b)⌝.
  Proof.
    iIntros "H1 H2".
    by iApply (rx_state_valid with "H1 H2").
  Qed.

  Lemma rx_state_update {σ} i x x' :
    ghost_map_auth gen_rx_state_name 1 (get_rx_gmap σ) -∗
    RX_state@i := x ==∗
    ghost_map_auth gen_rx_state_name 1 (<[i:=x']>(get_rx_gmap σ)) ∗
    RX_state@i := x'.
  Proof.
    iIntros "Hσ Hrx".
    rewrite rx_state_mapsto_eq /rx_state_mapsto_def.
    iDestruct (ghost_map_update (x') with "Hσ Hrx") as ">[Hσ2 Hrx]".
    iFrame.
    done.
  Qed.
  
  Lemma rx_state_fill {σ} i l x:
     ghost_map_auth gen_rx_state_name 1 (get_rx_gmap σ) -∗
     RX_state@i := None ==∗
     ghost_map_auth gen_rx_state_name 1 (<[i:=Some (l, x)]>(get_rx_gmap σ)) ∗
     RX_state@i:= Some(l,x).
  Proof.
    iIntros "Hσ Hrx".
    by iApply (rx_state_update with "Hσ Hrx").
  Qed.

  Lemma rx_state_empty {_l _a σ} i:
     ghost_map_auth gen_rx_state_name 1 (get_rx_gmap σ) -∗
     RX_state@i:= Some(_l,_a) ==∗
     ghost_map_auth gen_rx_state_name 1 (<[i:=None]>(get_rx_gmap σ)) ∗
     RX_state@i:= None.
  Proof.
    iIntros "Hσ Hrx".
    by iApply (rx_state_update with "Hσ Hrx").
  Qed.

  Lemma mb_valid_tx {σ} i p:
   ghost_map_auth gen_mb_name 1 (get_mb_gmap σ) -∗
   TX@ i := p -∗ ⌜(get_mail_box σ @ i).1 = p⌝.
  Proof.
    iIntros "Hσ Htx".
    rewrite mb_mapsto_eq /mb_mapsto_def.
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

  Lemma mb_valid_rx {σ} i p:
   ghost_map_auth gen_mb_name 1 (get_mb_gmap σ) -∗
   RX@ i := p -∗ ⌜(get_mail_box σ @ i).2.1 = p⌝.
  Proof.
    iIntros "Hσ Hrx".
    rewrite mb_mapsto_eq /mb_mapsto_def.
    destruct σ as [[[[[? mb] ?] ?] ?] ?].
    rewrite /get_mb_gmap.
    simpl.
    iDestruct (ghost_map_lookup with "Hσ Hrx") as %Hlookup.
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

  Definition rx_page i p_rx := (RX@i := p_rx ∗ p_rx -@O> - ∗ p_rx -@E> true)%I.
  Definition tx_page i p_tx := (TX@i := p_tx ∗ p_tx -@O> - ∗ p_tx -@E> true)%I.

End mailbox_rules.
