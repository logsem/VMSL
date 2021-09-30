From HypVeri.algebra Require Import base.

Section mailbox_rules.

  Context `{vmG :gen_VMG Σ}.

  (* rules for TX *)
  Lemma tx_dupl i p :
   TX@ i := p -∗ TX@ i := p ∗ TX@ i := p.
  Proof using.
    rewrite tx_mapsto_eq.
    iIntros "Htx".
    iApply own_op.
    rewrite -auth_frag_op singleton_op.
    rewrite agree_idemp.
    done.
  Qed.

  Lemma get_txrx_auth_agree_valid σ f:
   ✓ (get_txrx_auth_agree σ f).
  Proof.
    rewrite /get_txrx_auth_agree.
    induction list_of_vmids;cbn.
    done.
    apply (insert_valid _ a ((to_agree (f (get_vm_mail_box σ a))): (agreeR (leibnizO PID))));auto.
    done.
  Qed.

  Lemma gen_tx_valid {σ} i p:
   TX@ i := p -∗ own (gen_tx_name vmG) (● (get_tx_agree σ)) -∗ ⌜ (get_vm_mail_box σ i).1 = p ⌝.
  Proof.
    iIntros "Htx Hσ".
    rewrite tx_mapsto_eq /tx_mapsto_def.
    destruct σ as [[[[[? σ'] ?] ?] ?] ?].
    rewrite /get_tx_agree /get_txrx_auth_agree /get_vm_mail_box /get_mail_boxes.
    iDestruct (own_valid_2 with "Hσ Htx") as %Hown.
    apply auth_both_valid_discrete in Hown.
    destruct Hown as [Hown1 Hown2].
    iPureIntro.
    pose proof (@lookup_included
                  VMID _ _
                  ((agreeR (leibnizO PID)))
                  {[i := to_agree p]}
                  (list_to_map (map (λ v : VMID, (v, to_agree (σ' !!! v).1)) list_of_vmids))) as Heqv.
    rewrite ->Heqv in Hown1.
    pose proof (Hown1 i) as Hlt1.
    apply option_included in Hlt1.
    destruct Hlt1 as [Hnone | Hsome].
    simplify_map_eq.
    destruct Hsome as (? & ? & Hsgsome & Hltmsome & Hle).
    apply lookup_singleton_Some in Hsgsome.
    simplify_map_eq /=.
    apply (elem_of_list_to_map_2 _ i x0) in Hltmsome.
    apply elem_of_list_In in Hltmsome.
    apply in_map_iff in Hltmsome.
    destruct Hltmsome as (? & Heqp & _).
    inversion Heqp;clear Heqp;subst.
    destruct Hsgsome as [_ <-].
    destruct Hle as [Heq | Hlt].
    - destruct (Heq 0) as [Heq' Heq''].
      assert (p ∈ [p]) as Hinp. apply elem_of_list_here.
      cbn in Heq'.
      specialize Heq' with p.
      destruct (Heq' Hinp) as [b [b1 b2]].
      inversion b1 as [|]; subst.
      + unfold dist in b2.
        unfold ofe_dist in b2.
        unfold discrete_dist in b2.
        rewrite b2 //.
      + inversion H.
    - apply to_agree_included in Hlt.
      rewrite Hlt //.
  Qed.

  (* rules for RX *)
  Lemma rx_split_some i p n (v: VMID):
   RX@ i :=( p ! n , v)  -∗ RX@ i :=( p ! n, v)  ∗ RX@ i := p.
  Proof using.
    iIntros "[HRa HRo]".
    rewrite rx_agree_mapsto_eq rx_option_mapsto_eq.
    iFrame "HRo".
    iApply own_op.
    rewrite -auth_frag_op.
    rewrite singleton_op agree_idemp //.
  Qed.

  Lemma rx_split_none i p:
   RX@ i :=(p !) -∗ RX@ i :=(p !) ∗ RX@ i := p.
  Proof using.
    iIntros "[HRa HRo]".
    rewrite rx_agree_mapsto_eq rx_option_mapsto_eq.
    iFrame "HRo".
    iApply own_op.
    rewrite -auth_frag_op.
    rewrite singleton_op agree_idemp //.
  Qed.

  Lemma rx_dupl i p:
   RX@i:=p -∗ RX@i:=p ∗ RX@i:=p.
  Proof using.
    iIntros "HR".
    rewrite rx_agree_mapsto_eq.
    iApply own_op.
    rewrite -auth_frag_op.
    rewrite singleton_op agree_idemp.
    naive_solver.
  Qed.

  Lemma gen_rx_agree_valid {σ} i p:
   ✓ (● get_rx_agree σ ⋅ ◯ {[i := to_agree p]}) -> (get_vm_mail_box σ i).2.1 = p.
  Proof.
    intro Hvalid.
    rewrite /get_rx_agree /get_txrx_auth_agree in Hvalid.
    apply auth_both_valid_discrete in Hvalid;destruct Hvalid as [Hlt _].
    remember  ((list_to_map (map (λ v : VMID,
                                        (v, to_agree (get_vm_mail_box σ v).2.1)) list_of_vmids)): gmap VMID (agreeR (leibnizO PID))) as m.
    rewrite -> (lookup_included {[i := to_agree p]} m) in Hlt.
    specialize Hlt with i.
    simplify_map_eq /=.
    apply option_included_total in Hlt;destruct Hlt as [Hnone |Hsome].
    rewrite -> (lookup_singleton_None i i (to_agree p)) in Hnone;done.
    destruct Hsome as [x [x0 [Hlk [Hltmlk Hlt]]]].
    rewrite -> (lookup_singleton_Some i i (to_agree p)) in Hlk.
    destruct Hlk; subst x.
    apply elem_of_list_to_map_2 in Hltmlk.
    apply elem_of_list_In in Hltmlk.
    apply in_map_iff in Hltmlk.
    destruct Hltmlk as [? [Heqp _]]. inversion Heqp;subst;clear Heqp.
    rewrite -> (to_agree_included (p: (leibnizO PID)) _) in Hlt.
      by fold_leibniz.
  Qed.

  Lemma gen_rx_pid_valid {σ} i p:
   RX@ i := p -∗
   own (gen_rx_agree_name vmG) (● (get_rx_agree σ))-∗
   ⌜(get_vm_mail_box σ i).2.1 = p⌝.
  Proof.
    iIntros "Hrx Hσ".
    rewrite rx_agree_mapsto_eq /rx_agree_mapsto_def.
    iDestruct (own_valid_2 with "Hσ Hrx") as %?.
    iPureIntro.
      by apply gen_rx_agree_valid .
  Qed.

  Lemma gen_rx_valid_none {σ} i p:
   RX@ i :=( p !) -∗
   ghost_map_auth (gen_rx_option_name vmG) 1 (get_rx_gmap σ)-∗
   ⌜(get_vm_mail_box σ i).2.2 = None⌝.
  Proof.
    iIntros "[_ Hrx] Hσ".
    rewrite rx_option_mapsto_eq /rx_option_mapsto_def.
    iDestruct (ghost_map_lookup with "Hσ Hrx") as "%Hnone".
    rewrite /get_rx_gmap in Hnone.
    apply elem_of_list_to_map_2 in Hnone.
    apply elem_of_list_In in Hnone.
    apply in_map_iff in Hnone.
    destruct Hnone as [x [Heqp _]].
    destruct ((get_vm_mail_box σ x).2.2) eqn:Heqn.
    destruct p0;inversion Heqp.
    inversion Heqp;subst.
    rewrite -Heqn //.
  Qed.

  Lemma gen_rx_valid_some {σ} i p l v:
   RX@ i :=( p ! l , v) -∗
   ghost_map_auth (gen_rx_option_name vmG) 1 (get_rx_gmap σ)-∗
   ⌜(get_vm_mail_box σ  i).2.2 = Some(l,v)⌝.
  Proof.
    iIntros "[_ Hrx] Hσ".
    rewrite rx_option_mapsto_eq /rx_option_mapsto_def.
    iDestruct (ghost_map_lookup with "Hσ Hrx") as "%Hlk".
    rewrite /get_rx_gmap in Hlk.
    apply elem_of_list_to_map_2 in Hlk.
    apply elem_of_list_In in Hlk.
    apply in_map_iff in Hlk.
    destruct Hlk as [x [Heqp _]].
    destruct ((get_vm_mail_box σ x).2.2) eqn:Heqn.
    destruct p0;inversion Heqp.
    inversion Heqp;subst.
    iPureIntro.
    rewrite -Heqn //.
    inversion Heqp.
  Qed.

  Lemma gen_rx_gmap_update_global_Some {_l _a σ} i l x rxp:
     ghost_map_auth (gen_rx_option_name vmG) 1 (get_rx_gmap σ) -∗
     RX@i:=(rxp!_l,_a) ==∗
     ghost_map_auth (gen_rx_option_name vmG) 1 (<[i:=Some (l, x)]>(get_rx_gmap σ)) ∗
     RX@i:=(rxp!l,x).
  Proof.
    iIntros "Hσ Hrx".
    rewrite rx_option_mapsto_eq /rx_option_mapsto_def.
    iDestruct "Hrx" as "(Hrx1 & Hrx2)".
    iDestruct (ghost_map_update (Some (l, x)) with "Hσ Hrx2") as ">[Hσ2 Hrx]".
    iFrame.
    done.
  Qed.

  Lemma gen_rx_gmap_update_global_None {σ} i l x rxp:
     ghost_map_auth (gen_rx_option_name vmG) 1 (get_rx_gmap σ) -∗
     RX@i:=(rxp!) ==∗
     ghost_map_auth (gen_rx_option_name vmG) 1 (<[i:=Some (l, x)]>(get_rx_gmap σ)) ∗
     RX@i:=(rxp!l,x).
  Proof.
    iIntros "Hσ Hrx".
    rewrite rx_option_mapsto_eq /rx_option_mapsto_def.
    iDestruct "Hrx" as "(Hrx1 & Hrx2)".
    iDestruct (ghost_map_update (Some (l, x)) with "Hσ Hrx2") as ">[Hσ2 Hrx]".
    iFrame.
    done.
  Qed.

  Lemma gen_rx_gmap_update_empty_global_Some {_l _a σ} i rxp:
     ghost_map_auth (gen_rx_option_name vmG) 1 (get_rx_gmap σ) -∗
     RX@i:=(rxp!_l,_a) ==∗
     ghost_map_auth (gen_rx_option_name vmG) 1 (<[i:=None]>(get_rx_gmap σ)) ∗
     RX@i:=(rxp!).
  Proof.
    iIntros "Hσ Hrx".
    rewrite rx_option_mapsto_eq /rx_option_mapsto_def.
    iDestruct "Hrx" as "(Hrx1 & Hrx2)".
    iDestruct (ghost_map_update None with "Hσ Hrx2") as ">[Hσ2 Hrx]".
    iFrame.
    done.
  Qed.

End mailbox_rules.
