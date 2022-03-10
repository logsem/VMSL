From machine_program_logic.program_logic Require Import weakestpre.
From HypVeri Require Import lifting rules.rules_base stdpp_extra.
From HypVeri.algebra Require Import base reg mem pagetable mailbox base_extra.
From HypVeri.lang Require Import lang_extra mem_extra mailbox_extra reg_extra current_extra.

Section msg_send.
  Context `{hypparams: HypervisorParameters}.
  Context `{vmG: !gen_VMG Σ}.

Lemma msg_send_primary {E wi r0 w sacc p_tx mem_tx q p_rx mem_rx l} ai j :
  tpa ai ≠ p_tx ->
  tpa ai ∈ sacc ->
  decode_instruction wi = Some(Hvc) ->
  decode_hvc_func r0 = Some(Send) ->
  ((finz.to_z l) <= page_size)%Z ->
  decode_vmid w = Some j ->
  j ≠ V0 ->
  {SS{{ ▷(PC @@ V0 ->r ai) ∗
        ▷ ai ->a wi ∗
        ▷ V0 -@{q}A> sacc ∗
        ▷ (R0 @@ V0 ->r r0) ∗
        ▷ (R1 @@ V0 ->r w) ∗
        ▷ (R2 @@ V0 ->r l) ∗
        ▷ TX@ V0 := p_tx ∗
        ▷ memory_page p_tx mem_tx ∗
        ▷ RX@ j := p_rx ∗ ▷ RX_state@ j := None∗
        ▷ memory_page p_rx mem_rx}}}
   ExecI @ V0 ; E {{{ RET (false, ExecI) ;
                  PC @@ V0 ->r (ai ^+ 1)%f ∗ ai ->a wi
                  ∗ V0 -@{q}A> sacc
                  ∗ R0 @@ V0 ->r r0
                  ∗ R1 @@ V0 ->r w
                  ∗ R2 @@ V0 ->r l
                  ∗ TX@ V0 := p_tx
                  ∗ RX@ j := p_rx ∗ RX_state@ j :=Some(l, V0)
                  ∗ memory_page p_tx mem_tx
                  ∗ (∃ des, ⌜(Z.to_nat l) = length des ⌝ ∗ ⌜(list_to_map (zip (finz.seq p_tx (length des)) des))⊆ mem_tx⌝
                                          ∗ memory_page p_rx ((list_to_map (zip (finz.seq p_rx (length des)) des))∪ mem_rx)) }}}.
  Proof.
  iIntros (Hneq_tx Hin_acc Hdecode_i Hdecode_f Hle Hdecode_v Hneq_v Φ)
          "(>PC & >mem_ins & >acc & >R0 & >R1 & >R2 & >tx & >mem_tx & >rx & >rx_s & >mem_rx) HΦ".
  iApply (sswp_lift_atomic_step ExecI);[done|].
  iIntros (n σ1) "%Hsche state".
  rewrite /scheduled /= /scheduler in Hsche.
  assert (σ1.1.1.2 = V0) as Heq_cur. { case_bool_decide;last done. by apply fin_to_nat_inj. }
  clear Hsche.
  iModIntro.
  iDestruct "state" as "(Hnum & mem & regs & mb & rx_state & pgt_owned & pgt_acc & pgt_excl &
                            trans & hpool & retri & %Hwf & %Hconsis & %Hdisj)".
  (* valid regs *)
  iDestruct ((gen_reg_valid4 V0 PC ai R0 r0 R1 w R2 l Heq_cur) with "regs PC R0 R1 R2")
    as "(%Hlookup_PC & %Hlookup_R0 & %Hlookup_R1 & %Hlookup_R2)";eauto.
  (* valid pt *)
  iDestruct (access_agree_check_true (tpa ai) V0 with "pgt_acc acc") as %Hcheckpg_ai;eauto.
  (* valid mem *)
  iDestruct (gen_mem_valid ai wi with "mem mem_ins") as %Hlookup_ai.
  iDestruct (gen_mem_valid_SepM with "mem [mem_tx]") as %Hlookup_mem_tx.
  { iDestruct "mem_tx" as "[% mem_tx]". iExact "mem_tx". }
  iDestruct (gen_mem_valid_SepM with "mem [mem_rx]") as %Hlookup_mem_rx.
  { iDestruct "mem_rx" as "[% mem_rx]". iExact "mem_rx". }
  (* valid tx *)
  iDestruct (mb_valid_tx V0 p_tx with "mb tx") as %Heq_tx.
  iDestruct (mb_valid_rx j p_rx with "mb rx") as %Heq_rx.
  iDestruct (rx_state_valid_None with "rx_state rx_s") as %Heq_rx_state.
  iSplit.
  - (* reducible *)
    iPureIntro.
    apply (reducible_normal V0 Hvc ai wi);eauto.
    rewrite Heq_tx //.
  - iModIntro.
    iIntros (m2 σ2) "vmprop_auth %HstepP".
    iFrame "vmprop_auth".
    apply (step_ExecI_normal V0 Hvc ai wi) in HstepP;eauto.
    2: rewrite Heq_tx //.
    remember (exec Hvc σ1) as c2 eqn:Heqc2.
    rewrite /exec /hvc Hlookup_R0 /= Hdecode_f /send /= Hlookup_R1 /= Hdecode_v /= in Heqc2.
    case_bool_decide;first rewrite Heq_cur // in H0. clear H0.
    rewrite Hlookup_R2 /transfer_msg /= in Heqc2.
    case_bool_decide;first lia. clear H0.
    rewrite /fill_rx p_cp_mem_mb in Heqc2.
    destruct (σ1.1.1.1.1.2 !!! j) as [? [? ?]] eqn:Heq_mb_j.
    simpl in Heq_rx_state.
    rewrite Heq_rx_state /= /is_primary p_fill_rx_current_vm p_cp_mem_current_vm in Heqc2.
    case_bool_decide;last contradiction. clear H0.
    rewrite Heq_cur Heq_tx /= in Heqc2. subst c2.
    destruct HstepP; subst m2 σ2;simpl.
    rewrite /gen_vm_interp.
    (* preserved parts *)
    rewrite (preserve_get_own_gmap σ1).
    rewrite (preserve_get_access_gmap σ1).
    rewrite (preserve_get_excl_gmap σ1).
    2-4: rewrite p_upd_id_pgt p_upd_pc_pgt p_fill_rx_pgt p_cp_mem_pgt //.
    rewrite (preserve_get_trans_gmap σ1).
    rewrite (preserve_get_hpool_gset σ1).
    rewrite (preserve_get_retri_gmap σ1).
    2-4: rewrite p_upd_id_trans p_upd_pc_trans p_fill_rx_trans p_cp_mem_trans //.
    rewrite (preserve_inv_trans_pgt_consistent σ1).
    rewrite (preserve_inv_trans_wellformed σ1).
    rewrite (preserve_inv_trans_ps_disj σ1).
    2-4: rewrite p_upd_id_trans p_upd_pc_trans p_fill_rx_trans p_cp_mem_trans //.
    2: rewrite p_upd_id_pgt p_upd_pc_pgt p_fill_rx_pgt p_cp_mem_pgt //.
    rewrite (preserve_get_mb_gmap (fill_rx_unsafe (copy_page_segment σ1 p_tx p (Z.to_nat l)) l V0 j t p) (update_current_vmid _ _)).
    2: rewrite p_upd_id_mb p_upd_pc_mb //.
    rewrite p_fill_rx_mb.
    2-3: rewrite p_cp_mem_mb Heq_mb_j //.
    rewrite (preserve_get_mb_gmap σ1). 2: rewrite p_cp_mem_mb //.
    iFrame "Hnum mb pgt_owned pgt_acc pgt_excl trans hpool retri".
    (* mem *)
    rewrite p_upd_id_mem p_upd_pc_mem p_fill_rx_mem.
    iAssert(⌜dom (gset _) mem_tx = list_to_set (addr_of_page p_tx)⌝%I) as %Hdom_mem_tx.
    { iDestruct ("mem_tx") as "[H _]". done. }
    iDestruct ("mem_rx") as "[%Hdom_mem_rx mem_rx]". 
    feed pose proof (rd_mem_mem_Some mem_tx σ1.1.2 p_tx l);auto.
    rewrite map_subseteq_spec.
    intros. apply Hlookup_mem_tx;auto.
    destruct H0 as [des [Hsome Hlen]].
    erewrite u_cp_mem_mem.
    2: exact Hsome.
    simpl in Heq_rx. subst p.
    set des' := (list_to_map _).
    assert (Heq_dom : dom (gset Addr) mem_rx = dom (gset Addr) (des' ∪ mem_rx)).
    { symmetry. apply dom_wr_mem_subseteq.
      rewrite Hlen.
      lia. done.
    }
    iDestruct (gen_mem_update_SepM _ (des' ∪ mem_rx) with "mem mem_rx") as ">[mem mem_rx]";auto.
    rewrite -map_union_assoc.
    assert (mem_rx ∪ σ1.1.2 = σ1.1.2). apply map_subseteq_union.
    { apply map_subseteq_spec. intros. apply Hlookup_mem_rx;auto. }
    iEval (rewrite H0) in "mem". clear H0. iFrame "mem".
    (* reg *)
    rewrite (preserve_get_reg_gmap (update_incr_PC (fill_rx_unsafe (copy_page_segment σ1 p_tx p_rx (Z.to_nat l)) l V0 j t p_rx)) (update_current_vmid _ _)).
    2: rewrite p_upd_id_reg //.
    rewrite (u_upd_pc_regs _ V0 ai).
    2: { rewrite p_fill_rx_current_vm p_cp_mem_current_vm //. }
    2: {rewrite (preserve_get_reg_gmap σ1). solve_reg_lookup.
        rewrite p_fill_rx_regs p_cp_mem_regs //.
    }
    rewrite (preserve_get_reg_gmap σ1).
    2: rewrite p_fill_rx_regs p_cp_mem_regs //.
    iDestruct ((gen_reg_update1_global PC V0 _ (ai ^+ 1)%f) with "regs PC")
      as ">[$ PC]";eauto.
    (* rx_state *)
    rewrite (preserve_get_rx_gmap (fill_rx_unsafe (copy_page_segment σ1 p_tx p_rx (Z.to_nat l)) l V0 j t p_rx) (update_current_vmid _ _)).
    2: rewrite p_upd_id_mb p_upd_pc_mb //.
    rewrite (u_fill_rx_rx_state).
    rewrite (preserve_get_rx_gmap σ1).
    2: rewrite p_cp_mem_mb //.
    iDestruct (rx_state_update with "rx_state rx_s") as ">[$ rx_s]".
    iModIntro.
    iSplit. iPureIntro. auto.
    (* just_schedule *)
    rewrite /just_scheduled_vms /just_scheduled.
    rewrite /scheduled /machine.scheduler /= /scheduler.
    rewrite /update_current_vmid /= Heq_cur.
      set fl := (filter _ _).
    assert (fl = []) as ->.
    {
      rewrite /fl.
      induction n.
      - simpl.
        rewrite filter_nil //=.
      - rewrite seq_S.
        rewrite list.filter_app.
        rewrite IHn.
        simpl.
        rewrite filter_cons_False /=.
        rewrite filter_nil. auto.
        rewrite andb_negb_l.
        done.
    }
    iSplitR;first done.
    case_bool_decide; last contradiction.
    simpl.
    iApply "HΦ".
    iFrame.
    iExists des. iFrame.
    iPureIntro.
    split;first done.
    split. eapply rd_mem_mem_subseteq. symmetry. exact Hlen.
    eapply rd_mem_mem_Some'. lia. done. exact Hsome.
    rewrite map_subseteq_spec.
    intros. apply Hlookup_mem_tx. done.
    rewrite -Heq_dom //.
  Qed.

  Lemma msg_send_secondary {E i wi r0 w sacc p_tx mem_tx q p_rx mem_rx l r0_ r1_ r2_ P Q R'} ai j R P':
    tpa ai ≠ p_tx ->
    tpa ai ∈ sacc ->
    decode_instruction wi = Some(Hvc) ->
    decode_hvc_func r0 = Some(Send) ->
    decode_vmid w = Some j ->
    j ≠ i ->
    ((finz.to_z l) <= page_size)%Z ->
    i ≠ V0 ->
    let T' := (PC @@ i ->r (ai ^+ 1)%f ∗ ai ->a wi
                        ∗ i -@{q}A> sacc
                        ∗ R0 @@ i ->r r0 ∗ R1 @@ i ->r w ∗ R2 @@ i ->r l
                        ∗ R0 @@ V0 ->r (encode_hvc_func Send) ∗ R1 @@ V0 ->r w ∗ R2 @@ V0 ->r l
                        ∗ TX@ i := p_tx ∗ RX@ j := p_rx ∗ RX_state@j := Some(l, i)
                        ∗ memory_page p_tx mem_tx
                        ∗ (∃ des, ⌜(Z.to_nat l) = length des ⌝ ∗ ⌜(list_to_map (zip (finz.seq p_tx (length des)) des)) ⊆ mem_tx⌝
                                          ∗ memory_page p_rx ((list_to_map (zip (finz.seq p_rx (length des)) des))∪ mem_rx)))%I in
    {SS{{ ▷ (VMProp V0 Q (1/2)%Qp) ∗
          ▷ (VMProp i P 1%Qp) ∗
          ▷ (PC @@ i ->r ai) ∗ ▷ ai ->a wi ∗
          ▷ i -@{q}A> sacc ∗
          ▷ (R0 @@ i ->r r0) ∗ ▷ (R1 @@ i ->r w) ∗ ▷ (R2 @@ i ->r l) ∗
          ▷ (R0 @@ V0 ->r r0_) ∗ ▷ (R1 @@ V0 ->r r1_) ∗ ▷ (R2 @@ V0 ->r r2_) ∗
          ▷ TX@ i := p_tx ∗
          ▷ memory_page p_tx mem_tx ∗
          ▷ RX@ j := p_rx ∗ ▷ RX_state@ j := None ∗
          ▷ memory_page p_rx mem_rx ∗
          ▷ (T' ∗ R ∗ VMProp i P' (1/2)%Qp -∗ (Q ∗ R')) ∗
          ▷ R
    }}}
      ExecI @ i ; E {{{ RET (true, ExecI) ; R' ∗ VMProp i P' (1/2)%Qp}}}.
  Proof.
  iIntros (Hneq_tx Hin_acc Hdecode_i Hdecode_f Hdecode_v Hneq_v Hle Hneq_v0 T Φ)
          "(prop0 & propi & >PC & >mem_ins & >acc & >R0 & >R1 & >R2 &>R0_0 & >R1_0 & > R2_0 & >tx & >mem_tx & >rx & >rx_s & >mem_rx & Himp & R) HΦ".
  iApply (sswp_lift_atomic_step ExecI);[done|].
  iIntros (n σ1) "%Hsche state".
  rewrite /scheduled /= /scheduler in Hsche.
  assert (σ1.1.1.2 = i) as Heq_cur. { case_bool_decide;last done. by apply fin_to_nat_inj. }
  clear Hsche.
  iModIntro.
  iDestruct "state" as "(%Hnum & mem & regs & mb & rx_state & pgt_owned & pgt_acc & pgt_excl &
                            trans & hpool & retri & %Hwf & %Hconsis & %Hdisj)".
  (* valid regs *)
  iDestruct ((gen_reg_valid4 i PC ai R0 r0 R1 w R2 l Heq_cur) with "regs PC R0 R1 R2")
    as "(%Hlookup_PC & %Hlookup_R0 & %Hlookup_R1 & %Hlookup_R2)";eauto.
  (* valid pt *)
  iDestruct (access_agree_check_true (tpa ai) i with "pgt_acc acc") as %Hcheckpg_ai;eauto.
  (* valid mem *)
  iDestruct (gen_mem_valid ai wi with "mem mem_ins") as %Hlookup_ai.
  iDestruct (gen_mem_valid_SepM with "mem [mem_tx]") as %Hlookup_mem_tx.
  { iDestruct "mem_tx" as "[% mem_tx]". iExact "mem_tx". }
  iDestruct (gen_mem_valid_SepM with "mem [mem_rx]") as %Hlookup_mem_rx.
  { iDestruct "mem_rx" as "[% mem_rx]". iExact "mem_rx". }
  (* valid tx *)
  iDestruct (mb_valid_tx i p_tx with "mb tx") as %Heq_tx.
  iDestruct (mb_valid_rx j p_rx with "mb rx") as %Heq_rx.
  iDestruct (rx_state_valid_None with "rx_state rx_s") as %Heq_rx_state.
  iSplit.
  - (* reducible *)
    iPureIntro.
    apply (reducible_normal i Hvc ai wi);eauto.
    rewrite Heq_tx //.
  - iModIntro.
    iIntros (m2 σ2) "vmprop_auth %HstepP".
    iDestruct "vmprop_auth" as (P'') "vmprop_auth".
    iDestruct (VMProp_update i _ P P' with "vmprop_auth propi") as ">[vmprop_auth propi]".
    apply (step_ExecI_normal i Hvc ai wi) in HstepP;eauto.
    2: rewrite Heq_tx //.
    remember (exec Hvc σ1) as c2 eqn:Heqc2.
    rewrite /exec /hvc Hlookup_R0 /= Hdecode_f /send /= Hlookup_R1 /= Hdecode_v /= in Heqc2.
    case_bool_decide;first rewrite Heq_cur // in H0. clear H0.
    rewrite Hlookup_R2 /transfer_msg /= in Heqc2.
    case_bool_decide;first lia. clear H0.
    rewrite /fill_rx p_cp_mem_mb in Heqc2.
    destruct (σ1.1.1.1.1.2 !!! j) as [? [? ?]] eqn:Heq_mb_j.
    simpl in Heq_rx_state.
    rewrite Heq_rx_state /= /is_primary p_fill_rx_current_vm p_cp_mem_current_vm in Heqc2.
    case_bool_decide. rewrite H0 in Heq_cur. rewrite Heq_cur // in Hneq_v0. clear H0.
    rewrite Heq_cur Heq_tx /= in Heqc2. subst c2.
    destruct HstepP; subst m2 σ2;simpl.
    rewrite /gen_vm_interp.
    (* preserved parts *)
    rewrite (preserve_get_own_gmap σ1).
    rewrite (preserve_get_access_gmap σ1).
    rewrite (preserve_get_excl_gmap σ1).
    2-4: rewrite p_upd_id_pgt p_upd_pc_pgt 3!p_upd_reg_pgt p_fill_rx_pgt p_cp_mem_pgt //.
    rewrite (preserve_get_trans_gmap σ1).
    rewrite (preserve_get_hpool_gset σ1).
    rewrite (preserve_get_retri_gmap σ1).
    2-4: rewrite p_upd_id_trans p_upd_pc_trans 3!p_upd_reg_trans p_fill_rx_trans p_cp_mem_trans //.
    rewrite (preserve_inv_trans_pgt_consistent σ1).
    rewrite (preserve_inv_trans_wellformed σ1).
    rewrite (preserve_inv_trans_ps_disj σ1).
    2-4: rewrite p_upd_id_trans p_upd_pc_trans 3!p_upd_reg_trans p_fill_rx_trans p_cp_mem_trans //.
    2: rewrite p_upd_id_pgt p_upd_pc_pgt 3!p_upd_reg_pgt p_fill_rx_pgt p_cp_mem_pgt //.
    rewrite (preserve_get_mb_gmap (fill_rx_unsafe (copy_page_segment σ1 p_tx p (Z.to_nat l)) l i j t p) (update_current_vmid _ _)).
    2: rewrite p_upd_id_mb p_upd_pc_mb 3!p_upd_reg_mb //.
    rewrite p_fill_rx_mb.
    2-3: rewrite p_cp_mem_mb Heq_mb_j //.
    rewrite (preserve_get_mb_gmap σ1). 2: rewrite p_cp_mem_mb //.
    iFrame "mb pgt_owned pgt_acc pgt_excl trans hpool retri".
    (* mem *)
    rewrite p_upd_id_mem p_upd_pc_mem 3!p_upd_reg_mem p_fill_rx_mem.
    iAssert(⌜dom (gset _) mem_tx = list_to_set (addr_of_page p_tx)⌝%I) as %Hdom_mem_tx.
    { iDestruct ("mem_tx") as "[H _]". done. }
    iDestruct ("mem_rx") as "[%Hdom_mem_rx mem_rx]".
    feed pose proof (rd_mem_mem_Some mem_tx σ1.1.2 p_tx l);auto.
    rewrite map_subseteq_spec.
    intros. apply Hlookup_mem_tx;auto.
    destruct H0 as [des [Hsome Hlen]].
    erewrite u_cp_mem_mem.
    2: exact Hsome.
    simpl in Heq_rx. subst p.
    set des' := (list_to_map _).
    assert (Heq_dom : dom (gset Addr) mem_rx = dom (gset Addr) (des' ∪ mem_rx)).
    { symmetry. apply dom_wr_mem_subseteq.
      rewrite Hlen.
      lia. done.
    }
    iDestruct (gen_mem_update_SepM _ (des' ∪ mem_rx) with "mem mem_rx") as ">[mem mem_rx]";auto.
    rewrite -map_union_assoc.
    assert (mem_rx ∪ σ1.1.2 = σ1.1.2). apply map_subseteq_union.
    { apply map_subseteq_spec. intros. apply Hlookup_mem_rx;auto. }
    iEval (rewrite H0) in "mem". clear H0. iFrame "mem".
    (* reg *)
    rewrite (preserve_get_reg_gmap (update_incr_PC
                                      (update_reg_global
                   (update_reg_global
                      (update_reg_global (fill_rx_unsafe (copy_page_segment σ1 p_tx p_rx (Z.to_nat l)) l i j t p_rx) V0 R0
                         (encode_hvc_func Send)) V0 R1 w) V0 R2 l)) (update_current_vmid _ _)).
    2: rewrite p_upd_id_reg //.
    rewrite (u_upd_pc_regs _ i ai).
    2: { rewrite 3!p_upd_reg_current_vm p_fill_rx_current_vm p_cp_mem_current_vm //. }
    2: { rewrite 3!u_upd_reg_regs.
         rewrite (preserve_get_reg_gmap σ1).
         2: rewrite p_fill_rx_regs p_cp_mem_regs //.
         rewrite lookup_insert_ne;last done.
         rewrite lookup_insert_ne;last done.
         rewrite lookup_insert_ne;last done.
         solve_reg_lookup.
    }
    rewrite 3!u_upd_reg_regs.
    rewrite (preserve_get_reg_gmap σ1).
    2: rewrite p_fill_rx_regs p_cp_mem_regs //.
    iDestruct ((gen_reg_update4_global PC i (ai ^+ 1)%f R2 V0 l R1 V0 w R0 V0 (encode_hvc_func Send)) with "regs PC R2_0 R1_0 R0_0")
      as ">($ & PC & R2_0 & R1_0 & R0_0)";eauto.
    (* rx_state *)
    rewrite (preserve_get_rx_gmap (fill_rx_unsafe (copy_page_segment σ1 p_tx p_rx (Z.to_nat l)) l i j t p_rx) (update_current_vmid _ _)).
    2: rewrite p_upd_id_mb p_upd_pc_mb 3!p_upd_reg_mb //.
    rewrite (u_fill_rx_rx_state).
    rewrite (preserve_get_rx_gmap σ1).
    2: rewrite p_cp_mem_mb //.
    iDestruct (rx_state_update with "rx_state rx_s") as ">[$ rx_s]".
    iModIntro.
    iSplitL "vmprop_auth".
    iExists P'. iFrame.
    iSplit. iPureIntro. auto.
    (* just_schedule *)
    rewrite /just_scheduled_vms /just_scheduled.
    rewrite /scheduled /machine.scheduler /= /scheduler.
    rewrite /update_current_vmid /= Heq_cur.
    set fl := (filter _ _).
    assert (fl = [0]) as ->.
    {
        pose proof (NoDup_seq 0 vm_count) as ND.
        pose proof (NoDup_singleton 0) as ND'.
        set f := (λ id : nat, base.negb (bool_decide ((@fin_to_nat (@vm_count H) i) = id)) && bool_decide (fin_to_nat V0 = id) = true).
        pose proof (NoDup_filter f _ ND) as ND''.
        assert (f 0) as Prf.
        {
          subst f.
          simpl.
          unfold base.negb.
          repeat case_bool_decide;auto.
          exfalso.
          apply Hneq_v0.
          apply fin_to_nat_inj.
          rewrite H0.
          symmetry.
          done.
          exfalso.
          apply H1.
          apply V0eq.
          exfalso.
          apply H1.
          apply V0eq.
        }
        assert (In 0 (seq 0 vm_count)) as Prf'.
        {
          rewrite <-elem_of_list_In.
          rewrite elem_of_seq.
          split.
          - solve_finz.
          - rewrite plus_O_n.
            apply vm_count_pos.
        }
        rewrite <-elem_of_list_In in Prf'.
        assert (In 0 (filter f (seq 0 vm_count))) as Prf''.
        {
          rewrite <-elem_of_list_In.
          apply (iffRL (elem_of_list_filter f (seq 0 vm_count) 0)).
          split;auto.
        }
        rewrite <-elem_of_list_In in Prf''.
        assert (forall x, x ≠ 0 -> not (In x (filter f (seq 0 vm_count)))) as excl.
        {
          intros x neq c.
          rewrite <-elem_of_list_In in c.
          rewrite ->elem_of_list_filter in c.
          destruct c as [c' _].
          subst f.
          simpl in c'.
          unfold base.negb in c'.
          case_match.
          - by rewrite andb_false_l in c'.
          - rewrite andb_true_l in c'.
            apply neq.
            rewrite ->bool_decide_eq_true in c'.
            rewrite <-c'.
            apply V0eq.
        }
        apply Permutation_length_1_inv.
        apply NoDup_Permutation; auto.
        apply NoDup_filter.
        rewrite Hnum //.
        intros x'.
        split.
        - intros T'.
          rewrite ->elem_of_list_singleton in T'.
          subst x'.
          rewrite /fl Hnum.
          rewrite /f in Prf''.
          done.
        - intros T'.
          rewrite ->elem_of_list_singleton.
          rewrite ->elem_of_list_In in T'.
          destruct (decide (x' = 0)) as [? | n'].
          done.
          exfalso.
          apply (excl x' n').
          rewrite /f.
          rewrite /fl Hnum // in T'.
    }
    iDestruct (VMProp_split with "propi") as "[propi propi']".
    iDestruct ("Himp" with "[- HΦ prop0 propi']") as "[Q R]".
    iFrame.
    iExists des. iFrame.
    iPureIntro.
    split;first done.
    split. eapply rd_mem_mem_subseteq. symmetry. exact Hlen.
    eapply rd_mem_mem_Some'. lia. done. exact Hsome.
    rewrite map_subseteq_spec.
    intros. apply Hlookup_mem_tx. done.
    rewrite -Heq_dom //.
    iSplitR "R propi' HΦ".
    simpl.
    iSplitL;last done.
    iExists Q.
    rewrite V0eq.
    iFrame.
    case_bool_decide.
    apply fin_to_nat_inj in H0.
    rewrite H0 in Hneq_v0.
    contradiction.
    simpl.
    iApply "HΦ".
    iFrame.
  Qed.

  Lemma msg_send_invalid_receiver {E i wi r0 w sacc p_tx q l} ai:
  tpa ai ≠ p_tx ->
  tpa ai ∈ sacc ->
  decode_instruction wi = Some(Hvc) ->
  decode_hvc_func r0 = Some(Send) ->
  decode_vmid w = None ->
  {SS{{ ▷ (PC @@ i ->r ai) ∗
        ▷ ai ->a wi ∗
        ▷ i -@{q}A> sacc ∗
        ▷ TX@ i := p_tx ∗
        ▷ (R0 @@ i ->r r0) ∗
        ▷ (R1 @@ i ->r w) ∗
        ▷ (R2 @@ i ->r l)}}}
   ExecI @ i ; E {{{ RET (false, ExecI) ;
                  PC @@ i ->r (ai ^+ 1)%f ∗ ai ->a wi
                  ∗ i -@{q}A> sacc
                  ∗ TX@ i := p_tx
                  ∗ R0 @@ i ->r encode_hvc_ret_code Error
                  ∗ R1 @@ i ->r w
                  ∗ R2 @@ i ->r encode_hvc_error InvParam}}}.
  Proof.
  Admitted.

  Lemma msg_send_to_self {E i wi r0 w sacc p_tx q l} ai j :
  tpa ai ≠ p_tx ->
  tpa ai ∈ sacc ->
  decode_instruction wi = Some(Hvc) ->
  decode_hvc_func r0 = Some(Send) ->
  decode_vmid w = Some j ->
  j = i ->
  {SS{{ ▷(PC @@ i ->r ai) ∗
        ▷ ai ->a wi ∗
        ▷ i -@{q}A> sacc ∗
        ▷ TX@ i := p_tx ∗
        ▷ (R0 @@ i ->r r0) ∗
        ▷ (R1 @@ i ->r w) ∗
        ▷ (R2 @@ i ->r l)}}}
   ExecI @ i ; E {{{ RET (false, ExecI) ;
                  PC @@ i ->r (ai ^+ 1)%f ∗ ai ->a wi
                  ∗ i -@{q}A> sacc
                  ∗ TX@ i := p_tx
                  ∗ R0 @@ i ->r encode_hvc_ret_code Error
                  ∗ R1 @@ i ->r w
                  ∗ R2 @@ i ->r encode_hvc_error InvParam}}}.
  Proof.
  Admitted.

  Lemma msg_send_invalid_length {E i wi r0 w sacc p_tx q l} ai j:
  tpa ai ≠ p_tx ->
  tpa ai ∈ sacc ->
  decode_instruction wi = Some(Hvc) ->
  decode_hvc_func r0 = Some(Send) ->
  decode_vmid w = Some j ->
  j ≠ i ->
  ((finz.to_z l) > page_size)%Z ->
  {SS{{ ▷ (PC @@ i ->r ai) ∗
        ▷ ai ->a wi ∗
        ▷ i -@{q}A> sacc ∗
        ▷ TX@ i := p_tx ∗
        ▷ (R0 @@ i ->r r0) ∗
        ▷ (R1 @@ i ->r w) ∗
        ▷ (R2 @@ i ->r l)}}}
   ExecI @ i ; E {{{ RET (false, ExecI) ;
                  PC @@ i ->r (ai ^+ 1)%f ∗ ai ->a wi
                  ∗ i -@{q}A> sacc
                  ∗ TX@ i := p_tx
                  ∗ R0 @@ i ->r encode_hvc_ret_code Error
                  ∗ R1 @@ i ->r w
                  ∗ R2 @@ i ->r encode_hvc_error InvParam}}}.
  Proof.
  Admitted.

  Lemma msg_send_full_rx{E i wi r0 w sacc p_tx q q' l} ai j o:
  tpa ai ≠ p_tx ->
  tpa ai ∈ sacc ->
  decode_instruction wi = Some(Hvc) ->
  decode_hvc_func r0 = Some(Send) ->
  decode_vmid w = Some j ->
  j ≠ i ->
  ((finz.to_z l) <= page_size)%Z ->
  is_Some o ->
  {SS{{ ▷ (PC @@ i ->r ai) ∗
        ▷ ai ->a wi ∗
        ▷ i -@{q}A> sacc ∗
        ▷ TX@ i := p_tx ∗
        ▷ (R0 @@ i ->r r0) ∗
        ▷ (R1 @@ i ->r w) ∗
        ▷ (R2 @@ i ->r l) ∗
        ▷ (RX_state{q'}@j := o)}}}
   ExecI @ i ; E {{{ RET (false, ExecI) ;
                  PC @@ i ->r (ai ^+ 1)%f ∗ ai ->a wi
                  ∗ i -@{q}A> sacc
                  ∗ TX@ i := p_tx
                  ∗ R0 @@ i ->r encode_hvc_ret_code Error
                  ∗ R1 @@ i ->r w
                  ∗ R2 @@ i ->r encode_hvc_error Busy
                  ∗ RX_state{q'}@j := o}}}.
  Proof.
  Admitted.

End msg_send.
