From machine_program_logic.program_logic Require Import weakestpre.
From HypVeri Require Import lifting rules.rules_base.
From HypVeri.algebra Require Import base reg mem pagetable mailbox base_extra.
From HypVeri.lang Require Import lang_extra reg_extra current_extra mailbox_extra.
Require Import stdpp.fin.

Section msg_poll.

Context `{hypparams: HypervisorParameters}.
Context `{vmG: !gen_VMG Σ}.
  
Lemma msg_poll_full {E i wi r0 q s l j r1 r2 p_tx} ai:
  tpa ai ∈ s ->
  tpa ai ≠ p_tx ->
  decode_instruction wi = Some Hvc ->
  decode_hvc_func r0 = Some Poll ->
  {SS{{ ▷ (PC @@ i ->r ai)
          ∗ ▷ (ai ->a wi)
          ∗ ▷ (TX@ i := p_tx)
          ∗ ▷ (i -@{q}A> s)
          ∗ ▷ (R0 @@ i ->r r0)
          ∗ ▷ (R1 @@ i ->r r1)
          ∗ ▷ (R2 @@ i ->r r2)
          ∗ ▷ (RX_state@ i := Some (l, j))}}}
    ExecI @ i ;E
    {{{ RET (false,ExecI); PC @@ i ->r (ai ^+ 1)%f
                     ∗ ai ->a wi
                     ∗ TX@ i := p_tx
                     ∗ i -@{q}A> s
                     ∗ R0 @@ i ->r (encode_hvc_func Send)
                     ∗ R1 @@ i ->r l
                     ∗ R2 @@ i ->r (encode_vmid j)
                     ∗ RX_state@ i := None}}}.
Proof.
  iIntros (Hin_acc Hneq_tx Hdecode_i Hdecode_f Φ)
          "(>PC & >mem_ins & >tx & >acc & >R0 & >R1 & >R2 & >rx_s) HΦ".
  iApply (sswp_lift_atomic_step ExecI);[done|].
  iIntros (n σ1) "%Hsche state".
  rewrite /scheduled /= /scheduler in Hsche.
  assert (σ1.1.1.2 = i) as Heq_cur. { case_bool_decide;last done. by apply fin_to_nat_inj. }
  clear Hsche.
  iModIntro.
  iDestruct "state" as "(Hnum & mem & regs & mb & rx_state & pgt_owned & pgt_acc & pgt_excl &
                            trans & hpool & retri & %Hwf & %Hdisj & %Hconsis)".
  (* valid regs *)
  iDestruct ((gen_reg_valid4 i PC ai R0 r0 R1 r1 R2 r2 Heq_cur) with "regs PC R0 R1 R2")
    as "(%Hlookup_PC & %Hlookup_R0 & %Hlookup_R1 & %Hlookup_R2)";eauto.
  (* valid pt *)
  iDestruct (access_agree_check_true (tpa ai) i with "pgt_acc acc") as %Hcheckpg_ai;eauto.
  (* valid mem *)
  iDestruct (gen_mem_valid ai wi with "mem mem_ins") as %Hlookup_ai.
  (* valid tx rx *)
  iDestruct (mb_valid_tx i p_tx with "mb tx") as %Heq_tx.
  iDestruct (rx_state_valid_Some with "rx_state rx_s") as %Heq_rx_state.
  (* valid tran *)
  iSplit.
  - (* reducible *)
    iPureIntro.
    apply (reducible_normal i Hvc ai wi);auto.
    rewrite Heq_tx //.
  - iModIntro.
    iIntros (m2 σ2) "vmprop_auth %HstepP".
    iFrame "vmprop_auth".
    apply (step_ExecI_normal i Hvc ai wi) in HstepP;eauto.
    2: rewrite Heq_tx //.
    remember (exec Hvc σ1) as c2 eqn:Heqc2.
    rewrite /exec /hvc Hlookup_R0 /= Hdecode_f /= /poll /is_rx_ready /is_rx_ready_global Heq_cur in Heqc2.
    destruct (σ1.1.1.1.1.2 !!! i) as [? [? ?]] eqn:Heq_mb_i.
    simpl in Heq_rx_state.
    rewrite Heq_rx_state /= /get_rx_length /get_rx_length_global Heq_cur Heq_mb_i Heq_rx_state /= in Heqc2.
    rewrite /get_rx_sender /get_rx_sender_global Heq_cur Heq_mb_i Heq_rx_state /= in Heqc2.
    destruct HstepP;subst m2 σ2; subst c2; simpl.
    rewrite /gen_vm_interp.
    (* preserved parts *)
    rewrite (preserve_get_own_gmap σ1).
    rewrite (preserve_get_access_gmap σ1).
    rewrite (preserve_get_excl_gmap σ1).
    2-4: rewrite p_upd_pc_pgt 3!p_upd_reg_pgt p_empty_rx_pgt //.
    rewrite (preserve_get_trans_gmap σ1).
    rewrite (preserve_get_hpool_gset σ1).
    rewrite (preserve_get_retri_gmap σ1).
    2-4: rewrite p_upd_pc_trans 3!p_upd_reg_trans p_empty_rx_trans //.
    rewrite (preserve_inv_trans_pgt_consistent σ1).
    rewrite (preserve_inv_trans_wellformed σ1).
    rewrite (preserve_inv_trans_ps_disj σ1).
    2-4: rewrite p_upd_pc_trans 3!p_upd_reg_trans p_empty_rx_trans //.
    2: rewrite p_upd_pc_pgt 3!p_upd_reg_pgt p_empty_rx_pgt //.
    rewrite (preserve_get_mb_gmap (empty_rx σ1) (update_incr_PC _)).
    2: rewrite p_upd_pc_mb 3!p_upd_reg_mb //.
    rewrite p_empty_rx_mb.
    rewrite p_upd_pc_mem 3!p_upd_reg_mem p_empty_rx_mem.
    iFrame "Hnum mem mb pgt_owned pgt_acc pgt_excl trans hpool retri".
    rewrite (u_upd_pc_regs _ i ai).
    2: rewrite 3!p_upd_reg_current_vm p_empty_rx_current_vm //.
    2: { rewrite 3!u_upd_reg_regs.
         rewrite (preserve_get_reg_gmap σ1).
         2: rewrite p_empty_rx_regs//.
         rewrite lookup_insert_ne;last done.
         rewrite lookup_insert_ne;last done.
         rewrite lookup_insert_ne;last done.
         solve_reg_lookup.
    }
    rewrite 3!u_upd_reg_regs.
    rewrite (preserve_get_reg_gmap σ1).
    2: rewrite p_empty_rx_regs //.
    rewrite !p_upd_reg_current_vm !p_empty_rx_current_vm Heq_cur.
    iDestruct ((gen_reg_update4_global PC i (ai ^+ 1)%f R2 i (encode_vmid j) R1 i l R0 i (encode_hvc_func Send)) with "regs PC R2 R1 R0")
      as ">($ & PC & R2 & R1 & R0)";eauto.
    (* rx_state *)
    rewrite (preserve_get_rx_gmap (empty_rx σ1) (update_incr_PC _)).
    2: rewrite p_upd_pc_mb 3!p_upd_reg_mb //.
    rewrite (u_empty_rx_mb) Heq_cur.
    iDestruct (rx_state_update with "rx_state rx_s") as ">[$ rx_s]". done.
    iModIntro.
    iSplit. iPureIntro. auto.
    (* just_schedule *)
    rewrite /just_scheduled_vms /just_scheduled.
    rewrite /scheduled /machine.scheduler /= /scheduler.
    rewrite p_upd_pc_current_vm 3!p_upd_reg_current_vm p_empty_rx_current_vm /= Heq_cur.
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
  Qed.

Lemma msg_poll_empty {E i wi r0 q s r2 p_tx} ai:
  tpa ai ∈ s ->
  tpa ai ≠ p_tx ->
  decode_instruction wi = Some Hvc ->
  decode_hvc_func r0 = Some Poll ->
  {SS{{ ▷ (PC @@ i ->r ai)
          ∗ ▷ (ai ->a wi)
          ∗ ▷ (TX@ i := p_tx)
          ∗ ▷ (i -@{q}A> s)
          ∗ ▷ (R0 @@ i ->r r0)
          ∗ ▷ (R2 @@ i ->r r2)
          ∗ ▷ (RX_state@ i := None)}}}
    ExecI @ i ;E
    {{{ RET (false,ExecI); PC @@ i ->r (ai ^+ 1)%f
                     ∗ ai ->a wi
                     ∗ TX@ i := p_tx
                     ∗ i -@{q}A> s
                     ∗ R0 @@ i ->r (encode_hvc_ret_code Error)
                     ∗ R2 @@ i ->r (encode_hvc_error Denied)
                     ∗ RX_state@ i := None}}}.
Proof.
  iIntros (Hin_acc Hneq_tx Hdecode_i Hdecode_f Φ)
          "(>PC & >mem_ins & >tx & >acc & >R0 & >R2 & >rx_s) HΦ".
  iApply (sswp_lift_atomic_step ExecI);[done|].
  iIntros (n σ1) "%Hsche state".
  rewrite /scheduled /= /scheduler in Hsche.
  assert (σ1.1.1.2 = i) as Heq_cur. { case_bool_decide;last done. by apply fin_to_nat_inj. }
  clear Hsche.
  iModIntro.
  iDestruct "state" as "(Hnum & mem & regs & mb & rx_state & pgt_owned & pgt_acc & pgt_excl &
                            trans & hpool & retri & %Hwf & %Hdisj & %Hconsis)".
  (* valid regs *)
  iDestruct ((gen_reg_valid3 i PC ai R0 r0 R2 r2 Heq_cur) with "regs PC R0 R2")
    as "(%Hlookup_PC & %Hlookup_R0 & %Hlookup_R2)";eauto.
  (* valid pt *)
  iDestruct (access_agree_check_true (tpa ai) i with "pgt_acc acc") as %Hcheckpg_ai;eauto.
  (* valid mem *)
  iDestruct (gen_mem_valid ai wi with "mem mem_ins") as %Hlookup_ai.
  (* valid tx rx *)
  iDestruct (mb_valid_tx i p_tx with "mb tx") as %Heq_tx.
  iDestruct (rx_state_valid_None with "rx_state rx_s") as %Heq_rx_state.
  (* valid tran *)
  iSplit.
  - (* reducible *)
    iPureIntro.
    apply (reducible_normal i Hvc ai wi);auto.
    rewrite Heq_tx //.
  - iModIntro.
    iIntros (m2 σ2) "vmprop_auth %HstepP".
    iFrame "vmprop_auth".
    apply (step_ExecI_normal i Hvc ai wi) in HstepP;eauto.
    2: rewrite Heq_tx //.
    remember (exec Hvc σ1) as c2 eqn:Heqc2.
    rewrite /exec /hvc Hlookup_R0 /= Hdecode_f /= /poll /is_rx_ready /is_rx_ready_global Heq_cur in Heqc2.
    destruct (σ1.1.1.1.1.2 !!! i) as [? [? ?]] eqn:Heq_mb_i.
    simpl in Heq_rx_state.
    rewrite Heq_rx_state /= in Heqc2.
    destruct HstepP;subst m2 σ2; subst c2; simpl.
    iDestruct (hvc_error_update (E:= E) Denied with "PC R0 R2 [$Hnum $mem $regs $mb $rx_state $pgt_owned $pgt_acc $pgt_excl $ trans $hpool $retri]")
    as ">[[$ $] ?]";auto.
    rewrite /scheduled /machine.scheduler /= /scheduler.
    rewrite p_upd_pc_current_vm 2!p_upd_reg_current_vm Heq_cur.
    case_bool_decide;last contradiction.
    simpl. iApply "HΦ".
    iFrame.
    by iFrame.
Qed.

End msg_poll.
