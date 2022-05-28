From machine_program_logic.program_logic Require Import weakestpre.
From HypVeri Require Import lifting rules.rules_base.
From HypVeri.algebra Require Import base reg mem pagetable mailbox base_extra.
From HypVeri.lang Require Import lang_extra reg_extra current_extra mailbox_extra.
Require Import stdpp.fin.

Section msg_wait.
Context `{hypparams: HypervisorParameters}.
Context `{vmG: !gen_VMG Σ}.

Lemma msg_wait_filled {E i wi r0 r1 r2 q s l j p_tx} ai:
  tpa ai ∈ s ->
  tpa ai ≠ p_tx ->
  decode_instruction wi = Some Hvc ->
  decode_hvc_func r0 = Some Wait ->
  {SS{{▷ (PC @@ i ->r ai)
          ∗ ▷ (ai ->a wi)
          ∗ ▷ (TX@i := p_tx)
          ∗ ▷ (i -@{q}A> s )
          ∗ ▷ (R0 @@ i ->r r0)
          ∗ ▷ (R1 @@ i ->r r1)
          ∗ ▷ (R2 @@ i ->r r2)
          ∗ ▷ (RX_state@ i := Some (l, j))}}}
    ExecI @ i ;E
    {{{ RET (false, ExecI); PC @@ i ->r (ai ^+ 1)%f
                     ∗ ai ->a wi
                     ∗ TX@i := p_tx
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
    rewrite /exec /hvc Hlookup_R0 /= Hdecode_f /= /wait /is_rx_ready /is_rx_ready_global Heq_cur in Heqc2.
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
    2-4: rewrite p_upd_id_pgt p_upd_pc_pgt 3!p_upd_reg_pgt p_empty_rx_pgt //.
    rewrite (preserve_get_trans_gmap σ1).
    rewrite (preserve_get_hpool_gset σ1).
    rewrite (preserve_get_retri_gmap σ1).
    2-4: rewrite p_upd_id_trans p_upd_pc_trans 3!p_upd_reg_trans p_empty_rx_trans //.
    rewrite (preserve_inv_trans_pgt_consistent σ1).
    rewrite (preserve_inv_trans_wellformed σ1).
    rewrite (preserve_inv_trans_ps_disj σ1).
    2-4: rewrite p_upd_id_trans p_upd_pc_trans 3!p_upd_reg_trans p_empty_rx_trans //.
    2: rewrite p_upd_id_pgt p_upd_pc_pgt 3!p_upd_reg_pgt p_empty_rx_pgt //.
    rewrite (preserve_get_mb_gmap (empty_rx σ1) (update_current_vmid _ _)).
    2: rewrite p_upd_id_mb p_upd_pc_mb 3!p_upd_reg_mb //.
    rewrite p_empty_rx_mb.
    rewrite p_upd_id_mem p_upd_pc_mem 3!p_upd_reg_mem p_empty_rx_mem.
    iFrame "Hnum mem mb pgt_owned pgt_acc pgt_excl trans hpool retri".
    rewrite (preserve_get_reg_gmap (update_incr_PC (update_reg (update_reg (update_reg (empty_rx σ1) R0 (encode_hvc_func Send)) R1 l) R2 (encode_vmid j))) (update_current_vmid _ _)).
    2: rewrite p_upd_id_reg //.
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
    rewrite (preserve_get_rx_gmap (empty_rx σ1) (update_current_vmid _ _)).
    2: rewrite p_upd_id_mb p_upd_pc_mb 3!p_upd_reg_mb //.
    rewrite (u_empty_rx_mb) Heq_cur.
    iDestruct (rx_state_update with "rx_state rx_s") as ">[$ rx_s]". done.
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
  Qed.

Lemma msg_wait_empty_secondary {E i wi r0 q q' s r0' r1' p_tx P Q R'} ai R P':
  tpa ai ∈ s ->
  tpa ai ≠ p_tx ->
  decode_instruction wi = Some Hvc ->
  decode_hvc_func r0 = Some Wait ->
  i ≠ V0 ->
  let T' := (PC @@ i ->r (ai ^+ 1)%f
                     ∗ R0 @@ i ->r r0
                     ∗ ai ->a wi
                     ∗ i -@{q}A> s
                     ∗ TX@i := p_tx
                     ∗ RX_state{q'}@ i := None
                     ∗ R0 @@ V0 ->r (encode_hvc_func Wait)
                     ∗ R1 @@ V0 ->r (encode_vmid i))%I in
  {SS{{▷ (VMProp V0 Q (1/2)%Qp) ∗
          ▷ (VMProp i P 1%Qp) ∗
          ▷ (PC @@ i ->r ai) ∗
          ▷ (R0 @@ i ->r r0) ∗
          ▷ (ai ->a wi) ∗
          ▷ (i -@{q}A> s) ∗
          ▷ (TX@i := p_tx) ∗
          ▷ (RX_state{q'}@ i := None) ∗
          ▷ (R0 @@ V0 ->r r0') ∗
          ▷ (R1 @@ V0 ->r r1') ∗
          ▷ (T' ∗ R ∗ VMProp i P' (1/2)%Qp -∗ (Q ∗ R')) ∗
          ▷ R}}}
    ExecI @ i ;E
    {{{ RET (true,ExecI); R' ∗ VMProp i P' (1/2)%Qp}}}.
Proof.
  iIntros (Hin_acc Hneq_tx Hdecode_i Hdecode_f Hneq_v0 T Φ)
          "(prop0 & propi & >PC & > R0 & >mem_ins & >acc & >tx & >rx_s & >R0_0 & >R1_0 & Himp & R) HΦ".
  iApply (sswp_lift_atomic_step ExecI);[done|].
  iIntros (n σ1) "%Hsche state".
  rewrite /scheduled /= /scheduler in Hsche.
  assert (σ1.1.1.2 = i) as Heq_cur. { case_bool_decide;last done. by apply fin_to_nat_inj. }
  clear Hsche.
  iModIntro.
  iDestruct "state" as "(%Hnum & mem & regs & mb & rx_state & pgt_owned & pgt_acc & pgt_excl &
                            trans & hpool & retri & %Hwf & %Hdisj & %Hconsis)".
  (* valid regs *)
  iDestruct ((gen_reg_valid2 i PC ai R0 r0 Heq_cur) with "regs PC R0")
    as "(%Hlookup_PC & %Hlookup_R0 )";eauto.
  (* valid pt *)
  iDestruct (access_agree_check_true (tpa ai) i with "pgt_acc acc") as %Hcheckpg_ai;eauto.
  (* valid mem *)
  iDestruct (gen_mem_valid ai wi with "mem mem_ins") as %Hlookup_ai.
  (* valid tx rx *)
  iDestruct (mb_valid_tx i p_tx with "mb tx") as %Heq_tx.
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
    rewrite /exec /hvc Hlookup_R0 /= Hdecode_f /= /wait /is_rx_ready /is_rx_ready_global Heq_cur in Heqc2.
    destruct (σ1.1.1.1.1.2 !!! i) as [? [? ?]] eqn:Heq_mb_i.
    simpl in Heq_rx_state.
    rewrite Heq_rx_state /= in Heqc2.
    destruct HstepP;subst m2 σ2; subst c2; simpl.
    rewrite /gen_vm_interp.
    rewrite (preserve_get_own_gmap σ1).
    rewrite (preserve_get_access_gmap σ1).
    rewrite (preserve_get_excl_gmap σ1).
    2-4: rewrite p_upd_id_pgt p_upd_pc_pgt 2!p_upd_reg_pgt //.
    rewrite (preserve_get_trans_gmap σ1).
    rewrite (preserve_get_hpool_gset σ1).
    rewrite (preserve_get_retri_gmap σ1).
    2-4: rewrite p_upd_id_trans p_upd_pc_trans 2!p_upd_reg_trans //.
    rewrite (preserve_inv_trans_pgt_consistent σ1).
    rewrite (preserve_inv_trans_wellformed σ1).
    rewrite (preserve_inv_trans_ps_disj σ1).
    2-4: rewrite p_upd_id_trans p_upd_pc_trans 2!p_upd_reg_trans //.
    2: rewrite p_upd_id_pgt p_upd_pc_pgt 2!p_upd_reg_pgt //.
    rewrite (preserve_get_mb_gmap σ1 (update_current_vmid _ _)).
    2: rewrite p_upd_id_mb p_upd_pc_mb 2!p_upd_reg_mb //.
    rewrite p_upd_id_mem p_upd_pc_mem 2!p_upd_reg_mem.
    rewrite (preserve_get_rx_gmap σ1).
    2: rewrite p_upd_id_mb p_upd_pc_mb 2!p_upd_reg_mb //.
    iFrame "mem mb rx_state pgt_owned pgt_acc pgt_excl trans hpool retri".
    rewrite (preserve_get_reg_gmap (update_incr_PC (update_reg_global (update_reg_global σ1 V0 R0 (encode_hvc_func Wait)) V0 R1 (encode_vmid i))) (update_current_vmid _ _)).
    2: rewrite p_upd_id_reg //.
    rewrite (u_upd_pc_regs _ i ai).
    2: rewrite 2!p_upd_reg_current_vm //.
    2: { rewrite 2!u_upd_reg_regs.
         rewrite lookup_insert_ne;last done.
         rewrite lookup_insert_ne;last done.
         solve_reg_lookup.
    }
    rewrite 2!u_upd_reg_regs.
    iDestruct ((gen_reg_update3_global PC i (ai ^+ 1)%f R1 V0 (encode_vmid i) R0 V0 (encode_hvc_func Wait)) with "regs PC R1_0 R0_0")
      as ">($ & PC & R1_0 & R0_0)";eauto.
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
        pose proof (list.NoDup_filter f _ ND) as ND''.
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
        apply list.NoDup_filter.
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

Lemma msg_wait_empty_primary {E wi r0 r1 q q' s p_tx} ai:
  tpa ai ∈ s ->
  tpa ai ≠ p_tx ->
  decode_instruction wi = Some Hvc ->
  decode_hvc_func r0 = Some Wait ->
  {SS{{▷ (PC @@ V0 ->r ai) ∗
          ▷ (R0 @@ V0 ->r r0) ∗
          ▷ (R1 @@ V0 ->r r1) ∗
          ▷ (ai ->a wi) ∗
          ▷ (V0 -@{q}A> s) ∗
          ▷ (TX@V0 := p_tx) ∗
          ▷ (RX_state{q'}@ V0 := None) }}}
    ExecI @ V0;E
    {{{ RET (false,ExecI); PC @@ V0 ->r (ai ^+ 1)%f
                    ∗ R0 @@ V0 ->r (encode_hvc_func Wait)
                    ∗ R1 @@ V0 ->r (encode_vmid V0)
                    ∗ ai ->a wi
                    ∗ V0 -@{q}A> s
                    ∗ TX@V0 := p_tx
                    ∗ RX_state{q'}@ V0 := None}}}.
Proof.
  iIntros (Hin_acc Hneq_tx Hdecode_i Hdecode_f Φ)
          "(>PC & > R0 & > R1 & >mem_ins & >acc & >tx & >rx_s) HΦ".
  iApply (sswp_lift_atomic_step ExecI);[done|].
  iIntros (n σ1) "%Hsche state".
  rewrite /scheduled /= /scheduler in Hsche.
  assert (σ1.1.1.2 = V0) as Heq_cur. { case_bool_decide;last done. by apply fin_to_nat_inj. }
  clear Hsche.
  iModIntro.
  iDestruct "state" as "(Hnum & mem & regs & mb & rx_state & pgt_owned & pgt_acc & pgt_excl &
                            trans & hpool & retri & %Hwf & %Hdisj & %Hconsis)".
  (* valid regs *)
  iDestruct ((gen_reg_valid2 V0 PC ai R0 r0 Heq_cur) with "regs PC R0")
    as "(%Hlookup_PC & %Hlookup_R0 )";eauto.
  (* valid pt *)
  iDestruct (access_agree_check_true (tpa ai) V0 with "pgt_acc acc") as %Hcheckpg_ai;eauto.
  (* valid mem *)
  iDestruct (gen_mem_valid ai wi with "mem mem_ins") as %Hlookup_ai.
  (* valid tx rx *)
  iDestruct (mb_valid_tx V0 p_tx with "mb tx") as %Heq_tx.
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
    rewrite /exec /hvc Hlookup_R0 /= Hdecode_f /= /wait /is_rx_ready /is_rx_ready_global Heq_cur in Heqc2.
    destruct (σ1.1.1.1.1.2 !!! V0) as [? [? ?]] eqn:Heq_mb_i.
    simpl in Heq_rx_state.
    rewrite Heq_rx_state /= in Heqc2.
    destruct HstepP;subst m2 σ2; subst c2; simpl.
    rewrite /gen_vm_interp.
    rewrite (preserve_get_own_gmap σ1).
    rewrite (preserve_get_access_gmap σ1).
    rewrite (preserve_get_excl_gmap σ1).
    2-4: rewrite p_upd_id_pgt p_upd_pc_pgt 2!p_upd_reg_pgt //.
    rewrite (preserve_get_trans_gmap σ1).
    rewrite (preserve_get_hpool_gset σ1).
    rewrite (preserve_get_retri_gmap σ1).
    2-4: rewrite p_upd_id_trans p_upd_pc_trans 2!p_upd_reg_trans //.
    rewrite (preserve_inv_trans_pgt_consistent σ1).
    rewrite (preserve_inv_trans_wellformed σ1).
    rewrite (preserve_inv_trans_ps_disj σ1).
    2-4: rewrite p_upd_id_trans p_upd_pc_trans 2!p_upd_reg_trans //.
    2: rewrite p_upd_id_pgt p_upd_pc_pgt 2!p_upd_reg_pgt //.
    rewrite (preserve_get_mb_gmap σ1 (update_current_vmid _ _)).
    2: rewrite p_upd_id_mb p_upd_pc_mb 2!p_upd_reg_mb //.
    rewrite p_upd_id_mem p_upd_pc_mem 2!p_upd_reg_mem.
    rewrite (preserve_get_rx_gmap σ1).
    2: rewrite p_upd_id_mb p_upd_pc_mb 2!p_upd_reg_mb //.
    iFrame "Hnum mem mb rx_state pgt_owned pgt_acc pgt_excl trans hpool retri".
    rewrite (preserve_get_reg_gmap (update_incr_PC (update_reg_global (update_reg_global σ1 V0 R0 (encode_hvc_func Wait)) V0 R1 (encode_vmid V0))) (update_current_vmid _ _)).
    2: rewrite p_upd_id_reg //.
    rewrite (u_upd_pc_regs _ V0 ai).
    2: rewrite 2!p_upd_reg_current_vm //.
    2: { rewrite 2!u_upd_reg_regs.
         rewrite lookup_insert_ne;last done.
         rewrite lookup_insert_ne;last done.
         solve_reg_lookup.
    }
    rewrite 2!u_upd_reg_regs.
    iDestruct ((gen_reg_update3_global PC V0 (ai ^+ 1)%f R1 V0 (encode_vmid V0) R0 V0 (encode_hvc_func Wait)) with "regs PC R1 R0")
      as ">($ & PC & R1 & R0)";eauto.
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
  Qed.

End msg_wait.
