From machine_program_logic.program_logic Require Import weakestpre.
From HypVeri Require Import lifting rules.rules_base machine_extra.
From HypVeri.algebra Require Import base mem reg pagetable mailbox base_extra.
From HypVeri.lang Require Import lang_extra reg_extra.

Section cmp.

Context `{hypparams: HypervisorParameters}.
Context `{vmG: !gen_VMG Σ}.
  
Lemma cmp_word {i w1 w2 w3 w4 q s p} ai ra :
  decode_instruction w1 = Some(Cmp ra (inl w2)) ->
  tpa ai ∈ s ->
  tpa ai ≠ p ->
  {SS{{ ▷ (PC @@ i ->r ai) ∗ ▷ (ai ->a w1) ∗
        ▷ (ra @@ i ->r w3) ∗ ▷ (i -@{q}A> s) ∗ ▷ (NZ @@ i ->r w4) ∗ ▷ (TX@ i := p)}}}
    ExecI @ i
    {{{ RET (false, ExecI); PC @@ i ->r (ai ^+ 1)%f ∗ ai ->a w1 ∗ ra @@ i ->r w3 ∗
        (i -@{q}A> s) ∗ NZ @@ i ->r (if (w3 <? (of_imm w2))%f then W2 else if ((of_imm w2) <? w3)%f then W0 else W1) ∗ (TX@ i := p)}}}.
Proof.
  iIntros (Hdecode Hin Hne ϕ) "(>Hpc & >Hapc & >Hra & >Hacc & >Hnz & >HTX) Hϕ".
  iApply (sswp_lift_atomic_step ExecI);[done|].
  set (instr:= Cmp ra (inl w2)).
  iIntros (n σ1) "%Hsche Hσ".
  rewrite /scheduled in Hsche.
  simpl in Hsche.
  rewrite /scheduler in Hsche.
  apply bool_decide_unpack in Hsche as Hcur.
  clear Hsche.
  apply fin_to_nat_inj in Hcur.
  iModIntro.
  iDestruct "Hσ" as "(#Hneq & Hmem & Hreg & Hmb & Hrx & Hown & Haccess & Hrest)".
  pose proof (decode_instruction_valid w1 instr Hdecode) as Hvalidinstr.
  inversion Hvalidinstr as [| | | | src dst Hvalidra | | | | | | |] .
  subst src dst.
  inversion Hvalidra as [ HneqPCa HneqNZa ].
  (* valid regs *)
  iDestruct ((gen_reg_valid3 i PC ai ra w3 NZ w4 Hcur) with "Hreg Hpc Hra Hnz") as "[%HPC [%Hra %HNZ]]";eauto.
  (* valid pt *)
  iDestruct (access_agree_check_true (tpa ai) i with "Haccess Hacc") as "%Hai"; first set_solver.
  (* valid mem *)
  iDestruct (gen_mem_valid ai w1 with "Hmem Hapc") as %Hmem.
  iDestruct (mb_valid_tx i p with "Hmb HTX") as %Htx.
  iSplit.
  - (* reducible *)
    iPureIntro.
    apply (reducible_normal i instr ai w1);eauto.
    by rewrite Htx.
  - (* step *)
    iModIntro.
    iIntros (m2 σ2) "[%P PAuth] %HstepP".
    apply (step_ExecI_normal i instr ai w1 ) in HstepP;eauto.
    remember (exec instr σ1) as c2 eqn:Heqc2.
    rewrite /exec /instr (cmp_word_ExecI σ1 ra w3 w2 HneqPCa HneqNZa Hra) /update_incr_PC /update_reg in Heqc2; auto.
    destruct HstepP;subst m2 σ2; subst c2; simpl.
    rewrite /gen_vm_interp.
    (* unchanged part *)
    rewrite (preserve_get_mb_gmap σ1).
    rewrite (preserve_get_rx_gmap σ1).
    rewrite (preserve_get_own_gmap σ1).
    rewrite (preserve_get_access_gmap σ1).
    rewrite (preserve_get_excl_gmap σ1).
    rewrite (preserve_get_trans_gmap σ1).
    rewrite (preserve_get_hpool_gset σ1).
    rewrite (preserve_get_retri_gmap σ1).
    rewrite (preserve_inv_trans_pgt_consistent σ1).
    rewrite (preserve_inv_trans_wellformed σ1).
    rewrite p_upd_pc_mem p_upd_reg_mem.
    all: try rewrite p_upd_pc_pgt p_upd_reg_pgt //.
    all: try rewrite p_upd_pc_trans p_upd_reg_trans //.
    all: try rewrite p_upd_pc_mb p_upd_reg_mb //.
    rewrite Hcur. iFrame.
    (* updated part *)
    rewrite -> (u_upd_pc_regs _ i ai 1);eauto.
    rewrite u_upd_reg_regs.
    + destruct (w3 <? (of_imm w2))%f,  ((of_imm w2) <? w3)%f.
      iDestruct ((gen_reg_update2_global PC i ai (ai ^+ 1)%f NZ i w4 W2 ) with "Hreg Hpc Hnz") as ">[Hreg [Hpc Hnz]]";eauto.
      iModIntro.
      rewrite /just_scheduled_vms.
      rewrite /just_scheduled.
      assert (filter
                (λ id : vmid,
                        base.negb (scheduled σ1 id) && scheduled (update_offset_PC (update_reg_global σ1 i NZ W2) 1) id = true)
                (seq 0 n) = []) as ->.
      {
        rewrite /scheduled /machine.scheduler //= /scheduler Hcur.        
        rewrite p_upd_pc_current_vm p_upd_reg_current_vm.
        rewrite Hcur.
        induction n.
        - simpl.
          rewrite filter_nil //=.
        - rewrite seq_S.
          rewrite filter_app.
          rewrite IHn.
          simpl.
          rewrite filter_cons_False //=.
          rewrite andb_negb_l.
          done.
      }
      iSimpl.
      iFrame.
      iSplitL "PAuth".
      by iExists P.
      iSplit; first done.
      assert ((scheduled (update_offset_PC (update_reg_global σ1 i NZ W2) 1) i) = true) as ->.
      rewrite /scheduled.
      simpl.
      rewrite /scheduler.
      rewrite p_upd_pc_current_vm p_upd_reg_current_vm.
      rewrite Hcur.
      rewrite bool_decide_eq_true.
      reflexivity.
      simpl.
      iSplit; first done.
      iApply ("Hϕ" with "[Hapc Hacc Hra Hpc Hnz HTX]").
      iFrame.
      iDestruct ((gen_reg_update2_global PC i ai (ai ^+ 1)%f NZ i w4 W2 ) with "Hreg Hpc Hnz") as ">[Hreg [Hpc Hnz]]";eauto.
      iModIntro.
      rewrite /just_scheduled_vms.
      rewrite /just_scheduled.
      assert (filter
                (λ id : vmid,
                        base.negb (scheduled σ1 id) && scheduled (update_offset_PC (update_reg_global σ1 i NZ W2) 1) id = true)
                (seq 0 n) = []) as ->.
      {
        rewrite /scheduled /machine.scheduler //= /scheduler Hcur.        
        rewrite p_upd_pc_current_vm p_upd_reg_current_vm.
        rewrite Hcur.
        induction n.
        - simpl.
          rewrite filter_nil //=.
        - rewrite seq_S.
          rewrite filter_app.
          rewrite IHn.
          simpl.
          rewrite filter_cons_False //=.
          rewrite andb_negb_l.
          done.
      }
      iSimpl.
      iFrame.
      iSplitL "PAuth".
      by iExists P.
      iSplit; first done.
      assert ((scheduled (update_offset_PC (update_reg_global σ1 i NZ W2) 1) i) = true) as ->.
      rewrite /scheduled.
      simpl.
      rewrite /scheduler.
      rewrite p_upd_pc_current_vm p_upd_reg_current_vm.
      rewrite Hcur.
      rewrite bool_decide_eq_true.
      reflexivity.
      simpl.
      iSplit; first done.
      iApply ("Hϕ" with "[Hapc Hacc Hra Hpc Hnz HTX]").
      iFrame.
      iDestruct ((gen_reg_update2_global PC i ai (ai ^+ 1)%f NZ i w4 W0 ) with "Hreg Hpc Hnz") as ">[Hreg [Hpc Hnz]]";eauto.
      iModIntro.
      rewrite /just_scheduled_vms.
      rewrite /just_scheduled.
      assert (filter
                (λ id : vmid,
                        base.negb (scheduled σ1 id) && scheduled (update_offset_PC (update_reg_global σ1 i NZ W0) 1) id = true)
                (seq 0 n) = []) as ->.
      {
        rewrite /scheduled /machine.scheduler //= /scheduler Hcur.        
        rewrite p_upd_pc_current_vm p_upd_reg_current_vm.
        rewrite Hcur.
        induction n.
        - simpl.
          rewrite filter_nil //=.
        - rewrite seq_S.
          rewrite filter_app.
          rewrite IHn.
          simpl.
          rewrite filter_cons_False //=.
          rewrite andb_negb_l.
          done.
      }
      iSimpl.
      iFrame.
      iSplitL "PAuth".
      by iExists P.
      iSplit; first done.
      assert ((scheduled (update_offset_PC (update_reg_global σ1 i NZ W0) 1) i) = true) as ->.
      rewrite /scheduled.
      simpl.
      rewrite /scheduler.
      rewrite p_upd_pc_current_vm p_upd_reg_current_vm.
      rewrite Hcur.
      rewrite bool_decide_eq_true.
      reflexivity.
      simpl.
      iSplit; first done.
      iApply ("Hϕ" with "[Hapc Hacc Hra Hpc Hnz HTX]").
      iFrame.
      iDestruct ((gen_reg_update2_global PC i ai (ai ^+ 1)%f NZ i w4 W1 ) with "Hreg Hpc Hnz") as ">[Hreg [Hpc Hnz]]";eauto.
      iModIntro.
      rewrite /just_scheduled_vms.
      rewrite /just_scheduled.
      assert (filter
                (λ id : vmid,
                        base.negb (scheduled σ1 id) && scheduled (update_offset_PC (update_reg_global σ1 i NZ W1) 1) id = true)
                (seq 0 n) = []) as ->.
      {
        rewrite /scheduled /machine.scheduler //= /scheduler Hcur.        
        rewrite p_upd_pc_current_vm p_upd_reg_current_vm.
        rewrite Hcur.
        induction n.
        - simpl.
          rewrite filter_nil //=.
        - rewrite seq_S.
          rewrite filter_app.
          rewrite IHn.
          simpl.
          rewrite filter_cons_False //=.
          rewrite andb_negb_l.
          done.
      }
      iSimpl.
      iFrame.
      iSplitL "PAuth".
      by iExists P.
      iSplit; first done.
      assert ((scheduled (update_offset_PC (update_reg_global σ1 i NZ W1) 1) i) = true) as ->.
      rewrite /scheduled.
      simpl.
      rewrite /scheduler.
      rewrite p_upd_pc_current_vm p_upd_reg_current_vm.
      rewrite Hcur.
      rewrite bool_decide_eq_true.
      reflexivity.
      simpl.
      iSplit; first done.
      iApply ("Hϕ" with "[Hapc Hacc Hra Hpc Hnz HTX]").
      iFrame.
    + rewrite u_upd_reg_regs.
      apply (get_reg_gmap_get_reg_Some _ _ _ i) in HPC;eauto.
      by simplify_map_eq /=.
    + by rewrite Htx.
Qed.

Lemma cmp_reg {i w1 w2 w3 w4 q s p} ai ra rb :
  decode_instruction w1 = Some(Cmp ra (inr rb)) ->
  tpa ai ∈ s ->
  tpa ai ≠ p ->
  {SS{{ ▷ (PC @@ i ->r ai) ∗ ▷ (ai ->a w1) ∗
        ▷ (ra @@ i ->r w2) ∗ ▷ (rb @@ i ->r w3) ∗ ▷ (i -@{q}A> s) ∗ ▷ (NZ @@ i ->r w4) ∗ ▷ (TX@ i := p)}}}
    ExecI @ i
    {{{ RET (false, ExecI); PC @@ i ->r (ai ^+ 1)%f ∗ ai ->a w1 ∗ ra @@ i ->r w2 ∗ (rb @@ i ->r w3) ∗
        (i -@{q}A> s) ∗ NZ @@ i ->r (if (w2 <? w3)%f then W2 else if (w3 <? w2)%f then W0 else W1) ∗ (TX@ i := p)}}}.
Proof.
  iIntros (Hdecode Hin Hne ϕ) "(>Hpc & >Hapc & >Hra & >Hrb & >Hacc & >Hnz & >HTX) Hϕ".
  iApply (sswp_lift_atomic_step ExecI);[done|].
  set (instr:= Cmp ra (inr rb)).
  iIntros (n σ1) "%Hsche Hσ".
  rewrite /scheduled in Hsche.
  simpl in Hsche.
  rewrite /scheduler in Hsche.
  apply bool_decide_unpack in Hsche as Hcur.
  clear Hsche.
  apply fin_to_nat_inj in Hcur.
  iModIntro.
  iDestruct "Hσ" as "(#Hneq & Hmem & Hreg & Hmb & Hrx & Hown & Haccess & Hrest)".
  pose proof (decode_instruction_valid w1 instr Hdecode) as Hvalidinstr.
  inversion Hvalidinstr as [ | | | | | src dst Hvalidra Hvalidrb Hneqrarb | | | | | |] .
  subst src dst.
  destruct  Hvalidra as [ HneqPCa HneqNZa ].
  destruct  Hvalidrb as [ HneqPCb HneqNZb ].
  (* valid regs *)
  iDestruct ((gen_reg_valid4 i PC ai ra w2 rb w3 NZ w4 Hcur) with "Hreg Hpc Hra Hrb Hnz") as "[%HPC [%Hra [%Hrb %HNZ]]]";auto.
  (* valid pt *)
  iDestruct (access_agree_check_true (tpa ai) i with "Haccess Hacc") as %Hacc;first set_solver + Hin.
  (* valid mem *)
  iDestruct (gen_mem_valid ai w1 with "Hmem Hapc") as %Hmem.
  iDestruct (mb_valid_tx i p with "Hmb HTX") as %Htx.
  iSplit.
  - (* reducible *)
    iPureIntro.
    apply (reducible_normal i instr ai w1);eauto.
    by rewrite Htx.
  - (* step *)
    iModIntro.
    iIntros (m2 σ2) "[%P PAuth] %HstepP".
    apply (step_ExecI_normal i instr ai w1 ) in HstepP;eauto.
    remember (exec instr σ1) as c2 eqn:Heqc2.
    rewrite /exec /instr (cmp_reg_ExecI σ1 ra w2 rb w3 HneqPCa HneqNZa HneqPCb HneqNZb) /update_incr_PC /update_reg in Heqc2; auto.
    destruct HstepP;subst m2 σ2; subst c2; simpl.
    rewrite /gen_vm_interp.
    (* unchanged part *)
    rewrite (preserve_get_mb_gmap σ1).
    rewrite (preserve_get_rx_gmap σ1).
    rewrite (preserve_get_own_gmap σ1).
    rewrite (preserve_get_access_gmap σ1).
    rewrite (preserve_get_excl_gmap σ1).
    rewrite (preserve_get_trans_gmap σ1).
    rewrite (preserve_get_hpool_gset σ1).
    rewrite (preserve_get_retri_gmap σ1).
    rewrite (preserve_inv_trans_pgt_consistent σ1).
    rewrite (preserve_inv_trans_wellformed σ1).
    rewrite p_upd_pc_mem p_upd_reg_mem.
    all: try rewrite p_upd_pc_pgt p_upd_reg_pgt //.
    all: try rewrite p_upd_pc_trans p_upd_reg_trans //.
    all: try rewrite p_upd_pc_mb p_upd_reg_mb //.
    rewrite Hcur. iFrame.
    (* updated part *)
    rewrite -> (u_upd_pc_regs _ i ai 1);eauto.
    rewrite u_upd_reg_regs.
    + destruct (w2 <? w3)%f,  (w3 <? w2)%f.
      iDestruct ((gen_reg_update2_global PC i ai (ai ^+ 1)%f NZ i w4 W2 ) with "Hreg Hpc Hnz") as ">[Hreg [Hpc Hnz]]";eauto.
      iModIntro.
      rewrite /just_scheduled_vms.
      rewrite /just_scheduled.
      assert (filter
                (λ id : vmid,
                        base.negb (scheduled σ1 id) && scheduled (update_offset_PC (update_reg_global σ1 i NZ W2) 1) id = true)
                (seq 0 n) = []) as ->.
      {
        rewrite /scheduled /machine.scheduler //= /scheduler Hcur.        
        rewrite p_upd_pc_current_vm p_upd_reg_current_vm.
        rewrite Hcur.
        induction n.
        - simpl.
          rewrite filter_nil //=.
        - rewrite seq_S.
          rewrite filter_app.
          rewrite IHn.
          simpl.
          rewrite filter_cons_False //=.
          rewrite andb_negb_l.
          done.
      }
      iSimpl.
      iFrame.
      iSplitL "PAuth".
      by iExists P.
      iSplit; first done.
      assert ((scheduled (update_offset_PC (update_reg_global σ1 i NZ W2) 1) i) = true) as ->.
      rewrite /scheduled.
      simpl.
      rewrite /scheduler.
      rewrite p_upd_pc_current_vm p_upd_reg_current_vm.
      rewrite Hcur.
      rewrite bool_decide_eq_true.
      reflexivity.
      simpl.
      iSplit; first done.
      iApply ("Hϕ" with "[Hapc Hacc Hra Hrb Hpc Hnz HTX]").
      iFrame.
      iDestruct ((gen_reg_update2_global PC i ai (ai ^+ 1)%f NZ i w4 W2 ) with "Hreg Hpc Hnz") as ">[Hreg [Hpc Hnz]]";eauto.
      iModIntro.
      rewrite /just_scheduled_vms.
      rewrite /just_scheduled.
      assert (filter
                (λ id : vmid,
                        base.negb (scheduled σ1 id) && scheduled (update_offset_PC (update_reg_global σ1 i NZ W2) 1) id = true)
                (seq 0 n) = []) as ->.
      {
        rewrite /scheduled /machine.scheduler //= /scheduler Hcur.        
        rewrite p_upd_pc_current_vm p_upd_reg_current_vm.
        rewrite Hcur.
        induction n.
        - simpl.
          rewrite filter_nil //=.
        - rewrite seq_S.
          rewrite filter_app.
          rewrite IHn.
          simpl.
          rewrite filter_cons_False //=.
          rewrite andb_negb_l.
          done.
      }
      iSimpl.
      iFrame.
      iSplitL "PAuth".
      by iExists P.
      iSplit; first done.
      iSplit; first done.
      assert ((scheduled (update_offset_PC (update_reg_global σ1 i NZ W2) 1) i) = true) as ->.
      rewrite /scheduled.
      simpl.
      rewrite /scheduler.
      rewrite p_upd_pc_current_vm p_upd_reg_current_vm.
      rewrite Hcur.
      rewrite bool_decide_eq_true.
      reflexivity.
      simpl.
      iApply ("Hϕ" with "[Hapc Hacc Hra Hrb Hpc Hnz HTX]").
      iFrame.
      iDestruct ((gen_reg_update2_global PC i ai (ai ^+ 1)%f NZ i w4 W0 ) with "Hreg Hpc Hnz") as ">[Hreg [Hpc Hnz]]";eauto.
      iModIntro.
      rewrite /just_scheduled_vms.
      rewrite /just_scheduled.
      assert (filter
                (λ id : vmid,
                        base.negb (scheduled σ1 id) && scheduled (update_offset_PC (update_reg_global σ1 i NZ W0) 1) id = true)
                (seq 0 n) = []) as ->.
      {
        rewrite /scheduled /machine.scheduler //= /scheduler Hcur.
        rewrite p_upd_pc_current_vm p_upd_reg_current_vm.
        rewrite Hcur.
        induction n.
        - simpl.
          rewrite filter_nil //=.
        - rewrite seq_S.
          rewrite filter_app.
          rewrite IHn.
          simpl.
          rewrite filter_cons_False //=.
          rewrite andb_negb_l.
          done.
      }
      iSimpl.
      iFrame.
      iSplitL "PAuth".
      by iExists P.
      iSplit; first done.
      iSplit; first done.
      assert ((scheduled (update_offset_PC (update_reg_global σ1 i NZ W0) 1) i) = true) as ->.
      rewrite /scheduled.
      simpl.
      rewrite /scheduler.
      rewrite p_upd_pc_current_vm p_upd_reg_current_vm.
      rewrite Hcur.
      rewrite bool_decide_eq_true.
      reflexivity.
      simpl.
      iApply ("Hϕ" with "[Hapc Hacc Hra Hrb Hpc Hnz HTX]").
      iFrame.
      iDestruct ((gen_reg_update2_global PC i ai (ai ^+ 1)%f NZ i w4 W1 ) with "Hreg Hpc Hnz") as ">[Hreg [Hpc Hnz]]";eauto.
      iModIntro.
      rewrite /just_scheduled_vms.
      rewrite /just_scheduled.
      assert (filter
                (λ id : vmid,
                        base.negb (scheduled σ1 id) && scheduled (update_offset_PC (update_reg_global σ1 i NZ W1) 1) id = true)
                (seq 0 n) = []) as ->.
      {
        rewrite /scheduled /machine.scheduler //= /scheduler Hcur.        
        rewrite p_upd_pc_current_vm p_upd_reg_current_vm.
        rewrite Hcur.
        induction n.
        - simpl.
          rewrite filter_nil //=.
        - rewrite seq_S.
          rewrite filter_app.
          rewrite IHn.
          simpl.
          rewrite filter_cons_False //=.
          rewrite andb_negb_l.
          done.
      }
      iSimpl.
      iFrame.
      iSplitL "PAuth".
      by iExists P.
      iSplit; first done.
      iSplit; first done.
      assert ((scheduled (update_offset_PC (update_reg_global σ1 i NZ W1) 1) i) = true) as ->.
      rewrite /scheduled.
      simpl.
      rewrite /scheduler.
      rewrite p_upd_pc_current_vm p_upd_reg_current_vm.
      rewrite Hcur.
      rewrite bool_decide_eq_true.
      reflexivity.
      simpl.
      iApply ("Hϕ" with "[Hapc Hacc Hra Hrb Hpc Hnz HTX]").
      iFrame.
    + rewrite u_upd_reg_regs.
      apply (get_reg_gmap_get_reg_Some _ _ _ i) in HPC;eauto.
      by simplify_map_eq /=.
    + by rewrite Htx.
Qed.
End cmp.
