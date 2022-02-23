From machine_program_logic.program_logic Require Import weakestpre.
From HypVeri Require Import lifting rules.rules_base machine_extra.
From HypVeri.algebra Require Import base reg mem pagetable mailbox base_extra.
From HypVeri.lang Require Import lang_extra reg_extra.

Section br.

Context `{hypparams: HypervisorParameters}.
Context `{vmG: !gen_VMG Σ}.
  
Lemma br {E i w1 w2 q s p} ai  ra :
  decode_instruction w1 = Some(Br ra) ->
  tpa ai ∈ s ->
  tpa ai ≠ p ->
    {SS{{  ▷ (PC @@ i ->r ai)
           ∗ ▷ (ai ->a w1)
           ∗ ▷ (ra @@ i ->r w2)
           ∗ ▷ (i -@{q}A> s)
           ∗ ▷ (TX@ i := p) }}} ExecI @ i; E
    {{{ RET (false, ExecI);  (PC @@ i ->r  w2)
                    ∗ (ai ->a w1 ∗ ra @@ i ->r w2)
                    ∗ (i -@{q}A> s)
                    ∗ (TX@ i := p)}}}.
Proof.
  iIntros (Hdecode Hin Hne ϕ) "( >Hpc & >Hapc & >Hra & >Hacc & >HTX) Hϕ".
  iApply (sswp_lift_atomic_step ExecI);[done|].
  iIntros (n σ1) "%Hsche Hσ".
  rewrite /scheduled in Hsche.
  simpl in Hsche.
  rewrite /scheduler in Hsche.
  apply bool_decide_unpack in Hsche as Hcur.
  clear Hsche.
  apply fin_to_nat_inj in Hcur.
  iModIntro.
  iDestruct "Hσ" as "(#Hneq & Hmem & Hreg & Hmb & Hrx & Hown & Haccess & Hrest)".
  pose proof (decode_instruction_valid w1 (Br ra) Hdecode) as Hvalidinstr.
  inversion Hvalidinstr as [ | | | | | | | | | |src Hvalidra |] .
  subst src .
  inversion Hvalidra as [ HneqPCa HneqNZa ].
  (* valid regs *)
  iDestruct ((gen_reg_valid2 i PC ai ra w2 Hcur) with "Hreg Hpc Hra") as "[%HPC %Hra]";eauto.
  (* valid pt *)
  iDestruct (access_agree_check_true (tpa ai) i with "Haccess Hacc") as %Hacc;first set_solver + Hin.
  (* valid mem *)
  iDestruct (gen_mem_valid ai w1  with "Hmem Hapc") as %Hmem.
  iDestruct (mb_valid_tx i p with "Hmb HTX") as %Htx.
  iSplit.
  - (* reducible *)
    iPureIntro.
    apply (reducible_normal i (Br ra) ai w1);eauto.
    by rewrite Htx.
  - (* step *)
    iModIntro.
    iIntros (m2 σ2) "[%P PAuth] %HstepP".
    apply (step_ExecI_normal i (Br ra) ai w1 ) in HstepP;eauto.
    remember (exec (Br ra) σ1) as c2 eqn:Heqc2.
    rewrite /exec /br /update_incr_PC in Heqc2;eauto.
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
    2-12: destruct ra; try rewrite Hra //; done.
    iFrame.
    (* updated part *)
    iDestruct ((gen_reg_update1_global PC i ai w2) with "Hreg Hpc") as ">[Hreg Hpc]";eauto.
    iModIntro.
    rewrite /update_reg Hra //.
    destruct ra; try done.
    simpl.
    rewrite ->u_upd_reg_regs.
    rewrite Hcur.
    iFrame "Hreg".
    iSplitL "PAuth".
    by iExists P.
    rewrite /just_scheduled_vms.
    rewrite /just_scheduled.
    assert (filter
              (λ id : vmid,
                      base.negb (scheduled σ1 id) && scheduled (update_reg_global σ1 i PC w2) id = true)
              (seq 0 n) = []) as ->.
    {
      rewrite /scheduled /machine.scheduler //= /scheduler Hcur.
      rewrite p_upd_reg_current_vm.
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
    iSplitL "Hmem".
    iFrame.
    iFrame "Hneq".
    iSplit; first done.
    assert ((scheduled (update_reg_global σ1 i PC w2) i) = true) as ->.
    rewrite /scheduled.
    simpl.
    rewrite /scheduler.
    rewrite p_upd_reg_current_vm.
    rewrite Hcur.
    rewrite bool_decide_eq_true.
    reflexivity.
    simpl.
    iApply ("Hϕ" with "[Hpc Hapc Hacc Hra HTX]").
    iFrame.
    by rewrite Htx.
Qed.
End br.
