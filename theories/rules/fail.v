From machine_program_logic.program_logic Require Import weakestpre.
From HypVeri Require Import lifting rules.rules_base.
From HypVeri.algebra Require Import base reg mem pagetable.
From HypVeri.lang Require Import lang_extra.

Section fail.

Context `{hypparams:HypervisorParameters}.
Context `{vmG: !gen_VMG Σ}.
  
Lemma fail {i w1 q E s} ai :
  decode_instruction w1 = Some(Fail) ->
  i ∈ s ->
  {SS{{ ▷ (PC @@ i ->r ai)
        ∗ ▷ (ai ->a w1)
        ∗ ▷ ((tpa ai) -@{q}A> [s])}}} ExecI @ i; E
                                             {{{ RET (false, FailI); PC @@ i ->r ai  ∗ ai ->a w1
                       ∗ ((tpa ai) -@{q}A> [s]) }}}.
Proof.
  iIntros (Hdecode Hin ϕ) "(>Hpc & >Hapc & >Hacc) Hϕ".
  iApply (sswp_lift_atomic_step ExecI);[done|].
  iIntros (n σ1) "%Hsche Hσ".  
  rewrite /scheduled in Hsche.
  simpl in Hsche.
  rewrite /scheduler in Hsche.
  apply bool_decide_unpack in Hsche as Hcur.
  clear Hsche.
  apply fin_to_nat_inj in Hcur.
  iModIntro.
  iDestruct "Hσ" as "(#Hneq & Hmem & Hreg & Hrx & Hown & Hmb & Haccess & Hrest)".
  (* valid regs *)
  iDestruct ((gen_reg_valid1 PC i ai Hcur ) with "Hreg Hpc") as "%HPC";eauto.
  (* valid pt *)
  iDestruct (access_agree_check_true (tpa ai) i with "Haccess Hacc") as %Hacc;first set_solver + Hin.
  (* valid mem *)
  iDestruct (gen_mem_valid ai w1  with "Hmem Hapc") as %Hmem.
  iSplit.
  - (* reducible *)
    iPureIntro.
    apply (reducible_normal i Fail ai w1);eauto.
  - (* step *)
    iModIntro.
    iIntros (m2 σ2) "[%P PAuth] %HstepP".
    apply (step_ExecI_normal i Fail ai w1 ) in HstepP;eauto.
    remember (exec Fail σ1) as c2 eqn:Heqc2.
    rewrite /exec /fail /update_incr_PC in Heqc2;eauto.
    destruct HstepP;subst m2 σ2; subst c2; simpl.
    rewrite /gen_vm_interp.
    iFrame "Hreg Hneq Hmem Hrx Hown Hmb Haccess Hrest".
    iSplitL "PAuth".
    by iExists P.
    rewrite /just_scheduled_vms.
    rewrite /just_scheduled.
    assert (filter
              (λ id : vmid,
                      base.negb (scheduled σ1 id) && scheduled σ1 id = true)
              (seq 0 n) = []) as ->.
    {
      rewrite /scheduled /machine.scheduler //= /scheduler Hcur.
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
    iModIntro.
    iSimpl.
    iSplit; first done.
    assert ((scheduled σ1 i) = true) as ->.
    rewrite /scheduled.
    simpl.
    rewrite /scheduler.
    rewrite Hcur.
    rewrite bool_decide_eq_true.
    reflexivity.
    simpl.
    iApply ("Hϕ" with "[Hpc Hapc Hacc]").
    iFrame.
Qed.
End fail.
