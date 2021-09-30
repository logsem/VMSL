From machine_program_logic.program_logic Require Import weakestpre.
From HypVeri.algebra Require Import base.
From HypVeri.rules Require Import rules_base mov str.
From HypVeri.examples Require Import instr.
From HypVeri Require Import proofmode.

Section StoreSingle.
(* this is a very simple program that will store a word w to memory cell dst *)
(* the assumption is the dst addr is stored in R1 *)
(* the side-effect of it is the values of R0 will be changed *)

  Definition store_single (w:Imm) : list Word :=
    encode_instructions [
      Mov R0 (inl w);
      Str R0 R1
    ].
  Context `{hypparams:HypervisorParameters}.
  Context `{vmG:!gen_VMG Σ}.

  Definition store_single_spec { v q sacc ppg proga w a pa prx} :
      seq_in_page proga (length (store_single w)) ppg ->
      ppg∈ sacc ->
      (to_pid_aligned a) = pa ->
      prx ≠ pa ->
      pa ∈ sacc ->
      program (store_single w) proga ∗
      A@v :={q}[sacc] ∗
      PC @@ v ->r proga ∗
      (∃ r0, R0 @@ v ->r r0 )∗
      R1 @@ v ->r a ∗
      (∃ w0, a ->a w0) ∗
      RX@ v := prx
      ⊢ (PARWP ExecI @ v
            {{ (λ m, ⌜m = ExecI ⌝
            ∗ program (store_single w ) proga
            ∗ A@v :={q}[sacc]
            ∗ PC @@ v ->r (proga ^+ (length (store_single w)))%f
            ∗ R0 @@ v ->r (of_imm w)
            ∗ R1 @@ v ->r a
            ∗ a ->a w
            ∗ RX@ v := prx) }}%I).
  Proof.
    iIntros (HIn HppgIn Htop Hneprx HpIn) "((p_1 & p_2 & _) & Hacc & PC & R0 & R1 & Hmem & Hrx )".
    pose proof (seq_in_page_forall1 _ _ _ HIn) as Hforall.
    clear HIn; rename Hforall into HIn.
    apply Forall_forall in HIn.
    rewrite -parwp_sswp.
    iDestruct "R0" as (?) "R0".
    iApply (mov_word with "[p_1 PC Hacc R0]"); iFrameAutoSolve.
    by inversion HIn.
    auto.
    iNext.
    iIntros "(PC & p_1 & Hacc & R0)".
    iDestruct "Hmem" as (?) "Hmem".
    assert (to_pid_aligned (proga ^+ 1)%f = ppg ) as Htop2.
    {
        inversion HIn.
        inversion H3.
        apply to_pid_aligned_in_page.
        auto.
    }
    rewrite -parwp_sswp.
    iApply (str with "[p_2 PC Hacc R0 R1 Hmem Hrx]"); iFrameAutoSolve.
    { rewrite -Htop in Hneprx. exact Hneprx. }
    { set_solver. }
    iIntros "!> (p_2 & PC & Hacc & Hmem & R1 & R0 & Hrx)".
    iApply parwp_finish.
    iFrame.
    iSplitR.
    done.
    iSplitR.
    done.
    cbn.
    rewrite finz_plus_assoc;try lia.
    iFrame.
Qed.

End StoreSingle.
