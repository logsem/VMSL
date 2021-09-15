From machine_program_logic.program_logic Require Import weakestpre.
From HypVeri.algebra Require Import base.
From HypVeri.rules Require Import rules_base mov str.
From HypVeri.examples Require Import instr.

Section StoreSingle.
(* this is a very simple program that will store a word w to memory cell dst *)
(* the assumption is the dst addr is stored in R1 *)
(* the side-effect of it is the values of R0 will be changed *)

  Definition store_single (w:Imm) : list Word :=
    [
    mov_word_I R0 w;
    str_I R0 R1
    ].

  Context `{gen_VMG Σ}.

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
    apply seq_in_page_forall in HIn.
    rewrite -parwp_sswp.
    iDestruct "R0" as (?) "R0".
    iDestruct
      ((mov_word proga w R0) with "[p_1 PC Hacc R0]") as "J";auto.
    4:{  iFrame. }
    by rewrite decode_encode_instruction.
    by inversion HIn.
    auto.
    iApply "J".
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
    iDestruct
      ((str (proga ^+ 1)%f a R0 R1 sacc) with "[p_2 PC Hacc R0 R1 Hmem Hrx]") as "J".
    5:{ iFrame. }
    all: auto.
    by rewrite decode_encode_instruction.
    rewrite -Htop in Hneprx. exact Hneprx.
    set_solver.
    rewrite -parwp_sswp.
    iApply "J".
    iNext.
    iIntros "(p_2 & PC & Hacc & Hmem & R1 & R0 & Hrx)".
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
