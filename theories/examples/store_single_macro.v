From machine_program_logic.program_logic Require Import weakestpre.
From HypVeri.algebra Require Import base.
From HypVeri.rules Require Import rules_base mov str.

Section StoreSingle.
(* this is a very simple macro that will store a word w to memory cell dst *)
  (* the assumption is the dst addr is stored in R1 *)
(* the side-effect of it is the values of R0 will be changed *)

  Definition str_I r a := encode_instruction (Str r a).
  Definition mov_word_I ra w := encode_instruction (Mov ra (inl w)).

  Definition store_single (w:Imm) : list Word :=
    [
    mov_word_I R0 w;
    str_I R0 R1
    ].

  Context `{gen_VMG Σ} (N : namespace).

  Definition program (instr: list Word) (b:Addr):=
    ([∗ list] a;w ∈ (finz.seq b (length instr));instr, (a ->a w))%I.

  Definition store_single_spec { v q sacc progp proga w a pa} :
      seq_in_page proga (length (store_single w)) progp->
      progp∈ sacc ->
      (to_pid_aligned a) = pa ->
      pa ≠ progp ->
      pa ∈ sacc ->
      program (store_single w) proga ∗
      A@v :={q}[sacc] ∗
      PC @@ v ->r proga ∗
      (∃ r0, R0 @@ v ->r r0 )∗
      R1 @@ v ->r a ∗
      (∃ w0, a ->a w0)
      ⊢ (PARWP ExecI @ v
            {{ (λ m, ⌜m = ExecI ⌝
            ∗ program (store_single w ) proga
            ∗ A@v :={q}[sacc]
            ∗ PC @@ v ->r (proga ^+ (length (store_single w)))%f
            ∗ R0 @@ v ->r (of_imm w)
            ∗ R1 @@ v ->r a
            ∗ a ->a w) }}%I).
  Proof.
    iIntros (HIn HprogpIn Htop Hnep HpIn) "((p_1 & p_2 & _) & Hacc & PC & R0 & R1 & Hmem )".
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
    assert (to_pid_aligned (proga ^+ 1)%f = progp) as Htop2.
    {
        inversion HIn.
        inversion H3.
        apply to_pid_aligned_in_page.
        auto.
    }

    iDestruct
      ((str (proga ^+ 1)%f a R0 R1) with "[p_2 PC Hacc R0 R1 Hmem]") as "J".
    auto.
    2: {
   intro.
        subst a.
        rewrite Htop2 in Htop.
        rewrite Htop // in Hnep.
    }
    3:{ rewrite Htop Htop2. assert({[progp; pa]} ⊆ sacc) as HIn'. { set_solver. }
                                                                  exact HIn'.
        }
    3:{ iFrame. (*TODO: tweak the str rule *) admit. }
    by rewrite decode_encode_instruction.
    admit.
    rewrite -parwp_sswp.
    iApply "J".
    iNext.
    iIntros "(p_2 & PC & Hacc &  Hmem & R1 & R0 & _)".
    iApply parwp_finish.
    iFrame.
    iSplitR.
    done.
    iSplitR.
    done.
    cbn.
    (*TODO: need a lemma? *)
    Admitted.

End StoreSingle.
