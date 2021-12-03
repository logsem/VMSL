From machine_program_logic.program_logic Require Import weakestpre.
From HypVeri.algebra Require Import base.
From HypVeri.rules Require Import rules_base mov halt run yield.
From HypVeri.examples Require Import instr.
From HypVeri Require Import proofmode.
Require Import Setoid.

Program Instance vmconfig : HypervisorConstants :=
    {vm_count := 3;
     vm_count_pos:= _}.

Program Definition V0 : VMID := (@nat_to_fin 0 _ _).

Program Definition V1 : VMID := (@nat_to_fin 1 _ _).

Section run_yield.

  Context `{hypparams: !HypervisorParameters}.

  Definition program1 : list Word :=
    [
    mov_word_I R0 run_I;
    mov_word_I R1 (encode_vmid V1);
    hvc_I;
    halt_I
    ].

  Definition program2 : list Word :=
    [
    mov_word_I R0 yield_I;
    hvc_I
    ].

  Context `{!gen_VMG Σ}.


  Lemma machine_0_spec {q1 sacc prog1page} :
      seq_in_page (of_pid prog1page) (length program1) prog1page ->
      V0 ∈ sacc ->
      (program (program1) (of_pid prog1page)) ∗ (VMProp V0 True%I 1) ∗
      (VMProp V1 ((R0 @@ V0 ->r run_I ∗ R1 @@ V0 ->r encode_vmid V1) ∗ VMProp V0 ((R0 @@ V0 ->r yield_I ∗ R1 @@ V0 ->r encode_vmid V1) ∗ VMProp V1 False%I (1/2)%Qp) (1/2)%Qp)%I (1/2)%Qp) ∗
      (prog1page -@{q1}A> [sacc]) ∗
      (PC @@ V0 ->r (of_pid prog1page)) ∗
      (∃ r0, R0 @@ V0 ->r r0) ∗
      (∃ r1, R1 @@ V0 ->r r1)
        ⊢ (WP ExecI @ V0
              {{ (λ m, ⌜m = HaltI⌝
                            ∗ program program1 (of_pid prog1page)
                            ∗ (prog1page -@{q1}A> [sacc])
                            ∗ PC @@ V0 ->r ((of_pid prog1page) ^+ (length program1))%f
                            ∗ (R0 @@ V0 ->r yield_I)
                            ∗ (R1 @@ V0 ->r encode_vmid V1)
                            ∗ (VMProp V1 False%I (1/2)%Qp)
                            ∗ (VMProp V0 ((R0 @@ V0 ->r yield_I ∗ R1 @@ V0 ->r encode_vmid V1)%I ∗ VMProp V1 False%I (1 / 2)%Qp) 1%Qp))}}%I).
  Proof.
    iIntros (HIn HaccIn) "((p_1 & p_2 & p_3 & p_4 & _) & Hprop0 & Hprop1 & Hacc & PCz & R0z & R1z)".
    pose proof (seq_in_page_forall2 _ _ _ HIn) as Hforall.
    assert (0 = V0) as HV0.
    by simpl.
    clear HIn; rename Hforall into HIn.
    iDestruct "R0z" as "(%r0 & R0z)".
    iDestruct "R1z" as "(%r1 & R1z)".
    (* mov_word_I R0 run_I *)
    rewrite wp_sswp.
    iApply ((mov_word (of_pid prog1page) run_I R0) with "[p_1 PCz Hacc R0z]");try rewrite HIn //; iFrameAutoSolve; try set_solver + HaccIn.
    iModIntro.
    iIntros "(PCz & p_1 & Hacc & R0z)".
    iSimpl.
    iIntros "_".
    (* mov_word_I R1 (encode_vmid i) *)
    rewrite wp_sswp.
    rewrite HV0.
    iApply ((mov_word ((of_pid prog1page) ^+ 1)%f (encode_vmid V1) R1) with "[p_2 PCz Hacc R1z]"); try rewrite HIn //; iFrameAutoSolve; try set_solver + HaccIn.
    iModIntro.
    iIntros "(PCz & p_2 & Hacc & R1z)".
    iSimpl.
    iIntros "_".
    (* hvc_I *)
    rewrite wp_sswp.
    rewrite HV0.
    set (T := (PC @@ V0 ->r (((prog1page ^+ 1) ^+ 1) ^+ 1)%f ∗ ((prog1page ^+ 1) ^+ 1)%f ->a hvc_I ∗ prog1page -@{q1}A> [sacc])%I).
    iApply ((run (((of_pid prog1page) ^+ 1) ^+ 1)%f V1 (R := True%I) (R' := T) (i' := 1)) with "[PCz p_3 Hacc R0z R1z Hprop0 Hprop1]"); try rewrite HIn //;iFrameAutoSolve.
    { solve_finz. }
    { apply decode_encode_hvc_func. }
    { apply decode_encode_vmid. }
    {
      iSplitR "Hprop0".
      - iModIntro.
        iFrame "Hprop1".
      - iSplitL "Hprop0".
        iFrame "Hprop0".
        iSplitR "".
        + iNext.
          iIntros "[(PCz & p_4 & Hacc & R0z & R1z) R]".
          iFrame.
        + by iNext. 
    }
    {
    set_solver.
    }
    iModIntro.
    iSimpl.
    subst T.
    iIntros "[(HPC & p_3 & HAcc) Hprop0] [%P' [P' HProp']]".
    (* halt_I *)
    rewrite wp_sswp.
    rewrite HV0.
    iApply ((halt ((((of_pid prog1page) ^+ 1) ^+ 1) ^+1 )%f) with "[HPC p_4 HAcc]");
      try rewrite HIn //; iFrameAutoSolve;try set_solver + HaccIn.
    iDestruct (VMProp_holds_agree V0 with "[Hprop0 HProp' P']") as "[Prop VMProp]".
    iSplitL "HProp' P'".
    iExists P'.
    iFrame.
    iFrame "Hprop0".
    iNext.
    iIntros "( PCz & p_4 & Hacc )".
    iSimpl.
    iIntros "_".
    iApply wp_terminated'; eauto.
    assert (Hlen: (((((of_pid prog1page) ^+ 1) ^+ 1) ^+ 1) ^+ 1)%f = ((of_pid prog1page) ^+ length program1)%f).
    {
    assert (Hlen4 : (Z.of_nat (length program1)) = 4%Z). by compute.
    rewrite Hlen4;clear Hlen4.
    solve_finz.
    }
    rewrite Hlen.
    iFrame.
    iSplitR; first done.
    iSplitR; first done.
    iDestruct "Prop" as "((R0 & R1) & VMProp')".
    iFrame.
  Qed.

  Lemma machine_1_spec {q1 prog2page sacc} :
      seq_in_page (of_pid prog2page) (length program2) prog2page ->
      V1 ∈ sacc ->
      (program program2 (of_pid prog2page))
        ∗ (VMProp V1 ((R0 @@ V0 ->r run_I ∗ R1 @@ V0 ->r encode_vmid V1)
        ∗ VMProp V0 ((R0 @@ V0 ->r yield_I ∗ R1 @@ V0 ->r encode_vmid V1) ∗ VMProp V1 False%I (1/2)%Qp) (1/2)%Qp)%I (1/2)%Qp)
        ∗ (prog2page -@{q1}A> [sacc])
        ∗ (PC @@ V1 ->r (of_pid prog2page))
        ∗ (∃ r0, R0 @@ V1 ->r r0)
        ⊢ VMProp_holds V1 (1/2)%Qp -∗ (WP ExecI @ V1
              {{ (λ m, False)}}%I).
  Proof.
    iIntros (HIn HpIn) "((p_1 & p_2 & _) & HPropi & Hacc & PCi & R0i)".
    iIntros "HPropH".
    iDestruct "R0i" as "[%r0 R0i]".
    iDestruct (VMProp_holds_agree V1 with "[HPropH HPropi]") as "[Prop VMProp]".
    iFrame.
    pose proof (seq_in_page_forall2 _ _ _ HIn) as Hforall.
    clear HIn; rename Hforall into HIn.
    assert (1 = V1) as HV1.
    by simpl.
    (* mov_word_I R0 yield_I *)    
    rewrite wp_sswp.
    iApply ((mov.mov_word (of_pid prog2page) yield_I R0) with "[p_1 PCi Hacc R0i]");try rewrite HIn //;iFrameAutoSolve;try set_solver.
    iModIntro.
    iIntros "(PCi & p_1 & Hacc & R0i)".
    iSimpl.
    rewrite HV1.
    iIntros "_".
    (* hvc_I *)
    rewrite wp_sswp.
    iDestruct "Prop" as "[(HRz0 & HRz1) VMPropz]".
    iApply ((yield ((of_pid prog2page) ^+ 1)%f (z := V0) (Q := (R0 @@ V0 ->r yield_I ∗ R1 @@ V0 ->r encode_vmid V1)%I)
                   (P' := False%I) (R := True%I) (i' := 1)
                   (R' := (PC @@ V1 ->r ((prog2page ^+ 1) ^+ 1)%f ∗ (prog2page ^+ 1)%f ->a hvc_I ∗ prog2page -@{q1}A> [sacc]  ∗ R0 @@ V1 ->r yield_I)%I))
         with "[PCi p_2 Hacc R0i HRz0 HRz1 VMPropz VMProp]"); try rewrite HIn //;iFrameAutoSolve.
    { solve_finz. }
    { apply decode_encode_hvc_func. }
    { iSplitL "VMPropz".
      iNext.
      iFrame "VMPropz".
      iSplitL "VMProp".
      iNext.
      iFrame "VMProp".
      iSplitL "".
      - iNext.
        iIntros "[(? & ? & ? & ? & ? & ?) ?]".
        iFrame.
      - by iNext.
    }
    { set_solver +. }
    iModIntro.
    iIntros "[? VMProp] VMPropH".
    simpl.
    iDestruct (VMProp_holds_agree V1 with "[VMProp VMPropH]") as "[Prop VMProp]".
    iFrame "VMProp VMPropH".
    iMod "Prop".
    by iExFalso.
  Qed.
  
  
  Lemma run_yield_1_spec q1 q2 prog1page prog2page sacc1 sacc2 :
      prog1page ≠ prog2page ->
      seq_in_page (of_pid prog1page) (length program1) prog1page ->
      V0 ∈ sacc1 ->
      seq_in_page (of_pid prog2page) (length program2) prog2page ->
      V1 ∈ sacc2 ->
      program (program1) (of_pid prog1page) ∗
      program (program2) (of_pid prog2page) ∗
      (VMProp V0 True%I 1) ∗
      (VMProp V1 ((R0 @@ V0 ->r run_I ∗ R1 @@ V0 ->r encode_vmid V1) ∗ VMProp V0 ((R0 @@ V0 ->r yield_I ∗ R1 @@ V0 ->r encode_vmid V1) ∗ VMProp V1 False%I (1/2)%Qp) (1/2)%Qp)%I 1%Qp) ∗
      (prog1page -@{q1}A> [sacc1]) ∗
      (prog2page -@{q2}A> [sacc2]) ∗
      (PC @@ V0 ->r (of_pid prog1page)) ∗
      (PC @@ V1 ->r (of_pid prog2page)) ∗
      (∃ r0, R0 @@ V0 ->r r0) ∗
      (∃ r1, R1 @@ V0 ->r r1) ∗
      (∃ r0, R0 @@ V1 ->r r0)
        ⊢ (True -∗ WP ExecI @ V0 {{ (λ m, (⌜m = HaltI⌝)
                                       ∗ (program (program1) (of_pid prog1page))
                                       ∗ (prog1page -@{q1}A> [sacc1])
                                       ∗ (PC @@ V0 ->r ((of_pid prog1page) ^+ (length program1))%f)
                                       ∗ (R0 @@ V0 ->r yield_I)
                                       ∗ (R1 @@ V0 ->r encode_vmid V1)
                                       ∗ (VMProp V1 False%I (1/2)%Qp)
                                       ∗ (VMProp V0 ((R0 @@ V0 ->r yield_I ∗ R1 @@ V0 ->r encode_vmid V1)%I ∗ VMProp V1 False%I (1 / 2)%Qp) 1%Qp))}}%I)
      ∗ (VMProp_holds V1 (1/2)%Qp -∗ WP ExecI @ V1 {{ (λ m, False) }}%I).
  Proof.
    iIntros (Hpne HInz HpInz HIni HpIni) "(Hprogz & Hprogi & Hprop0 & Hprop1 & Haccz & Hacci & PCz & PCi & R0z & R1z & R0i)".
    iDestruct (VMProp_split with "Hprop1") as "[Hprop1 Hprop1']".
    iSplitL  "Hprogz Haccz PCz R0z R1z Hprop0 Hprop1".
    - iIntros "_".
      iApply machine_0_spec; eauto.
      iFrame.
    - iApply machine_1_spec; eauto.
      iFrame.
  Qed.

End run_yield.
