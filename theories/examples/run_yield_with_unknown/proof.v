From machine_program_logic.program_logic Require Import weakestpre.
From HypVeri.algebra Require Import base.
From HypVeri.rules Require Import rules_base mov halt run yield.
From HypVeri.examples Require Import instr.
From HypVeri.logrel Require Import logrel.
From HypVeri Require Import proofmode.
Require Import Setoid.

Program Instance rywu_vmconfig : HypervisorConstants :=
    {vm_count := 3;
     vm_count_pos:= _}.

Program Definition V0 : VMID := (@nat_to_fin 0 _ _).
Program Definition V1 : VMID := (@nat_to_fin 1 _ _).
Program Definition V2 : VMID := (@nat_to_fin 2 _ _).

Section proof.

  Context `{hypparams: !HypervisorParameters}.

  Definition rywu_program1 : list Word :=
    [
    mov_word_I R0 run_I;
    mov_word_I R1 (encode_vmid V1);
    hvc_I;
    mov_word_I R0 run_I;
    mov_word_I R1 (encode_vmid V2);
    hvc_I;
    halt_I
    ].

  Definition rywu_program2 : list Word :=
    [
    mov_word_I R0 yield_I;
    hvc_I
    ].

  Context `{!gen_VMG Σ}.

  (* TODO *)
  Lemma rywu_machine0 {prog1page} R :
      let Q := ((* R0 & R1 of pvm *)
        (R0 @@ V0 ->r encode_hvc_func(Run) ∗ R1 @@ V0 ->r encode_vmid(V2)))%I in
      seq_in_page (of_pid prog1page) (length rywu_program1) prog1page ->
      R ∗
      (program (rywu_program1) (of_pid prog1page)) ∗ (VMProp V0 True%I 1) ∗
      (VMProp V1 ((R0 @@ V0 ->r run_I ∗ R1 @@ V0 ->r encode_vmid V1 ) ∗
                    VMProp V0 ((R0 @@ V0 ->r yield_I ∗ R1 @@ V0 ->r encode_vmid V1 ) ∗
                                 VMProp V1 False%I (1/2)%Qp) (1/2)%Qp)%I (1/2)%Qp) ∗
      (VMProp V2 (Q ∗ VMProp V0 ((R0 @@ V0 ->r yield_I ∗ R1 @@ V0 ->r encode_vmid V2 ∗
                                  (R )) ∨ False) (1/2)%Qp) (1/2%Qp)) ∗
      (V0 -@A> [{[prog1page]}]) ∗
      (PC @@ V0 ->r (of_pid prog1page)) ∗
      (∃ r0, R0 @@ V0 ->r r0) ∗
      (∃ r1, R1 @@ V0 ->r r1)
      ⊢ WP ExecI @ V0
            {{ (λ m,
                 ⌜m = HaltI⌝ ∗
                 program rywu_program1 (of_pid prog1page) ∗
                 (V0 -@A> [{[prog1page]}]) ∗
                 PC @@ V0 ->r ((of_pid prog1page) ^+ (length rywu_program1))%f∗
                 R0 @@ V0 ->r yield_I ∗
                 R1 @@ V0 ->r encode_vmid V2 ∗
                 R)}}%I.
  Proof.
    iIntros (Q HIn) "(R & Q & (p_1 & p_2 & p_3 & p_4 & p_5 & p_6 & p_7 & _) & Hprop0 & Hprop1 & Hprop2 & Hacc & Hacc' & PCz & R0z & R1z)".
    pose proof (seq_in_page_forall2 _ _ _ HIn) as Hforall.
    clear HIn; rename Hforall into HIn.
    iDestruct "R0z" as "(%r0 & R0z)".
    iDestruct "R1z" as "(%r1 & R1z)".
    (* mov_word_I R0 run_I *)
    rewrite wp_sswp.
    iApply ((mov_word (of_pid prog1page) run_I R0) with "[p_1 PCz Hacc R0z]");try rewrite HIn //; iFrameAutoSolve; try set_solver +.
    iModIntro.
    iIntros "(PCz & p_1 & Hacc & R0z)".
    iIntros "_".
    (* mov_word_I R1 V1 *)
    rewrite wp_sswp.
    iApply ((mov_word ((of_pid prog1page) ^+ 1)%f (encode_vmid V1) R1) with "[p_2 PCz Hacc R1z]"); try rewrite HIn //; iFrameAutoSolve; try set_solver +.
    iModIntro.
    iIntros "(PCz & p_2 & Hacc & R1z)".
    iIntros "_".
    (* hvc_I *)
    rewrite wp_sswp.
    set (T := (PC @@ V0 ->r (((prog1page ^+ 1) ^+ 1) ^+ 1)%f ∗ ((prog1page ^+ 1) ^+ 1)%f ->a hvc_I ∗ prog1page -@A> V0)%I).
    iApply ((run (((of_pid prog1page) ^+ 1) ^+ 1)%f V1 (s:= {[V0]}) (R := (prog2page -@A> V1)%I) (R' := T) (i' := 1))
             with "[PCz p_3 Hacc Hacc' R0z R1z Hprop0 Hprop1]"); try rewrite HIn //;iFrameAutoSolve.
    { set_solver +. }
    { solve_finz. }
    { solve_finz. }
    { apply decode_encode_hvc_func. }
    { apply decode_encode_vmid. }
    {
      iSplitR "Hprop0".
      - iModIntro.
        iFrame "Hprop1".
      - iSplitL "Hprop0".
        iFrame "Hprop0".
        iNext.
          iIntros "[(PCz & p_4 & Hacc & R0z & R1z) R]".
          iFrame.
    }
    {
    set_solver.
    }
    iModIntro.
    subst T.
    iIntros "[(PC & p_3 & Hacc) Hprop0] Hholds".
    iDestruct (VMProp_holds_agree with "[Hholds Hprop0]") as "[P' Hprop0]".
    iFrame "Hprop0".
    iSimpl.
    iSimpl in "Hholds".
    done.
    (* getting back resources *)
    iDestruct "P'" as "((>R0z & >R1z & >Hacc') & Hprop1)".
    rewrite wp_sswp.
    iApply ((mov_word _ run_I R0) with "[p_4 PC Hacc R0z]");try rewrite HIn //; iFrameAutoSolve; try set_solver +.
    iModIntro.
    iIntros "(PCz & p_4 & Hacc & R0z)".
    iIntros "_".
    (* mov_word_I R1 V2 *)
    rewrite wp_sswp.
    iApply ((mov_word _ (encode_vmid V2) R1) with "[p_5 PCz Hacc R1z]"); try rewrite HIn //; iFrameAutoSolve; try set_solver +.
    iModIntro.
    iIntros "(PCz & p_5 & Hacc & R1z)".
    iIntros "_".
    (* hvc_I *)
    rewrite wp_sswp.
    set (R' := (PC @@ V0 ->r ((((((prog1page ^+ 1) ^+ 1) ^+ 1) ^+ 1) ^+ 1) ^+ 1)%f ∗
            (((((prog1page ^+ 1) ^+ 1) ^+ 1) ^+ 1) ^+ 1)%f ->a hvc_I ∗
                    prog1page -@A> V0)%I).
    iApply ((run (((((prog1page ^+ 1) ^+ 1) ^+ 1) ^+ 1) ^+ 1)%f V2 (R := R%I)
                (R' := PC @@ V0 ->r ((((((prog1page ^+ 1) ^+ 1) ^+ 1) ^+ 1) ^+ 1) ^+ 1)%f
                                 ∗(((((prog1page ^+ 1) ^+ 1) ^+ 1) ^+ 1) ^+ 1)%f ->a hvc_I )
                (i' := 2)) with "[PCz p_6 Hacc Hacc' R0z R1z Hprop0 Hprop2 Q R]"); try rewrite HIn //;iFrameAutoSolve.
    { set_solver +. }
    { solve_finz. }
    { solve_finz. }
    { apply decode_encode_hvc_func. }
    { apply decode_encode_vmid. }
    { iSplitL "Hprop2".
      done.
      iSplitL "Hprop0".
      done.
      iFrame "R".
      iNext.
      iIntros "((PC & addr & acc & R0 & R1) & R)".
      iFrame "PC addr".
      unfold Q.
      iFrame.
      iApply "Q".
      iFrame.
    }
    { set_solver +. }
    iNext.
    iIntros "((PC & p_6) & Hprop0) Hholds0".
    iDestruct (VMProp_holds_agree with "[Hholds0 Hprop0]") as "[P' Hprop0]".
    iSplitR "Hprop0".
    2: { iFrame "Hprop0". }
    iSimpl.
    iSimpl in "Hholds0".
    done.
    (* getting back resources *)
    iDestruct "P'" as "[(>R0z & >R1z & R & >acc)|>False]".
    2: { (* V2 does not yield *)
    iExFalso.
    iExact "False".
    }
    (* halt_I *)
    rewrite wp_sswp.
    iApply ((halt (((((((of_pid prog1page) ^+ 1) ^+ 1) ^+ 1) ^+ 1) ^+ 1) ^+ 1)%f) with "[PC p_7 acc]");
      try rewrite HIn //; iFrameAutoSolve;try set_solver +.
    iNext.
    iIntros "( PCz & p_7 & acc)".
    iIntros "_".
    iApply wp_terminated'; eauto.
    assert (Hlen: (((((((prog1page ^+ 1) ^+ 1) ^+ 1) ^+ 1) ^+ 1) ^+ 1) ^+ 1)%f = ((of_pid prog1page) ^+ length rywu_program1)%f).
    {
    assert (Hlen4 : (Z.of_nat (length rywu_program1)) = 7%Z). by compute.
    rewrite Hlen4;clear Hlen4.
    solve_finz.
    }
    rewrite Hlen.
    iFrame.
    iSplitR; first done.
    done.
  Qed.

  Lemma rywu_machine1 {prog2page} :
      seq_in_page (of_pid prog2page) (length rywu_program2) prog2page ->
      (program rywu_program2 (of_pid prog2page))
        ∗ (VMProp V1 ((R0 @@ V0 ->r run_I ∗ R1 @@ V0 ->r encode_vmid V1 ∗ (prog2page -@A> V1))
        ∗ VMProp V0 ((R0 @@ V0 ->r yield_I ∗ R1 @@ V0 ->r encode_vmid V1 ∗ (prog2page -@A> V1)) ∗ VMProp V1 False%I (1/2)%Qp) (1/2)%Qp)%I (1/2)%Qp)
        ∗ (PC @@ V1 ->r (of_pid prog2page))
        ∗ (∃ r0, R0 @@ V1 ->r r0)
        ⊢ VMProp_holds V1 (1/2)%Qp -∗ (WP ExecI @ V1
              {{ (λ m, False)}}%I).
  Proof.
    iIntros (HIn ) "((p_1 & p_2 & _) & HPropi & PC1 & R01)".
    iIntros "HPropH".
    iDestruct "R01" as "[%r0 R01]".
    iDestruct (VMProp_holds_agree V1 with "[HPropH HPropi]") as "[Prop VMProp]".
    iFrame.
    pose proof (seq_in_page_forall2 _ _ _ HIn) as Hforall.
    clear HIn; rename Hforall into HIn.
    assert (1 = V1) as HV1.
    by simpl.
    (* mov_word_I R0 yield_I *)    
    rewrite wp_sswp.
    iDestruct "Prop" as "[(HRz0 & HRz1 & Hacc) VMPropz]".
    iApply ((mov.mov_word (of_pid prog2page) yield_I R0) with "[p_1 PC1 Hacc R01]");try rewrite HIn //;iFrameAutoSolve;try set_solver.
    { iFrame. }
    iModIntro.
    iIntros "(PC1 & p_1 & Hacc & R0i)".
    iSimpl.
    rewrite HV1.
    iIntros "_".
    (* hvc_I *)
    rewrite wp_sswp.
    iApply ((yield ((of_pid prog2page) ^+ 1)%f (z := V0) (Q := (R0 @@ V0 ->r yield_I ∗ R1 @@ V0 ->r encode_vmid V1 ∗ (prog2page -@A> V1))%I)
                   (P' := False%I) (R := True%I) (i' := 1)
                   (R' := (PC @@ V1 ->r ((prog2page ^+ 1) ^+ 1)%f ∗ (prog2page ^+ 1)%f ->a hvc_I ∗ R0 @@ V1 ->r yield_I)%I))
         with "[PC1 p_2 Hacc R0i HRz0 HRz1 VMPropz VMProp]"); try rewrite HIn //;iFrameAutoSolve.
    { set_solver +. }
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
  
  
End proof.
