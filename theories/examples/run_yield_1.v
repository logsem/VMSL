From machine_program_logic.program_logic Require Import weakestpre.
From HypVeri.algebra Require Import base.
From HypVeri.rules Require Import rules_base mov halt run yield.
From HypVeri.examples Require Import instr.
From HypVeri Require Import proofmode.
Require Import Setoid.

Section RunYield1.

  Local Program Instance vmconfig : HypervisorConstants :=
    {vm_count := 2;
     vm_count_pos:= _}.

  Program Definition V0 : VMID := (@nat_to_fin 0 _ _).

  Program Definition V1 : VMID := (@nat_to_fin 1 _ _).

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

  Lemma machine_z_spec {q1 sacc prog1page} :
      seq_in_page (of_pid prog1page) (length program1) prog1page ->
      prog1page ∈ sacc ->
      (program (program1) (of_pid prog1page)) ∗ (VMProp V0 True%I 1) ∗
      (VMProp V1 ((R0 @@ V0 ->r run_I ∗ R1 @@ V0 ->r encode_vmid V1) ∗ VMProp V0 (R0 @@ V0 ->r yield_I ∗ R1 @@ V0 ->r encode_vmid V1 ∗ VMProp V1 False%I (1/2)%Qp) (1/2)%Qp)%I (1/2)%Qp) ∗
      (A@V0 :={q1}[sacc]) ∗
      (PC @@ V0 ->r (of_pid prog1page)) ∗
      (∃ r0, R0 @@ V0 ->r r0) ∗
      (∃ r1, R1 @@ V0 ->r r1)
        ⊢ (WP ExecI @ V0
              {{ (λ m, ⌜m = HaltI⌝
                            ∗ program program1 (of_pid prog1page)
                            ∗ (A@V0 :={q1}[sacc])
                            ∗ PC @@ V0 ->r ((of_pid prog1page) ^+ (length program1))%f)}}%I).
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
    iApply ((mov_word (of_pid prog1page) run_I R0) with "[p_1 PCz Hacc R0z]"); iFrameAutoSolve.
    { rewrite HIn. set_solver + HaccIn. set_solver +. }
    iModIntro.
    iIntros "(PCz & p_1 & Hacc & R0z)".
    iSimpl.
    iIntros "_".
    (* mov_word_I R1 (encode_vmid i) *)
    rewrite wp_sswp.
    rewrite HV0.
    iApply ((mov_word ((of_pid prog1page) ^+ 1)%f (encode_vmid V1) R1) with "[p_2 PCz Hacc R1z]"); iFrameAutoSolve.
    { rewrite HIn. set_solver + HaccIn. set_solver +. }
    iModIntro.
    iIntros "(PCz & p_2 & Hacc & R1z)".
    iSimpl.
    iIntros "_".
    (* hvc_I *)
    rewrite wp_sswp.
    rewrite HV0.
    set (T := (PC @@ V0 ->r (((prog1page ^+ 1) ^+ 1) ^+ 1)%f ∗ ((prog1page ^+ 1) ^+ 1)%f ->a hvc_I ∗ A@V0:={q1}[sacc])%I).
    iApply ((run (((of_pid prog1page) ^+ 1) ^+ 1)%f V1 (R := True%I) (R' := T)) with "[PCz p_3 Hacc R0z R1z Hprop0 Hprop1]"); iFrameAutoSolve.
    { rewrite HIn. set_solver + HaccIn. set_solver +. }
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
    iModIntro.
    iSimpl.
    subst T.
    iIntros "[(HPC & p_3 & HAcc) Hprop0] [%P' [P' HProp']]".
    (* halt_I *)
    rewrite wp_sswp.
    rewrite HV0.
    iApply ((halt ((((of_pid prog1page) ^+ 1) ^+ 1) ^+1 )%f) with "[HPC p_4 HAcc]");iFrameAutoSolve.
    { rewrite HIn. set_solver + HaccIn. set_solver +. }
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
    iSimpl.
    done.
  Qed.

  Lemma machine_i_spec {q1 prog2page sacc r0_} :
      seq_in_page (of_pid prog2page) (length program2) prog2page ->
      prog2page ∈ sacc ->
      (program program2 (of_pid prog2page))
        ∗ (VMProp V1 ((R0 @@ V0 ->r run_I ∗ R1 @@ V0 ->r encode_vmid V1) ∗ VMProp V0 ((R0 @@ V0 ->r yield_I ∗ R1 @@ V0 ->r encode_vmid V1) ∗ VMProp V1 False%I (1/2)%Qp) (1/2)%Qp)%I (1/2)%Qp)
        ∗ (A@V1 :={q1}[sacc])
        ∗ (PC @@ V1 ->r (of_pid prog2page))
        ∗ (R0 @@ V1 ->r r0_)
        ⊢ VMProp_holds V1 (1/2)%Qp -∗ (WP ExecI @ V1
              {{ (λ m, ⌜m = ExecI⌝
                                 ∗ (program program2 (of_pid prog2page))
                                 ∗ (A@V1 :={q1}[sacc])
                                 ∗ (PC @@ V1 ->r ((of_pid prog2page) ^+ (length program2))%f)
                                 ∗ R0 @@ V1 ->r yield_I)}}%I).
  Proof.
    iIntros (HIn HpIn) "((p_1 & p_2 & _) & HPropi & Hacc & PCi & R0i)".
    iIntros "HPropH".
    iDestruct (VMProp_holds_agree V1 with "[HPropH HPropi]") as "[Prop VMProp]".
    iFrame.
    pose proof (seq_in_page_forall2 _ _ _ HIn) as Hforall.
    clear HIn; rename Hforall into HIn.
    assert (1 = V1) as HV1.
    by simpl.
    (* mov_word_I R0 yield_I *)    
    rewrite wp_sswp.
    iApply ((mov.mov_word (of_pid prog2page) yield_I R0) with "[p_1 PCi Hacc R0i]");iFrameAutoSolve.
    { rewrite HIn. set_solver + HpIn. set_solver +. }
    iModIntro.
    iIntros "(PCi & p_1 & Hacc & R0i)".
    iSimpl.
    rewrite HV1.
    iIntros "_".
    (* hvc_I *)
    rewrite wp_sswp.
    iDestruct "Prop" as "[(HRz0 & HRz1) VMPropz]".
    iApply ((yield ((of_pid prog2page) ^+ 1)%f (z := V0) (Q := (R0 @@ V0 ->r yield_I ∗ R1 @@ V0 ->r encode_vmid V1)%I) (P' := False%I) (R := True%I) (R' := (PC @@ V1 ->r ((prog2page ^+ 1) ^+ 1)%f ∗ (prog2page ^+ 1)%f ->a hvc_I ∗ A@V1:={q1}[sacc]  ∗ R0 @@ V1 ->r yield_I)%I))
         with "[PCi p_2 Hacc R0i HRz0 HRz1 VMPropz VMProp]"); iFrameAutoSolve.
    { rewrite HIn. set_solver + HpIn. set_solver +. }
    { by simpl. }
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
    iModIntro.
    iIntros "[? VMProp] VMPropH".
    simpl.
    iDestruct (VMProp_holds_agree V1 with "[VMProp VMPropH]") as "[Prop VMProp]".
    iFrame "VMProp VMPropH".
    iMod "Prop".
    by iExFalso.
  Qed.
  (* TODO *)
  (*
  Lemma run_yield_1_spec' γ1 γ2 γ3 ι ι1 z i q1 q2 prog1page prog2page sacc1 sacc2 r0_:
      ι ## ι1 ->
      fin_to_nat z = 0 ->
      z ≠ i ->
      prog1page ≠ prog2page ->
      seq_in_page (of_pid prog1page) (length (program1 i)) prog1page ->
      prog1page ∈ sacc1 ->
      seq_in_page (of_pid prog2page) (length program2) prog2page ->
      prog2page ∈ sacc2 ->
      program (program1 i) (of_pid prog1page) ∗
      program (program2) (of_pid prog2page) ∗
      inv ι (inv' z i γ1 γ2 γ3 ι1) ∗
      nainv ι1 (na_inv  γ2 γ3 z i) ∗ tokI γ1 ∗
      A@z :={q1}[sacc1] ∗ A@i :={q2}[sacc2] ∗
      PC @@ z ->r (of_pid prog1page) ∗ PC @@ i ->r (of_pid prog2page) ∗
      R0 @@ i ->r r0_
        ⊢ (WP ExecI @ z {{ (λ m, ⌜m = HaltI⌝
            ∗ program (program1 i) (of_pid prog1page)
            ∗ A@z :={q1}[sacc1]
            ∗ PC @@ z ->r ((of_pid prog1page) ^+ (length (program1 i)))%f )}}%I)
       ∗ (WP ExecI @ i {{ (λ m, ⌜m = ExecI⌝
            ∗ tokI γ1
            ∗ program (program1 i) (of_pid prog2page)
            ∗ A@i :={q2}[sacc2]
            ∗ PC @@ i ->r ((of_pid prog2page) ^+ (length program2))%f
            ∗ R0 @@ i ->r yield_I) }}%I).
  Proof.
    iIntros (Hdisj Z Hvne Hpne HInz HpInz HIni HpIni) "(Hprogz & Hprogi & #Hinv & #Hnainv & H△ & Haccz & Hacci & PCz & PCi & R0i)".
    iSplitL  "Hprogz H△ Haccz PCz".
    - iApply machine_z_spec;eauto.
      iFrame.
      iSplitL;done.
    - iApply machine_i_spec;eauto.
      iFrame.
      iSplitL;done.
  Qed.

  Lemma run_yield_1_spec z i q1 q2 prog1page prog2page sacc1 sacc2 r0_ r1_ r0_':
      fin_to_nat z = 0 ->
      z ≠ i ->
      prog1page ≠ prog2page ->
      prog1page ∈ sacc1 ->
      prog2page ∈ sacc2 ->
      program (program1 i) (of_pid prog1page) ∗
      program (program2) (of_pid prog2page) ∗
      nainv_closed ⊤ ∗
      <<z>>{ 1%Qp} ∗ R0 @@ z ->r r0_ ∗ R1 @@ z ->r r1_ ∗
      A@z :={q1}[sacc1] ∗ A@i :={q2}[sacc2] ∗
      PC @@ z ->r (of_pid prog1page) ∗ PC @@ i ->r (of_pid prog2page) ∗
      R0 @@ i ->r r0_'
        ⊢ |={⊤}=>
        (WP ExecI @ z {{ (λ m, ⌜m = HaltI⌝
            ∗ program (program1 i) (of_pid prog1page)
            ∗ A@z :={q1}[sacc1]
            ∗ PC @@ z ->r ((of_pid prog1page) ^+ (length (program1 i)))%f )}}%I)
       ∗ (WP ExecI @ i {{ (λ m, ⌜m = ExecI⌝
            ∗ program (program1 i) (of_pid prog2page)
            ∗ A@i :={q2}[sacc2]
            ∗ PC @@ i ->r ((of_pid prog2page) ^+ (length program2))%f
            ∗ R0 @@ i ->r yield_I) }}%I).
  Proof.
    iIntros ( Z Hvne Hpne HInz HIni) "(Hprogz & Hprogi & Hnatok & Hstok & R0z & R1z & Haccz & Hacci & PCz & PCi & R0i)".
    iMod (own_alloc (Excl ())) as (γ1) "Htok1". done.
    iMod (own_alloc (Excl ())) as (γ2) "Htok2". done.
    iMod (own_alloc (Excl ())) as (γ3) "Htok3". done.
    iMod ((nainv_alloc nainvN ⊤ (na_inv  γ2 γ3 z i)) with "[ R0z R1z Htok2 ]" ) as "Hnainv".
    { iNext. iLeft. iExists r0_, r1_. iFrame. }
    iMod (inv_alloc invN _ (inv' z i γ1 γ2 γ3 nainvN) with "[Hstok Hnatok Htok3]") as "Hinv".
    { iNext. iRight;iLeft. iFrame. }
    iModIntro.
    iDestruct (run_yield_1_spec' γ1 γ2 γ3 invN nainvN z i q1 q2 prog1page prog2page sacc1 sacc2 r0_'
                 with "[Hprogz Hprogi Haccz Hacci PCz PCi R0i Htok1 Hnainv Hinv]") as "[WP1 WP2]";eauto.
    { apply namespace_disjoint. }
    {
      rewrite /seq_in_page.
      split.
      simpl;lia.
      split.
      rewrite Z.leb_refl //.
      split.
      cbn.
      pose proof (last_addr_in_bound prog1page).
      solve_finz.
      cbn.
      rewrite /Is_true.
      case_match;[done|].
      apply Z.leb_nle in Heqb.
      solve_finz.
    }
    {
      rewrite /seq_in_page.
      split.
      simpl;lia.
      split.
      rewrite Z.leb_refl //.
      split.
      cbn.
      pose proof (last_addr_in_bound prog2page).
      solve_finz.
      cbn.
      rewrite /Is_true.
      case_match;[done|].
      apply Z.leb_nle in Heqb.
      solve_finz.
    }
    { iFrame. }
    iFrame.
    iApply (wp_mono with "WP2").
    iIntros (?) "(? & ? & ? & ? & ? & ? )".
    iFrame.
  Qed.
   *)

End RunYield1.
