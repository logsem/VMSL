From machine_program_logic.program_logic Require Import weakestpre.
From HypVeri.algebra Require Import base lower_bound.
From HypVeri.rules Require Import rules_base mov halt run yield.
From HypVeri.examples Require Import instr.
From HypVeri.logrel Require Import logrel logrel_extra.
From HypVeri Require Import proofmode machine_extra.
Require Import Setoid.

Program Instance rywu_vmconfig : HypervisorConstants :=
    {vm_count := 3;
     vm_count_pos:= _}.

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
 (*TODO change ps*)
  Notation VMProp2 ps p:= (VMProp_unknown V2 ps p ∅) (only parsing).

  Lemma rywu_machine0 {prog1page prog3page} p_rx2 :
      let R2 := (RX@V2 :=() ∗ RX@ V2 := p_rx2 ∗ memory_pages {[p_rx2]})%I in
      prog1page ≠ prog3page ->
      seq_in_page (of_pid prog1page) (length rywu_program1) prog1page ->
      (program (rywu_program1) (of_pid prog1page)) ∗
      (V0 -@A> [{[prog1page]}]) ∗
      (PC @@ V0 ->r (of_pid prog1page)) ∗
      (∃ r0, R0 @@ V0 ->r r0) ∗
      (∃ r1, R1 @@ V0 ->r r1) ∗
      (VMProp V0 True%I 1) ∗
      (VMProp V1 ((R0 @@ V0 ->r run_I ∗ R1 @@ V0 ->r encode_vmid V1) ∗
                    VMProp V0 ((R0 @@ V0 ->r yield_I ∗ R1 @@ V0 ->r encode_vmid V1) ∗
                                 VMProp V1 False%I (1/2)%Qp) (1/2)%Qp)%I (1/2)%Qp) ∗
      (VMProp2 {[prog3page]} p_rx2) ∗
      V2 -@{1/2}A> prog3page ∗
      LB_auth ∅ ∗
      hp [hs_all] ∗
      R2
      ⊢ WP ExecI @ V0
            {{ (λ m,
                 ⌜m = HaltI⌝ ∗
                 program rywu_program1 (of_pid prog1page) ∗
                 (V0 -@A> [{[prog1page]}]) ∗
                 PC @@ V0 ->r ((of_pid prog1page) ^+ (length rywu_program1))%f∗
                 R0 @@ V0 ->r yield_I ∗
                 R1 @@ V0 ->r encode_vmid V2
                 )}}%I.
  Proof.
    rewrite /VMProp_unknown.
    iIntros (Hneq_p HIn) "((p_1 & p_2 & p_3 & p_4 & p_5 & p_6 & p_7 & _) & acc & PCz & (%r0 & R0z) & (%r1 & R1z)
                            & prop0 & prop1 & prop2 & acc2 & LB_auth & hp & R2)".
    pose proof (seq_in_page_forall2 _ _ _ HIn) as Hforall.
    clear HIn; rename Hforall into HIn.
    (* mov_word_I R0 run_I *)
    rewrite wp_sswp.
    iApply ((mov_word (of_pid prog1page) run_I R0) with "[p_1 PCz acc R0z]");try rewrite HIn //; iFrameAutoSolve; try set_solver +.
    iModIntro.
    iIntros "(PCz & p_1 & acc & R0z) _".
    (* mov_word_I R1 V1 *)
    rewrite wp_sswp.
    iApply ((mov_word ((of_pid prog1page) ^+ 1)%f (encode_vmid V1) R1) with "[p_2 PCz acc R1z]"); try rewrite HIn //; iFrameAutoSolve; try set_solver +.
    iModIntro.
    iIntros "(PCz & p_2 & acc & R1z) _".
    (* hvc_I *)
    rewrite wp_sswp.
    set (T := (PC @@ V0 ->r (((prog1page ^+ 1) ^+ 1) ^+ 1)%f ∗ ((prog1page ^+ 1) ^+ 1)%f ->a hvc_I ∗ V0 -@A> [{[prog1page]}])%I).
    iApply ((run (((of_pid prog1page) ^+ 1) ^+ 1)%f V1 (R := True) (R' := T))
             with "[PCz p_3 acc R0z R1z prop0 prop1]"); try rewrite HIn //;iFrameAutoSolve.
    { set_solver +. }
    { set_solver +. }
    { apply decode_encode_hvc_func. }
    { apply decode_encode_vmid. }
    {
      iSplitR "prop0".
      - iModIntro.
        iFrame "prop1".
      - iSplitL "prop0".
        iFrame "prop0".
        iSplitR "";last done.
        iNext.
        iIntros "((PCz & p_4 & acc & R0z & R1z) & _ & prop)".
        iFrame.
    }
    iModIntro.
    iIntros "[(PC & p_3 & acc) prop0] Hholds".
    iDestruct (VMProp_holds_agree with "[Hholds prop0]") as "[P' prop0]".
    iFrame "prop0".
    iFrame.
    (* getting back resources *)
    iDestruct "P'" as "((>R0z & >R1z) & prop1)".
    rewrite wp_sswp.
    iApply ((mov_word _ run_I R0) with "[p_4 PC acc R0z]");try rewrite HIn //; iFrameAutoSolve; try set_solver +.
    iModIntro.
    iIntros "(PCz & p_4 & acc & R0z)".
    iIntros "_".
    (* mov_word_I R1 V2 *)
    rewrite wp_sswp.
    iApply ((mov_word _ (encode_vmid V2) R1) with "[p_5 PCz acc R1z]"); try rewrite HIn //; iFrameAutoSolve; try set_solver +.
    iModIntro.
    iIntros "(PCz & p_5 & acc & R1z) _".
    (* hvc_I *)
    iDestruct (lb_update_alloc V2 {[prog1page]} with "LB_auth") as ">[LB_auth LB2]";first done.
    rewrite wp_sswp.
    iApply ((run (((((prog1page ^+ 1) ^+ 1) ^+ 1) ^+ 1) ^+ 1)%f V2 (R := True%I)
                (R' := PC @@ V0 ->r ((((((prog1page ^+ 1) ^+ 1) ^+ 1) ^+ 1) ^+ 1) ^+ 1)%f
                                 ∗(((((prog1page ^+ 1) ^+ 1) ^+ 1) ^+ 1) ^+ 1)%f ->a hvc_I ∗ V0 -@A> [{[prog1page]}] )
                ) with "[PCz p_6 acc R0z R1z prop0 prop2 acc2 LB2 hp R2]"); try rewrite HIn //;iFrameAutoSolve.
    { set_solver +. }
    { set_solver +. }
    { apply decode_encode_hvc_func. }
    { apply decode_encode_vmid. }
    { iSplitL "prop2".
      iFrame.
      iSplitL "prop0".
      done.
      iSplitR "";last done.
      iNext.
      iIntros "((PC & addr & acc & R0 & R1) & _ & prop)".
      iFrame "PC addr R0 R1 acc".
      iExists {[prog1page]}, ∅, hs_all.
      iFrame.
      iSplitL "";first done.
      iSplitL "".
      { rewrite disjoint_singleton_l not_elem_of_singleton //. }
      iSplitL "".
      { iPureIntro.
        rewrite /inv_trans_hpool_consistent'. split.
        {
          rewrite /inv_trans_hpool_disj dom_empty_L.
          apply disjoint_empty_l.
        }
        {
          rewrite /inv_finite_handles dom_empty_L union_empty_l_L //.
        }
      }
      iSplitL "".
      {
        rewrite /transferred_tran_entries.
        by iApply big_sepM_empty.
      }
      iSplitL "".
      {
        rewrite /transferred_pgt_entries.
        by iApply big_sepM_empty.
      }
      iSplitL "".
      {
        rewrite /accessible_trans.
        rewrite map_filter_empty.
        rewrite /ps_trans map_fold_empty.
        rewrite /memory_pages.
        iExists ∅.
        iSplitL "".
        iPureIntro.
        rewrite set_of_addr_empty.
        set_solver +.
        by iApply big_sepM_empty.
      }
      iDestruct "R2" as "(rx_s & rx & rx_mem)".
      iFrame.
    }
    iNext.
    iIntros "((PC & p_6 & acc) & Hprop0) Hholds0".
    iDestruct (VMProp_holds_agree with "[Hholds0 Hprop0]") as "[P' Hprop0]".
    iSplitR "Hprop0".
    2: { iFrame "Hprop0". }
    iSimpl.
    iSimpl in "Hholds0".
    done.
    (* getting back resources *)
    iDestruct "P'" as ">[(% & % & % & ? & ? & ? & ? & ? & ? & ? & R0z & R1z)|False]".
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
        ∗ (VMProp V1 ((R0 @@ V0 ->r run_I ∗ R1 @@ V0 ->r encode_vmid V1 )
        ∗ VMProp V0 ((R0 @@ V0 ->r yield_I ∗ R1 @@ V0 ->r encode_vmid V1 ) ∗ VMProp V1 False%I (1/2)%Qp) (1/2)%Qp)%I (1/2)%Qp)
        ∗ (PC @@ V1 ->r (of_pid prog2page))
        ∗ (∃ r0, R0 @@ V1 ->r r0)
        ∗ (V1 -@A> [{[prog2page]}] )
        ⊢ VMProp_holds V1 (1/2)%Qp -∗ (WP ExecI @ V1
              {{ (λ m, False)}}%I).
  Proof.
    iIntros (HIn ) "((p_1 & p_2 & _) & prop1 & PC1 & [%r0 R01] & acc)".
    iIntros "Hholds".
    iDestruct (VMProp_holds_agree V1 with "[Hholds prop1]") as "[P prop1]".
    iFrame.
    pose proof (seq_in_page_forall2 _ _ _ HIn) as Hforall.
    clear HIn; rename Hforall into HIn.
    assert (1 = V1) as HV1.
    by simpl.
    (* mov_word_I R0 yield_I *)    
    rewrite wp_sswp.
    iDestruct "P" as "[(R0z & R1z) prop0]".
    iApply ((mov.mov_word (of_pid prog2page) yield_I R0) with "[p_1 PC1 acc R01]");try rewrite HIn //;iFrameAutoSolve;try set_solver.
    iModIntro.
    iIntros "(PC1 & p_1 & acc & R01)".
    iSimpl.
    rewrite HV1.
    iIntros "_".
    (* hvc_I *)
    rewrite wp_sswp.
    iApply ((yield ((of_pid prog2page) ^+ 1)%f (P' := False%I) (R := True%I)
                   (R' := (PC @@ V1 ->r ((prog2page ^+ 1) ^+ 1)%f ∗ (prog2page ^+ 1)%f ->a hvc_I ∗ R0 @@ V1 ->r yield_I)%I))
         with "[PC1 p_2 acc R01 R0z R1z prop0 prop1]"); try rewrite HIn //;iFrameAutoSolve.
    { set_solver +. }
    { set_solver +. }
    { apply decode_encode_hvc_func. }
    { iSplitL "prop0".
      iFrame.
      iSplitL "prop1".
      iFrame.
      iSplitL "";last done.
      iNext.
      iIntros "((? & ? & ? & ? & ? & ?) & _ & ?)".
      iFrame.
    }
    iModIntro.
    iIntros "[? prop1] Hholds".
    simpl.
    iDestruct (VMProp_holds_agree V1 with "[prop1 Hholds]") as "[P prop1]".
    iFrame.
    iMod "P".
    by iExFalso.
  Qed.

End proof.
