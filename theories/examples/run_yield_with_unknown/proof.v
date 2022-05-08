From machine_program_logic.program_logic Require Import weakestpre.
From HypVeri.algebra Require Import base lower_bound mem.
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

  Definition rywu_program0 : list Word :=
    [
    mov_word_I R0 run_I;
    mov_word_I R1 (encode_vmid V2);
    hvc_I;
    mov_word_I R0 run_I;
    mov_word_I R1 (encode_vmid V1);
    hvc_I;
    halt_I
    ].

  Definition rywu_program1 : list Word :=
    [
    mov_word_I R0 yield_I;
    hvc_I
    ].

  Context `{!gen_VMG Σ}.
  Notation VMProp_2 p_tx p_rx:= (vmprop_unknown V2 p_tx p_rx ∅) (only parsing).

  Lemma rywu_machine0 p_pg0 p_tx0 p_pg2 p_tx2 p_rx0 p_rx1 p_rx2 :
    let R2' := (RX_state@V2 := None ∗ mailbox.rx_page V2 p_rx2 ∗ ∃ mem_rx, memory_page p_rx2 mem_rx)%I in
    let R0' := (RX_state@V0 := None ∗ mailbox.rx_page V0 p_rx0 ∗ ∃ mem_rx, memory_page p_rx0 mem_rx)%I in
    let R1' := (RX_state@V1 := None ∗ mailbox.rx_page V1 p_rx1 ∗ ∃ mem_rx, memory_page p_rx1 mem_rx)%I
    in
      (p_pg0 ∉ ({[p_tx0; p_pg2; p_tx2; p_rx2]}:gset _)) ->
      seq_in_page (of_pid p_pg0) (length rywu_program0) p_pg0 ->
      (program (rywu_program0) (of_pid p_pg0)) ∗
      V0 -@A> {[p_pg0]} ∗
      TX@ V0 := p_tx0 ∗
      PC @@ V0 ->r (of_pid p_pg0) ∗
      (∃ r0, R0 @@ V0 ->r r0) ∗
      (∃ r1, R1 @@ V0 ->r r1) ∗
      (∃ r2, R2 @@ V0 ->r r2) ∗
      VMProp V0 True%I 1 ∗
      VMProp V1 ((R0 @@ V0 ->r run_I ∗ R1 @@ V0 ->r encode_vmid V1) ∗
                    VMProp V0 ((R0 @@ V0 ->r yield_I ∗ R1 @@ V0 ->r encode_vmid V1) ∗
                                 VMProp V1 False%I (1/2)%Qp) (1/2)%Qp)%I (1/2)%Qp ∗
      VMProp V2 (VMProp_2 p_tx2 p_rx2) (1/2)%Qp ∗
      V2 -@{1/2}A> {[p_pg2;p_tx2;p_rx2]} ∗
      LB_auth ∅ ∗
      trans.fresh_handles 1 hs_all ∗
      R0' ∗ R1' ∗ R2' 
      ⊢ WP ExecI @ V0
            {{ (λ m,
                 ⌜m = HaltI⌝ ∗
                 program rywu_program0 (of_pid p_pg0) ∗
                 V0 -@A> {[p_pg0]} ∗
                 TX@ V0 := p_tx0 ∗
                 PC @@ V0 ->r ((of_pid p_pg0) ^+ (length rywu_program0))%f ∗
                 R0 @@ V0 ->r yield_I ∗
                 R1 @@ V0 ->r encode_vmid V1
                 )}}%I.
  Proof.
    rewrite /vmprop_unknown.
    iIntros (HnIn_p HIn) "((p_1 & p_2 & p_3 & p_4 & p_5 & p_6 & p_7 & _) & acc & tx & PCz & (%r0 & R0z) & (%r1 & R1z) & (%r2 & R2z)
                            & prop0 & prop1 & prop2 & acc2 & LB_auth & hp & R0 & R1 &R2)".
    pose proof (seq_in_page_forall2 _ _ _ HIn) as Hforall.
    clear HIn; rename Hforall into HIn.
    assert (p_pg0 ≠ p_tx0) as Hnottx. set_solver + HnIn_p.
    (* mov_word_I R0 run_I *)
    rewrite wp_sswp.
    iApply ((mov_word (of_pid p_pg0) run_I R0) with "[p_1 PCz acc tx R0z]");try rewrite HIn //; iFrameAutoSolve; try set_solver +.
    iModIntro.
    iIntros "(PCz & p_1 & acc & tx & R0z) _".
    (* mov_word_I R1 V2 *)
    rewrite wp_sswp.
    iApply ((mov_word _ (encode_vmid V2) R1) with "[p_2 PCz acc tx R1z]"); try rewrite HIn //; iFrameAutoSolve; try set_solver +.
    iModIntro.
    iIntros "(PCz & p_2 & acc & tx & R1z) _".
    (* hvc_I *)
    iDestruct (lb_update_alloc V2 {[p_pg0]} with "LB_auth") as ">[LB_auth LB2]";first done.
    rewrite wp_sswp.
    iApply ((run (((p_pg0 ^+ 1) ^+ 1))%f V2 (R := True%I)
                (R' := PC @@ V0 ->r (((p_pg0 ^+ 1) ^+ 1) ^+ 1)%f
                                 ∗((p_pg0 ^+ 1) ^+ 1)%f ->a hvc_I ∗ V0 -@A> {[p_pg0]} ∗ TX@ V0 := p_tx0)
                ) with "[PCz p_3 acc tx R0z R1z R2z prop0 prop2 acc2 LB2 hp R0 R1 R2]"); try rewrite HIn //; iFrameAutoSolve.
    { set_solver +. }
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
      iIntros "((PC & addr & acc & tx & R0' & R1') & _ & prop0)".
      iFrame "PC addr R0' R1' acc tx".
      iExists {[p_pg0]}, {[p_pg2;p_tx2;p_rx2]} , ∅, None.
      iFrame "acc2 LB2".
      iSplitL "".
      iPureIntro. set_solver + HnIn_p.
      iSplitL "hp".
      {
        iExists hs_all.
        iSplitL "".
        iPureIntro.
        rewrite dom_empty_L union_empty_r_L //.
        iFrame.
        rewrite big_sepM_empty //.
      }
      iSplitL "".
      {
        rewrite /transaction_pagetable_entries_transferred.
        rewrite /base_extra.big_sepFM.
        rewrite map_filter_empty big_sepM_empty //.
      }
      iSplitL "".
      {
        rewrite /retrieval_entries_transferred.
        rewrite /base_extra.big_sepFM.
        rewrite map_filter_empty big_sepM_empty //.
      }
      iSplitL "".
      {
        rewrite /memory_transferred.
        rewrite /trans_memory_in_trans /pages_in_trans.
        rewrite map_filter_empty map_fold_empty.
        iExists ∅.
        iApply memory_pages_empty.
      }
      iDestruct "R2" as "(R1' & R2 & R3)".
      iFrame "R1' R2 R3 prop0".
      iSplitL "R2z"; first (iExists r2; done).
      iSplitL "R0 R1".
      {
        rewrite /rx_pages.
        rewrite /list_of_vmids.
        rewrite /vm_count /rywu_vmconfig.
        simpl.
        rewrite /V2.
        simpl.
        assert (({[2%fin]} ∪ ∅) = {[2%fin]}) as ->.
        { set_solver. }
        assert (({[0%fin]} ∪ {[1%fin; 2%fin]}) = ({[2%fin]} ∪ {[0%fin; 1%fin]})) as ->.
        { set_solver. }
        rewrite difference_union_distr_l_L.
        rewrite difference_diag_L.
        set p := {[0%fin; 1%fin]}.
        set q := {[2%fin]}.
        assert ((∅ ∪ p ∖ q) = p) as ->.
        { subst p q; set_solver. }
        subst p.
        clear q.
        rewrite big_sepS_union; last set_solver.
        iSplitL "R0".
        - rewrite big_sepS_singleton.
          iExists p_rx0.
          iDestruct "R0" as "(R0 & R1 & R2)".
          iFrame.
          rewrite /mailbox.rx_page.
          iDestruct "R1" as "(R1 & R2)".
          iFrame.
          iExists None.
          rewrite mailbox.rx_state_split.
          iDestruct "R0" as "(R0 & R0')".
          iFrame.
          done.
        - rewrite big_sepS_singleton.
          iExists p_rx1.
          iDestruct "R1" as "(R0 & R1 & R2)".
          iFrame.
          rewrite /mailbox.rx_page.
          iDestruct "R1" as "(R1 & R2)".
          iFrame.
          iExists None.
          rewrite mailbox.rx_state_split.
          iDestruct "R0" as "(R0 & R0')".
          iFrame.
          done.
      }
      iSplit.
      iIntros;done.
      iSplitL "".
      iIntros;done.
      iSplitL "".
      iIntros;done.
      {
        rewrite /trans_memory_in_trans /pages_in_trans.
        rewrite map_filter_empty map_fold_empty.
        iIntros "[? _]".
        rewrite difference_empty_L union_empty_r_L.
        done.
      }
    }
    iNext.
    iIntros "((PCz & p_3 & acc & tx) & Hprop0) Hholds0".
    iDestruct (VMProp_holds_agree with "[Hholds0 Hprop0]") as "[P' prop0]".
    iSplitR "Hprop0".
    2: { iFrame "Hprop0". }
    iSimpl.
    iSimpl in "Hholds0".
    done.
    (* getting back resources *)
    iDestruct "P'" as ">[(% & % & % & ? & ? & % & ? & ? & ? & ? & ? & ? & ? & returnreg)|False]".
    2: { (* V2 does not yield *)
    iExFalso.
    iExact "False".
    }
    (* mov_word_I R0 run *)
    rewrite wp_sswp.
    rewrite /return_reg_rx.
    iDestruct "returnreg" as "[returnreg | returnreg]".
    {
      iDestruct "returnreg" as "(R0z & R1z & R2z)".
      iDestruct "R0z" as "[R0z | R0z]".
      {
        iDestruct "R0z" as "(R0z & ?)".
        iApply ((mov_word ((((of_pid p_pg0) ^+ 1) ^+ 1)^+ 1)%f run_I R0) with "[p_4 PCz acc tx R0z]");try rewrite HIn //; iFrameAutoSolve; try set_solver +.
        iModIntro.
        iIntros "(PCz & p_4 & acc & tx & R0z) _".
        (* mov_word_I R1 V1 *)
        rewrite wp_sswp.
        iApply ((mov_word (((((of_pid p_pg0) ^+ 1) ^+ 1)^+ 1) ^+ 1)%f (encode_vmid V1) R1) with "[p_5 PCz acc tx R1z]"); try rewrite HIn //; iFrameAutoSolve; try set_solver +.
        iModIntro.
        iIntros "(PCz & p_5 & acc & tx & R1z) _".
        (* hvc_I *)
        rewrite wp_sswp.
        iApply ((run ((((((of_pid p_pg0) ^+ 1) ^+ 1)^+ 1) ^+ 1) ^+ 1)%f V1 (R := True))
                  with "[PCz p_6 acc tx R0z R1z prop0 prop1]"); try rewrite HIn //;iFrameAutoSolve.
        { set_solver +. }
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
            iIntros "((PCz & p_6 & acc & tx & R0z & R1z) & _ & prop)".
            iFrame "R0z R1z prop".
            iCombine "PCz p_6 acc tx" as "R'".
            iExact "R'".
        }
        iModIntro.
        iIntros "[(PC & p_6 & acc & tx) prop0] Hholds".
        iDestruct (VMProp_holds_agree with "[Hholds prop0]") as "[P' prop0]".
        simpl.
        iFrame "Hholds prop0".
        (* getting back resources *)
        iDestruct "P'" as "((>R0z & >R1z) & prop1)".
        (* halt_I *)
        rewrite wp_sswp.
        iApply ((halt (((((((of_pid p_pg0) ^+ 1) ^+ 1) ^+ 1) ^+ 1) ^+ 1) ^+ 1)%f) with "[PC p_7 acc tx]");
          try rewrite HIn //; iFrameAutoSolve;try set_solver +.
        iNext.
        iIntros "( PCz & p_7 & acc & tx)".
        iIntros "_".
        iApply wp_terminated'; eauto.
        assert ((((((((p_pg0 ^+ 1) ^+ 1) ^+ 1) ^+ 1) ^+ 1) ^+ 1) ^+ 1)%f = ((of_pid p_pg0) ^+ length rywu_program0)%f) as ->.
        {
          assert ( (Z.of_nat (length rywu_program0)) = 7%Z) as ->. by compute.
          solve_finz.
        }
        iFrame.
        iSplitR; first done.
        done.
      }
      {
        iDestruct "R0z" as "(R0z & ?)".
        iApply ((mov_word ((((of_pid p_pg0) ^+ 1) ^+ 1)^+ 1)%f run_I R0) with "[p_4 PCz acc tx R0z]");try rewrite HIn //; iFrameAutoSolve; try set_solver +.
        iModIntro.
        iIntros "(PCz & p_4 & acc & tx & R0z) _".
        (* mov_word_I R1 V1 *)
        rewrite wp_sswp.
        iApply ((mov_word (((((of_pid p_pg0) ^+ 1) ^+ 1)^+ 1) ^+ 1)%f (encode_vmid V1) R1) with "[p_5 PCz acc tx R1z]"); try rewrite HIn //; iFrameAutoSolve; try set_solver +.
        iModIntro.
        iIntros "(PCz & p_5 & acc & tx & R1z) _".
        (* hvc_I *)
        rewrite wp_sswp.
        iApply ((run ((((((of_pid p_pg0) ^+ 1) ^+ 1)^+ 1) ^+ 1) ^+ 1)%f V1 (R := True))
                  with "[PCz p_6 acc tx R0z R1z prop0 prop1]"); try rewrite HIn //;iFrameAutoSolve.
        { set_solver +. }
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
            iIntros "((PCz & p_6 & acc & tx & R0z & R1z) & _ & prop)".
            iFrame "R0z R1z prop".
            iCombine "PCz p_6 acc tx" as "R'".
            iExact "R'".
        }
        iModIntro.
        iIntros "[(PC & p_6 & acc & tx) prop0] Hholds".
        iDestruct (VMProp_holds_agree with "[Hholds prop0]") as "[P' prop0]".
        simpl.
        iFrame "Hholds prop0".
        (* getting back resources *)
        iDestruct "P'" as "((>R0z & >R1z) & prop1)".
        (* halt_I *)
        rewrite wp_sswp.
        iApply ((halt (((((((of_pid p_pg0) ^+ 1) ^+ 1) ^+ 1) ^+ 1) ^+ 1) ^+ 1)%f) with "[PC p_7 acc tx]");
          try rewrite HIn //; iFrameAutoSolve;try set_solver +.
        iNext.
        iIntros "( PCz & p_7 & acc & tx)".
        iIntros "_".
        iApply wp_terminated'; eauto.
        assert ((((((((p_pg0 ^+ 1) ^+ 1) ^+ 1) ^+ 1) ^+ 1) ^+ 1) ^+ 1)%f = ((of_pid p_pg0) ^+ length rywu_program0)%f) as ->.
        {
          assert ( (Z.of_nat (length rywu_program0)) = 7%Z) as ->. by compute.
          solve_finz.
        }
        iFrame.
        iSplitR; first done.
        done.
      }      
    }
    {
      iDestruct "returnreg" as "(R0z & ? & R1z)".
      iApply ((mov_word ((((of_pid p_pg0) ^+ 1) ^+ 1)^+ 1)%f run_I R0) with "[p_4 PCz acc tx R0z]");try rewrite HIn //; iFrameAutoSolve; try set_solver +.
      iModIntro.
      iIntros "(PCz & p_4 & acc & tx & R0z) _".
      (* mov_word_I R1 V1 *)
      rewrite wp_sswp.
      iDestruct "R1z" as "(%j & %p_rx & %l & ? & ? & ? & R1z & R2z & ?)".
      iDestruct "R1z" as "(%r3 & R1z & ?)".
      iApply ((mov_word (((((of_pid p_pg0) ^+ 1) ^+ 1)^+ 1) ^+ 1)%f (encode_vmid V1) R1) with "[p_5 PCz acc tx R1z]"); try rewrite HIn //; iFrameAutoSolve; try set_solver +.
      iModIntro.
      iIntros "(PCz & p_5 & acc & tx & R1z) _".
      (* hvc_I *)
      rewrite wp_sswp.
      iApply ((run ((((((of_pid p_pg0) ^+ 1) ^+ 1)^+ 1) ^+ 1) ^+ 1)%f V1 (R := True))
                with "[PCz p_6 acc tx R0z R1z prop0 prop1]"); try rewrite HIn //;iFrameAutoSolve.
      { set_solver +. }
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
          iIntros "((PCz & p_6 & acc & tx & R0z & R1z) & _ & prop)".
          iFrame "R0z R1z prop".
          iCombine "PCz p_6 acc tx" as "R'".
          iExact "R'".
      }
      iModIntro.
      iIntros "[(PC & p_6 & acc & tx) prop0] Hholds".
      iDestruct (VMProp_holds_agree with "[Hholds prop0]") as "[P' prop0]".
      simpl.
      iFrame "Hholds prop0".
      (* getting back resources *)
      iDestruct "P'" as "((>R0z & >R1z) & prop1)".
      (* halt_I *)
      rewrite wp_sswp.
      iApply ((halt (((((((of_pid p_pg0) ^+ 1) ^+ 1) ^+ 1) ^+ 1) ^+ 1) ^+ 1)%f) with "[PC p_7 acc tx]");
        try rewrite HIn //; iFrameAutoSolve;try set_solver +.
      iNext.
      iIntros "( PCz & p_7 & acc & tx)".
      iIntros "_".
      iApply wp_terminated'; eauto.
      assert ((((((((p_pg0 ^+ 1) ^+ 1) ^+ 1) ^+ 1) ^+ 1) ^+ 1) ^+ 1)%f = ((of_pid p_pg0) ^+ length rywu_program0)%f) as ->.
      {
        assert ( (Z.of_nat (length rywu_program0)) = 7%Z) as ->. by compute.
        solve_finz.
      }
      iFrame.
      iSplitR; first done.
      done.
    }
  Qed.

  Lemma rywu_machine1 p_pg1 p_tx1:
    p_tx1 ≠ p_pg1 ->
    seq_in_page (of_pid p_pg1) (length rywu_program1) p_pg1 ->
    (program rywu_program1 (of_pid p_pg1))
    ∗ VMProp V1 ((R0 @@ V0 ->r run_I ∗ R1 @@ V0 ->r encode_vmid V1 )
                 ∗ VMProp V0 ((R0 @@ V0 ->r yield_I ∗ R1 @@ V0 ->r encode_vmid V1 ) ∗ VMProp V1 False%I (1/2)%Qp) (1/2)%Qp)%I (1/2)%Qp
    ∗ PC @@ V1 ->r (of_pid p_pg1)
    ∗ (∃ r0, R0 @@ V1 ->r r0)
    ∗ V1 -@A> {[p_pg1]}
    ∗ TX@ V1 := p_tx1
    ⊢ VMProp_holds V1 (1/2)%Qp -∗
    (WP ExecI @ V1 {{ (λ m, False)}}).
  Proof.
    iIntros (Hnottx HIn) "((p_1 & p_2 & _) & prop1 & PC1 & [%r0 R01] & acc & tx)".
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
    iApply ((mov.mov_word (of_pid p_pg1) yield_I R0) with "[p_1 PC1 acc tx R01]");try rewrite HIn //;iFrameAutoSolve;try set_solver.
    iModIntro.
    iIntros "(PC1 & p_1 & acc & tx & R01)".
    iSimpl.
    rewrite HV1.
    iIntros "_".
    (* hvc_I *)
    rewrite wp_sswp.
    iApply ((yield ((of_pid p_pg1) ^+ 1)%f True False%I)
         with "[PC1 p_2 acc tx R01 R0z R1z prop0 prop1]"); try rewrite HIn //;iFrameAutoSolve.
    { set_solver +. }
    { set_solver +. }
    { set_solver +. }
    { apply decode_encode_hvc_func. }
    { iSplitL "prop0".
      iFrame.
      iSplitL "prop1".
      iFrame.
      iSplitL "";last done.
      iNext.
      iIntros "((H1 & H2 & H3 & H4 & H5 & H6) & _ & H7)".
      iFrame.
      iCombine "H1 H2 H3 H4 H5" as "R'".
      iExact "R'".
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
