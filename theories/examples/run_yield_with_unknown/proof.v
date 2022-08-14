From iris.proofmode Require Import tactics.
From machine_program_logic.program_logic Require Import weakestpre.
From HypVeri.algebra Require Import base mem.
From HypVeri.rules Require Import rules_base mov halt run yield.
From HypVeri.examples Require Import instr.
From HypVeri.logrel Require Import logrel logrel_extra logrel_prim_extra.
From HypVeri Require Import proofmode machine_extra.
Import uPred.
Require Import Setoid.

Program Instance rywu_vmconfig : HypervisorConstants :=
    {vm_count := 3;
     vm_count_pos:= _;
     valid_handles := {[W0]}}.

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

  Definition rywu_slice_trans trans i j : iProp Σ := slice_transfer_all trans i j.

  Definition rywu_slice_rxs i os (j: VMID) : iProp Σ :=
    (match os with
    | None => True
    | _ => slice_rx_state i os
    end)%I.

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
      VMProp V2 ((vmprop_unknown V2 rywu_slice_trans rywu_slice_rxs ∅ )) (1/2)%Qp ∗
      trans.fresh_handles 1 valid_handles ∗
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
    intros ???.
    iIntros (HnIn_p HIn) "((p_1 & p_2 & p_3 & p_4 & p_5 & p_6 & p_7 & _) & acc & tx & PCz & (%r0 & R0z) & (%r1 & R1z) & (%r2 & R2z)
                            & prop0 & prop1 & prop2 & hp & R0 & R1 & R2)".
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
    rewrite wp_sswp.
    iApply ((run (((p_pg0 ^+ 1) ^+ 1))%f V2  True
                (vmprop_zero V2 rywu_slice_trans rywu_slice_rxs ∅ {[V0 := None; V1 := None; V2 := None]})
                (R' := PC @@ V0 ->r (((p_pg0 ^+ 1) ^+ 1) ^+ 1)%f
                                 ∗((p_pg0 ^+ 1) ^+ 1)%f ->a hvc_I ∗ V0 -@A> {[p_pg0]} ∗ TX@ V0 := p_tx0)
                ) with "[PCz p_3 acc tx R0z R1z R2z prop0 prop2 hp R0 R1 R2]"); try rewrite HIn //; iFrameAutoSolve.
    { set_solver +. }
    { set_solver +. }
    { set_solver +. }
    { apply decode_encode_hvc_func. }
    { apply decode_encode_vmid. }
    { iSplitL "prop2". iFrame.
      iSplitL "prop0". done.
      iSplitR ""; last done.
      iNext. iIntros "((PC & addr & acc & tx & R0' & R1') & _ & prop0)".
      setoid_rewrite vmprop_unknown_eq.
      iFrame "PC addr acc tx".
      iExists ∅, {[V0 := None; V1 := None; V2 := None]}.
      iSplitR. done.
      iSplitL "hp".
      {
        iExists valid_handles.
        iSplitL "". iPureIntro. rewrite dom_empty_L union_empty_r_L //.
        iFrame.
        rewrite big_sepM_empty //.
      }
      iSplitL "".
      {
        rewrite /rywu_slice_trans /=.
        rewrite transferred_only_equiv.
        rewrite /transaction_pagetable_entries_transferred.
        rewrite /retrievable_transaction_transferred.
        iSplitL. iApply (big_sepFM_empty).
        iSplitL. iSplitL;iApply (big_sepFM_empty).
        rewrite /transferred_memory_pages.
        rewrite map_filter_empty pages_in_trans_empty.
        iExists ∅.
        iApply memory_pages_empty.
        intros. done.
        rewrite /trans_neq. apply map_Forall_empty.
        rewrite /trans_ps_disj /inv_trans_ps_disj'. rewrite /lift_option_gmap fmap_empty. apply map_Forall_empty.
      }
      iSplitL "R0'".
      iExists _. iSplit. iExact "R0'". iPureIntro. apply decode_encode_hvc_func.
      iSplitL "R1'".
      iExists _. iSplit. iExact "R1'". iPureIntro. apply decode_encode_vmid.
      iSplitL "R2z".
      iExists _. iExact "R2z".
      iSplitL "R2".
      {
        iIntros (??).
        simplify_map_eq /=.
        iDestruct "R2" as "($ & R2 & R3)".
        iExists p_rx2. iFrame "R3". iDestruct "R2" as "[$ ?]".
      }
      iSplitL "R0 R1".
      {
        rewrite /rx_states_global.
        assert (delete V2 {[V0 := None; V1 := None; V2 := None]} = {[V0 := None; V1 := None]}) as ->.
        {
          simpl.
          assert ({[V0 := None; V1 := None; V2 := None]} = {[V2 := None; V0 := None; V1 := None]}) as ->.
          {
            rewrite (map_insert_swap _ V1 V2) //.
            rewrite (map_insert_swap _ V0 V2) //.
          }
          rewrite delete_insert //.
        }
        rewrite big_sepM_insert //.
        rewrite big_sepM_singleton.
        rewrite /rx_state_match.
        iSplitL "R0".
        iDestruct "R0" as "($ & R1 & R2)".
        iExists p_rx0. iFrame "R2". iDestruct "R1" as "[$ ?]".
        iDestruct "R1" as "($ & R1 & R2)".
        iExists p_rx1. iFrame "R2". iDestruct "R1" as "[$ ?]".
      }
      iSplitR.
      {
        iPureIntro.
        rewrite /base_extra.is_total_gmap.
        intro. pose proof (in_list_of_vmids k).
        rewrite /list_of_vmids /= in H.
        clear -H.
        repeat destruct H as [<- | H];
          exists None;
          simplify_map_eq;auto. done.
      }
      iExact "prop0".
      }
    iNext.
    iIntros "((PCz & p_3 & acc & tx) & Hprop0) Hholds0".
    iDestruct (VMProp_holds_agree with "[Hholds0 Hprop0]") as "[P prop0]".
    iSplitR "Hprop0".
    2: { iFrame "Hprop0". }
    iSimpl. iSimpl in "Hholds0". done.
    (* getting back resources *)
    iEval(rewrite /vmprop_zero /vmprop_zero_pre) in "P".
    iEval (rewrite later_exist) in "P". iDestruct "P" as (trans' rs') "P".
    iEval (rewrite 8!later_sep) in "P".
    (* rewrite /rywu_slice_trans. *)
    iDestruct "P" as "(_ & _ & >trans_hpool_global & trans & >mem_rx_2 & >rx_2 &>returnreg & prop2)".
    (* mov_word_I R0 run *)
    rewrite wp_sswp.
    rewrite /return_reg_rx.
    iDestruct "returnreg" as "[returnreg | returnreg]".
    {
      iDestruct "returnreg" as "(R0z & rx & R1z & R2z)".
      iDestruct "R0z" as "[R0z | R0z]".
      {
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
        iApply ((run ((((((of_pid p_pg0) ^+ 1) ^+ 1)^+ 1) ^+ 1) ^+ 1)%f V1 True ((R0 @@ V0 ->r yield_I ∗ R1 @@ V0 ->r encode_vmid V1) ∗ VMProp V1 False (1 / 2)))
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
        iApply ((run ((((((of_pid p_pg0) ^+ 1) ^+ 1)^+ 1) ^+ 1) ^+ 1)%f V1 True ((R0 @@ V0 ->r yield_I ∗ R1 @@ V0 ->r encode_vmid V1) ∗ VMProp V1 False (1 / 2)))
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
      iDestruct "returnreg" as "[R0z [% [% [rx (? & ? & [% [R1z _ ]] & R2z)]]]]".
      iApply ((mov_word ((((of_pid p_pg0) ^+ 1) ^+ 1)^+ 1)%f run_I R0) with "[p_4 PCz acc tx R0z]");try rewrite HIn //; iFrameAutoSolve; try set_solver +.
      iModIntro.
      iIntros "(PCz & p_4 & acc & tx & R0z) _".
      (* mov_word_I R1 V1 *)
      rewrite wp_sswp.
      (* iDestruct "R1z" as "(%j & %p_rx & %l & ? & ? & ? & R1z & R2z & ?)". *)
      (* iDestruct "R1z" as "(%r3 & R1z & ?)". *)
      iApply ((mov_word (((((of_pid p_pg0) ^+ 1) ^+ 1)^+ 1) ^+ 1)%f (encode_vmid V1) R1) with "[p_5 PCz acc tx R1z]"); try rewrite HIn //; iFrameAutoSolve; try set_solver +.
      iModIntro.
      iIntros "(PCz & p_5 & acc & tx & R1z) _".
      (* hvc_I *)
      rewrite wp_sswp.
      iApply ((run ((((((of_pid p_pg0) ^+ 1) ^+ 1)^+ 1) ^+ 1) ^+ 1)%f V1 True ((R0 @@ V0 ->r yield_I ∗ R1 @@ V0 ->r encode_vmid V1) ∗ VMProp V1 False (1 / 2)))
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
