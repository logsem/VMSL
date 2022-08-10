From machine_program_logic.program_logic Require Import weakestpre.
From HypVeri.algebra Require Import base base_extra mem pagetable trans.
From HypVeri.rules Require Import rules_base mov halt run yield ldr str br.
From HypVeri.examples Require Import instr utils.
From HypVeri.logrel Require Import logrel logrel_extra fundamental logrel_prim logrel_prim_extra fundamental_prim.
From HypVeri Require Import proofmode machine_extra.
Require Import Setoid.

Program Instance up_vmconfig : HypervisorConstants :=
    {vm_count := 4;
     vm_count_pos := _;
     valid_handles := {[W0]}}.

Section up_proof.

Program Definition V1 : VMID := (@nat_to_fin 1 _ _).
Program Definition V2 : VMID := (@nat_to_fin 2 _ _).
Program Definition V3 : VMID := (@nat_to_fin 3 _ _).

Program Definition fortytwo : Imm := I (finz.FinZ 42 _ _) _.
(* Program Definition one : Imm := I (finz.FinZ 1 _ _) _. *)
(* Program Definition two : Imm := I (finz.FinZ 2 _ _) _. *)
(* Program Definition four : Imm := I (finz.FinZ 4 _ _) _. *)
(* Program Definition mem_descriptor_length : Imm := I (finz.FinZ 5 _ _) _. *)

  Context `{hypparams: !HypervisorParameters}.
  Context (pshare:PID) (pshare_i: Imm) (Hpshare_eq: of_pid pshare = pshare_i).
  Context (pprog0 pprog1 pprog2 pprog3:PID) (pprog1_i: Imm) (Hpprog1_eq: of_pid pprog1 = pprog1_i).
  Context (ptx1 ptx3 prx1 prx3 :PID).
  Context (ptx0 ptx2 prx0 prx2 :PID).
  Context (Hps_nd: NoDup [pprog0;pprog1;pprog2;pprog3;pshare;ptx0;ptx1;ptx2;ptx3;prx0;prx1;prx2;prx3]).

  Definition up_program1 (jump : Imm) : list Word :=
    [
      (* Store 42 to shared page *)
      mov_word_I R1 fortytwo;
      mov_word_I R2 pshare_i;
      str_I R1 R2;
      (* addr to jump *)
      mov_word_I R2 jump;
      mov_word_I R0 yield_I;
      hvc_I;
      br_I R2
    ].

  Definition up_program3 : list Word :=
    [
      (* Store 42 to shared page *)
      mov_word_I R2 pshare_i;
      ldr_I R1 R2;
      halt_I
    ].

  Class exclG Σ :=
    excl_G :> inG Σ (exclR unitO).
  Definition exclΣ : gFunctors :=
    #[ GFunctor (exclR unitO)].

  Instance subG_issuedΣ {Σ} : subG exclΣ Σ → exclG Σ.
  Proof. solve_inG. Qed.


  Context `{!gen_VMG Σ, !exclG Σ} (N : namespace).

  Definition EXCL γ : iProp Σ := (own γ (Excl ()))%I.
  Lemma excl_exclusive (γ : gname) : EXCL γ  -∗ EXCL γ  -∗ False.
  Proof.
    iDestruct 1 as  "H1". iDestruct 1 as  "H2".
    iDestruct (own_valid_2 with "H1 H2") as %[].
  Qed.


  (* don't transfer anything if i,j = 1,3 or 3,1 *)
  Definition up_slice_trans trans i j : iProp Σ :=
    match (bool_decide (i = V1)), (bool_decide (j = V3)) with
    | true, true => True
    | _, _ => match (bool_decide (i = V3)), (bool_decide (j = V1)) with
           | true, true => True
           | _, _ => slice_transfer_all trans i j
           end
    end.

  Definition up_slice_rxs i os j : iProp Σ :=
    (match os with
    | None => True
    | Some (_, k) => if (bool_decide (k=V0)) then
                       (if (bool_decide (j = V0)) then
                          slice_rx_state i os
                        else if (bool_decide (i = j)) then
                               slice_rx_state i os
                             else True)
                     else slice_rx_state i os
    end)%I.

  Instance up_slice_trans_wf : SliceTransWf up_slice_trans.
  Proof.
    rewrite /up_slice_trans /=.
    split.
    intros.
    case_bool_decide;
    case_bool_decide;auto.
    subst i. simpl. by apply slice_transfer_all_wf.
    case_bool_decide;auto.
    subst i. simpl. by apply slice_transfer_all_wf.
    by apply slice_transfer_all_wf.
  Qed.

  Instance up_slice_rxs_wf : SliceRxsWf up_slice_rxs.
  Proof.
    rewrite /up_slice_rxs /=.
    split. done.
    intros.
    destruct os;auto.
    destruct p. intros.
    case_bool_decide;auto.
    case_bool_decide;auto.
    done. done.
  Qed.


  Notation VMProp1 := (vmprop_unknown V1 up_slice_trans up_slice_rxs {[W0 := (V1, V3, {[pshare]}, Sharing, true)]}) (only parsing).
  Notation VMProp3 := (vmprop_unknown V3 up_slice_trans up_slice_rxs {[W0 := (V1, V3, {[pshare]}, Sharing, true)]}) (only parsing).


  Class SliceWfPrim Φ_t Φ_r :=
    {
     trans_wf_prim : ∀ i j trans, (i = V0 ∨ j = V0) -> Φ_t trans i j ⊣⊢ slice_transfer_all trans i j;
     rxs_wf_prim_diag : ∀ i os, (match os with
                 | None => True
                 | Some (_,j) => j = V0 -> Φ_r i os i ⊣⊢ slice_rx_state i os
                end);
     rxs_wf_prim_eq: ∀ i os, match os with
               | None => True
               | Some (_ ,k) => k = V0
               end -> Φ_r i os i ⊣⊢ Φ_r i os V0;
     rxs_wf_prim_none : ∀ i j os, (match os with
                 | None => True
                 | Some (_,j) => j = V0
                end) -> j ≠ i -> j ≠ V0 -> Φ_r i os j ⊣⊢ True;
     rxs_wf_prim_zero: ∀ os, (match os with
              | None => True
              | _ => Φ_r V0 os V0 ⊣⊢ slice_rx_state V0 os
              end);
    }.

  Global Instance up_slice_wf: SliceWfPrim up_slice_trans up_slice_rxs.
  Proof.
    split;rewrite /up_slice_trans /up_slice_rxs.
    {
      intros ? ? ? [|].
      case_bool_decide. subst i. done.
      case_bool_decide. subst i. done.
      done.
      case_bool_decide.
      case_bool_decide. subst j. done.
      case_bool_decide. subst j. done.
      done.
      case_bool_decide;auto.
      case_bool_decide;auto.
      subst j. done.
    }
    {
      intros.
      destruct os. destruct p. intro.
      case_bool_decide;auto.
      case_bool_decide;auto.
      case_bool_decide;auto.
      done. done.
    }
    {
      intros.
      destruct os;auto. destruct p.
      case_bool_decide;auto.
      case_bool_decide;auto.
      case_bool_decide;auto.
      done.
    }
    {
      intros.
      destruct os;auto. destruct p.
      case_bool_decide;auto.
      case_bool_decide;auto. done.
      case_bool_decide;auto. done.
      done.
    }
    {
      intros.
      destruct os;auto. destruct p.
      case_bool_decide;auto.
    }
  Qed.

  Definition inv_pshare γ1 γ3 pshare : iProp Σ:=
   inv (N .@ "shared")
     ((EXCL γ3 ∗ ∃ w, pshare ->a w) ∨ EXCL γ1 ∗ pshare ->a (of_imm fortytwo)).


  Lemma up_machine1 jump_i γ1 γ3 :
    let program1 := up_program1 jump_i in
    of_imm (jump_i) = (pprog1 ^+ 4)%f ->
    seq_in_page (of_pid pprog1) (length program1) pprog1->
    inv_pshare γ1 γ3 pshare ∗
    EXCL γ1 ∗
    (program (program1) (of_pid pprog1)) ∗
    V1 -@A> {[pprog1;pshare;ptx1;prx1]} ∗
    (* TX page *)
    TX@ V1 := (tpa ptx1) ∗
    RX@ V1 := (tpa prx1) ∗
    PC @@ V1 ->r (of_pid pprog1) ∗
    (* Work registers *)
    (∃ r0, R0 @@ V1 ->r r0) ∗
    (∃ r1, R1 @@ V1 ->r r1) ∗
    (∃ r2, R2 @@ V1 ->r r2) ∗
    VMProp V1 (VMProp1) (1/2)%Qp
    ⊢ VMProp_holds V1 (1/2)%Qp -∗ WP ExecI @ V1
          {{ (λ m, False)}}%I.
  Proof.
    intro. rewrite /program1.
    iIntros (Hjump HIn) "(#inv & excl1 & (p_1 & p_2 & p_3 & p_4 & p_5 & p_6 & p7 & _) & acc & tx & rx & pc & (%r0 & r0) & (%r1 & r1) & (%r2 & r2)
                   & vmprop) holds".
    (* iDestruct (VMProp_holds_agree V1 with "[holds vmprop]") as "[P prop1]". *)
    (* iFrame. *)
    assert (pprog1 ≠ ptx1) as Hneqtx.
    {
      intro.
      feed pose proof (NoDup_lookup _ 1 6 ptx1 Hps_nd).
      simplify_eq /=. done.
      simplify_eq /=. done.
      lia.
    }
    rewrite to_pid_aligned_eq.
    pose proof (seq_in_page_forall2 _ _ _ HIn) as Hforall.
    clear HIn; rename Hforall into HIn.
    rewrite wp_sswp.
    iApply ((mov_word pprog1) with "[p_1 pc acc tx r1]"); rewrite ?to_pid_aligned_eq; iFrameAutoSolve.
    set_solver.
    iNext. iIntros "(pc & _ & acc & tx & r1) _".
    rewrite wp_sswp.
    iApply ((mov_word (pprog1 ^+ 1)%f) with "[p_2 pc acc tx r2]"); rewrite ?to_pid_aligned_eq; iFrameAutoSolve.
    set_solver.
    rewrite HIn. done.
    set_solver +.
    iNext. iIntros "(pc & _ & acc & tx & r2) _".
    rewrite wp_sswp.
    iApply (sswp_fupd_around _ ⊤ (⊤ ∖ ↑(N .@ "shared")) ⊤).
    iInv (N .@ "shared") as ">Inv" "HIClose".
    iDestruct "Inv" as "[[excl3 (%w & share)] | [excl1' _]]".
    2:{
      iExFalso.
      iApply (excl_exclusive with "excl1 excl1'").
    }
    iApply ((str ((pprog1 ^+ 1) ^+ 1)%f) with "[p_3 pc acc tx rx r1 r2 share]");
      rewrite -?Hpshare_eq ?to_pid_aligned_eq; iFrameAutoSolve.
    rewrite (HIn ((pprog1 ^+ 1) ^+ 1)%f).
    rewrite to_pid_aligned_eq.
    set_solver +.
    set_solver +.
    rewrite HIn. done.
    set_solver +.
    {
      rewrite to_pid_aligned_eq.
      intro.
      feed pose proof (NoDup_lookup _ 4 10 prx1 Hps_nd).
      simplify_eq /=. done.
      simplify_eq /=. done.
      lia.
    }
    iModIntro. iNext. iIntros "(pc & _ & r2 & share & r1 & acc & tx & rx)".
    iDestruct ("HIClose" with "[excl1 share]") as "HIClose".
    iNext;iRight;iFrame.
    iMod "HIClose" as "_". iModIntro. iIntros "_".
    rewrite wp_sswp.
    iApply ((mov_word (((pprog1 ^+ 1) ^+ 1) ^+ 1)%f) with "[p_4 pc acc tx r2]"); rewrite ?to_pid_aligned_eq; iFrameAutoSolve.
    rewrite HIn. set_solver +.
    set_solver +.
    rewrite HIn //. set_solver +.
    iNext. iIntros "(pc & _ & acc & tx & r2) _".
    iAssert (∃trans, VMProp V1 (vmprop_unknown V1 up_slice_trans up_slice_rxs trans) (1 / 2))%I with "[vmprop]" as "vmprop".
    {
      iExists _. iExact "vmprop".
    }
    iLöb as "L" forall (r0) "r0".
    iApply wp_sswp.
    iApply (mov_word ((((pprog1 ^+ 1) ^+ 1) ^+ 1) ^+ 1)%f with "[p_5 pc acc tx r0]"); rewrite ?to_pid_aligned_eq; iFrameAutoSolve.
    rewrite HIn. set_solver +.
    set_solver +.
    rewrite HIn //. set_solver +.
    iNext. iIntros "(pc & p5 & acc & tx & r0) _".
    iApply wp_sswp.
    iDestruct "vmprop" as "[% vmprop]".
    iDestruct (VMProp_holds_agree with "[holds vmprop]") as "[P prop1]".
    iSplitR "vmprop".
    iDestruct "holds" as "[% [? vmprop]]". iExists _. iSplitR "vmprop".
    2: iExact "vmprop". done.
    iExact "vmprop".
    iDestruct (vmprop_unknown_eq with "P") as "P".
    rewrite bi.later_exist. iDestruct "P" as "[% P]".
    rewrite bi.later_exist. iDestruct "P" as "[% P]".
    rewrite 9!bi.later_sep.
    iDestruct "P" as "(>P1 & >P2 & P3 & >[% [r0z _]] & >[% [r1z _]] & >P6 & P7 & >P8 & >%P9 & prop0)".
    pose proof (P9 V1). destruct H.
    iApply (yield (((((pprog1 ^+ 1) ^+ 1) ^+ 1) ^+ 1) ^+1)%f (True) (vmprop_unknown V1 up_slice_trans up_slice_rxs a)
             with "[p_6 pc acc tx r0 prop1 r0z r1z prop0 P1 P2 P3 P6 P7 P8]"); rewrite ?to_pid_aligned_eq; iFrameAutoSolve.
    rewrite HIn. set_solver +.
    set_solver +.
    rewrite HIn //. set_solver +.
    apply decode_encode_hvc_func.
    iSplitL "prop0". iExact "prop0".
    iSplitL "prop1". iExact "prop1".
    iSplitL. iNext. iIntros "[(pc & p_6 & acc & tx & r0 & r0z & r1z) [_ prop1]]".
    iSplitL "P1 P2 P3 P6 P7 P8 prop1 r0z r1z".
    rewrite /vmprop_zero /vmprop_zero_pre.
    iExists a, x.
    iSplit. iPureIntro. apply only_except_disjoint.
    rewrite only_except_union.
    iSplit. iPureIntro. intros. done.
    iFrame "P2 P3".
    iDestruct ("P7" $! x H) as "[$ P7]".
    iSplitL "P7".
    destruct x. destruct p. destruct (decide (v = V0)).
    rewrite rxs_wf_prim_eq //.
    pose proof (slice_rxs_sym up_slice_rxs V1 V0 (i:= V1) (os:=(Some (f, v)))).
    simpl in H0. pose proof n. apply H0 in n. case_bool_decide;auto.
    pose proof (slice_rxs_empty up_slice_rxs V1 V0).
    rewrite H0 //.
    iSplitR "prop1";[|done].
    rewrite /return_reg_rx.
    iLeft. iSplitL "r0z". iLeft. done.
    iFrame "P8 P6 r1z".
    iCombine "pc p_6 acc tx r0" as "R'". iExact "R'".
    done.
    iNext. iIntros "[(pc & p6 & acc & tx & r0) prop1] holds".
    iApply wp_sswp.
    iApply (br ((((((pprog1 ^+ 1) ^+ 1) ^+ 1) ^+ 1) ^+ 1) ^+ 1)%f with "[p7 pc acc tx r2]"); rewrite ?to_pid_aligned_eq; iFrameAutoSolve.
    rewrite HIn. set_solver +.
    set_solver +.
    rewrite HIn //. set_solver +.
    iNext. iIntros "(pc & [p7 r2] & acc & tx) _".
    iApply ("L" with "p5 p6 p7 holds excl3 r1 rx [pc] acc tx r2 [prop1] r0").
    assert (((((pprog1 ^+ 1) ^+ 1) ^+ 1) ^+ 1)%f = jump_i) as ->.
    solve_finz + Hjump.
    done.
    iExists _. iExact "prop1".
   Qed.


  Lemma up_machine3 γ1 γ3 :
    let program3 := up_program3 in
    (* Addresses-values connection *)
    seq_in_page (of_pid pprog3) (length program3) pprog3 ->
    inv_pshare γ1 γ3 pshare ∗
    EXCL γ3 ∗
    (* Mem for program *)
    (program (program3) (of_pid pprog3)) ∗
    V3 -@A> {[pprog3;pshare;ptx3;prx3]} ∗
    TX@ V3 := (tpa ptx3) ∗
    RX@ V3 := (tpa prx3) ∗
    (* Program counter *)
    PC @@ V3 ->r (of_pid pprog3) ∗
    (* Work registers *)
    (∃ r0, R0 @@ V3 ->r r0) ∗
    (∃ r1, R1 @@ V3 ->r r1) ∗
    (∃ r2, R2 @@ V3 ->r r2) ∗
    VMProp V3 (VMProp3) (1/2)%Qp
    ⊢ VMProp_holds V3 (1/2)%Qp -∗ WP ExecI @ V3
           {{ (λ m, ⌜m = HaltI⌝ ∗ R1 @@ V3 ->r fortytwo)}}%I.
  Proof.
    intro. rewrite /program3.
    iIntros (HIn) "(#inv & excl3 & (p_1 & p_2 & p_3 & _) & acc & tx & rx & pc & (%r0 & r0) & (%r1 & r1) & (%r2 & r2)
                   & vmprop) holds".
    assert (pprog3 ≠ ptx3) as Hneqtx.
    {
      intro.
      feed pose proof (NoDup_lookup _ 3 8 ptx3 Hps_nd).
      simplify_eq /=. done.
      simplify_eq /=. done.
      lia.
    }
    rewrite to_pid_aligned_eq.
    pose proof (seq_in_page_forall2 _ _ _ HIn) as Hforall.
    clear HIn; rename Hforall into HIn.
    rewrite wp_sswp.
    iApply ((mov_word pprog3) with "[p_1 pc acc tx r2]"); rewrite ?to_pid_aligned_eq; iFrameAutoSolve.
    set_solver.
    iNext. iIntros "(pc & _ & acc & tx & r2) _".
    rewrite wp_sswp.
    iApply (sswp_fupd_around _ ⊤ (⊤ ∖ ↑(N .@ "shared")) ⊤).
    iInv (N .@ "shared") as ">Inv" "HIClose".
    iDestruct "Inv" as "[[excl3' _] | [excl1' share]]".
    {
      iExFalso.
      iApply (excl_exclusive with "excl3 excl3'").
    }
    iApply ((ldr (pprog3 ^+ 1)%f) with "[p_2 pc acc tx r1 r2 share]"); rewrite -?Hpshare_eq ?to_pid_aligned_eq; iFrameAutoSolve.
    rewrite (HIn (pprog3 ^+ 1)%f).
    rewrite to_pid_aligned_eq.
    set_solver +.
    set_solver +.
    {
      rewrite to_pid_aligned_eq.
      intro.
      feed pose proof (NoDup_lookup _ 4 8 ptx3 Hps_nd).
      simplify_eq /=. done.
      simplify_eq /=. done.
      lia.
    }
    rewrite HIn. done.
    set_solver +. iModIntro.
    iNext. iIntros "(pc & _ & r2 & share & r1 & acc & tx)".
    iDestruct ("HIClose" with "[excl1' share]") as ">_".
    iNext;iRight. iFrame.
    iModIntro. iIntros "_".
    rewrite wp_sswp.
    iApply ((halt ((pprog3 ^+ 1) ^+ 1)%f) with "[p_3 pc acc tx]"); rewrite ?to_pid_aligned_eq; iFrameAutoSolve.
    rewrite HIn. set_solver +.
    set_solver +.
    rewrite HIn //. set_solver +.
    iNext. iIntros "(pc & _ & acc & tx) _".
    iApply wp_terminated. done.
    simpl. iSplit;done.
  Qed.

  Definition up_interp_access2 := interp_access (V2 : leibnizO VMID) ptx2 prx2 {[pprog2; ptx2; prx2]}
                                    ({[W0 := (V1, V3, {[pshare]}, Sharing, true)]}).

  Lemma up_ftlr2: up_interp_access2 ⊢ interp_execute V2.
  Proof. iApply ftlr. Qed.

  Definition up_interp_access0 rxs := interp_access_prim up_slice_trans up_slice_rxs ptx0 prx0 {[pprog0; ptx0; prx0]}
                                    {[W0 := (V1, V3, {[pshare]}, Sharing, true)]} rxs.

  Lemma up_ftlr0 rxs : up_interp_access0 rxs ⊢ interp_execute_prim.
  Proof. iApply ftlr_p. Qed.

End up_proof.
