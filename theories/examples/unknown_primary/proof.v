From machine_program_logic.program_logic Require Import weakestpre.
From HypVeri.algebra Require Import base base_extra mem pagetable trans.
From HypVeri.rules Require Import rules_base mov halt run yield ldr str br.
From HypVeri.examples Require Import instr utils.
From HypVeri.logrel Require Import logrel logrel_extra logrel_prim logrel_prim_extra.
From HypVeri Require Import proofmode machine_extra.
Require Import Setoid.

Section proof.
Program Instance rywu_vmconfig : HypervisorConstants :=
    {vm_count := 4;
     vm_count_pos := _;
     valid_handles := {[W0]}}.

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
  Context (Hps_nd: NoDup [pprog0;pprog1;pprog2;pprog3;pshare;ptx1;ptx3;prx1;prx3]).

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

  Instance up_slice_wf: SliceWfPrim up_slice_trans up_slice_rxs.
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
    (* let RX0 := (RX_state@V0 := None ∗ mailbox.rx_page V0 p_rx0 ∗ ∃ mem_rx, memory_page p_rx0 mem_rx)%I in *)
    (* let RX1 := (RX_state@V1 := None ∗ mailbox.rx_page V1 p_rx1 ∗ ∃ mem_rx, memory_page p_rx1 mem_rx)%I in *)
    (* let RX2 := (RX_state@V2 := None ∗ RX@V2:=p_rx2 ∗ ∃ mem_rx, memory_page p_rx2 mem_rx)%I in *)
    let program1 := up_program1 jump_i in
    of_imm (jump_i) = (pprog1 ^+ 4)%f ->
    (* (* Disjoint pages *) *)
    (* (of_pid p_tx0 = p_tx0imm) -> *)
    (* (of_pid p_rx1 = p_rx1imm) -> *)
    (* (of_pid p_pg0 = p_pg0imm) -> *)
    (* (p_pg0 ∉ ({[(tpa addr); p_tx0; p_pg2; p_tx2; p_rx2]}:gset _)) -> *)
    (* tpa addr ≠ p_rx0 -> *)
    (* tpa addr ≠ p_pg0 -> *)
    (* tpa addr ≠ p_tx0 -> *)
    (* p_tx0 ≠ p_rx0 -> *)
    (* Addresses-values connection *)
    seq_in_page (of_pid pprog1) (length program1) pprog1->
    inv_pshare γ1 γ3 pshare ∗
    EXCL γ1 ∗
    (* Mem for program *)
    (program (program1) (of_pid pprog1)) ∗
      (* Work mem *)
      (* (∃ w, addr ->a w) ∗ *)
      (* TX mem *)
      (* (∃ (v1 v2 v3 v4 v5 : Word), ([∗ list] a;w ∈ (finz.seq p_tx0 5);[v1; v2; v3; v4; v5], (a ->a w))) ∗ *)
      (* (∃ txmem, memory_page (tpa p_tx0) txmem) ∗ *)
      (* (* Pages for VM 0 *) *)
      (* ([∗ set] p ∈ {[tpa addr]}, p -@O> V0 ∗ p -@E> true) ∗ *)
      V1 -@A> {[pprog1;pshare;ptx1]} ∗
      (* TX page *)
      TX@ V1 := (tpa ptx1) ∗
      RX@ V1 := (tpa prx1) ∗
      (* Program counter *)
      PC @@ V1 ->r (of_pid pprog1) ∗
      (* Work registers *)
      (∃ r0, R0 @@ V1 ->r r0) ∗
      (∃ r1, R1 @@ V1 ->r r1) ∗
      (∃ r2, R2 @@ V1 ->r r2) ∗
      (* Protocol for VM 0 *)
      (* VMProp V0 True%I 1 ∗ *)
      (* Protocol for VM 1 *)
      (* VMProp V1 (R0 @@ V0 ->r run_I ∗ R1 @@ V0 ->r encode_vmid V1 ∗ addr ->a two  ∗ (∃ (wh : Addr), (∃ (β : mem), wh ->t (V0, V1, {[tpa addr]}, Sharing) ∗ *)
      (*                                                                               wh ->re false ∗ RX_state@V1 := Some (of_imm one, V0) ∗ RX@V1:=p_rx1 ∗ memory_page p_rx1 β ∗ ⌜β !! (of_imm p_rx1imm) = Some wh⌝) ∗ *)
      (*               VMProp V0 ((R0 @@ V0 ->r yield_I ∗ R1 @@ V0 ->r encode_vmid V1 ∗ addr ->a four ∗ wh ->t (V0, V1, {[tpa addr]}, Sharing) ∗ RX@V1:=p_rx1 ∗ RX_state@V1 := None ∗ (∃ mem_rx, memory_page p_rx1 mem_rx)) ∗ *)
      (*                            VMProp V1 False%I (1/2)%Qp) (1/2)%Qp))%I (1/2)%Qp ∗ *)
      (* Protocol for unknown vm *)
      VMProp V1 (VMProp1 (* p_tx2 p_rx2 *)) (1/2)%Qp 
      (* Pages for unknown VM *)
      (* V2 -@{1/2}A> {[p_pg2;p_tx2;p_rx2]} ∗ *)
      (* trans.fresh_handles 1 \ ∗ *)
      (* (* RX states *) *)
      (* RX0 ∗ RX1 ∗ RX2 *)
      ⊢ VMProp_holds V1 (1/2)%Qp -∗ WP ExecI @ V1
            {{ (λ m,
                 (* ⌜m = HaltI⌝ ∗ *)
                 (* (* program program0 (of_pid p_pg0) ∗ *) *)
                 (* addr ->a four ∗ *)
                 (* V0 -@A> (union (singleton (tpa addr)) (union (singleton p_pg0) (singleton (tpa p_tx0)))) ∗ *)
                 (* TX@ V0 := (tpa p_tx0) ∗ *)
                 (* PC @@ V0 ->r ((of_pid p_pg0) ^+ (length program0))%f *)
                 (* R0 @@ V0 ->r yield_I ∗ *)
                 (* R1 @@ V0 ->r encode_vmid V2 *)
                 False
                 )}}%I.
  Proof.
    intro. rewrite /program1.
    iIntros (Hjump HIn) "(#inv & excl1 & (p_1 & p_2 & p_3 & p_4 & p_5 & p_6 & p7 & _) & acc & tx & rx & pc & (%r0 & r0) & (%r1 & r1) & (%r2 & r2)
                   & vmprop) holds".
    (* iDestruct (VMProp_holds_agree V1 with "[holds vmprop]") as "[P prop1]". *)
    (* iFrame. *)
    assert (pprog1 ≠ ptx1) as Hneqtx.
    {
      intro.
      feed pose proof (NoDup_lookup _ 1 5 ptx1 Hps_nd).
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
      feed pose proof (NoDup_lookup _ 4 7 prx1 Hps_nd).
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
    (* set vmprop1 := ({[W0 := (V1, V3, {[pshare]}, Sharing, true)]}). *)
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
