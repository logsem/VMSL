From machine_program_logic.program_logic Require Import weakestpre.
From HypVeri.algebra Require Import base base_extra mem pagetable trans.
From HypVeri.rules Require Import rules_base mov halt run yield mem_send mem_retrieve
  mem_relinquish mem_reclaim ldr str msg_send msg_wait msg_poll add.
From HypVeri.examples Require Import instr utils.
From HypVeri.logrel Require Import logrel logrel_extra logrel_prim_extra fundamental.
From HypVeri Require Import proofmode machine_extra.
Require Import Setoid.

Fixpoint finz_succN_def {z : Z} (f : finz z) (n : nat) : finz.finz z :=
  match n with
  | 0 => f
  | S n' => ((finz_succN_def f n') ^+ 1)%f
  end.

Local Definition finz_succN_aux : seal (@finz_succN_def). Proof. by eexists. Qed.
Definition finz_succN := finz_succN_aux.(unseal).
Global Arguments finz_succN {_} _ _.
Local Definition finz_succN_unseal :
  @finz_succN = @finz_succN_def := finz_succN_aux.(seal_eq).

Lemma finz_succN_correct {z : Z} (f : finz z) (n : nat) : finz_succN f n = (f ^+ n)%f.
Proof.
  rewrite finz_succN_unseal.
  induction n; simpl; solve_finz.
Qed.

Lemma finz_succN_one {z : Z} (f : finz z) : (f ^+ 1)%f = finz_succN f 1.
Proof.
  rewrite finz_succN_correct.
  reflexivity.
Qed.

Lemma finz_succN_assoc {z : Z} (f : finz z) (n m : nat) : finz_succN (f ^+ m)%f n = ((finz_succN f n) ^+ m)%f.
Proof.
  rewrite finz_succN_unseal.
  induction n.
  - reflexivity.
  - simpl.
    rewrite IHn.
    rewrite finz_plus_assoc.
    assert (m + 1 = 1 + m)%Z as ->.
    { lia. }
    rewrite finz_plus_assoc.
    reflexivity.
    all: lia.
Qed.

Lemma finz_succN_idemp {z : Z} (f : finz z) (n m : nat) : finz_succN (finz_succN f n) m = finz_succN f (n + m).
Proof.  
  rewrite finz_succN_unseal.
  induction n.
  - reflexivity.
  - simpl.
    rewrite <-IHn.
    rewrite <-finz_succN_unseal.
    rewrite (finz_succN_assoc _ _ 1).
    reflexivity.
Qed.

Lemma finz_succN_pid (p : PID) (n : nat) (lt : n < 1000) : tpa (finz_succN p n) = p.
Proof.
  apply to_pid_aligned_in_page.
  rewrite finz_succN_correct.
  unfold addr_in_page.
  destruct p.
  simpl in *.
  destruct z.
  simpl in *.
  assert ((z <=? 1999000)%Z = true).
  {
    rewrite Z.eqb_eq in align.
    rewrite Z.rem_mod_nonneg in align; [| lia | lia].
    rewrite Zmod_divides in align; last lia.
    destruct align as [c align].
    simplify_eq.
    assert (c <? 2000 = true)%Z.
    lia.
    assert (1999000 = 1000 * 1999)%Z as ->.
    lia.
    apply Zle_imp_le_bool.
    apply Zmult_le_compat_l; lia.
  }
  split.
  - apply Is_true_true_2.
    solve_finz.
  - apply Is_true_true_2.
    solve_finz.
Qed.

Lemma finz_succN_pid' (p : PID) (n : nat) (lt : n < 1000) : tpa (p ^+ n)%f = p.
Proof.
  rewrite <-finz_succN_correct.
  apply finz_succN_pid; assumption.
Qed.

Lemma finz_succN_in_seq (p : PID) (n m : nat) (lt : n < m) : (p ^+ n)%f ∈ finz.seq p m.
Proof.
  induction m.
  - inversion lt.
  - assert (S m = m + 1) as ->.
    { rewrite <-PeanoNat.Nat.add_1_r; reflexivity. }  
    apply finz_seq_in_inv.
    + solve_finz.
    + solve_finz.
Qed.

Lemma finz_nat_add_assoc (p : PID) (n m : nat) : ((p ^+ n) ^+ m)%f = (p ^+ (n + m))%f.
Proof.
  rewrite finz_plus_assoc.
  reflexivity.
  all: lia.
Qed.

Lemma finz_plus_one_simpl {z : Z} (f : finz z) (n : nat) : ((f ^+ (Z.of_nat n)) ^+ 1)%f = (f ^+ (n + 1%nat))%f.
Proof.
  rewrite finz_plus_assoc.
  reflexivity.
  all: lia.
Qed.

Lemma Z_of_nat_simpl (n m : nat) : (n%nat + m%nat)%Z = ((n + m)%nat)%Z.
Proof.
  lia.
Qed.

Ltac fold_finz_plus_one :=
  repeat (rewrite finz_succN_one);
  repeat (rewrite finz_succN_idemp);
  iEval (simpl) in "∗".

Program Instance mtms_vmconfig : HypervisorConstants :=
    {vm_count := 3;
     vm_count_pos := _;
     valid_handles := {[W0]}}.

Program Definition V1 : VMID := (@nat_to_fin 1 _ _).
Program Definition V2 : VMID := (@nat_to_fin 2 _ _).

Program Definition zero : Imm := I (finz.FinZ 0 _ _) _.
Program Definition one : Imm := I (finz.FinZ 1 _ _) _.
Program Definition two : Imm := I (finz.FinZ 2 _ _) _.
Program Definition four : Imm := I (finz.FinZ 4 _ _) _.
Program Definition mem_descriptor_length : Imm := I (finz.FinZ 5 _ _) _.

Section proof.

  Context `{hypparams: !HypervisorParameters}.
  Context (pprog0 pprog1 pprog2 : PID).
  Context (ptx0 prx0 ptx1 prx1 ptx2 prx2 : PID).
  Context (pshare : PID).
  Context (Hps_nd: NoDup [pprog0;pprog1;pprog2;pshare;ptx0;ptx1;ptx2;prx0;prx1;prx2]).
  Context (addr : Imm) (Heq_pshare : of_pid pshare = addr).
  Context (i_ptx0 : Imm) (Heq_ptx0 : of_pid ptx0 = i_ptx0).
  Context (i_prx1 : Imm) (Heq_prx1 : of_pid prx1 = i_prx1).


  Definition mtms_program0 : list Word :=
    [
      (* Store 2 to mem *)
      mov_word_I R4 two;
      mov_word_I R5 addr;
      str_I R4 R5;
      (* Memory descriptor *)
      mov_word_I R5 i_ptx0;
      mov_word_I R3 one;
      mov_word_I R4 (encode_vmid V0);
      str_I R4 R5;
      add_I R5 R3;
      mov_word_I R4 zero;
      str_I R4 R5;
      add_I R5 R3;
      mov_word_I R4 one;
      str_I R4 R5;
      add_I R5 R3;
      mov_word_I R4 (encode_vmid V1);
      str_I R4 R5;
      add_I R5 R3;
      mov_word_I R4 addr;
      str_I R4 R5;
      (* Lend page *)
      mov_word_I R0 mem_share_I;
      mov_word_I R1 mem_descriptor_length;
      hvc_I;
      (* Send handle *)
      mov_word_I R5 i_ptx0;
      str_I R2 R5;
      mov_reg_I R3 R2;
      mov_word_I R0 msg_send_I;
      mov_word_I R1 (encode_vmid V1);
      mov_word_I R2 one;
      hvc_I;
      (* Run VM 1 *)
      mov_word_I R0 run_I;
      mov_word_I R1 (encode_vmid V1);
      hvc_I;
      (* Run VM 2 (unknown vm *)
      mov_word_I R0 run_I;
      mov_word_I R1 (encode_vmid V2);
      hvc_I;
      (* Stop *)
      halt_I
    ].

  Definition mtms_program1 : list Word :=
    [
      (* Fetch handle *)
      mov_word_I R5 i_prx1;
      ldr_I R4 R5;
      (* Clean rx status *)
      mov_word_I R0 msg_poll_I;
      hvc_I;
      (* Retrieve page *)
      mov_reg_I R1 R4;
      mov_word_I R0 mem_retrieve_I;
      hvc_I;
      (* Rewrite 2 to 4 *)
      mov_word_I R3 four;
      mov_word_I R5 addr;
      str_I R3 R5;
      (* hvc_I; *)
      mov_word_I R0 msg_poll_I;
      hvc_I;
      (* Yield back *)
      mov_word_I R0 yield_I;
      hvc_I
    ].

  Context `{!gen_VMG Σ}.

  Definition mtms_slice_trans trans i j : iProp Σ := slice_transfer_all trans i j.

  Definition mtms_slice_rxs i os (j: VMID) : iProp Σ :=
    (match os with
    | None => True
    | _ => slice_rx_state i os
    end)%I.

  Lemma mtms_machine0 :
    let RX0 := (RX_state@V0 := None ∗ mailbox.rx_page V0 prx0 ∗ ∃ mem_rx, memory_page prx0 mem_rx)%I in
    let RX1 := (RX_state@V1 := None ∗ RX@V1:=prx1 ∗ ∃ mem_rx, memory_page prx1 mem_rx)%I in
    let RX2 := (RX_state@V2 := None ∗ RX@V2:=prx2 ∗ ∃ mem_rx, memory_page prx2 mem_rx)%I in
    let program0 := mtms_program0 in
    (* Addresses-values connection *)
    seq_in_page (of_pid pprog0) (length program0) pprog0 ->
    (* Mem for program *)
    (program (program0) (of_pid pprog0)) ∗
      (* Work mem *)
      (∃ w, addr ->a w) ∗
      (* TX mem *)
      (∃ txmem, memory_page ptx0 txmem) ∗
      (* Pages for VM 0 *)
      ([∗ set] p ∈ {[pshare]}, p -@O> V0 ∗ p -@E> true) ∗
      V0 -@A> {[pshare;pprog0;ptx0]} ∗
      (* TX page *)            
      TX@ V0 := ptx0 ∗
      (* Program counter *)                      
      PC @@ V0 ->r (of_pid pprog0) ∗
      (* Work registers *)                        
      (∃ r0, R0 @@ V0 ->r r0) ∗
      (∃ r1, R1 @@ V0 ->r r1) ∗
      (∃ r2, R2 @@ V0 ->r r2) ∗
      (∃ r3, R3 @@ V0 ->r r3) ∗
      (∃ r4, R4 @@ V0 ->r r4) ∗
      (∃ r5, R5 @@ V0 ->r r5) ∗                  
      (* Protocol for VM 0 *)            
      VMProp V0 True%I 1 ∗
      (* Protocol for VM 1 *)            
      VMProp V1 (R0 @@ V0 ->r run_I ∗ R1 @@ V0 ->r encode_vmid V1 ∗ addr ->a two  ∗ (∃ (wh : Addr), (∃ (β : mem), wh ->t (V0, V1, {[pshare]}, Sharing) ∗
                                                                                    wh ->re false ∗ RX_state@V1 := Some (of_imm one, V0) ∗ RX@V1:=prx1 ∗ memory_page prx1 β ∗ ⌜β !! (of_imm i_prx1) = Some wh⌝) ∗
                    VMProp V0 ((R0 @@ V0 ->r yield_I ∗ R1 @@ V0 ->r encode_vmid V1 ∗ addr ->a four ∗ wh ->t (V0, V1, {[pshare]}, Sharing) ∗ RX@V1:=prx1 ∗ RX_state@V1 := None ∗ (∃ mem_rx, memory_page prx1 mem_rx)) ∗
                                 VMProp V1 False%I (1/2)%Qp) (1/2)%Qp))%I (1/2)%Qp ∗
      (* Protocol for unknown vm *)
      VMProp V2 (vmprop_unknown V2 mtms_slice_trans mtms_slice_rxs ∅) (1/2)%Qp ∗
      (* Pages for unknown VM *)            
      trans.fresh_handles 1 valid_handles ∗
      (* RX states *)               
      RX0 ∗ RX1 ∗ RX2 
      ⊢ WP ExecI @ V0
            {{ (λ m,
                 ⌜m = HaltI⌝ ∗
                 addr ->a four ∗
                 V0 -@A> {[pshare;pprog0;ptx0]} ∗
                 TX@ V0 := ptx0 ∗
                 PC @@ V0 ->r ((of_pid pprog0) ^+ (length program0))%f
                 )}}%I.
  Proof.
    rewrite /vmprop_unknown.
    iIntros (HIn) "((p_1 & p_2 & p_3 & p_4 & p_5 & p_6 & p_7
            & p_8 & p_9 & p_10 & p_11 & p_12 & p_13 & p_14 & p_15 & p_16 
            & p_17 & p_18 & p_19 & p_20 & p_21 & p_22 & p_23 & p_24 & p_25
            & p_26 & p_27 & p_28 & p_29 & p_30 & p_31 & p_32 & p_33 & p_34
            & p_35 & p_36 & _) 
         & (%memv & mem) & (%txmemgm & txmem) & OE & acc & tx & PCz & (%r0 & R0z) & (%r1 & R1z) & (%r2 & R2z) 
         & (%r3 & R3z) & (%r4 & R4z) & (%r5 & R5z) 
         & prop0 & prop1 & prop2 & hp & ((RX0st & _) & (RX0page & RX0own & RX0excl) & RX0mem)
         & ((RX1st & _) & RX1page & RX1mem) & ((RX2st & _) & RX2page & RX2mem))".
    pose proof (seq_in_page_forall2 _ _ _ HIn) as Hforall.
    fold_finz_plus_one.
    repeat (rewrite finz_succN_correct).
    clear HIn; rename Hforall into HIn.
    assert (pprog0 ≠ ptx0) as Hnottx.
    {
      intro.
      feed pose proof (NoDup_lookup _ 0 4 ptx0 Hps_nd).
      simplify_eq /=. done.
      simplify_eq /=. done.
      lia.
    }
    (* mov_word_I R4 two *)
    rewrite wp_sswp.    
    iApply ((mov_word (of_pid pprog0) two R4) with "[p_1 PCz acc tx R4z]"); rewrite ?to_pid_aligned_eq; iFrameAutoSolve.
    set_solver +.
    iModIntro.
    iIntros "(PCz & _ & acc & tx & R4z) _".    
    (* mov_word_I R5 addr *)
    rewrite wp_sswp.
    iApply ((mov_word _ addr R5) with "[p_2 PCz acc tx R5z]"); rewrite ?to_pid_aligned_eq; iFrameAutoSolve.
    rewrite HIn.
    set_solver +.
    set_solver +.
    rewrite HIn. done.
    set_solver +.
    iModIntro.
    iIntros "(PCz & _ & acc & tx & R5z) _".
    (* str_I R4 R5 *)
    rewrite wp_sswp.    
    iEval (repeat (rewrite finz_succN_one)) in "PCz".
    iEval (repeat (rewrite finz_succN_idemp)) in "PCz".
    iEval (simpl) in "PCz".
    iEval (repeat (rewrite finz_succN_correct)) in "PCz".
    iApply ((str _ addr R4 R5) with "[p_3 PCz acc mem RX0page tx R4z R5z]"); rewrite ?to_pid_aligned_eq; iFrameAutoSolve.
    rewrite -Heq_pshare.
    rewrite to_pid_aligned_eq.
    rewrite HIn.
    set_solver +.
    apply finz_succN_in_seq.
    simpl. lia.
    rewrite HIn. done.
    apply finz_succN_in_seq; simpl; lia.
    rewrite -Heq_pshare.
    rewrite to_pid_aligned_eq.
    {
      intro.
      feed pose proof (NoDup_lookup _ 3 7 prx0 Hps_nd).
      simplify_eq /=. done.
      simplify_eq /=. done.
      lia.
    }
    iModIntro.
    iIntros "(PCz & _ & R5z & mem & R4z & acc & tx & RX0page) _".
    (* mov_word_I R5 tx_addr *)
    rewrite wp_sswp.
    iEval (rewrite finz_plus_one_simpl) in "PCz".
    rewrite Z_of_nat_simpl.
    iEval (simpl) in "PCz".
    iApply ((mov_word _ i_ptx0 R5) with "[p_4 PCz acc tx R5z]"); iFrameAutoSolve.
    rewrite HIn.
    set_solver +.
    apply finz_succN_in_seq; simpl; lia.
    rewrite HIn. done.
    apply finz_succN_in_seq; simpl; lia.
    iModIntro.
    iIntros "(PCz & _ & acc & tx & R5z) _".
    (* mov_word_I R3 one *)
    rewrite wp_sswp.
    iEval (rewrite finz_plus_one_simpl) in "PCz".
    rewrite Z_of_nat_simpl.
    iEval (simpl) in "PCz".
    iApply ((mov_word _ one R3) with "[p_5 PCz acc tx R3z]"); iFrameAutoSolve.
    rewrite HIn.
    set_solver +.
    apply finz_succN_in_seq; simpl; lia.
    rewrite HIn. done.
    apply finz_succN_in_seq; simpl; lia.
    iModIntro.
    iIntros "(PCz & _ & acc & tx & R3z) _".
    (* mov_word_I R4 (encode_vmid V0) *)
    rewrite wp_sswp.
    iEval (rewrite finz_plus_one_simpl) in "PCz".
    rewrite Z_of_nat_simpl.
    iEval (simpl) in "PCz".
    iApply ((mov_word _ (encode_vmid V0) R4) with "[p_6 PCz acc tx R4z]"); iFrameAutoSolve.
    rewrite HIn.
    set_solver +.
    apply finz_succN_in_seq; simpl; lia.
    rewrite HIn.
    done.
    apply finz_succN_in_seq; simpl; lia.
    iModIntro.
    iIntros "(PCz & _ & acc & tx & R4z) _".
    (* str_I R4 R5 *)
    rewrite wp_sswp.
    iEval (rewrite finz_plus_one_simpl) in "PCz".
    rewrite Z_of_nat_simpl.
    iEval (simpl) in "PCz".
    iEval (unfold memory_page) in "txmem".
    iDestruct "txmem" as "(%domtxmem & txmem)".
    (* Set *)
    pose proof (last_addr_in_bound ptx0) as Hlast_ptx.
    iDestruct (@mem_big_sepM_split_upd5 _ txmemgm i_ptx0 (ptx0 ^+ 1)%f ((ptx0 ^+ 1) ^+ 1)%f (((ptx0 ^+ 1) ^+ 1) ^+ 1)%f ((((ptx0 ^+ 1) ^+ 1) ^+ 1) ^+ 1)%f with "txmem") as "txmem";rewrite -?Heq_ptx0.
    solve_finz + Hlast_ptx.
    solve_finz + Hlast_ptx.
    solve_finz + Hlast_ptx.
    solve_finz + Hlast_ptx.
    solve_finz + Hlast_ptx.
    solve_finz + Hlast_ptx.
    solve_finz + Hlast_ptx.
    solve_finz + Hlast_ptx.
    solve_finz + Hlast_ptx.
    solve_finz + Hlast_ptx.
    {
      rewrite <-elem_of_dom.
      rewrite domtxmem.
      rewrite elem_of_list_to_set.
      apply elem_of_addr_of_page_iff.
      rewrite to_pid_aligned_eq //.
    }
    {
      rewrite <-elem_of_dom.
      rewrite domtxmem.
      rewrite elem_of_list_to_set.      
      apply elem_of_addr_of_page_iff.
      rewrite (finz_succN_pid' ptx0 1).
      reflexivity.
      lia.
    }
    {
      rewrite <-elem_of_dom.
      rewrite domtxmem.
      rewrite elem_of_list_to_set.      
      apply elem_of_addr_of_page_iff.
      symmetry.
      repeat (rewrite finz_succN_one).
      repeat (rewrite finz_succN_idemp).
      simpl.
      rewrite finz_succN_correct.
      rewrite (finz_succN_pid' ptx0 2).
      reflexivity.
      lia.
    }
    {
      rewrite <-elem_of_dom.
      rewrite domtxmem.
      rewrite elem_of_list_to_set.      
      apply elem_of_addr_of_page_iff.
      symmetry.
      repeat (rewrite finz_succN_one).
      repeat (rewrite finz_succN_idemp).
      simpl.
      rewrite finz_succN_correct.
      rewrite (finz_succN_pid' ptx0 3).
      reflexivity.
      lia.
    }
    {
      rewrite <-elem_of_dom.
      rewrite domtxmem.
      rewrite elem_of_list_to_set.      
      apply elem_of_addr_of_page_iff.
      symmetry.
      repeat (rewrite finz_succN_one).
      repeat (rewrite finz_succN_idemp).
      simpl.
      rewrite finz_succN_correct.
      rewrite (finz_succN_pid' ptx0 4).
      reflexivity.
      lia.
    }
    iDestruct "txmem" as "(%w1 & %w2 & %w3 & %w4 & %w5 & txmem1 & txmem2 & txmem3 & txmem4 & txmem5 & txacc)".    
    iApply ((@str _ _ _ _ _ V0 (str_I R4 R5) (encode_vmid V0) w1 1%Qp prx0 ptx0 {[pshare;pprog0; ptx0]} (pprog0 ^+ 6%nat)%f
               i_ptx0 R4 R5) with "[PCz p_7 acc txmem1 RX0page tx R4z R5z]") ; rewrite ?to_pid_aligned_eq.
    apply decode_encode_instruction.
    rewrite -Heq_ptx0.
    rewrite ?to_pid_aligned_eq.
    rewrite HIn.
    set_solver +.
    apply finz_succN_in_seq; simpl; lia.
    rewrite HIn. done.
    apply finz_succN_in_seq; simpl; lia.
    rewrite -Heq_ptx0.
    rewrite to_pid_aligned_eq.
    {
      intros Heq.
      feed pose proof (NoDup_lookup _ 4 7 prx0 Hps_nd).
      rewrite Heq. done.
      rewrite Heq. done.
      lia.
    }
    rewrite -Heq_ptx0.
    iFrame.
    iModIntro.
    iIntros "(PCz & _ & R5z & txmem1 & R4z & acc & tx & RX0page) _".
    (* add_I R5 R3 *)
    rewrite wp_sswp.
    iEval (rewrite finz_plus_one_simpl) in "PCz".
    rewrite Z_of_nat_simpl.
    iEval (simpl) in "PCz".
    iApply ((@add _ _ _ _ _ _ (add_I R5 R3) i_ptx0 one 1%Qp ptx0 (pprog0 ^+ 7%nat)%f R5 R3 {[pshare;pprog0; tpa ptx0]})
             with "[p_8 PCz acc R5z R3z tx]"); rewrite ?to_pid_aligned_eq.
    apply decode_encode_instruction.
    rewrite HIn.
    set_solver +.
    apply finz_succN_in_seq; simpl; lia.
    rewrite HIn. done.
    apply finz_succN_in_seq; simpl; lia.
    iFrame.    
    iModIntro.
    iIntros "(PCz & _ & R5z & R3z & acc & tx) _".
    (* mov_word_I R4 zero *)
    rewrite wp_sswp.
    iEval (rewrite finz_plus_one_simpl) in "PCz".
    rewrite Z_of_nat_simpl.
    iEval (simpl) in "PCz".
    iApply ((@mov_word _ _ _ _ _ _ _ _ _ {[pshare;pprog0; ptx0]} ptx0 (pprog0 ^+ 8%nat)%f zero R4) with "[p_9 PCz acc tx R4z]").
    apply decode_encode_instruction.
    rewrite HIn. set_solver +.
    apply finz_succN_in_seq; simpl; lia.
    rewrite HIn. done.
    apply finz_succN_in_seq; simpl; lia.
    iFrame.
    iModIntro.
    iIntros "(PCz & _ & acc & tx & R4z) _".
    (* str_I R4 R5 *)
    rewrite wp_sswp.
    iEval (rewrite finz_plus_one_simpl) in "PCz".
    rewrite Z_of_nat_simpl.
    iEval (simpl) in "PCz".
    iApply ((@str _ _ _ _ _ _ _ zero w2 1%Qp prx0 ptx0 {[pshare;pprog0; ptx0]} (pprog0 ^+ 9%nat)%f (ptx0 ^+ 1)%f R4 R5) with "[p_10 PCz acc txmem2 RX0page tx R4z R5z]").
    apply decode_encode_instruction.
    rewrite (finz_succN_pid' ptx0 1);try lia.
    rewrite HIn.
    set_solver +.
    apply finz_succN_in_seq; simpl; lia.
    rewrite HIn. done.
    apply finz_succN_in_seq; simpl; lia.
    rewrite (finz_succN_pid' ptx0 1); try lia.
    {
      intros Heq.
      feed pose proof (NoDup_lookup _ 4 7 prx0 Hps_nd).
      rewrite Heq. done.
      rewrite Heq. done.
      lia.
    }
    iFrame. rewrite Heq_ptx0. simpl. iFrame.
    iModIntro.
    iIntros "(PCz & _ & R5z & txmem2 & R4z & acc & tx & RX0page) _".
    (* add_I R5 R3 *)
    rewrite wp_sswp.
    iEval (rewrite finz_plus_one_simpl) in "PCz".
    rewrite Z_of_nat_simpl.
    iEval (simpl) in "PCz".
    iApply (@add _ _ _ _ _ _ (add_I R5 R3) (i_ptx0 ^+ 1)%f one 1%Qp ptx0
              (pprog0 ^+ 10%nat)%f
              R5 R3 {[pshare;pprog0; ptx0]} with "[p_11 PCz acc R5z R3z tx]").
    apply decode_encode_instruction. 
    rewrite HIn.
    set_solver +.
    apply finz_succN_in_seq; simpl; lia.
    rewrite (finz_succN_pid' pprog0 10);[|lia].
    done.
    iFrame. rewrite Heq_ptx0. simpl. iFrame.
    iModIntro.
    iIntros "(PCz & _ & R5z & R3z & acc & tx) _".
    (* (* mov_word_I R4 one *) *)
    rewrite wp_sswp.
    iEval (rewrite finz_plus_one_simpl) in "PCz".
    rewrite Z_of_nat_simpl.
    iEval (simpl) in "PCz".
    iApply ((@mov_word _ _ _ _ _ _ _ _ _ {[pshare;pprog0; ptx0]} ptx0
               (pprog0 ^+ 11%nat)%f
               one R4) with "[p_12 PCz acc tx R4z]").
    apply decode_encode_instruction.
    rewrite HIn.
    set_solver +.
    apply finz_succN_in_seq; simpl; lia.
    rewrite (finz_succN_pid' pprog0 11);[|lia].
    done.
    iFrame.
    iModIntro.
    iIntros "(PCz & _ & acc & tx & R4z) _".
    rewrite wp_sswp.
    iEval (rewrite finz_plus_one_simpl) in "PCz".
    rewrite Z_of_nat_simpl.
    iEval (simpl) in "PCz".
    iApply ((@str _ _ _ _ _ _ _ one w3 1%Qp prx0 ptx0 {[pshare;pprog0; ptx0]} (pprog0 ^+ 12%nat)%f ((ptx0 ^+ 1) ^+ 1)%f R4 R5) with "[p_13 PCz acc txmem3 RX0page tx R4z R5z]").
    apply decode_encode_instruction.
    repeat (rewrite finz_succN_one).
    repeat (rewrite finz_succN_idemp).
    simpl.
    rewrite finz_succN_correct.
    rewrite (finz_succN_pid' ptx0 2);[|lia].
    rewrite HIn.
    set_solver +.
    apply finz_succN_in_seq; simpl; lia.
    rewrite finz_succN_pid';[|lia].
    done.
    repeat (rewrite finz_succN_one).
    repeat (rewrite finz_succN_idemp).
    simpl.
    rewrite finz_succN_correct.
    rewrite (finz_succN_pid' ptx0 2);[|lia].
    {
      intros Heq.
      feed pose proof (NoDup_lookup _ 4 7 prx0 Hps_nd).
      rewrite Heq. done.
      rewrite Heq. done.
      lia.
    }
    rewrite Heq_ptx0. iFrame.
    iModIntro.
    iIntros "(PCz & _ & R5z & txmem3 & R4z & acc & tx & RX0page) _".
    (* add_I R5 R3 *)
    rewrite wp_sswp.
    iEval (rewrite finz_plus_one_simpl) in "PCz".
    rewrite Z_of_nat_simpl.
    iEval (simpl) in "PCz".
    iApply (@add _ _ _ _ _ _ (add_I R5 R3) (ptx0 ^+ 2)%f one 1%Qp ptx0
              (pprog0 ^+ 13%nat)%f
              R5 R3 {[pshare;pprog0; ptx0]} with "[p_14 PCz acc R5z R3z tx]").
    apply decode_encode_instruction. 
    rewrite (finz_succN_pid' pprog0 13);[|lia].
    set_solver +.
    rewrite (finz_succN_pid' pprog0 13);[|lia].
    done.
    iFrame.
    repeat (rewrite finz_succN_one).
    repeat (rewrite finz_succN_idemp).
    simpl.
    rewrite !finz_succN_correct.
    iFrame.
    iModIntro.
    iIntros "(PCz & _ & R5z & R3z & acc & tx) _".
    (* (* mov_word_I R4 one *) *)
    rewrite wp_sswp.
    iEval (rewrite finz_plus_one_simpl) in "PCz".
    rewrite Z_of_nat_simpl.
    iEval (simpl) in "PCz".
    iApply ((@mov_word _ _ _ _ _ _ _ _ _ {[pshare;pprog0; ptx0]} ptx0
               (pprog0 ^+ 14%nat)%f
               (encode_vmid V1) R4) with "[p_15 PCz acc tx R4z]").
    apply decode_encode_instruction.
    rewrite (finz_succN_pid' pprog0 14);[|lia].
    set_solver +.
    rewrite HIn. done.
    apply finz_succN_in_seq; simpl; lia.
    iFrame.
    iModIntro.
    iIntros "(PCz & _ & acc & tx & R4z) _".
    rewrite wp_sswp.
    iEval (rewrite finz_plus_one_simpl) in "PCz".
    rewrite Z_of_nat_simpl.
    iEval (simpl) in "PCz".
    iApply ((@str _ _ _ _ _ _ _ (encode_vmid V1) w4 1%Qp prx0 ptx0
               {[pshare;pprog0; ptx0]} (pprog0 ^+ 15%nat)%f (ptx0 ^+3)%f R4 R5) with "[p_16 PCz acc txmem4 RX0page tx R4z R5z]").
    apply decode_encode_instruction.
    rewrite (finz_succN_pid' ptx0 3);[|lia].
    rewrite HIn.
    set_solver +.
    apply finz_succN_in_seq; simpl; lia.
    rewrite (finz_succN_pid' pprog0 15);[|lia].
    done.
    rewrite (finz_succN_pid' ptx0 3);[|lia].
    {
      intros Heq.
      feed pose proof (NoDup_lookup _ 4 7 prx0 Hps_nd).
      rewrite Heq. done.
      rewrite Heq. done.
      lia.
    }
    iFrame.
    repeat (rewrite finz_succN_one).
    repeat (rewrite finz_succN_idemp).
    simpl.
    rewrite !finz_succN_correct.
    iFrame.
    rewrite -finz_succN_correct.
    rewrite -(finz_succN_correct ptx0 2).
    repeat (rewrite finz_succN_idemp).
    simpl.
    rewrite !finz_succN_correct.
    iFrame.
    iModIntro.
    iIntros "(PCz & _ & R5z & txmem4 & R4z & acc & tx & RX0page) _".
    (* add_I R5 R3 *)
    rewrite wp_sswp.
    iEval (rewrite finz_plus_one_simpl) in "PCz".
    rewrite Z_of_nat_simpl.
    iEval (simpl) in "PCz".
    iApply (@add _ _ _ _ _ _ (add_I R5 R3) (ptx0 ^+ 3)%f one 1%Qp ptx0
              (pprog0 ^+ 16%nat)%f
              R5 R3 {[pshare;pprog0; ptx0]} with "[p_17 PCz acc R5z R3z tx]").
    apply decode_encode_instruction. 
    rewrite (finz_succN_pid' pprog0 16);[|lia].
    set_solver +.
    rewrite (finz_succN_pid' pprog0 16);[|lia].
    done.
    iFrame.
    iModIntro.
    iIntros "(PCz & _ & R5z & R3z & acc & tx) _".
    (* (* mov_word_I R4 one *) *)
    rewrite wp_sswp.
    iEval (rewrite finz_plus_one_simpl) in "PCz".
    rewrite Z_of_nat_simpl.
    iEval (simpl) in "PCz".
    iApply ((@mov_word _ _ _ _ _ _ _ _ _ {[pshare;pprog0; ptx0]} ptx0
               (pprog0 ^+ 17%nat)%f
               addr R4) with "[p_18 PCz acc tx R4z]").
    apply decode_encode_instruction.
    rewrite (finz_succN_pid' pprog0 17);[|lia].
    set_solver +.
    rewrite (finz_succN_pid' pprog0 17);[|lia].
    done.
    iFrame.
    iModIntro.
    iIntros "(PCz & _ & acc & tx & R4z) _".
    rewrite wp_sswp.
    iEval (rewrite finz_plus_one_simpl) in "PCz".
    rewrite Z_of_nat_simpl.
    iEval (simpl) in "PCz".
    iApply ((@str _ _ _ _ _ _ _ addr w5 1%Qp prx0 ptx0 {[pshare;pprog0; ptx0]} (pprog0 ^+ 18%nat)%f
               (ptx0 ^+ 4)%f R4 R5) with "[p_19 PCz acc txmem5 RX0page tx R4z R5z]").
    apply decode_encode_instruction.
    rewrite (finz_succN_pid' ptx0 4);[|lia].
    rewrite (finz_succN_pid' pprog0 18);[|lia].
    set_solver +.
    rewrite (finz_succN_pid' pprog0 18);[|lia].
    done.
    rewrite (finz_succN_pid' ptx0 4);[|lia].
    {
      intros Heq.
      feed pose proof (NoDup_lookup _ 4 7 prx0 Hps_nd).
      rewrite Heq. done.
      rewrite Heq. done.
      lia.
    }
    iFrame.
    rewrite -(finz_succN_correct ptx0 3).
    repeat (rewrite finz_succN_one).
    repeat (rewrite finz_succN_idemp).
    simpl.
    rewrite !finz_succN_correct.
    iFrame.
    repeat (rewrite finz_succN_one).
    rewrite !finz_succN_correct.
    iModIntro.
    iIntros "(PCz & _ & R5z & txmem5 & R4z & acc & tx & RX0page) _".
    rewrite wp_sswp.
    iEval (rewrite finz_plus_one_simpl) in "PCz".
    rewrite Z_of_nat_simpl.
    iEval (simpl) in "PCz".
    iApply ((@mov_word _ _ _ _ _ _ _ _ _ {[pshare;pprog0; ptx0]} ptx0
               (pprog0 ^+ 19%nat)%f
               mem_share_I R0) with "[p_20 PCz acc tx R0z]").
    apply decode_encode_instruction.
    rewrite (finz_succN_pid' pprog0 19);[|lia].
    set_solver +.
    rewrite (finz_succN_pid' pprog0 19);[|lia].
    done.
    iFrame.
    iModIntro.
    iIntros "(PCz & _ & acc & tx & R0z) _".
    rewrite wp_sswp.
    iEval (rewrite finz_plus_one_simpl) in "PCz".
    rewrite Z_of_nat_simpl.
    iEval (simpl) in "PCz".
    iApply ((@mov_word _ _ _ _ _ _ _ _ _ {[pshare;pprog0; ptx0]} ptx0
               (pprog0 ^+ 20%nat)%f
               mem_descriptor_length R1) with "[p_21 PCz acc tx R1z]").
    apply decode_encode_instruction.
    rewrite (finz_succN_pid' pprog0 20);[|lia].
    set_solver +.
    rewrite (finz_succN_pid' pprog0 20);[|lia].
    done.
    iFrame.
    iModIntro.
    iIntros "(PCz & _ & acc & tx & R1z) _".
    rewrite wp_sswp.
    iEval (rewrite finz_plus_one_simpl) in "PCz".
    rewrite Z_of_nat_simpl.
    iEval (simpl) in "PCz".
    iSpecialize ("txacc" $! (encode_vmid V0) zero one (encode_vmid V1) addr).
    rewrite -Heq_ptx0.
    (* rewrite finz_plus_one_simpl. *)
    (* simpl. *)

    iDestruct ("txacc" with "[txmem1 txmem2 txmem3 txmem4 txmem5]") as "txmem".
    {
      repeat (rewrite finz_succN_one).
      repeat (rewrite finz_succN_idemp).
      simpl.
      rewrite !finz_succN_correct.
      iFrame.
    }
    match goal with
    | |- context [([∗ map] k↦y ∈ ?p, k ->a y)%I] => set q := p
    end.
    iApply ((mem_share (p_tx := ptx0) (wi := hvc_I) (hvcf := Share)
               (sacc := {[pshare;pprog0; ptx0]})
               (r0 := mem_share_I) (r1 := mem_descriptor_length) (r2 := r2)
               (pprog0 ^+ 21%nat)%f
               V1 q
               valid_handles (singleton pshare))
             with "[p_22 PCz acc R0z R1z R2z hp tx txmem OE]").
    rewrite HIn.
    set_solver +.
    apply finz_succN_in_seq; simpl; lia.
    rewrite HIn. done.
    apply finz_succN_in_seq; simpl; lia.
    apply decode_encode_instruction.
    apply decode_encode_hvc_func.
    reflexivity.
    unfold mem_descriptor_length. simpl. lia.
    unfold parse_transaction_descriptor.
    assert (parse_list_of_Word q ptx0 (Z.to_nat mem_descriptor_length) = Some ([of_imm (encode_vmid V0); of_imm zero; of_imm one; of_imm (encode_vmid V1); of_pid pshare] : list Addr)) as ->.
    {
        clear -Heq_ptx0 Heq_pshare.
        pose proof (last_addr_in_bound ptx0) as Hlast_ptx.
        unfold parse_list_of_Word.
        unfold sequence_a.
        match goal with
        | |- context G [Some ?l] => remember l as l'
        end.
        simpl.
        match goal with
        | |- context G [monad.List.sequence_a_list [?a; ?b; ?c; ?d; ?e]] => set a' := a; set b' := b; set c' := c; set d' := d; set e' := e
        end.
        assert (a' = Some (of_imm (encode_vmid V0))) as ->.
        {
          subst a'.
          subst q.
          clear -Heq_ptx0.
          rewrite lookup_insert_Some.
          left.
          split; last done.
          done.
        }
        assert (b' = Some (of_imm zero)) as ->.
        {
          subst b'.
          subst q.
          rewrite lookup_insert_Some.
          right.
          split.
          solve_finz + Hlast_ptx.
          - rewrite lookup_insert_Some.
            left.
            split; last done.
            solve_finz +.
        }
        assert (c' = Some (of_imm one)) as ->.
        {
          subst c'.
          subst q.
          rewrite lookup_insert_Some.
          right.
          split.
          solve_finz + Hlast_ptx.
          rewrite lookup_insert_Some.
          right.
          split.
          solve_finz + Hlast_ptx.
          rewrite lookup_insert_Some.
          left.
          split; last done.
          solve_finz + Hlast_ptx.
        }
        assert (d' = Some (of_imm (encode_vmid V1))) as ->.
        {
          subst d'.
          subst q.
          rewrite lookup_insert_Some.
          right.
          split.
          solve_finz + Hlast_ptx.
          rewrite lookup_insert_Some.
          right.
          split.
          solve_finz + Hlast_ptx.
          rewrite lookup_insert_Some.
          right.
          split.
          solve_finz + Hlast_ptx.
          rewrite lookup_insert_Some.
          left.
          split; last done.
          solve_finz + Hlast_ptx.
        }
        assert (e' = Some (of_pid pshare)) as ->.
        {
          subst e'.
          subst q.
          rewrite lookup_insert_Some.
          right.
          split.
          solve_finz + Hlast_ptx.
          rewrite lookup_insert_Some.
          right.
          split.
          solve_finz + Hlast_ptx.
          rewrite lookup_insert_Some.
          right.
          split.
          solve_finz + Hlast_ptx.
          rewrite lookup_insert_Some.
          right.
          split.
          solve_finz + Hlast_ptx.
          rewrite lookup_insert_Some.
          left.
          split; last done.
          solve_finz + Hlast_ptx.
        }
        rewrite Heql'.
        unfold monad.List.sequence_a_list.
        simpl.
        reflexivity.        
      }
      cbn.
      rewrite decode_encode_vmid.
      rewrite decode_encode_vmid.
      assert (Z.to_nat 1 = 1) as ->.
      { lia. }
      rewrite Nat.eqb_refl.
      cbn.
      assert (to_pid pshare = Some pshare) as ->.
      {
        rewrite to_of_pid.
        reflexivity.
      }
      simpl.
      rewrite union_empty_r_L.
      reflexivity.
      done.
      set_solver +.
      set_solver +.
      iFrame.
      iNext.
      subst q.
      iPureIntro.
      (* rewrite <-elem_of_dom. *)
      (* rewrite domtxmem. *)
      (* rewrite elem_of_list_to_set. *)
      (* rewrite elem_of_addr_of_page_iff. *)
      repeat (rewrite finz_succN_one).
      repeat (rewrite finz_succN_idemp).
      rewrite !finz_succN_correct.
      rewrite !dom_insert_lookup_L;cbn;
      rewrite -?elem_of_dom;
      try rewrite !dom_insert_lookup_L -?elem_of_dom;
      try rewrite !dom_insert_lookup_L -?elem_of_dom;
      try rewrite !dom_insert_lookup_L -?elem_of_dom;
      try rewrite !dom_insert_lookup_L -?elem_of_dom;
      rewrite ?domtxmem ?elem_of_list_to_set;
      rewrite ?elem_of_addr_of_page_iff;
      rewrite ?(finz_succN_pid' ptx0);try lia;auto.
      rewrite to_pid_aligned_eq //.
    iModIntro.
    iIntros "(PCz & _ & OE & acc & R0z & R1z & (%wh & %whin & R2z & whtans & whretri & whfresh) & tx & txmem) _".
    assert (wh = W0) as wheq.
    {
      rewrite /valid_handles /= in whin.
      apply elem_of_singleton_1 in whin.
      assumption.      
    }
    rewrite wp_sswp.    
    iEval (rewrite finz_plus_one_simpl) in "PCz".
    rewrite Z_of_nat_simpl.
    iEval (simpl) in "PCz".
    iApply ((@mov_word _ _ _ _ _ _ _ _ _ {[pshare;pprog0; ptx0]} ptx0
               (pprog0 ^+ 22%nat)%f i_ptx0 R5) with "[p_23 PCz acc tx R5z]").
    apply decode_encode_instruction.
    rewrite HIn.
    set_solver +.
    apply finz_succN_in_seq; simpl; lia.
    rewrite HIn. done.
    apply finz_succN_in_seq; simpl; lia.
    iFrame.
    iModIntro.
    iIntros "(PCz & _ & acc & tx & R5z) _".
    (* str_I R2 R5 *)
    rewrite wp_sswp.
    iEval (rewrite finz_plus_one_simpl) in "PCz".
    rewrite Z_of_nat_simpl.
    iEval (simpl) in "PCz".
    iEval (unfold memory_page) in "txmem".
    iDestruct "txmem" as "(%domtxmem' & txmem)".
    (* Set *)
    iDestruct (@mem_big_sepM_split_upd _ q i_ptx0 (encode_vmid V0) with "txmem") as "txmem".
    {
      subst q.
      rewrite lookup_insert_Some.
      left.
      rewrite Heq_ptx0.
      split; reflexivity.
    }
    iDestruct "txmem" as "(txmem1 & txacc)".
    iApply ((@str _ _ _ _ _ _ _ wh (encode_vmid V0) 1%Qp prx0 ptx0 {[pshare;pprog0; ptx0]} (pprog0 ^+ 23%nat)%f i_ptx0 R2 R5) with "[p_24 PCz acc txmem1 RX0page tx R2z R5z]").
    apply decode_encode_instruction.
    rewrite <-Heq_ptx0.
    rewrite to_pid_aligned_eq.
    rewrite HIn.
    set_solver +.
    apply finz_succN_in_seq; simpl; lia.
    rewrite HIn. done.
    apply finz_succN_in_seq; simpl; lia.
    rewrite <-Heq_ptx0.
    rewrite to_pid_aligned_eq.
    {
      intros Heq.
      feed pose proof (NoDup_lookup _ 4 7 prx0 Hps_nd).
      rewrite Heq. done.
      rewrite Heq. done.
      lia.
    }
    iFrame.
    iModIntro.
    iIntros "(PCz & _ & R5z & txmem1 & R2z & acc & tx & RX0page) _".
    rewrite wp_sswp.
    iEval (rewrite finz_plus_one_simpl) in "PCz".
    rewrite Z_of_nat_simpl.
    iEval (simpl) in "PCz".
    iSpecialize ("txacc" $! wh).
    iDestruct ("txacc" with "[$txmem1]") as "txmem".
    iApply ((@mov_reg _ _ _ _ _ _ _ wh 1%Qp {[pshare;pprog0; ptx0]} ptx0 (pprog0 ^+ 24%nat)%f one R3 R2) with "[PCz p_25 acc tx R2z R3z]").
    apply decode_encode_instruction.
    rewrite HIn.
    set_solver +.
    apply finz_succN_in_seq; simpl; lia.
    rewrite HIn. done.
    apply finz_succN_in_seq; simpl; lia.
    iFrame.
    iModIntro.
    iIntros "(PCz & _ & acc & tx & R3z & R2z) _".
    rewrite wp_sswp.
    iEval (rewrite finz_plus_one_simpl) in "PCz".
    rewrite Z_of_nat_simpl.
    iEval (simpl) in "PCz".
    iApply ((@mov_word _ _ _ _ _ _ _ _ _ {[pshare;pprog0; ptx0]} ptx0 (pprog0 ^+ 25%nat)%f msg_send_I R0) with "[p_26 PCz acc tx R0z]").
    apply decode_encode_instruction.
    rewrite HIn.
    set_solver +.
    apply finz_succN_in_seq; simpl; lia.
    rewrite HIn. done.
    apply finz_succN_in_seq; simpl; lia.
    iFrame.
    iModIntro.
    iIntros "(PCz & _ & acc & tx & R0z) _".
    rewrite wp_sswp.
    iEval (rewrite finz_plus_one_simpl) in "PCz".
    rewrite Z_of_nat_simpl.
    iEval (simpl) in "PCz".
    iApply ((@mov_word _ _ _ _ _ _ _ _ _ {[pshare;pprog0; ptx0]} ptx0 (pprog0 ^+ 26%nat)%f (encode_vmid V1) R1) with "[p_27 PCz acc tx R1z]").
    apply decode_encode_instruction.
    rewrite HIn.
    set_solver +.
    apply finz_succN_in_seq; simpl; lia.
    rewrite HIn. done.
    apply finz_succN_in_seq; simpl; lia.
    iFrame.
    iModIntro.
    iIntros "(PCz & _ & acc & tx & R1z) _".
    rewrite wp_sswp.
    iEval (rewrite finz_plus_one_simpl) in "PCz".
    rewrite Z_of_nat_simpl.
    iEval (simpl) in "PCz".
    iApply ((@mov_word _ _ _ _ _ _ _ _ _ {[pshare;pprog0; ptx0]} ptx0 (pprog0 ^+ 27%nat)%f one R2) with "[p_28 PCz acc tx R2z]").
    apply decode_encode_instruction.
    rewrite HIn.
    set_solver +.
    apply finz_succN_in_seq; simpl; lia.
    rewrite HIn. done.
    apply finz_succN_in_seq; simpl; lia.
    iFrame.
    iModIntro.
    iIntros "(PCz & _ & acc & tx & R2z) _".
    rewrite wp_sswp.
    iEval (rewrite finz_plus_one_simpl) in "PCz".
    rewrite Z_of_nat_simpl.
    iEval (simpl) in "PCz".
    iDestruct "RX1mem" as "(%rxmem & rxmem)".
    match goal with
    | |- context [([∗ map] k↦y ∈ ?p, k ->a y)%I] => set q' := p
    end.
    iApply ((@msg_send_primary _ _ _ _ _ hvc_I msg_send_I (encode_vmid V1) {[pshare;pprog0; ptx0]} ptx0 q' 1%Qp prx1 rxmem one (pprog0 ^+ 28%nat)%f V1) with "[p_29 PCz acc tx R0z R1z R2z txmem RX1st rxmem RX1page]").
    rewrite HIn. done.
    apply finz_succN_in_seq; simpl; lia.
    rewrite HIn.
    set_solver +.
    apply finz_succN_in_seq; simpl; lia.
    by rewrite decode_encode_instruction.
    by rewrite decode_encode_hvc_func.
    simpl; lia.
    by rewrite decode_encode_vmid.
    done.
    iFrame.
    iNext.
    iPureIntro. subst q'. subst q.
    rewrite dom_insert_L.
    rewrite subseteq_union_1_L.
    assumption.
    apply singleton_subseteq_l.
    apply elem_of_dom.
    exists (encode_vmid V0).
    rewrite -Heq_ptx0.
    apply lookup_insert.
    iModIntro.
    iIntros "(PCz & _ & acc & R0z & R1z & R2z & tx & RX1page & RX1st & txmem & %descr & %descrlen & %descrsubseteq & rxmem) _".
    rewrite wp_sswp.
    iEval (rewrite finz_plus_one_simpl) in "PCz".
    rewrite Z_of_nat_simpl.
    iEval (simpl) in "PCz".
    iApply ((@mov_word _ _ _ _ _ _ _ _ _ {[pshare;pprog0; ptx0]} ptx0 (pprog0 ^+ 29%nat)%f run_I R0) with "[p_30 PCz acc tx R0z]").
    apply decode_encode_instruction.
    rewrite HIn.
    set_solver +.
    apply finz_succN_in_seq; simpl; lia.
    rewrite HIn. done.
    apply finz_succN_in_seq; simpl; lia.
    iFrame.
    iModIntro.
    iIntros "(PCz & _ & acc & tx & R0z) _".
    rewrite wp_sswp.
    iEval (rewrite finz_plus_one_simpl) in "PCz".
    rewrite Z_of_nat_simpl.
    iEval (simpl) in "PCz".
    iApply ((@mov_word _ _ _ _ _ _ _ _ _ {[pshare;pprog0; ptx0]} ptx0 (pprog0 ^+ 30%nat)%f (encode_vmid V1) R1) with "[p_31 PCz acc tx R1z]").
    apply decode_encode_instruction.
    rewrite HIn.
    set_solver +.
    apply finz_succN_in_seq; simpl; lia.
    rewrite HIn. done.
    apply finz_succN_in_seq; simpl; lia.
    iFrame.
    iModIntro.
    iIntros "(PCz & _ & acc & tx & R1z) _".
    rewrite wp_sswp.
    iEval (rewrite finz_plus_one_simpl) in "PCz".
    rewrite Z_of_nat_simpl.
    iEval (simpl) in "PCz".
    subst q'.
    subst q.
    rewrite <-descrlen in descrsubseteq.
    assert (∃ α, descr = [α]) as (α & Hdescr).
    {
      destruct descr.
      discriminate.
      destruct descr.
      eauto.
      discriminate.
    }
    rewrite Hdescr in descrsubseteq.
    match goal with
    | |- context G [memory_page prx1 ?s] => set β := s
    end.
    assert (β !! (of_imm i_prx1) = Some wh) as Hrx.
    {
      subst β.
      simpl.
      apply lookup_union_Some_l.
      rewrite Hdescr.
      simpl.
      assert (α = wh) as ->.
      {
        rewrite map_subseteq_spec in descrsubseteq.
        specialize (descrsubseteq (of_imm i_ptx0) α).
        feed specialize descrsubseteq.
        {
          apply elem_of_list_to_map_1.
          apply NoDup_singleton.
          rewrite <-Heq_ptx0.
          apply elem_of_list_singleton.
          reflexivity.
        }
        apply lookup_insert_rev in descrsubseteq.
        by symmetry.
      }
      rewrite Heq_prx1.
      apply lookup_insert.
    }    
    iApply ((@run _ _ _ _ _ hvc_I run_I (encode_vmid V1) 1%Qp {[pshare;pprog0; ptx0]} ptx0 ((PC @@ V0 ->r (pprog0 ^+ 32%nat)%f) ∗ (V0 -@A> {[pshare;pprog0; ptx0]}) ∗ (TX@V0:=ptx0))%I (R0 @@ V0 ->r run_I ∗ R1 @@ V0 ->r encode_vmid V1 ∗ addr ->a two  ∗ (∃ (wh : Addr), (∃ (β : mem), wh ->t (V0, V1, {[pshare]}, Sharing) ∗ wh ->re false ∗ (rx_state_mapsto V1 1 (Some (of_imm one, V0)) ∗ ⌜V0 ≠ V1⌝) ∗ RX@V1:=prx1 ∗ memory_page prx1 β ∗ ⌜β !! (of_imm i_prx1) = Some wh⌝) ∗
              VMProp V0 ((R0 @@ V0 ->r yield_I ∗ R1 @@ V0 ->r encode_vmid V1 ∗ addr ->a four ∗ wh ->t (V0, V1, {[pshare]}, Sharing) ∗ RX@V1:=prx1 ∗ (rx_state_mapsto V1 1 None ∗ True) ∗ (∃ mem_rx, memory_page prx1 mem_rx)) ∗
              VMProp V1 False%I (1/2)%Qp) (1/2)%Qp))%I True%I (pprog0 ^+ 31%nat)%f V1 True%I ((R0 @@ V0 ->r yield_I ∗ R1 @@ V0 ->r encode_vmid V1 ∗ addr ->a four ∗ wh ->t (V0, V1, {[pshare]}, Sharing) ∗ RX@V1:=prx1 ∗ (rx_state_mapsto V1 1 None ∗ True) ∗ (∃ mem_rx, memory_page prx1 mem_rx)) ∗ VMProp 1 False (1 / 2))%I) with "[PCz p_32 acc tx R0z R1z prop0 prop1 mem rxmem whretri whtans RX1page RX1st]").
    rewrite HIn.
    set_solver +.
    apply finz_succN_in_seq; simpl; lia.
    rewrite HIn. done.
    apply finz_succN_in_seq; simpl; lia.
    done.
    apply decode_encode_instruction.
    by rewrite decode_encode_hvc_func.
    by rewrite decode_encode_vmid.
    iSplitL "PCz p_32 acc tx R0z R1z".
    iFrame.
    iSplitL "prop1".
    iNext. simpl.
    iExact "prop1".
    iFrame "prop0".
    iSplit; last done.
    {
      iNext.
      iIntros "temp".
      iDestruct "temp" as "((PCz & _ & acc & tx & R0z & R1z) & _ & prop0)".
      iEval (rewrite finz_plus_one_simpl) in "PCz".
      rewrite Z_of_nat_simpl.
      iEval (simpl) in "PCz".
      iFrame.
      iExists wh.
      iSplitR "prop0".
      iExists β. simpl. iFrame.
      done.
      simpl.
      iFrame.
    }
    iModIntro.
    iIntros "[(PCz & acc & tx) prop0] Hholds".
    iDestruct (VMProp_holds_agree with "[Hholds prop0]") as "[P' prop0]".
    simpl.
    iFrame "Hholds prop0".
    iDestruct "P'" as "(P' & prop1)".
    iDestruct "P'" as "(>R0z & >R1z & >mem & >whtrans & >RX1page & >RX1st & >RX1mem)".
    rewrite wp_sswp.
    iApply ((@mov_word _ _ _ _ _ _ _ _ _ {[pshare;pprog0; ptx0]} ptx0 (pprog0 ^+ 32%nat)%f run_I R0) with "[p_33 PCz acc tx R0z]").
    apply decode_encode_instruction.
    rewrite HIn.
    set_solver +.
    apply finz_succN_in_seq; simpl; lia.
    rewrite HIn. done.
    apply finz_succN_in_seq; simpl; lia.
    iFrame.
    iModIntro.
    iIntros "(PCz & _ & acc & tx & R0z) _".
    rewrite wp_sswp.
    iEval (rewrite finz_plus_one_simpl) in "PCz".
    rewrite Z_of_nat_simpl.
    iEval (simpl) in "PCz".
    iApply ((@mov_word _ _ _ _ _ _ _ _ _ {[pshare;pprog0; ptx0]} ptx0 (pprog0 ^+ 33%nat)%f (encode_vmid V2) R1) with "[p_34 PCz acc tx R1z]").
    apply decode_encode_instruction.
    rewrite HIn.
    set_solver +.
    apply finz_succN_in_seq; simpl; lia.
    rewrite HIn. done.
    apply finz_succN_in_seq; simpl; lia.
    iFrame.
    iModIntro.
    iIntros "(PCz & _ & acc & tx & R1z) _".
    rewrite wp_sswp.
    iEval (rewrite finz_plus_one_simpl) in "PCz".
    rewrite Z_of_nat_simpl.
    iEval (simpl) in "PCz".    
    iApply ((@run _ _ _ _ _ hvc_I run_I (encode_vmid V2) 1%Qp {[pshare;pprog0; ptx0]} ptx0 ((PC @@ V0 ->r (pprog0 ^+ 35%nat)%f) ∗ (V0 -@A> {[pshare;pprog0; ptx0]}) ∗ (TX@V0:=ptx0))%I
               (vmprop_unknown V2 mtms_slice_trans mtms_slice_rxs ∅) ((R0 @@ V0 ->r yield_I ∗ R1 @@ V0 ->r encode_vmid V1 ∗ addr ->a finz.FinZ 4 four_obligation_1 four_obligation_2 ∗ wh ->t (V0, V1, {[pshare]}, Sharing) ∗ RX@V1:=prx1 ∗ (rx_state_mapsto V1 1 None ∗ True) ∗ (∃ mem_rx : mem, memory_page prx1 mem_rx)) ∗ VMProp 1 False (1 / 2))%I (pprog0 ^+ 34%nat)%f V2 (trans.fresh_handles 1 (valid_handles ∖ {[wh]}) ∗ (∃ mem_rx : mem, memory_page prx0 mem_rx) ∗ (∃ mem_rx : mem, memory_page prx1 mem_rx) ∗ (∃ mem_rx : mem, memory_page prx2 mem_rx) ∗ RX@V0:=prx0 ∗ RX@V1:=prx1 ∗ RX@V2:=prx2 ∗ rx_state_mapsto V0 1 None ∗ (rx_state_mapsto V1 1 None ∗ True) ∗ rx_state_mapsto V2 1 None ∗ ([∗ set] p ∈ {[pshare]}, p -@O> V0 ∗ p -@E> false) ∗ R2 @@ V0 ->r one)%I
               (vmprop_zero V2 mtms_slice_trans mtms_slice_rxs (<[wh := ((V0, V1, ({[pshare]} : gset PID), Sharing), true)]> ∅) (<[V2 := None]>(<[V1 := None]>(<[V0 := None]>∅))))%I) with "[PCz p_35 acc tx R0z R1z prop0 prop2 whfresh RX0page RX0mem RX0st RX1page RX1mem RX1st RX2page RX2mem RX2st R2z OE whtrans]").
    rewrite HIn.
    set_solver +.
    apply finz_succN_in_seq; simpl; lia.
    rewrite HIn. done.
    apply finz_succN_in_seq; simpl; lia.
    done.
    apply decode_encode_instruction.
    by rewrite decode_encode_hvc_func.
    by rewrite decode_encode_vmid.
    iFrame.
    {    
      iNext.
      iIntros "((PCz & _ & acc & tx & R0z & R1z) & (whfresh & RX0mem & RX1mem & RX2mem & RX0page & RX1page & RX2page & RX0st & RX1st & RX2st & OE & R2z) & prop0)".
      iEval (rewrite finz_plus_one_simpl) in "PCz".
      rewrite Z_of_nat_simpl.
      iEval (simpl) in "PCz".    
      iFrame.
      iApply vmprop_unknown_eq.
      iExists ({[wh := ((V0, V1, ({[pshare]} : gset PID), Sharing), true)]}), (<[V2 := None]>(<[V1 := None]>(<[V0 := None]>∅))).
      iSplit.
      iPureIntro.
      unfold trans_rel_secondary.
      split.
      rewrite map_filter_singleton_False.
      rewrite map_filter_empty.
      rewrite fmap_empty //.
      simpl.
      intros [? _]. done.
      rewrite map_filter_singleton_False.
      rewrite map_filter_empty //.
      intros [? _]. done.
      iSplitL "whfresh OE whtrans".
      unfold transaction_hpool_global_transferred.
      iExists (valid_handles ∖ {[wh]}). simpl.
      rewrite wheq.
      rewrite difference_diag_L.
      rewrite union_empty_l_L.
      iSplit.
      rewrite dom_singleton_L //.
      rewrite big_opM_singleton.
      rewrite elem_of_singleton.
      simpl.
      rewrite bool_decide_eq_false_2.
      unfold pgt_3_4. unfold pgt.
      rewrite !big_opS_singleton.
      unfold valid_transaction.
      simpl.
      iFrame.
      iSplitL "whtrans".
      iDestruct "whtrans" as "(whtrans & %P1 & %P2)".
      iSplit.
      rewrite trans_mapsto_eq /trans_mapsto_def.            
      iDestruct (ghost_map_elem_split with "whtrans") as "[H1 H2]".
      iFrame.
      iPureIntro.
      split; done.            
      iDestruct "OE" as "(O & E)".
      iDestruct (own_split with "O") as "(O1 & O2)".
      iDestruct (own_split with "O2") as "(O2 & O3)".
      iDestruct (excl_split with "E") as "(E1 & E2)".
      iDestruct (excl_split with "E2") as "(E2 & E3)".
      rewrite half_of_half.
      iFrame.
      intros contra; contradiction.
      iSplitR.
      rewrite transferred_only_equiv.
      unfold transaction_pagetable_entries_transferred.
      rewrite big_sepFM_insert_False.
      iSplitR. iApply big_sepFM_empty.
      2: {
        intros contra.
        destruct contra; discriminate.
      }
      2: apply lookup_empty.
      iSplitR.
      unfold retrievable_transaction_transferred.
      iSplitL.
      rewrite big_sepFM_insert_False.
      iApply big_sepFM_empty.
      intros contra.
      destruct contra; discriminate.
      apply lookup_empty.
      rewrite big_sepFM_insert_False.
      iApply big_sepFM_empty.
      intros contra.
      destruct contra; discriminate.
      apply lookup_empty.
      iExists ∅.
      unfold memory_pages.
      iSplit; last done.
      iPureIntro.
      unfold transferred_memory_pages.
      rewrite dom_empty_L.
      rewrite map_filter_singleton_False.
      rewrite pages_in_trans_empty.
      rewrite set_of_addr_empty //.
      intros contra.
      destruct contra as [contra ?].
      destruct contra; discriminate.
      {
        intros. rewrite /mtms_slice_trans //.
      }
      {
        rewrite /trans_neq.
        rewrite map_Forall_singleton.
        simpl. done.
      }
      {
        rewrite /trans_ps_disj.
        rewrite /inv_trans_ps_disj'.
        rewrite /lift_option_gmap.
        rewrite map_fmap_singleton.
        rewrite map_Forall_singleton.
        rewrite delete_singleton.
        rewrite /pages_in_trans'.
        rewrite map_fold_empty.
        set_solver +.
      }
      iSplitL "R0z".
      iExists run_I.
      iFrame.
      iPureIntro.
      apply decode_encode_hvc_func.
      iSplitL "R1z".
      iExists (encode_vmid V2).
      iFrame.
      iPureIntro.
      apply decode_encode_vmid.
      iSplitL "R2z".
      iExists one.
      iFrame.
      iSplitL "RX2mem RX2page RX2st".
      iIntros.
      rewrite lookup_insert in H.
      inversion H. subst rs.
      unfold rx_state_match.
      iFrame.
      iExists prx2.
      iFrame.
      iSplitR "prop0".
      unfold rx_states_global.
      rewrite delete_insert.
      unfold rx_state_match.
      rewrite insert_empty.
      rewrite big_opM_insert_delete.
      iFrame "RX1st".
      iSplitL "RX1page RX1mem".
      iExists prx1.
      iFrame.
      assert (delete V1 {[V0 := None]} = {[V0 := None]}) as ->.
      {
        rewrite delete_notin.
        reflexivity.
        apply lookup_singleton_ne.
        done.
      }
      rewrite big_opM_singleton.
      iSplitL "RX0st"; first iFrame.
      iExists prx0.
      iFrame.
      rewrite insert_empty.
      rewrite lookup_insert_None.
      split; last done.
      by apply lookup_singleton_ne.
      iSplit.
      iPureIntro.
      unfold base_extra.is_total_gmap.
      intros k.
      rewrite insert_empty.
      pose proof (in_list_of_vmids k) as G.
      unfold list_of_vmids in G.
      rewrite /vm_count /mtms_vmconfig /= in G.
      simpl.
      rewrite /V2 /V1 /V0 /=.
      destruct G as [<- | [<- | [<- | ?]]]; last contradiction; done.
      iFrame.
    }
    iModIntro.
    iIntros "[(PCz & acc & tx) prop0] Hholds".
    iDestruct (VMProp_holds_agree with "[Hholds prop0]") as "[P' prop0]".
    simpl.
    iFrame "Hholds prop0".
    (* getting back resources *)
    rewrite wp_sswp.
    clear -HIn Hnottx.
    iApply ((halt (pprog0 ^+ 35%nat)%f) with "[PCz p_36 acc tx]"); iFrameAutoSolve.
    rewrite HIn.
    set_solver +.
    apply finz_succN_in_seq; simpl; lia.
    rewrite HIn. done.
    apply finz_succN_in_seq; simpl; lia.
    iNext.
    iIntros "(PCz & _ & acc & tx)".
    iIntros "_".
    iApply wp_terminated'; eauto.
    iFrame.
    iEval (rewrite finz_plus_one_simpl) in "PCz".
    rewrite Z_of_nat_simpl.
    iEval (simpl) in "PCz".
    iSplit; first done.
    done.
  Qed.

  Lemma mtms_machine1 :
    (* Addresses-values connection *)
    seq_in_page (of_pid pprog1) (length mtms_program1) pprog1 ->
    (* Mem for program *)
    (program (mtms_program1) (of_pid pprog1)) ∗
    (* TX mem *)
    (∃ txmem, memory_page ptx1 txmem) ∗
    V1 -@A> {[pprog1;ptx1;prx1]} ∗
    (* TX page *)            
    TX@ V1 := ptx1 ∗
    (* Program counter *)                      
    PC @@ V1 ->r (of_pid pprog1) ∗
    (* Work registers *)                        
    (∃ r0, R0 @@ V1 ->r r0) ∗
    (∃ r1, R1 @@ V1 ->r r1) ∗
    (∃ r2, R2 @@ V1 ->r r2) ∗            
    (∃ r3, R3 @@ V1 ->r r3) ∗
    (∃ r4, R4 @@ V1 ->r r4) ∗
    (∃ r5, R5 @@ V1 ->r r5) ∗                        
    VMProp V1 (R0 @@ V0 ->r run_I ∗ R1 @@ V0 ->r encode_vmid V1 ∗ addr ->a two  ∗ (∃ (wh : Addr), (∃ (β : mem), wh ->t (V0, V1, {[pshare]}, Sharing) ∗
               wh ->re false ∗ RX_state@V1 := Some (of_imm one, V0) ∗ RX@V1:=prx1 ∗ memory_page prx1 β ∗ ⌜β !! (of_imm i_prx1) = Some wh⌝) ∗
      VMProp V0 ((R0 @@ V0 ->r yield_I ∗ R1 @@ V0 ->r encode_vmid V1 ∗ addr ->a four ∗ wh ->t (V0, V1, {[pshare]}, Sharing) ∗ RX@V1:=prx1 ∗ RX_state@V1 := None ∗ (∃ mem_rx, memory_page prx1 mem_rx)) ∗
        VMProp V1 False%I (1/2)%Qp) (1/2)%Qp))%I (1/2)%Qp
    ⊢ VMProp_holds V1 (1/2)%Qp -∗ WP ExecI @ V1 {{ (λ m, False) }}%I.
  Proof.
    iIntros (HIn) "((p_1 & p_2 & p_3 & p_4 & p_5 & p_6 & p_7
            & p_8 & p_9 & p_10 & p_11 & p_12 & p_13 & p_14 & _)
         & (%txmemgm & txmem) & acc & tx & PCs & (%r0 & R0s) & (%r1 & R1s) & (%r2 & R2s)
         & (%r3 & R3s) & (%r4 & R4s) & (%r5 & R5s) 
         & prop1)".
    iIntros "Hholds".
    iDestruct (VMProp_holds_agree V1 with "[Hholds prop1]") as "[P prop1]".
    iFrame.
    pose proof (seq_in_page_forall2 _ _ _ HIn) as Hforall.
    fold_finz_plus_one.
    repeat (rewrite finz_succN_correct).
    clear HIn; rename Hforall into HIn.
    assert (pprog1 ≠ ptx1) as Hnottx.
    {
      intros Heq.
      feed pose proof (NoDup_lookup _ 1 5 ptx1 Hps_nd).
      rewrite Heq. done.
      rewrite Heq. done.
      lia.
    }
    rewrite wp_sswp.
    iDestruct "P" as "(R0z & R1z & mem & temp)".
    iApply ((mov_word (of_pid pprog1) i_prx1 R5) with "[p_1 PCs acc tx R5s]"); iFrameAutoSolve.
    rewrite to_pid_aligned_eq.
    set_solver +.
    rewrite to_pid_aligned_eq.
    done.
    iNext.
    iDestruct "temp" as "(%wh & (%rxmem & (whtrans & whretri & RX1st & RX1page & RX1mem & %Hrxmem)) & prop0)".
    iIntros "(PCs & _ & acc & tx & R5s) _".
    rewrite wp_sswp.
    iEval (unfold memory_page) in "RX1mem".
    iDestruct "RX1mem" as "(%rxmemdom & RX1mem)".
    iDestruct (@mem_big_sepM_split_upd _ _ i_prx1 wh with "RX1mem") as "(rxbase & rxmemacc)"; auto.
    rewrite -Heq_prx1.
    iApply ((ldr (p := ptx1) (w1 := ldr_I R4 R5) (s := {[pprog1; ptx1; prx1]}) (w2 := wh) (w3 := r4) (q := 1%Qp) (pprog1 ^+ 1)%f i_prx1 R4 R5) with "[PCs p_2 acc tx R4s R5s rxbase]").
    by rewrite decode_encode_instruction.
    rewrite -Heq_prx1.
    rewrite to_pid_aligned_eq.
    rewrite HIn.
    set_solver +.
    set_solver +.
    rewrite -Heq_prx1.
    rewrite to_pid_aligned_eq.
    {
      intros Heq.
      feed pose proof (NoDup_lookup _ 5 8 ptx1 Hps_nd).
      rewrite Heq. done.
      rewrite Heq. done.
      lia.
    }
    rewrite HIn. done.
    set_solver +.
    rewrite -Heq_prx1.
    iFrame.
    iModIntro.
    iIntros "(PCs & _ & R5s & rxbase & R4s & acc & tx) _".
    rewrite wp_sswp.
    iEval (repeat (rewrite finz_succN_one)) in "PCs".
    iEval (repeat (rewrite finz_succN_idemp)) in "PCs".
    iEval (simpl) in "PCs".
    iEval (repeat (rewrite finz_succN_correct)) in "PCs".
    iApply ((mov_word (w3 := r0) (p_tx := ptx1) (w1 := mov_word_I R0 msg_poll_I) (q := 1%Qp) (s := {[pprog1; ptx1; prx1]}) (pprog1 ^+ 2%nat)%f msg_poll_I R0) with "[p_3 PCs acc tx R0s]").
    by rewrite decode_encode_instruction.
    rewrite HIn.
    set_solver +.
    apply finz_succN_in_seq; simpl; lia.
    rewrite HIn. done.
    apply finz_succN_in_seq; simpl; lia.
    iFrame.
    iModIntro.
    iIntros "(PCs & _ & acc & tx & R0s) _".
    rewrite wp_sswp.
    iEval (rewrite finz_plus_one_simpl) in "PCs".
    rewrite Z_of_nat_simpl.
    iEval (simpl) in "PCs".
    iApply ((msg_poll_full (r0 := msg_poll_I) (r1 := r1) (r2 := r2) (wi := hvc_I) (l := one) (i := V1) (j := V0) (p_tx := ptx1) (q := 1%Qp) (s := {[pprog1; ptx1; prx1]}) (pprog1 ^+ 3%nat)%f) with "[p_4 PCs acc tx R0s R1s R2s RX1st]").
    do 2 apply elem_of_union_l.
    apply elem_of_singleton_2.    
    rewrite HIn.
    reflexivity.
    apply finz_succN_in_seq; simpl; lia.
    rewrite HIn.
    assumption.
    apply finz_succN_in_seq; simpl; lia.
    by rewrite decode_encode_instruction.
    by rewrite decode_encode_hvc_func.
    iFrame.
    iModIntro.
    iIntros "(PCs & _ & tx & acc & R0s & R1s & R2s & RX1st & _) _".
    rewrite wp_sswp.
    iEval (rewrite finz_plus_one_simpl) in "PCs".
    rewrite Z_of_nat_simpl.
    iEval (simpl) in "PCs".
    iApply ((@mov_reg _ _ _ _ _ _ _ wh 1%Qp {[pprog1; ptx1; prx1]} ptx1 (pprog1 ^+ 4%nat)%f one R1 R4) with "[PCs p_5 acc tx R1s R4s]").
    apply decode_encode_instruction.
    do 2 apply elem_of_union_l.    
    apply elem_of_singleton_2.
    apply HIn.
    apply finz_succN_in_seq; simpl; lia.
    rewrite HIn. done.
    apply finz_succN_in_seq; simpl; lia.
    iFrame.
    iModIntro.
    iIntros "(PCs & _ & acc & tx & R1s & R4s) _".
    rewrite wp_sswp.
    iEval (rewrite finz_plus_one_simpl) in "PCs".
    rewrite Z_of_nat_simpl.
    iEval (simpl) in "PCs".
    iApply ((@mov_word _ _ _ _ _ _ _ _ _ {[pprog1; ptx1; prx1]} ptx1 (pprog1 ^+ 5%nat)%f mem_retrieve_I R0) with "[p_6 PCs acc tx R0s]").
    apply decode_encode_instruction.
    rewrite HIn.
    set_solver +.
    apply finz_succN_in_seq; simpl; lia.
    rewrite HIn. done.
    apply finz_succN_in_seq; simpl; lia.
    iFrame.
    iModIntro.
    iIntros "(PCs & _ & acc & tx & R0s) _".
    rewrite wp_sswp.
    iEval (rewrite finz_plus_one_simpl) in "PCs".
    rewrite Z_of_nat_simpl.
    iEval (simpl) in "PCs".
    rewrite -Heq_prx1.
    iSpecialize ("rxmemacc" $! wh with "rxbase").
    iApply ((mem_retrieve_share (sacc := {[pprog1; ptx1; prx1]}) (p_tx := ptx1) (pprog1 ^+ 6%nat)%f wh) with "[PCs p_7 R0s R1s acc tx whretri whtrans RX1page RX1st rxmemacc]").
    rewrite HIn. done.
    apply finz_succN_in_seq; simpl; lia.
    rewrite HIn.
    set_solver +.
    apply finz_succN_in_seq; simpl; lia.
    apply decode_encode_instruction.
    apply decode_encode_hvc_func.
    iFrame "PCs p_7 R0s R1s acc tx RX1st".
    iFrame "whretri". iSplitL "whtrans".
    iExact "whtrans".
    iSplitL "RX1page". iExact "RX1page".
    rewrite /memory_page. iSplit.
    2: { iExact "rxmemacc". }
    iPureIntro.
    rewrite -rxmemdom.
    rewrite !dom_insert_lookup_L;cbn. done.
    rewrite -?elem_of_dom;
      try rewrite !dom_insert_lookup_L -?elem_of_dom.
    rewrite rxmemdom.
    rewrite elem_of_list_to_set.
    rewrite elem_of_addr_of_page_iff.
    rewrite to_pid_aligned_eq //.
    iNext.
    iIntros "(PCs & _ & R0s & R1s & acc & tx & whretri & whtrans & RX1page & (%l & %des & (RX1st & _) & %deslen & %desshape & RX1mem)) _".
    rewrite wp_sswp.
    iEval (rewrite finz_plus_one_simpl) in "PCs".
    rewrite Z_of_nat_simpl.
    iEval (simpl) in "PCs".
    iApply ((@mov_word _ _ _ _ _ _ _ _ _ ({[pshare]} ∪ {[pprog1; ptx1; prx1]}) ptx1 (pprog1 ^+ 7%nat)%f four R3) with "[p_8 PCs acc tx R3s]").
    apply decode_encode_instruction.
    rewrite HIn.
    set_solver +.
    apply finz_succN_in_seq; simpl; lia.
    rewrite HIn. done.
    apply finz_succN_in_seq; simpl; lia.
    iFrame.
    iModIntro.
    iIntros "(PCs & _ & acc & tx & R3s) _".
    rewrite wp_sswp.
    iEval (rewrite finz_plus_one_simpl) in "PCs".
    rewrite Z_of_nat_simpl.
    iEval (simpl) in "PCs".
    iApply ((@mov_word _ _ _ _ _ _ _ _ _ ({[pshare]} ∪ {[pprog1; ptx1; prx1]}) ptx1 (pprog1 ^+ 8%nat)%f addr R5) with "[p_9 PCs acc tx R5s]").
    apply decode_encode_instruction.
    rewrite HIn.
    set_solver +.
    apply finz_succN_in_seq; simpl; lia.
    rewrite HIn. done.
    apply finz_succN_in_seq; simpl; lia.
    iFrame.
    iModIntro.
    iIntros "(PCs & _ & acc & tx & R5s) _".
    rewrite wp_sswp.
    iEval (rewrite finz_plus_one_simpl) in "PCs".
    rewrite Z_of_nat_simpl.
    iEval (simpl) in "PCs".
    iApply ((@str _ _ _ _ _ _ _ four two 1%Qp prx1 ptx1 ({[pshare]} ∪ {[pprog1; ptx1; prx1]}) (pprog1 ^+ 9%nat)%f addr R3 R5) with "[p_10 PCs acc mem RX1page tx R3s R5s]").
    apply decode_encode_instruction.
    rewrite -Heq_pshare.
    rewrite to_pid_aligned_eq.
    rewrite (finz_succN_pid' pprog1 9);[|lia].
    set_solver +.
    rewrite HIn. done.
    apply finz_succN_in_seq; simpl; lia.
    rewrite -Heq_pshare.
    rewrite to_pid_aligned_eq.
    {
      intros Heq.
      feed pose proof (NoDup_lookup _ 3 8 prx1 Hps_nd).
      rewrite Heq. done.
      rewrite Heq. done.
      lia.
    }
    iFrame.
    iModIntro.
    iIntros "(PCs & _ & R5s & mem & R3s & acc & tx & RX1page) _".
    rewrite wp_sswp.
    iEval (rewrite finz_plus_one_simpl) in "PCs".
    rewrite Z_of_nat_simpl.
    iEval (simpl) in "PCs".
    iApply ((mov_word (w3 := encode_hvc_ret_code Succ) (p_tx := ptx1) (w1 := mov_word_I R0 msg_poll_I) (q := 1%Qp) (s := {[pshare]} ∪ {[pprog1; ptx1; prx1]}) (pprog1 ^+ 10%nat)%f msg_poll_I R0) with "[p_11 PCs acc tx R0s]").
    by rewrite decode_encode_instruction.
    rewrite HIn.
    set_solver +.
    apply finz_succN_in_seq; simpl; lia.
    rewrite HIn. done.
    apply finz_succN_in_seq; simpl; lia.
    iFrame.
    iModIntro.
    iIntros "(PCs & _ & acc & tx & R0s) _".
    rewrite wp_sswp.
    iEval (rewrite finz_plus_one_simpl) in "PCs".
    rewrite Z_of_nat_simpl.
    iEval (simpl) in "PCs".
    iApply ((msg_poll_full (r0 := msg_poll_I) (r1 := wh) (r2 := encode_vmid V0) (wi := hvc_I) (l := l) (i := V1) (j := V0) (p_tx := ptx1) (q := 1%Qp) (s := {[pshare]} ∪ {[pprog1; ptx1; prx1]}) (pprog1 ^+ 11%nat)%f) with "[p_12 PCs acc tx R0s R1s R2s RX1st]").
    rewrite HIn.
    set_solver +.
    apply finz_succN_in_seq; simpl; lia.
    rewrite HIn. done.
    apply finz_succN_in_seq; simpl; lia.
    by rewrite decode_encode_instruction.
    by rewrite decode_encode_hvc_func.
    iFrame.
    done.
    iModIntro.
    iIntros "(PCs & _ & tx & acc & R0s & R1s & R2s & RX1st & _) _".
    rewrite wp_sswp.
    iEval (rewrite finz_plus_one_simpl) in "PCs".
    rewrite Z_of_nat_simpl.
    iEval (simpl) in "PCs".
    iApply ((@mov_word _ _ _ _ _ _ _ _ _ ({[pshare]} ∪ {[pprog1; ptx1; prx1]}) ptx1 (pprog1 ^+ 12%nat)%f yield_I R0) with "[p_13 PCs acc tx R0s]").
    apply decode_encode_instruction.
    rewrite HIn.
    set_solver +.
    apply finz_succN_in_seq; simpl; lia.
    rewrite HIn. done.
    apply finz_succN_in_seq; simpl; lia.
    iFrame.
    iModIntro.
    iIntros "(PCs & _ & acc & tx & R0s) _".
    rewrite wp_sswp.
    iEval (rewrite finz_plus_one_simpl) in "PCs".
    rewrite Z_of_nat_simpl.
    iEval (simpl) in "PCs".
    iApply ((yield (s := {[pshare]} ∪ {[pprog1; ptx1; prx1]}) (p_tx := ptx1) (pprog1 ^+ 13%nat)%f True False%I) with "[PCs p_14 acc tx R0s R0z R1z prop0 prop1 mem whtrans RX1page RX1st RX1mem]").
    rewrite HIn.
    set_solver +.
    apply finz_succN_in_seq; simpl; lia.
    rewrite HIn. done.
    apply finz_succN_in_seq; simpl; lia.
    done.
    apply decode_encode_instruction.
    apply decode_encode_hvc_func.
    {
      iSplitL "PCs p_14 acc tx R0s R0z R1z".
      iFrame.
      iSplitL "prop0". iExact "prop0".
      iSplitL "prop1". iExact "prop1".
      iSplit; last done.
      iNext.
      iIntros "((H1 & H2 & H3 & H4 & H5 & H6 & H7) & _ & H8)".
      iFrame.
      iSplitL "RX1mem".
      match goal with
        |- context G [memory_page _ ?a] => set m := a
      end.
      iExists m.
      iFrame "RX1mem".
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

  Definition mtms_interp_access2 := interp_access (V2 : leibnizO VMID)
                                                  mtms_slice_trans mtms_slice_rxs
                                      ptx2 prx2 {[pprog2; ptx2; prx2]} ∅.


  Lemma mtms_ftlr2 : mtms_interp_access2 ⊢ interp_execute V2.
  Proof. iApply ftlr. Qed.
End proof.
