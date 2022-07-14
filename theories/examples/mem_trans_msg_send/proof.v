From machine_program_logic.program_logic Require Import weakestpre.
From HypVeri.algebra Require Import base mem.
From HypVeri.rules Require Import rules_base mov halt run yield mem_send mem_retrieve mem_relinquish mem_reclaim ldr str msg_send msg_wait msg_poll add.
From HypVeri.examples Require Import instr utils.
From HypVeri.logrel Require Import logrel logrel_extra.
From HypVeri Require Import proofmode machine_extra.
Require Import Setoid.

Section proof.

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


Local Program Instance rywu_vmconfig : HypervisorConstants :=
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

  Context `{hypparams: !HypervisorParameters}.

  Definition lending_program0 (addr tx_base : Imm) : list Word :=
    [
      (* Store 2 to mem *)
      mov_word_I R4 two;
      mov_word_I R5 addr;
      str_I R4 R5;
      (* Memory descriptor *)
      mov_word_I R5 tx_base;
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
      mov_word_I R5 tx_base;
      str_I R2 R5;
      mov_reg_I R3 R2;
      mov_word_I R0 msg_send_I;
      mov_word_I R1 (encode_vmid V1);
      mov_word_I R2 one;
      hvc_I;
      (* (* Run VM 2 (unknown vm *) *)
      (* mov_word_I R0 run_I; *)
      (* mov_word_I R1 (encode_vmid V2); *)
      (* hvc_I; *)
      (* Run VM 1 *)
      mov_word_I R0 run_I;
      mov_word_I R1 (encode_vmid V1);
      hvc_I;
      (* (* Reclaim page *) *)
      (* mov_word_I R0 mem_reclaim_I; *)
      (* mov_reg_I R1 R3; *)
      (* hvc_I; *)
      (* Run VM 2 (unknown vm *)
      mov_word_I R0 run_I;
      mov_word_I R1 (encode_vmid V2);
      hvc_I;
      (* Stop *)
      halt_I
    ].

  Definition lending_program1 (addr rx_base : Imm) : list Word :=
    [
      (* Fetch handle *)
      mov_word_I R5 rx_base;
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
      (* (* Relinquish page *) *)
      (* mov_word_I R0 mem_relinquish_I; *)
      (* mov_reg_I R1 R4; *)
      (* hvc_I; *)
      (* Yield back *)
      mov_word_I R0 yield_I;
      hvc_I
    ].

  (* Lemma tpa_plus_one_simple : ∀ p, tpa (p ^+ 1)%f = tpa p. *)
  (* Proof. *)
  (*   intros p. *)
    
  (* Qed. *)

  Context `{!gen_VMG Σ}.
  Notation VMProp_2 (* p_tx p_rx *) := (vmprop_unknown V2 (* p_tx p_rx  *) ∅) (only parsing).


  Lemma lending_machine0 p_pg0 (p_tx0 : PID) p_pg2 p_tx2 p_rx0 p_rx1 p_rx2 (addr : Imm) p_tx0imm (p_rx1imm p_pg0imm : Imm) :
    let RX0 := (RX_state@V0 := None ∗ mailbox.rx_page V0 p_rx0 ∗ ∃ mem_rx, memory_page p_rx0 mem_rx)%I in
    let RX1 := (RX_state@V1 := None ∗ mailbox.rx_page V1 p_rx1 ∗ ∃ mem_rx, memory_page p_rx1 mem_rx)%I in
    let RX2 := (RX_state@V2 := None ∗ mailbox.rx_page V2 p_rx2 ∗ ∃ mem_rx, memory_page p_rx2 mem_rx)%I in
    let program0 := lending_program0 addr p_tx0imm in
    of_pid (tpa addr) = addr ->
    (* Disjoint pages *)
    (of_pid p_tx0 = p_tx0imm) ->
    (of_pid p_rx1 = p_rx1imm) ->
    (of_pid p_pg0 = p_pg0imm) ->
    (p_pg0 ∉ ({[(tpa addr); p_tx0; p_pg2; p_tx2; p_rx2]}:gset _)) ->
    tpa addr ≠ p_rx0 ->
    tpa addr ≠ p_pg0 ->
    tpa addr ≠ p_tx0 ->
    p_tx0 ≠ p_rx0 ->
    (* Addresses-values connection *)
    seq_in_page (of_pid p_pg0) (length program0) p_pg0 ->
    (* Mem for program *)
    (program (program0) (of_pid p_pg0)) ∗
      (* Work mem *)
      (∃ w, addr ->a w) ∗
      (* TX mem *)
      (* (∃ (v1 v2 v3 v4 v5 : Word), ([∗ list] a;w ∈ (finz.seq p_tx0 5);[v1; v2; v3; v4; v5], (a ->a w))) ∗ *)
      (∃ txmem, memory_page (tpa p_tx0) txmem) ∗
      (* Pages for VM 0 *)
      ([∗ set] p ∈ {[tpa addr]}, p -@O> V0 ∗ p -@E> true) ∗
      V0 -@A> (union (singleton (tpa addr)) (union (singleton p_pg0) (singleton (tpa p_tx0)))) ∗
      (* TX page *)            
      TX@ V0 := (tpa p_tx0) ∗
      (* Program counter *)                      
      PC @@ V0 ->r (of_pid p_pg0) ∗
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
      VMProp V1 (R0 @@ V0 ->r run_I ∗ R1 @@ V0 ->r encode_vmid V1 ∗ addr ->a two  ∗ (∃ (wh : Addr) (β : mem), (trans_mapsto wh (DfracOwn 1) (Some (V0, V1, singleton (tpa addr), Sharing)) ∗ ⌜valid_transaction (V0, V1, singleton (tpa addr), Sharing)⌝) ∗
                                                                                    retri_mapsto wh (DfracOwn 1) (Some false) ∗ rx_state_mapsto V1 1 (Some (of_imm one, V0)) ∗ ⌜V0 ≠ V1⌝ ∗ RX@V1:=p_rx1 ∗ memory_page p_rx1 β ∗ ⌜β !! (of_imm p_rx1imm) = Some wh⌝) ∗
                    VMProp V0 ((R0 @@ V0 ->r yield_I ∗ R1 @@ V0 ->r encode_vmid V1 ∗ addr ->a four) ∗
                                 VMProp V1 False%I (1/2)%Qp) (1/2)%Qp)%I (1/2)%Qp ∗
      (* Protocol for unknown vm *)
      VMProp V2 (VMProp_2 (* p_tx2 p_rx2 *)) (1/2)%Qp ∗
      (* Pages for unknown VM *)            
      V2 -@{1/2}A> {[p_pg2;p_tx2;p_rx2]} ∗
      trans.fresh_handles 1 valid_handles ∗
      (* RX states *)               
      RX0 ∗ RX1 ∗ RX2 
      ⊢ WP ExecI @ V0
            {{ (λ m,
                 ⌜m = HaltI⌝ ∗
                 (* program program0 (of_pid p_pg0) ∗ *)
                 addr ->a four ∗       
                 V0 -@A> (union (singleton (tpa addr)) (union (singleton p_pg0) (singleton (tpa p_tx0)))) ∗
                 TX@ V0 := (tpa p_tx0) ∗
                 PC @@ V0 ->r ((of_pid p_pg0) ^+ (length program0))%f ∗
                 R0 @@ V0 ->r yield_I ∗
                 R1 @@ V0 ->r encode_vmid V2
                 )}}%I.
  Proof.
    rewrite /vmprop_unknown.
    iIntros (Haddr Htxeq Hrxeq Hpgeq HnIn_p HneAddr_RX0 HneAddr_PG0 HneAddr_TX0 HneTX0_RX0 HIn) "((p_1 & p_2 & p_3 & p_4 & p_5 & p_6 & p_7 
            & p_8 & p_9 & p_10 & p_11 & p_12 & p_13 & p_14 & p_15 & p_16 
            & p_17 & p_18 & p_19 & p_20 & p_21 & p_22 & p_23 & p_24 & p_25
            & p_26 & p_27 & p_28 & p_29 & p_30 & p_31 & p_32 & p_33 & p_34
            & p_35 & p_36 & _) 
         & (%memv & mem) & (%txmemgm & txmem) & OE & acc & tx & PCz & (%r0 & R0z) & (%r1 & R1z) & (%r2 & R2z) 
         & (%r3 & R3z) & (%r4 & R4z) & (%r5 & R5z) 
         & prop0 & prop1 & prop2 & acc2 & hp & ((RX0st & _) & (RX0page & RX0own & RX0excl) & RX0mem)
         & ((RX1st & _) & (RX1page & RX1own & RX1excl) & RX1mem) & ((RX2st & _) & (RX2page & RX2own & RX2excl) & RX2mem))". 
   pose proof (seq_in_page_forall2 _ _ _ HIn) as Hforall.
    fold_finz_plus_one.
    repeat (rewrite finz_succN_correct).
    (* iEval (rewrite finz_succN_one) in "p_2". *)
    clear HIn; rename Hforall into HIn.
    assert (p_pg0 ≠ p_tx0) as Hnottx. set_solver + HnIn_p.
    (* mov_word_I R4 two *)
    rewrite wp_sswp.    
    iApply ((mov_word (of_pid p_pg0) two R4) with "[p_1 PCz acc tx R4z]"); iFrameAutoSolve.
    apply elem_of_union_r.
    apply elem_of_union_l.
    apply elem_of_singleton_2.
    apply to_pid_aligned_eq.
    rewrite HIn.
    rewrite to_pid_aligned_eq.
    assumption.
    set_solver +.
    iModIntro.
    iIntros "(PCz & _ & acc & tx & R4z) _".    
    (* mov_word_I R5 addr *)
    rewrite wp_sswp.
    iApply ((mov_word _ addr R5) with "[p_2 PCz acc tx R5z]"); iFrameAutoSolve.
    rewrite HIn.
    set_solver +.
    set_solver +.
    rewrite HIn.
    rewrite to_pid_aligned_eq.
    assumption.
    set_solver +.
    iModIntro.
    iIntros "(PCz & _ & acc & tx & R5z) _".
    (* str_I R4 R5 *)
    rewrite wp_sswp.    
    iEval (repeat (rewrite finz_succN_one)) in "PCz".
    iEval (repeat (rewrite finz_succN_idemp)) in "PCz".
    iEval (simpl) in "PCz".
    iEval (repeat (rewrite finz_succN_correct)) in "PCz".
    iApply ((str _ addr R4 R5) with "[p_3 PCz acc mem RX0page tx R4z R5z]"); iFrameAutoSolve.
    apply union_mono_l.
    apply union_subseteq_l'.
    rewrite singleton_subseteq.    
    rewrite HIn.
    reflexivity.
    apply finz_succN_in_seq.
    simpl.
    lia.
    rewrite HIn.
    rewrite to_pid_aligned_eq.
    intros contra.
    contradiction.
    apply finz_succN_in_seq; simpl; lia.
    iModIntro.
    iIntros "(PCz & _ & R5z & mem & R4z & acc & tx & RX0page) _".
    (* mov_word_I R5 tx_addr *)
    rewrite wp_sswp.
    iEval (rewrite finz_plus_one_simpl) in "PCz".
    rewrite Z_of_nat_simpl.
    iEval (simpl) in "PCz".
    iApply ((mov_word _ p_tx0imm R5) with "[p_4 PCz acc tx R5z]"); iFrameAutoSolve.
    rewrite HIn.
    set_solver +.
    apply finz_succN_in_seq; simpl; lia.
    rewrite HIn.
    rewrite to_pid_aligned_eq.
    assumption.
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
    rewrite HIn.
    rewrite to_pid_aligned_eq.
    assumption.
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
    rewrite to_pid_aligned_eq.
    assumption.
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
    iDestruct (@mem_big_sepM_split_upd5 _ txmemgm p_tx0imm (p_tx0 ^+ 1)%f ((p_tx0 ^+ 1) ^+ 1)%f (((p_tx0 ^+ 1) ^+ 1) ^+ 1)%f ((((p_tx0 ^+ 1) ^+ 1) ^+ 1) ^+ 1)%f with "txmem") as "txmem".
    {
      rewrite <-Htxeq.
      intros contra.
      clear -contra.
      destruct p_tx0.
      simpl in *.
      destruct z.
      simpl in *.
      unfold finz.incr_default in contra.
      destruct (finz.FinZ z finz_lt finz_nonneg + 1)%f eqn:Heqn.
      destruct f.
      simplify_eq.
      solve_finz.
      clear -align Heqn.
      unfold finz.incr in Heqn.
      repeat case_match; simplify_eq.
      solve_finz.
      apply n.
      simpl.
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
      lia.
    }
    {
      rewrite <-Htxeq.
      intros contra.
      clear -contra.
      destruct p_tx0.
      simpl in *.
      destruct z.
      simpl in *.
      unfold finz.incr_default in contra.
      destruct (finz.FinZ z finz_lt finz_nonneg + 1)%f eqn:Heqn.
      destruct f.
      simplify_eq.
      solve_finz.
      clear -align Heqn.
      unfold finz.incr in Heqn.
      repeat case_match; simplify_eq.
      solve_finz.
      apply n.
      simpl.
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
      lia.
    }
    {
      rewrite <-Htxeq.
      intros contra.
      clear -contra.
      destruct p_tx0.
      simpl in *.
      destruct z.
      simpl in *.
      unfold finz.incr_default in contra.
      destruct (finz.FinZ z finz_lt finz_nonneg + 1)%f eqn:Heqn.
      destruct f.
      simplify_eq.
      solve_finz.
      clear -align Heqn.
      unfold finz.incr in Heqn.
      repeat case_match; simplify_eq.
      solve_finz.
      apply n.
      simpl.
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
      lia.
    }
    {
      rewrite <-Htxeq.
      intros contra.
      clear -contra.
      destruct p_tx0.
      simpl in *.
      destruct z.
      simpl in *.
      unfold finz.incr_default in contra.
      destruct (finz.FinZ z finz_lt finz_nonneg + 1)%f eqn:Heqn.
      destruct f.
      simplify_eq.
      solve_finz.
      clear -align Heqn.
      unfold finz.incr in Heqn.
      repeat case_match; simplify_eq.
      solve_finz.
      apply n.
      simpl.
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
      lia.
    }
    {
      intros contra.
      clear -contra.
      destruct p_tx0.
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
      solve_finz.
    }
    {
      intros contra.
      clear -contra.
      destruct p_tx0.
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
      solve_finz.
    }
    {
      intros contra.
      clear -contra.
      destruct p_tx0.
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
      solve_finz.
    }
    {
      intros contra.
      clear -contra.
      destruct p_tx0.
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
      solve_finz.
    }
    {
      intros contra.
      clear -contra.
      destruct p_tx0.
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
      solve_finz.
    }
    {
      intros contra.
      clear -contra.
      destruct p_tx0.
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
      solve_finz.
    }
    {
      rewrite <-elem_of_dom.
      rewrite domtxmem.
      rewrite elem_of_list_to_set.
      rewrite Htxeq.        
      apply elem_of_addr_of_page_tpa.
    }
    {
      rewrite <-elem_of_dom.
      rewrite domtxmem.
      rewrite elem_of_list_to_set.      
      apply elem_of_addr_of_page_iff.
      rewrite to_pid_aligned_eq.
      symmetry.
      rewrite (finz_succN_pid' p_tx0 1).
      reflexivity.
      lia.
    }
    {
      rewrite <-elem_of_dom.
      rewrite domtxmem.
      rewrite elem_of_list_to_set.      
      apply elem_of_addr_of_page_iff.
      rewrite to_pid_aligned_eq.
      symmetry.
      repeat (rewrite finz_succN_one).
      repeat (rewrite finz_succN_idemp).
      simpl.
      rewrite finz_succN_correct.
      rewrite (finz_succN_pid' p_tx0 2).
      reflexivity.
      lia.
    }
    {
      rewrite <-elem_of_dom.
      rewrite domtxmem.
      rewrite elem_of_list_to_set.      
      apply elem_of_addr_of_page_iff.
      rewrite to_pid_aligned_eq.
      symmetry.
      repeat (rewrite finz_succN_one).
      repeat (rewrite finz_succN_idemp).
      simpl.
      rewrite finz_succN_correct.
      rewrite (finz_succN_pid' p_tx0 3).
      reflexivity.
      lia.
    }
    {
      rewrite <-elem_of_dom.
      rewrite domtxmem.
      rewrite elem_of_list_to_set.      
      apply elem_of_addr_of_page_iff.
      rewrite to_pid_aligned_eq.
      symmetry.
      repeat (rewrite finz_succN_one).
      repeat (rewrite finz_succN_idemp).
      simpl.
      rewrite finz_succN_correct.
      rewrite (finz_succN_pid' p_tx0 4).
      reflexivity.
      lia.
    }
    iDestruct "txmem" as "(%w1 & %w2 & %w3 & %w4 & %w5 & txmem1 & txmem2 & txmem3 & txmem4 & txmem5 & txacc)".    
    iApply ((@str _ _ _ _ _ V0 (str_I R4 R5) (encode_vmid V0) w1 1%Qp p_rx0 (tpa p_tx0) ({[tpa addr]} ∪ {[p_pg0; tpa p_tx0]}) (p_pg0 ^+ 6%nat)%f p_tx0imm R4 R5) with "[PCz p_7 acc txmem1 RX0page tx R4z R5z]").
    apply decode_encode_instruction.
    apply union_subseteq_r'.
    apply union_least.
    rewrite singleton_subseteq_l.    
    apply elem_of_union_r.
    rewrite Htxeq.
    apply elem_of_singleton_2.
    reflexivity.
    rewrite singleton_subseteq_l.    
    apply elem_of_union_l.
    rewrite HIn.
    apply elem_of_singleton_2.
    reflexivity.
    apply finz_succN_in_seq; simpl; lia.
    rewrite HIn.
    rewrite to_pid_aligned_eq.
    assumption.
    apply finz_succN_in_seq; simpl; lia.
    rewrite <-Htxeq.
    rewrite to_pid_aligned_eq.
    assumption.
    iFrame.
    iModIntro.
    iIntros "(PCz & _ & R5z & txmem1 & R4z & acc & tx & RX0page) _".
    (* add_I R5 R3 *)
    rewrite wp_sswp.
    iEval (rewrite finz_plus_one_simpl) in "PCz".
    rewrite Z_of_nat_simpl.
    iEval (simpl) in "PCz".
    iApply ((@add _ _ _ _ _ _ (add_I R5 R3) p_tx0imm one 1%Qp (tpa p_tx0) (p_pg0 ^+ 7%nat)%f R5 R3 ({[tpa addr]} ∪ {[p_pg0; tpa p_tx0]})) with "[p_8 PCz acc R5z R3z tx]").
    apply decode_encode_instruction.
    apply elem_of_union_r.
    apply elem_of_union_l.
    apply elem_of_singleton_2.
    rewrite HIn.
    reflexivity.
    apply finz_succN_in_seq; simpl; lia.
    rewrite HIn.
    rewrite to_pid_aligned_eq.
    assumption.
    apply finz_succN_in_seq; simpl; lia.
    iFrame.    
    iModIntro.
    iIntros "(PCz & _ & R5z & R3z & acc & tx) _".
    (* mov_word_I R4 zero *)
    rewrite wp_sswp.
    iEval (rewrite finz_plus_one_simpl) in "PCz".
    rewrite Z_of_nat_simpl.
    iEval (simpl) in "PCz".
    iApply ((@mov_word _ _ _ _ _ _ _ _ _ ({[tpa addr]} ∪ {[p_pg0; tpa p_tx0]}) (tpa p_tx0) (p_pg0 ^+ 8%nat)%f zero R4) with "[p_9 PCz acc tx R4z]").
    apply decode_encode_instruction.
    apply elem_of_union_r.
    apply elem_of_union_l.
    apply elem_of_singleton_2.
    rewrite HIn.
    reflexivity.
    apply finz_succN_in_seq; simpl; lia.
    rewrite HIn.
    rewrite to_pid_aligned_eq.
    assumption.
    apply finz_succN_in_seq; simpl; lia.
    iFrame.
    iModIntro.
    iIntros "(PCz & _ & acc & tx & R4z) _".
    (* str_I R4 R5 *)
    rewrite wp_sswp.
    iEval (rewrite finz_plus_one_simpl) in "PCz".
    rewrite Z_of_nat_simpl.
    iEval (simpl) in "PCz".
    iApply ((@str _ _ _ _ _ _ _ zero w2 1%Qp p_rx0 (tpa p_tx0) ({[tpa addr]} ∪ {[p_pg0; tpa p_tx0]}) (p_pg0 ^+ 9%nat)%f (p_tx0 ^+ 1)%f R4 R5) with "[p_10 PCz acc txmem2 RX0page tx R4z R5z]").
    apply decode_encode_instruction.
    apply union_subseteq_r'.
    apply union_least.
    rewrite singleton_subseteq_l.    
    apply elem_of_union_r.
    apply elem_of_singleton_2.
    {
      rewrite to_pid_aligned_eq.
      rewrite (finz_succN_pid' p_tx0 1).
      reflexivity.
      lia.
    }
    rewrite singleton_subseteq_l.
    apply elem_of_union_l.
    apply elem_of_singleton_2.
    apply HIn.
    apply finz_succN_in_seq; simpl; lia.
    rewrite HIn.
    rewrite to_pid_aligned_eq.
    assumption.
    apply finz_succN_in_seq; simpl; lia.
    rewrite (finz_succN_pid' p_tx0 1).
    assumption.
    lia.
    rewrite Htxeq.
    iFrame.
    iModIntro.
    iIntros "(PCz & _ & R5z & txmem2 & R4z & acc & tx & RX0page) _".
    (* add_I R5 R3 *)
    rewrite wp_sswp.
    iEval (rewrite finz_plus_one_simpl) in "PCz".
    rewrite Z_of_nat_simpl.
    iEval (simpl) in "PCz".
    iApply (@add _ _ _ _ _ _ (add_I R5 R3) (p_tx0imm ^+ 1)%f one 1%Qp (tpa p_tx0)
              (p_pg0 ^+ 10%nat)%f
              R5 R3 ({[tpa addr]} ∪ {[p_pg0; tpa p_tx0]}) with "[p_11 PCz acc R5z R3z tx]").
    apply decode_encode_instruction. 
    apply elem_of_union_r.
    apply elem_of_union_l.
    apply elem_of_singleton_2.
    rewrite (finz_succN_pid' p_pg0 10).
    reflexivity.
    lia.
    rewrite HIn.
    rewrite to_pid_aligned_eq.
    assumption.
    apply finz_succN_in_seq; simpl; lia.
    rewrite Htxeq.
    iFrame.
    iModIntro.
    iIntros "(PCz & _ & R5z & R3z & acc & tx) _".
    (* (* mov_word_I R4 one *) *)
    rewrite wp_sswp.
    iEval (rewrite finz_plus_one_simpl) in "PCz".
    rewrite Z_of_nat_simpl.
    iEval (simpl) in "PCz".
    iApply ((@mov_word _ _ _ _ _ _ _ _ _ ({[tpa addr]} ∪ {[p_pg0; tpa p_tx0]}) (tpa p_tx0)
               (p_pg0 ^+ 11%nat)%f
               one R4) with "[p_12 PCz acc tx R4z]").
    apply decode_encode_instruction.
    apply elem_of_union_r.
    apply elem_of_union_l.
    apply elem_of_singleton_2.
    rewrite (finz_succN_pid' p_pg0 11).
    reflexivity.
    lia.
    rewrite HIn.
    rewrite to_pid_aligned_eq.
    assumption.
    apply finz_succN_in_seq; simpl; lia.
    rewrite Htxeq.
    iFrame.
    iModIntro.
    iIntros "(PCz & _ & acc & tx & R4z) _".
    rewrite wp_sswp.
    iEval (rewrite finz_plus_one_simpl) in "PCz".
    rewrite Z_of_nat_simpl.
    iEval (simpl) in "PCz".
    iApply ((@str _ _ _ _ _ _ _ one w3 1%Qp p_rx0 (tpa p_tx0) ({[tpa addr]} ∪ {[p_pg0; tpa p_tx0]}) (p_pg0 ^+ 12%nat)%f ((p_tx0 ^+ 1) ^+ 1)%f R4 R5) with "[p_13 PCz acc txmem3 RX0page tx R4z R5z]").
    apply decode_encode_instruction.
    apply union_subseteq_r'.
    apply union_least.
    rewrite singleton_subseteq_l.    
    apply elem_of_union_r.
    apply elem_of_singleton_2.
    {
      rewrite to_pid_aligned_eq.
      repeat (rewrite finz_succN_one).
      repeat (rewrite finz_succN_idemp).
      simpl.
      rewrite finz_succN_correct.
      rewrite (finz_succN_pid' p_tx0 2).
      reflexivity.
      lia.
    }
    rewrite singleton_subseteq_l.
    apply elem_of_union_l.
    apply elem_of_singleton_2.
    apply HIn.
    apply finz_succN_in_seq; simpl; lia.
    rewrite HIn.
    rewrite to_pid_aligned_eq.
    assumption.
    apply finz_succN_in_seq; simpl; lia.
    repeat (rewrite finz_succN_one).
    repeat (rewrite finz_succN_idemp).
    simpl.
    rewrite finz_succN_correct.
    rewrite (finz_succN_pid' p_tx0 2).
    assumption.
    lia.
    rewrite Htxeq.
    iFrame.
    iModIntro.
    iIntros "(PCz & _ & R5z & txmem3 & R4z & acc & tx & RX0page) _".
    (* add_I R5 R3 *)
    rewrite wp_sswp.
    iEval (rewrite finz_plus_one_simpl) in "PCz".
    rewrite Z_of_nat_simpl.
    iEval (simpl) in "PCz".
    iApply (@add _ _ _ _ _ _ (add_I R5 R3) ((p_tx0imm ^+ 1) ^+ 1)%f one 1%Qp (tpa p_tx0)
              (p_pg0 ^+ 13%nat)%f
              R5 R3 ({[tpa addr]} ∪ {[p_pg0; tpa p_tx0]}) with "[p_14 PCz acc R5z R3z tx]").
    apply decode_encode_instruction. 
    apply elem_of_union_r.
    apply elem_of_union_l.
    apply elem_of_singleton_2.
    rewrite (finz_succN_pid' p_pg0 13).
    reflexivity.
    lia.
    rewrite HIn.
    rewrite to_pid_aligned_eq.
    assumption.
    apply finz_succN_in_seq; simpl; lia.
    rewrite Htxeq.
    iFrame.
    iModIntro.
    iIntros "(PCz & _ & R5z & R3z & acc & tx) _".
    (* (* mov_word_I R4 one *) *)
    rewrite wp_sswp.
    iEval (rewrite finz_plus_one_simpl) in "PCz".
    rewrite Z_of_nat_simpl.
    iEval (simpl) in "PCz".
    iApply ((@mov_word _ _ _ _ _ _ _ _ _ ({[tpa addr]} ∪ {[p_pg0; tpa p_tx0]}) (tpa p_tx0)
               (p_pg0 ^+ 14%nat)%f
               (encode_vmid V1) R4) with "[p_15 PCz acc tx R4z]").
    apply decode_encode_instruction.
    apply elem_of_union_r.
    apply elem_of_union_l.
    apply elem_of_singleton_2.
    rewrite (finz_succN_pid' p_pg0 14).
    reflexivity.
    lia.
    rewrite HIn.
    rewrite to_pid_aligned_eq.
    assumption.
    apply finz_succN_in_seq; simpl; lia.
    rewrite Htxeq.
    iFrame.
    iModIntro.
    iIntros "(PCz & _ & acc & tx & R4z) _".
    rewrite wp_sswp.
    iEval (rewrite finz_plus_one_simpl) in "PCz".
    rewrite Z_of_nat_simpl.
    iEval (simpl) in "PCz".
    iApply ((@str _ _ _ _ _ _ _ (encode_vmid V1) w4 1%Qp p_rx0 (tpa p_tx0) ({[tpa addr]} ∪ {[p_pg0; tpa p_tx0]}) (p_pg0 ^+ 15%nat)%f (((p_tx0 ^+ 1) ^+ 1) ^+ 1)%f R4 R5) with "[p_16 PCz acc txmem4 RX0page tx R4z R5z]").
    apply decode_encode_instruction.
    apply union_subseteq_r'.
    apply union_least.
    rewrite singleton_subseteq_l.    
    apply elem_of_union_r.
    apply elem_of_singleton_2.
    {
      rewrite to_pid_aligned_eq.
      repeat (rewrite finz_succN_one).
      repeat (rewrite finz_succN_idemp).
      simpl.
      rewrite finz_succN_correct.
      rewrite (finz_succN_pid' p_tx0 3).
      reflexivity.
      lia.
    }
    rewrite singleton_subseteq_l.
    apply elem_of_union_l.
    apply elem_of_singleton_2.
    apply HIn.
    apply finz_succN_in_seq; simpl; lia.
    rewrite HIn.
    rewrite to_pid_aligned_eq.
    assumption.
    apply finz_succN_in_seq; simpl; lia.
    repeat (rewrite finz_succN_one).
    repeat (rewrite finz_succN_idemp).
    simpl.
    rewrite finz_succN_correct.
    rewrite (finz_succN_pid' p_tx0 3).
    assumption.
    lia.
    rewrite Htxeq.
    iFrame.
    iModIntro.
    iIntros "(PCz & _ & R5z & txmem4 & R4z & acc & tx & RX0page) _".
    (* add_I R5 R3 *)
    rewrite wp_sswp.
    iEval (rewrite finz_plus_one_simpl) in "PCz".
    rewrite Z_of_nat_simpl.
    iEval (simpl) in "PCz".
    iApply (@add _ _ _ _ _ _ (add_I R5 R3) (((p_tx0imm ^+ 1) ^+ 1) ^+ 1)%f one 1%Qp (tpa p_tx0)
              (p_pg0 ^+ 16%nat)%f
              R5 R3 ({[tpa addr]} ∪ {[p_pg0; tpa p_tx0]}) with "[p_17 PCz acc R5z R3z tx]").
    apply decode_encode_instruction. 
    apply elem_of_union_r.
    apply elem_of_union_l.
    apply elem_of_singleton_2.
    rewrite (finz_succN_pid' p_pg0 16).
    reflexivity.
    lia.
    rewrite HIn.
    rewrite to_pid_aligned_eq.
    assumption.
    apply finz_succN_in_seq; simpl; lia.
    rewrite Htxeq.
    iFrame.
    iModIntro.
    iIntros "(PCz & _ & R5z & R3z & acc & tx) _".
    (* (* mov_word_I R4 one *) *)
    rewrite wp_sswp.
    iEval (rewrite finz_plus_one_simpl) in "PCz".
    rewrite Z_of_nat_simpl.
    iEval (simpl) in "PCz".
    iApply ((@mov_word _ _ _ _ _ _ _ _ _ ({[tpa addr]} ∪ {[p_pg0; tpa p_tx0]}) (tpa p_tx0)
               (p_pg0 ^+ 17%nat)%f
               addr R4) with "[p_18 PCz acc tx R4z]").
    apply decode_encode_instruction.
    apply elem_of_union_r.
    apply elem_of_union_l.
    apply elem_of_singleton_2.
    rewrite (finz_succN_pid' p_pg0 17).
    reflexivity.
    lia.
    rewrite HIn.
    rewrite to_pid_aligned_eq.
    assumption.
    apply finz_succN_in_seq; simpl; lia.
    rewrite Htxeq.
    iFrame.
    iModIntro.
    iIntros "(PCz & _ & acc & tx & R4z) _".
    rewrite wp_sswp.
    iEval (rewrite finz_plus_one_simpl) in "PCz".
    rewrite Z_of_nat_simpl.
    iEval (simpl) in "PCz".
    iApply ((@str _ _ _ _ _ _ _ addr w5 1%Qp p_rx0 (tpa p_tx0) ({[tpa addr]} ∪ {[p_pg0; tpa p_tx0]}) (p_pg0 ^+ 18%nat)%f ((((p_tx0 ^+ 1) ^+ 1) ^+ 1) ^+ 1)%f R4 R5) with "[p_19 PCz acc txmem5 RX0page tx R4z R5z]").
    apply decode_encode_instruction.
    apply union_subseteq_r'.
    apply union_least.
    rewrite singleton_subseteq_l.    
    apply elem_of_union_r.
    apply elem_of_singleton_2.
    {
      rewrite to_pid_aligned_eq.
      repeat (rewrite finz_succN_one).
      repeat (rewrite finz_succN_idemp).
      simpl.
      rewrite finz_succN_correct.
      rewrite (finz_succN_pid' p_tx0 4).
      reflexivity.
      lia.
    }
    rewrite singleton_subseteq_l.
    apply elem_of_union_l.
    apply elem_of_singleton_2.
    apply HIn.
    apply finz_succN_in_seq; simpl; lia.
    rewrite HIn.
    rewrite to_pid_aligned_eq.
    assumption.
    apply finz_succN_in_seq; simpl; lia.
    repeat (rewrite finz_succN_one).
    repeat (rewrite finz_succN_idemp).
    simpl.
    rewrite finz_succN_correct.
    rewrite (finz_succN_pid' p_tx0 4).
    assumption.
    lia.
    rewrite Htxeq.
    iFrame.
    iModIntro.
    iIntros "(PCz & _ & R5z & txmem5 & R4z & acc & tx & RX0page) _".
    rewrite wp_sswp.
    iEval (rewrite finz_plus_one_simpl) in "PCz".
    rewrite Z_of_nat_simpl.
    iEval (simpl) in "PCz".
    iApply ((@mov_word _ _ _ _ _ _ _ _ _ ({[tpa addr]} ∪ {[p_pg0; tpa p_tx0]}) (tpa p_tx0)
               (p_pg0 ^+ 19%nat)%f
               mem_share_I R0) with "[p_20 PCz acc tx R0z]").
    apply decode_encode_instruction.
    apply elem_of_union_r.
    apply elem_of_union_l.
    apply elem_of_singleton_2.
    rewrite (finz_succN_pid' p_pg0 19).
    reflexivity.
    lia.
    rewrite HIn.
    rewrite to_pid_aligned_eq.
    assumption.
    apply finz_succN_in_seq; simpl; lia.
    rewrite Htxeq.
    iFrame.
    iModIntro.
    iIntros "(PCz & _ & acc & tx & R0z) _".
    rewrite wp_sswp.
    iEval (rewrite finz_plus_one_simpl) in "PCz".
    rewrite Z_of_nat_simpl.
    iEval (simpl) in "PCz".
    iApply ((@mov_word _ _ _ _ _ _ _ _ _ ({[tpa addr]} ∪ {[p_pg0; tpa p_tx0]}) (tpa p_tx0)
               (p_pg0 ^+ 20%nat)%f
               mem_descriptor_length R1) with "[p_21 PCz acc tx R1z]").
    apply decode_encode_instruction.
    apply elem_of_union_r.
    apply elem_of_union_l.
    apply elem_of_singleton_2.
    rewrite (finz_succN_pid' p_pg0 20).
    reflexivity.
    lia.
    rewrite HIn.
    rewrite to_pid_aligned_eq.
    assumption.
    apply finz_succN_in_seq; simpl; lia.
    rewrite Htxeq.
    iFrame.
    iModIntro.
    iIntros "(PCz & _ & acc & tx & R1z) _".
    rewrite wp_sswp.
    iEval (rewrite finz_plus_one_simpl) in "PCz".
    rewrite Z_of_nat_simpl.
    iEval (simpl) in "PCz".
    iSpecialize ("txacc" $! (encode_vmid V0) zero one (encode_vmid V1) addr).
    iDestruct ("txacc" with "[$txmem1 $txmem2 $txmem3 $txmem4 $txmem5]") as "txmem".
    match goal with
    | |- context [([∗ map] k↦y ∈ ?p, k ->a y)%I] => set q := p
    end.
    iApply ((mem_share (p_tx := tpa p_tx0) (wi := hvc_I) (hvcf := Share)
               (sacc := ({[tpa addr]} ∪ {[p_pg0; tpa p_tx0]}))
               (r0 := mem_share_I) (r1 := mem_descriptor_length) (r2 := r2)
               (p_pg0 ^+ 21%nat)%f
               V1 q
               valid_handles (singleton (tpa addr)))
             with "[p_22 PCz acc R0z R1z R2z hp tx txmem OE]").
    {
      apply elem_of_union_r.
      apply elem_of_union_l.
      apply elem_of_singleton_2.
      rewrite HIn.
      reflexivity.
      apply finz_succN_in_seq; simpl; lia.
    }
    {
      rewrite HIn.
      rewrite to_pid_aligned_eq.
      assumption.
      apply finz_succN_in_seq; simpl; lia.
    }
    {
      apply decode_encode_instruction.
    }
    {
      apply decode_encode_hvc_func.
    }
    {
      reflexivity.
    }
    {
      unfold mem_descriptor_length.
      simpl.
      lia.
    }
    {
      unfold parse_transaction_descriptor.
      assert (parse_list_of_Word q (tpa p_tx0) (Z.to_nat mem_descriptor_length) = Some ([of_imm (encode_vmid V0); of_imm zero; of_imm one; of_imm (encode_vmid V1); of_pid (tpa addr)] : list Addr)) as ->.
      {
        clear -Htxeq Haddr.
        unfold parse_list_of_Word.
        unfold sequence_a.
        remember (tpa p_tx0) as A.
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
          rewrite HeqA.
          clear -Htxeq.
          rewrite lookup_insert_Some.
          left.
          split; last done.
          rewrite <-Htxeq.
          by rewrite to_pid_aligned_eq.
        }
        assert (b' = Some (of_imm zero)) as ->.
        {
          subst b'.
          subst q.
          rewrite HeqA.
          clear -Htxeq.
          rewrite lookup_insert_Some.
          right.
          split.
          - rewrite to_pid_aligned_eq.
            rewrite <-Htxeq.
            intros contra.
            destruct p_tx0.
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
            solve_finz.
          - rewrite lookup_insert_Some.
            left.
            split; last done.
            by rewrite to_pid_aligned_eq.
        }
        assert (c' = Some (of_imm one)) as ->.
        {
          subst c'.
          subst q.
          rewrite HeqA.
          clear -Htxeq.
          rewrite lookup_insert_Some.
          right.
          split.
          - rewrite to_pid_aligned_eq.
            rewrite <-Htxeq.
            intros contra.
            destruct p_tx0.
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
            solve_finz.
          - rewrite lookup_insert_Some.
            right.
            split.
            + rewrite to_pid_aligned_eq.
              intros contra.
              destruct p_tx0.
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
              solve_finz.
            + rewrite lookup_insert_Some.
              left.
              split; last done.
              by rewrite to_pid_aligned_eq.
        }
        assert (d' = Some (of_imm (encode_vmid V1))) as ->.
        {
          subst d'.
          subst q.
          rewrite HeqA.
          clear -Htxeq.
          rewrite lookup_insert_Some.
          right.
          split.
          - rewrite to_pid_aligned_eq.
            rewrite <-Htxeq.
            intros contra.
            destruct p_tx0.
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
            solve_finz.
          - rewrite lookup_insert_Some.
            right.
            split.
            + rewrite to_pid_aligned_eq.              
              intros contra.
              destruct p_tx0.
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
              solve_finz.
            + rewrite lookup_insert_Some.
              right.
              split.
              * rewrite to_pid_aligned_eq.
                intros contra.
                destruct p_tx0.
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
                solve_finz.
              * rewrite lookup_insert_Some.
                left.
                split; last done.
                by rewrite to_pid_aligned_eq.
        }
        assert (e' = Some (of_pid (tpa addr))) as ->.
        {
          subst e'.
          subst q.
          rewrite HeqA.
          clear -Htxeq Haddr.
          rewrite lookup_insert_Some.
          right.
          split.
          - rewrite to_pid_aligned_eq.
            rewrite <-Htxeq.
            intros contra.
            destruct p_tx0.
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
            solve_finz.
          - rewrite lookup_insert_Some.
            right.
            split.
            + rewrite to_pid_aligned_eq.
              intros contra.
              destruct p_tx0.
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
              solve_finz.
            + rewrite lookup_insert_Some.
              right.
              split.
              * rewrite to_pid_aligned_eq.
                intros contra.
                destruct p_tx0.
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
                solve_finz.
              * rewrite lookup_insert_Some.
                right.
                split.
                -- rewrite to_pid_aligned_eq.                   
                   intros contra.
                   destruct p_tx0.
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
                   solve_finz.
                -- rewrite lookup_insert_Some.
                   left.
                   split; last done.
                   by rewrite to_pid_aligned_eq.
        }
        rewrite Heql'.
        unfold monad.List.sequence_a_list.
        simpl.
        reflexivity.        
      }
      remember (tpa addr) as A.
      cbn.
      rewrite decode_encode_vmid.
      rewrite decode_encode_vmid.
      assert (Z.to_nat 1 = 1) as ->.
      { lia. }
      rewrite Nat.eqb_refl.
      cbn.
      rewrite HeqA.
      assert (to_pid (tpa addr) = Some (tpa addr)) as ->.
      {
        rewrite to_of_pid.
        reflexivity.
      }
      simpl.
      rewrite union_empty_r_L.
      reflexivity.
    }
    {
      auto.
    }
    {
      set_solver +.
    }
    {
      unfold valid_handles.
      clear.
      apply non_empty_inhabited_L with W0.
      unfold rywu_vmconfig.
      apply elem_of_singleton_2.
      reflexivity.
    }
    {
      iFrame.      
      iNext.
      subst q.
      iPureIntro.
      rewrite !dom_insert_lookup_L.
      assumption.
      rewrite <-elem_of_dom.
      rewrite domtxmem.
      rewrite elem_of_list_to_set.
      rewrite elem_of_addr_of_page_iff.
      rewrite to_pid_aligned_eq.
      repeat (rewrite finz_succN_one).
      repeat (rewrite finz_succN_idemp).
      simpl.
      rewrite finz_succN_correct.
      rewrite (finz_succN_pid' p_tx0 4).
      reflexivity.
      lia.
      rewrite <-elem_of_dom.
      rewrite !dom_insert_lookup_L.
      rewrite domtxmem.
      rewrite elem_of_list_to_set.
      rewrite elem_of_addr_of_page_iff.
      rewrite to_pid_aligned_eq.
      repeat (rewrite finz_succN_one).
      repeat (rewrite finz_succN_idemp).
      simpl.
      rewrite finz_succN_correct.
      rewrite (finz_succN_pid' p_tx0 3).
      reflexivity.
      lia.
      rewrite <-elem_of_dom.
      rewrite domtxmem.
      rewrite elem_of_list_to_set.
      rewrite elem_of_addr_of_page_iff.
      rewrite to_pid_aligned_eq.
      repeat (rewrite finz_succN_one).
      repeat (rewrite finz_succN_idemp).
      simpl.
      rewrite finz_succN_correct.
      rewrite (finz_succN_pid' p_tx0 4).
      reflexivity.
      lia.
      rewrite <-elem_of_dom.
      rewrite !dom_insert_lookup_L.
      rewrite domtxmem.
      rewrite elem_of_list_to_set.
      rewrite elem_of_addr_of_page_iff.
      rewrite to_pid_aligned_eq.
      repeat (rewrite finz_succN_one).
      repeat (rewrite finz_succN_idemp).
      simpl.
      rewrite finz_succN_correct.
      rewrite (finz_succN_pid' p_tx0 2).
      reflexivity.
      lia.
      rewrite <-elem_of_dom.
      rewrite domtxmem.
      rewrite elem_of_list_to_set.
      rewrite elem_of_addr_of_page_iff.
      rewrite to_pid_aligned_eq.
      repeat (rewrite finz_succN_one).
      repeat (rewrite finz_succN_idemp).
      simpl.
      rewrite finz_succN_correct.
      rewrite (finz_succN_pid' p_tx0 4).
      reflexivity.
      lia.
      rewrite <-elem_of_dom.
      rewrite !dom_insert_lookup_L.
      rewrite domtxmem.
      rewrite elem_of_list_to_set.
      rewrite elem_of_addr_of_page_iff.
      rewrite to_pid_aligned_eq.
      repeat (rewrite finz_succN_one).
      repeat (rewrite finz_succN_idemp).
      simpl.
      rewrite finz_succN_correct.
      rewrite (finz_succN_pid' p_tx0 3).
      reflexivity.
      lia.
      rewrite <-elem_of_dom.
      rewrite domtxmem.
      rewrite elem_of_list_to_set.
      rewrite elem_of_addr_of_page_iff.
      rewrite to_pid_aligned_eq.
      repeat (rewrite finz_succN_one).
      repeat (rewrite finz_succN_idemp).
      simpl.
      rewrite finz_succN_correct.
      rewrite (finz_succN_pid' p_tx0 4).
      reflexivity.
      lia.
      rewrite <-elem_of_dom.
      rewrite !dom_insert_lookup_L.
      rewrite domtxmem.
      rewrite elem_of_list_to_set.
      rewrite elem_of_addr_of_page_iff.
      rewrite to_pid_aligned_eq.
      repeat (rewrite finz_succN_one).
      repeat (rewrite finz_succN_idemp).
      simpl.
      rewrite finz_succN_correct.
      rewrite (finz_succN_pid' p_tx0 1).
      reflexivity.
      lia.
      rewrite <-elem_of_dom.
      rewrite domtxmem.
      rewrite elem_of_list_to_set.
      rewrite elem_of_addr_of_page_iff.
      rewrite to_pid_aligned_eq.
      repeat (rewrite finz_succN_one).
      repeat (rewrite finz_succN_idemp).
      simpl.
      rewrite finz_succN_correct.
      rewrite (finz_succN_pid' p_tx0 4).
      reflexivity.
      lia.
      rewrite <-elem_of_dom.
      rewrite !dom_insert_lookup_L.
      rewrite domtxmem.
      rewrite elem_of_list_to_set.
      rewrite elem_of_addr_of_page_iff.
      rewrite to_pid_aligned_eq.
      repeat (rewrite finz_succN_one).
      repeat (rewrite finz_succN_idemp).
      simpl.
      rewrite finz_succN_correct.
      rewrite (finz_succN_pid' p_tx0 3).
      reflexivity.
      lia.
      rewrite <-elem_of_dom.
      rewrite domtxmem.
      rewrite elem_of_list_to_set.
      rewrite elem_of_addr_of_page_iff.
      rewrite to_pid_aligned_eq.
      repeat (rewrite finz_succN_one).
      repeat (rewrite finz_succN_idemp).
      simpl.
      rewrite finz_succN_correct.
      rewrite (finz_succN_pid' p_tx0 4).
      reflexivity.
      lia.
      rewrite <-elem_of_dom.
      rewrite !dom_insert_lookup_L.
      rewrite domtxmem.
      rewrite elem_of_list_to_set.
      rewrite elem_of_addr_of_page_iff.
      rewrite to_pid_aligned_eq.
      repeat (rewrite finz_succN_one).
      repeat (rewrite finz_succN_idemp).
      simpl.
      rewrite finz_succN_correct.
      rewrite (finz_succN_pid' p_tx0 2).
      reflexivity.
      lia.
      rewrite <-elem_of_dom.      
      rewrite domtxmem.
      rewrite elem_of_list_to_set.
      rewrite elem_of_addr_of_page_iff.
      rewrite to_pid_aligned_eq.
      repeat (rewrite finz_succN_one).
      repeat (rewrite finz_succN_idemp).
      simpl.
      rewrite finz_succN_correct.
      rewrite (finz_succN_pid' p_tx0 4).
      reflexivity.
      lia.
      rewrite <-elem_of_dom.
      rewrite !dom_insert_lookup_L.
      rewrite domtxmem.
      rewrite elem_of_list_to_set.
      rewrite elem_of_addr_of_page_iff.
      rewrite to_pid_aligned_eq.
      repeat (rewrite finz_succN_one).
      repeat (rewrite finz_succN_idemp).
      simpl.
      rewrite finz_succN_correct.
      rewrite (finz_succN_pid' p_tx0 3).
      reflexivity.
      lia.
      rewrite <-elem_of_dom.
      rewrite domtxmem.
      rewrite elem_of_list_to_set.
      rewrite elem_of_addr_of_page_iff.
      rewrite to_pid_aligned_eq.
      repeat (rewrite finz_succN_one).
      repeat (rewrite finz_succN_idemp).
      simpl.
      rewrite finz_succN_correct.
      rewrite (finz_succN_pid' p_tx0 4).
      reflexivity.
      lia.
      rewrite <-elem_of_dom.
      rewrite !dom_insert_lookup_L.
      rewrite domtxmem.
      rewrite elem_of_list_to_set.
      rewrite elem_of_addr_of_page_iff.
      rewrite to_pid_aligned_eq.
      repeat (rewrite finz_succN_one).
      repeat (rewrite finz_succN_idemp).
      simpl.
      rewrite <-Htxeq.
      rewrite to_pid_aligned_eq.
      reflexivity.
      rewrite <-elem_of_dom.
      rewrite domtxmem.
      rewrite elem_of_list_to_set.
      rewrite elem_of_addr_of_page_iff.
      rewrite to_pid_aligned_eq.
      repeat (rewrite finz_succN_one).
      repeat (rewrite finz_succN_idemp).
      simpl.
      rewrite finz_succN_correct.
      rewrite (finz_succN_pid' p_tx0 4).
      reflexivity.
      lia.
      rewrite <-elem_of_dom.
      rewrite !dom_insert_lookup_L.
      rewrite domtxmem.
      rewrite elem_of_list_to_set.
      rewrite elem_of_addr_of_page_iff.
      rewrite to_pid_aligned_eq.
      repeat (rewrite finz_succN_one).
      repeat (rewrite finz_succN_idemp).
      simpl.
      rewrite finz_succN_correct.
      rewrite (finz_succN_pid' p_tx0 3).
      reflexivity.
      lia.
      rewrite <-elem_of_dom.
      rewrite domtxmem.
      rewrite elem_of_list_to_set.
      rewrite elem_of_addr_of_page_iff.
      rewrite to_pid_aligned_eq.
      repeat (rewrite finz_succN_one).
      repeat (rewrite finz_succN_idemp).
      simpl.
      rewrite finz_succN_correct.
      rewrite (finz_succN_pid' p_tx0 4).
      reflexivity.
      lia.
      rewrite <-elem_of_dom.
      rewrite !dom_insert_lookup_L.
      rewrite domtxmem.
      rewrite elem_of_list_to_set.
      rewrite elem_of_addr_of_page_iff.
      rewrite to_pid_aligned_eq.
      repeat (rewrite finz_succN_one).
      repeat (rewrite finz_succN_idemp).
      simpl.
      rewrite finz_succN_correct.
      rewrite (finz_succN_pid' p_tx0 2).
      reflexivity.
      lia.
      rewrite <-elem_of_dom.
      rewrite domtxmem.
      rewrite elem_of_list_to_set.
      rewrite elem_of_addr_of_page_iff.
      rewrite to_pid_aligned_eq.
      repeat (rewrite finz_succN_one).
      repeat (rewrite finz_succN_idemp).
      simpl.
      rewrite finz_succN_correct.
      rewrite (finz_succN_pid' p_tx0 4).
      reflexivity.
      lia.
      rewrite <-elem_of_dom.
      rewrite !dom_insert_lookup_L.
      rewrite domtxmem.
      rewrite elem_of_list_to_set.
      rewrite elem_of_addr_of_page_iff.
      rewrite to_pid_aligned_eq.
      repeat (rewrite finz_succN_one).
      repeat (rewrite finz_succN_idemp).
      simpl.
      rewrite finz_succN_correct.
      rewrite (finz_succN_pid' p_tx0 3).
      reflexivity.
      lia.
      rewrite <-elem_of_dom.      
      rewrite domtxmem.
      rewrite elem_of_list_to_set.
      rewrite elem_of_addr_of_page_iff.
      rewrite to_pid_aligned_eq.
      repeat (rewrite finz_succN_one).
      repeat (rewrite finz_succN_idemp).
      simpl.
      rewrite finz_succN_correct.
      rewrite (finz_succN_pid' p_tx0 4).
      reflexivity.
      lia.
      rewrite <-elem_of_dom.
      rewrite !dom_insert_lookup_L.
      rewrite domtxmem.
      rewrite elem_of_list_to_set.
      rewrite elem_of_addr_of_page_iff.
      rewrite to_pid_aligned_eq.
      repeat (rewrite finz_succN_one).
      repeat (rewrite finz_succN_idemp).
      simpl.
      rewrite finz_succN_correct.
      rewrite (finz_succN_pid' p_tx0 1).
      reflexivity.
      lia.
      rewrite <-elem_of_dom.
      rewrite domtxmem.
      rewrite elem_of_list_to_set.
      rewrite elem_of_addr_of_page_iff.
      rewrite to_pid_aligned_eq.
      repeat (rewrite finz_succN_one).
      repeat (rewrite finz_succN_idemp).
      simpl.
      rewrite finz_succN_correct.
      rewrite (finz_succN_pid' p_tx0 4).
      reflexivity.
      lia.
      rewrite <-elem_of_dom.
      rewrite !dom_insert_lookup_L.
      rewrite domtxmem.
      rewrite elem_of_list_to_set.
      rewrite elem_of_addr_of_page_iff.
      rewrite to_pid_aligned_eq.
      repeat (rewrite finz_succN_one).
      repeat (rewrite finz_succN_idemp).
      simpl.
      rewrite finz_succN_correct.
      rewrite (finz_succN_pid' p_tx0 3).
      reflexivity.
      lia.
      rewrite <-elem_of_dom.      
      rewrite domtxmem.
      rewrite elem_of_list_to_set.
      rewrite elem_of_addr_of_page_iff.
      rewrite to_pid_aligned_eq.
      repeat (rewrite finz_succN_one).
      repeat (rewrite finz_succN_idemp).
      simpl.
      rewrite finz_succN_correct.
      rewrite (finz_succN_pid' p_tx0 4).
      reflexivity.
      lia.
      rewrite <-elem_of_dom.
      rewrite !dom_insert_lookup_L.
      rewrite domtxmem.
      rewrite elem_of_list_to_set.
      rewrite elem_of_addr_of_page_iff.
      rewrite to_pid_aligned_eq.
      repeat (rewrite finz_succN_one).
      repeat (rewrite finz_succN_idemp).
      simpl.
      rewrite finz_succN_correct.
      rewrite (finz_succN_pid' p_tx0 2).
      reflexivity.
      lia.
      rewrite <-elem_of_dom.
      rewrite domtxmem.
      rewrite elem_of_list_to_set.
      rewrite elem_of_addr_of_page_iff.
      rewrite to_pid_aligned_eq.
      repeat (rewrite finz_succN_one).
      repeat (rewrite finz_succN_idemp).
      simpl.
      rewrite finz_succN_correct.
      rewrite (finz_succN_pid' p_tx0 4).
      reflexivity.
      lia.
      rewrite <-elem_of_dom.
      rewrite !dom_insert_lookup_L.
      rewrite domtxmem.
      rewrite elem_of_list_to_set.
      rewrite elem_of_addr_of_page_iff.
      rewrite to_pid_aligned_eq.
      repeat (rewrite finz_succN_one).
      repeat (rewrite finz_succN_idemp).
      simpl.
      rewrite finz_succN_correct.
      rewrite (finz_succN_pid' p_tx0 3).
      reflexivity.
      lia.
      rewrite <-elem_of_dom.
      rewrite domtxmem.
      rewrite elem_of_list_to_set.
      rewrite elem_of_addr_of_page_iff.
      rewrite to_pid_aligned_eq.
      repeat (rewrite finz_succN_one).
      repeat (rewrite finz_succN_idemp).
      simpl.
      rewrite finz_succN_correct.
      rewrite (finz_succN_pid' p_tx0 4).
      reflexivity.
      lia.
    }
    iModIntro.
    iIntros "(PCz & _ & OE & acc & R0z & R1z & (%wh & whin & R2z & whtans & whretri & whfresh) & tx & txmem) _".
    (* assert ((({[tpa addr]} ∪ {[p_pg0; tpa p_tx0]}) ∖ {[tpa addr]}) = {[p_pg0; tpa p_tx0]}) as ->. *)
    (* { *)
    (*   rewrite difference_union_distr_l_L. *)
    (*   rewrite difference_diag_L. *)
    (*   rewrite union_empty_l_L. *)
    (*   rewrite difference_disjoint_L. *)
    (*   reflexivity. *)
    (*   rewrite disjoint_singleton_r. *)
    (*   apply not_elem_of_union. *)
    (*   split. *)
    (*   - apply not_elem_of_singleton_2. *)
    (*     assumption. *)
    (*   - apply not_elem_of_singleton_2. *)
    (*     rewrite to_pid_aligned_eq. *)
    (*     assumption. *)
    (* }  *)
    (* mov_word_I R5 p_tx0 *)
    rewrite wp_sswp.    
    iEval (rewrite finz_plus_one_simpl) in "PCz".
    rewrite Z_of_nat_simpl.
    iEval (simpl) in "PCz".
    iApply ((@mov_word _ _ _ _ _ _ _ _ _ ({[tpa addr]} ∪ {[p_pg0; tpa p_tx0]}) (tpa p_tx0) (p_pg0 ^+ 22%nat)%f p_tx0imm R5) with "[p_23 PCz acc tx R5z]").
    apply decode_encode_instruction.
    apply elem_of_union_r.
    apply elem_of_union_l.
    apply elem_of_singleton_2.
    rewrite HIn.
    reflexivity.
    apply finz_succN_in_seq; simpl; lia.
    rewrite HIn.
    rewrite to_pid_aligned_eq.
    assumption.
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
    iDestruct (@mem_big_sepM_split_upd _ q p_tx0imm (encode_vmid V0) with "txmem") as "txmem".
    {
      subst q.
      rewrite lookup_insert_Some.
      left.
      split; reflexivity.
    }
    iDestruct "txmem" as "(txmem1 & txacc)".    
    iApply ((@str _ _ _ _ _ _ _ wh (encode_vmid V0) 1%Qp p_rx0 (tpa p_tx0) ({[tpa addr]} ∪ {[p_pg0; tpa p_tx0]}) (p_pg0 ^+ 23%nat)%f p_tx0imm R2 R5) with "[p_24 PCz acc txmem1 RX0page tx R2z R5z]").
    apply decode_encode_instruction.
    apply union_subseteq_r'.
    apply union_least.
    rewrite singleton_subseteq_l.    
    apply elem_of_union_r.
    apply elem_of_singleton_2.
    {
      rewrite <-Htxeq.
      rewrite to_pid_aligned_eq.
      reflexivity.
    }
    rewrite singleton_subseteq_l.
    apply elem_of_union_l.
    apply elem_of_singleton_2.
    apply HIn.
    apply finz_succN_in_seq; simpl; lia.
    rewrite HIn.
    rewrite to_pid_aligned_eq.
    assumption.
    apply finz_succN_in_seq; simpl; lia.
    rewrite <-Htxeq.
    rewrite to_pid_aligned_eq.
    assumption.
    iFrame.
    iModIntro.
    iIntros "(PCz & _ & R5z & txmem1 & R2z & acc & tx & RX0page) _".
    rewrite wp_sswp.
    iEval (rewrite finz_plus_one_simpl) in "PCz".
    rewrite Z_of_nat_simpl.
    iEval (simpl) in "PCz".
    iSpecialize ("txacc" $! wh).
    iDestruct ("txacc" with "[$txmem1]") as "txmem".
    iApply ((@mov_reg _ _ _ _ _ _ _ wh 1%Qp ({[tpa addr]} ∪ {[p_pg0; tpa p_tx0]}) (tpa p_tx0) (p_pg0 ^+ 24%nat)%f one R3 R2) with "[PCz p_25 acc tx R2z R3z]").
    apply decode_encode_instruction.
    apply elem_of_union_r.
    apply elem_of_union_l.
    apply elem_of_singleton_2.
    apply HIn.
    apply finz_succN_in_seq; simpl; lia.
    rewrite HIn.
    rewrite to_pid_aligned_eq.
    assumption.
    apply finz_succN_in_seq; simpl; lia.
    iFrame.
    iModIntro.
    iIntros "(PCz & _ & acc & tx & R3z & R2z) _".
    rewrite wp_sswp.
    iEval (rewrite finz_plus_one_simpl) in "PCz".
    rewrite Z_of_nat_simpl.
    iEval (simpl) in "PCz".
    iApply ((@mov_word _ _ _ _ _ _ _ _ _ ({[tpa addr]} ∪ {[p_pg0; tpa p_tx0]}) (tpa p_tx0) (p_pg0 ^+ 25%nat)%f msg_send_I R0) with "[p_26 PCz acc tx R0z]").
    apply decode_encode_instruction.
    apply elem_of_union_r.
    apply elem_of_union_l.
    apply elem_of_singleton_2.
    rewrite HIn.
    reflexivity.
    apply finz_succN_in_seq; simpl; lia.
    rewrite HIn.
    rewrite to_pid_aligned_eq.
    assumption.
    apply finz_succN_in_seq; simpl; lia.
    iFrame.
    iModIntro.
    iIntros "(PCz & _ & acc & tx & R0z) _".
    rewrite wp_sswp.
    iEval (rewrite finz_plus_one_simpl) in "PCz".
    rewrite Z_of_nat_simpl.
    iEval (simpl) in "PCz".
    iApply ((@mov_word _ _ _ _ _ _ _ _ _ ({[tpa addr]} ∪ {[p_pg0; tpa p_tx0]}) (tpa p_tx0) (p_pg0 ^+ 26%nat)%f (encode_vmid V1) R1) with "[p_27 PCz acc tx R1z]").
    apply decode_encode_instruction.
    apply elem_of_union_r.
    apply elem_of_union_l.
    apply elem_of_singleton_2.
    rewrite HIn.
    reflexivity.
    apply finz_succN_in_seq; simpl; lia.
    rewrite HIn.
    rewrite to_pid_aligned_eq.
    assumption.
    apply finz_succN_in_seq; simpl; lia.
    iFrame.
    iModIntro.
    iIntros "(PCz & _ & acc & tx & R1z) _".
    rewrite wp_sswp.
    iEval (rewrite finz_plus_one_simpl) in "PCz".
    rewrite Z_of_nat_simpl.
    iEval (simpl) in "PCz".
    iApply ((@mov_word _ _ _ _ _ _ _ _ _ ({[tpa addr]} ∪ {[p_pg0; tpa p_tx0]}) (tpa p_tx0) (p_pg0 ^+ 27%nat)%f one R2) with "[p_28 PCz acc tx R2z]").
    apply decode_encode_instruction.
    apply elem_of_union_r.
    apply elem_of_union_l.
    apply elem_of_singleton_2.
    rewrite HIn.
    reflexivity.
    apply finz_succN_in_seq; simpl; lia.
    rewrite HIn.
    rewrite to_pid_aligned_eq.
    assumption.
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
    iApply ((@msg_send_primary _ _ _ _ _ hvc_I msg_send_I (encode_vmid V1) ({[tpa addr]} ∪ {[p_pg0; tpa p_tx0]}) (tpa p_tx0) q' 1%Qp p_rx1 rxmem one (p_pg0 ^+ 28%nat)%f V1) with "[p_29 PCz acc tx R0z R1z R2z txmem RX1st rxmem RX1page]").
    rewrite HIn.
    rewrite to_pid_aligned_eq.
    assumption.
    apply finz_succN_in_seq; simpl; lia.
    apply elem_of_union_r.
    apply elem_of_union_l.
    apply elem_of_singleton_2.
    rewrite HIn.
    reflexivity.
    apply finz_succN_in_seq; simpl; lia.
    by rewrite decode_encode_instruction.
    by rewrite decode_encode_hvc_func.
    simpl; lia.
    by rewrite decode_encode_vmid.
    done.
    iFrame.
    iNext.
    iPureIntro.
    subst q'.
    subst q.
    rewrite dom_insert_L.
    rewrite subseteq_union_1_L.
    assumption.
    apply singleton_subseteq_l.
    apply elem_of_dom.
    exists (encode_vmid V0).
    apply lookup_insert.
    iModIntro.
    iIntros "(PCz & _ & acc & R0z & R1z & R2z & tx & RX1page & RX1st & txmem & %descr & %descrlen & %descrsubseteq & rxmem) _".
    rewrite wp_sswp.
    iEval (rewrite finz_plus_one_simpl) in "PCz".
    rewrite Z_of_nat_simpl.
    iEval (simpl) in "PCz".
    iApply ((@mov_word _ _ _ _ _ _ _ _ _ ({[tpa addr]} ∪ {[p_pg0; tpa p_tx0]}) (tpa p_tx0) (p_pg0 ^+ 29%nat)%f run_I R0) with "[p_30 PCz acc tx R0z]").
    apply decode_encode_instruction.
    apply elem_of_union_r.
    apply elem_of_union_l.
    apply elem_of_singleton_2.
    rewrite HIn.
    reflexivity.
    apply finz_succN_in_seq; simpl; lia.
    rewrite HIn.
    rewrite to_pid_aligned_eq.
    assumption.
    apply finz_succN_in_seq; simpl; lia.
    iFrame.
    iModIntro.
    iIntros "(PCz & _ & acc & tx & R0z) _".
    rewrite wp_sswp.
    iEval (rewrite finz_plus_one_simpl) in "PCz".
    rewrite Z_of_nat_simpl.
    iEval (simpl) in "PCz".
    iApply ((@mov_word _ _ _ _ _ _ _ _ _ ({[tpa addr]} ∪ {[p_pg0; tpa p_tx0]}) (tpa p_tx0) (p_pg0 ^+ 30%nat)%f (encode_vmid V1) R1) with "[p_31 PCz acc tx R1z]").
    apply decode_encode_instruction.
    apply elem_of_union_r.
    apply elem_of_union_l.
    apply elem_of_singleton_2.
    rewrite HIn.
    reflexivity.
    apply finz_succN_in_seq; simpl; lia.
    rewrite HIn.
    rewrite to_pid_aligned_eq.
    assumption.
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
    | |- context G [memory_page p_rx1 ?s] => set β := s
    end.
    assert (β !! (of_imm p_rx1imm) = Some wh) as Hrx.
    {
      subst β.
      simpl.
      apply lookup_union_Some_l.
      rewrite Hdescr.
      simpl.
      assert (α = wh) as ->.
      {
        rewrite map_subseteq_spec in descrsubseteq.
        specialize (descrsubseteq (of_imm p_tx0imm) α).
        feed specialize descrsubseteq.
        {
          apply elem_of_list_to_map_1.
          apply NoDup_singleton.
          rewrite <-Htxeq.
          rewrite to_pid_aligned_eq.
          apply elem_of_list_singleton.
          reflexivity.
        }
        apply lookup_insert_rev in descrsubseteq.
        by symmetry.
      }
      rewrite Hrxeq.
      apply lookup_insert.
    }
    iApply ((@run _ _ _ _ _ hvc_I run_I (encode_vmid V1) 1%Qp ({[tpa addr]} ∪ {[p_pg0; tpa p_tx0]}) (tpa p_tx0) ((PC @@ V0 ->r (p_pg0 ^+ 32%nat)%f) ∗ (V0 -@A> ({[tpa addr]} ∪ {[p_pg0; tpa p_tx0]})) ∗ (TX@V0:=tpa p_tx0))%I (R0 @@ V0 ->r run_I ∗ R1 @@ V0 ->r encode_vmid V1 ∗ addr ->a two ∗ (∃ (wh0 : Addr) (β0 : mem), (trans_mapsto wh0 (DfracOwn 1) (Some (V0, V1, {[tpa addr]}, Sharing)) ∗ ⌜valid_transaction (V0, V1, {[tpa addr]}, Sharing)⌝) ∗ retri_mapsto wh0 (DfracOwn 1) (Some false) ∗ rx_state_mapsto V1 1 (Some (finz.FinZ 1 one_obligation_1 one_obligation_2, V0)) ∗ ⌜
                  V0 ≠ V1⌝ ∗ RX@V1:=p_rx1 ∗ memory_page p_rx1 β0 ∗ ⌜β0 !! (of_imm p_rx1imm) = Some wh0⌝) ∗ VMProp 0 ((R0 @@ V0 ->r yield_I ∗ R1 @@ V0 ->r encode_vmid V1 ∗ addr ->a four) ∗ VMProp 1 False (1 / 2)) (1 / 2)) True%I (p_pg0 ^+ 31%nat)%f V1 True%I ((R0 @@ V0 ->r yield_I ∗ R1 @@ V0 ->r encode_vmid V1 ∗ addr ->a four) ∗ VMProp 1 False (1 / 2))%I) with "[PCz p_32 acc tx R0z R1z prop0 prop1 mem rxmem whretri whtans RX1page RX1st]").
    apply elem_of_union_r.
    apply elem_of_union_l.
    apply elem_of_singleton_2.
    rewrite HIn.
    reflexivity.
    apply finz_succN_in_seq; simpl; lia.
    rewrite HIn.
    rewrite to_pid_aligned_eq.
    assumption.
    apply finz_succN_in_seq; simpl; lia.
    done.
    apply decode_encode_instruction.
    by rewrite decode_encode_hvc_func.
    by rewrite decode_encode_vmid.
    iSplitL "PCz p_32 acc tx R0z R1z".
    iFrame.
    iSplitL "prop1".
    iNext.
    simpl.
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
      iExists wh, β.
      simpl.
      iFrame.
      iSplitL "whtans".
      iDestruct "whtans" as "(whtans & %whprop)".
      iFrame.
      iPureIntro.
      done.
      iDestruct "whretri" as "(whretri & %whprop)".
      iDestruct "RX1st" as "(RX1st & %whprop')".
      iFrame.
      iSplit; done.
    }
    iModIntro.
    iIntros "[(PCz & acc & tx) prop0] Hholds".
    iDestruct (VMProp_holds_agree with "[Hholds prop0]") as "[P' prop0]".
    simpl.
    iFrame "Hholds prop0".
    (* getting back resources *)
    iDestruct "P'" as "((>R0z & >R1z & >mem) & prop1)".
    rewrite wp_sswp.
    iApply ((@mov_word _ _ _ _ _ _ _ _ _ ({[tpa addr]} ∪ {[p_pg0; tpa p_tx0]}) (tpa p_tx0) (p_pg0 ^+ 32%nat)%f run_I R0) with "[p_33 PCz acc tx R0z]").
    apply decode_encode_instruction.
    apply elem_of_union_r.
    apply elem_of_union_l.
    apply elem_of_singleton_2.
    rewrite HIn.
    reflexivity.
    apply finz_succN_in_seq; simpl; lia.
    rewrite HIn.
    rewrite to_pid_aligned_eq.
    assumption.
    apply finz_succN_in_seq; simpl; lia.
    iFrame.
    iModIntro.
    iIntros "(PCz & _ & acc & tx & R0z) _".
    rewrite wp_sswp.
    iEval (rewrite finz_plus_one_simpl) in "PCz".
    rewrite Z_of_nat_simpl.
    iEval (simpl) in "PCz".
    iApply ((@mov_word _ _ _ _ _ _ _ _ _ ({[tpa addr]} ∪ {[p_pg0; tpa p_tx0]}) (tpa p_tx0) (p_pg0 ^+ 33%nat)%f (encode_vmid V2) R1) with "[p_34 PCz acc tx R1z]").
    apply decode_encode_instruction.
    apply elem_of_union_r.
    apply elem_of_union_l.
    apply elem_of_singleton_2.
    rewrite HIn.
    reflexivity.
    apply finz_succN_in_seq; simpl; lia.
    rewrite HIn.
    rewrite to_pid_aligned_eq.
    assumption.
    apply finz_succN_in_seq; simpl; lia.
    iFrame.
    iModIntro.
    iIntros "(PCz & _ & acc & tx & R1z) _".
    rewrite wp_sswp.
    iEval (rewrite finz_plus_one_simpl) in "PCz".
    rewrite Z_of_nat_simpl.
    iEval (simpl) in "PCz".    
    iApply ((@run _ _ _ _ _ hvc_I run_I (encode_vmid V2) 1%Qp ({[tpa addr]} ∪ {[p_pg0; tpa p_tx0]}) (tpa p_tx0) ((PC @@ V0 ->r (p_pg0 ^+ 35%nat)%f) ∗ (V0 -@A> ({[tpa addr]} ∪ {[p_pg0; tpa p_tx0]})) ∗ (TX@V0:=tpa p_tx0))%I (fixpoint (vmprop_unknown_pre V2) ∅) ((R0 @@ V0 ->r yield_I ∗ R1 @@ V0 ->r encode_vmid V1 ∗ addr ->a finz.FinZ 4 four_obligation_1 four_obligation_2) ∗ VMProp 1 False (1 / 2))%I (p_pg0 ^+ 34%nat)%f V2 True%I ((R0 @@ V0 ->r yield_I ∗ R1 @@ V0 ->r encode_vmid V2) ∗ VMProp 1 False (1 / 2))%I) with "[PCz p_35 acc tx R0z R1z prop0 prop2]").
    apply elem_of_union_r.
    apply elem_of_union_l.
    apply elem_of_singleton_2.
    rewrite HIn.
    reflexivity.
    apply finz_succN_in_seq; simpl; lia.
    rewrite HIn.
    rewrite to_pid_aligned_eq.
    assumption.
    apply finz_succN_in_seq; simpl; lia.
    done.
    apply decode_encode_instruction.
    by rewrite decode_encode_hvc_func.
    by rewrite decode_encode_vmid.
    iFrame.
    {
      iSplitL.
      iNext.
      iIntros "((PCz & _ & acc & tx & R0z & R1z) & _ & prop0)".
      iEval (rewrite finz_plus_one_simpl) in "PCz".
      rewrite Z_of_nat_simpl.
      iEval (simpl) in "PCz".    
      iFrame.
      unfold vmprop_unknown_pre.
      admit.
      done.
    }
    iModIntro.
    iIntros "[(PCz & acc & tx) prop0] Hholds".
    iDestruct (VMProp_holds_agree with "[Hholds prop0]") as "[P' prop0]".
    simpl.
    iFrame "Hholds prop0".
    (* getting back resources *)
    iDestruct "P'" as "((>R0z & >R1z) & prop1')".
    rewrite wp_sswp.
    clear -HIn Hnottx.
    iApply ((halt (p_pg0 ^+ 35%nat)%f) with "[PCz p_36 acc tx]"); iFrameAutoSolve.
    apply elem_of_union_r.
    apply elem_of_union_l.
    apply elem_of_singleton_2.
    rewrite HIn.
    reflexivity.
    apply finz_succN_in_seq; simpl; lia.
    rewrite HIn.
    rewrite to_pid_aligned_eq.
    assumption.
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
  Admitted.

End proof.
