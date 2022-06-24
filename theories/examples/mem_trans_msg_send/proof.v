From machine_program_logic.program_logic Require Import weakestpre.
From HypVeri.algebra Require Import base lower_bound mem.
From HypVeri.rules Require Import rules_base mov halt run yield mem_send mem_retrieve mem_relinquish mem_reclaim ldr str msg_send msg_wait msg_poll add.
From HypVeri.examples Require Import instr utils.
From HypVeri.logrel Require Import logrel logrel_extra.
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

(* Ltac fold_finz_plus_one := *)
(*   match goal with *)
(*   | H : context G [(?p ^+ 1)%f] |- _ => fold_finz_plus_one' H *)
(*   end. *)

Program Instance rywu_vmconfig : HypervisorConstants :=
    {vm_count := 3;
     vm_count_pos:= _}.

Program Definition V1 : VMID := (@nat_to_fin 1 _ _).
Program Definition V2 : VMID := (@nat_to_fin 2 _ _).

Program Definition zero : Imm := I (finz.FinZ 0 _ _) _.
Program Definition one : Imm := I (finz.FinZ 1 _ _) _.
Program Definition two : Imm := I (finz.FinZ 2 _ _) _.
Program Definition four : Imm := I (finz.FinZ 4 _ _) _.
Program Definition mem_descriptor_length : Imm := I (finz.FinZ 6 _ _) _.

Section proof.

  Context `{hypparams: !HypervisorParameters}.  

  Definition rywu_program0 (addr tx_base : Imm) : list Word :=
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
      mov_word_I R0 mem_lend_I;
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
      (* Run VM 1 *)
      mov_word_I R0 run_I;
      mov_word_I R1 (encode_vmid V1);
      hvc_I;
      (* Reclaim page *)
      mov_word_I R0 mem_reclaim_I;
      mov_reg_I R1 R3;
      hvc_I;
      (* Run VM 2 (unknown vm *)
      mov_word_I R0 run_I;
      mov_word_I R1 (encode_vmid V2);
      hvc_I;
      (* Stop *)
      halt_I
    ].

  Definition rywu_program1 (addr rx_base : Imm) : list Word :=
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
      (* Relinquish page *)
      mov_word_I R0 mem_relinquish_I;
      mov_reg_I R1 R4;
      hvc_I;
      (* Yield back *)
      mov_word_I R0 yield_I;
      hvc_I
    ].

  (* Lemma tpa_plus_one_simple : ∀ p, tpa (p ^+ 1)%f = tpa p. *)
  (* Proof. *)
  (*   intros p. *)
    
  (* Qed. *)

  Context `{!gen_VMG Σ}.
  Notation VMProp_2 p_tx p_rx:= (vmprop_unknown V2 p_tx p_rx ∅) (only parsing).
  
  Lemma rywu_machine0 p_pg0 (p_tx0 : PID) p_pg2 p_tx2 p_rx0 p_rx1 p_rx2 (addr : Imm) p_tx0imm (p_pg0imm : Imm) :
    let RX0 := (RX_state@V0 := None ∗ mailbox.rx_page V0 p_rx0 ∗ ∃ mem_rx, memory_page p_rx0 mem_rx)%I in
    let RX1 := (RX_state@V1 := None ∗ mailbox.rx_page V1 p_rx1 ∗ ∃ mem_rx, memory_page p_rx1 mem_rx)%I in
    let RX2 := (RX_state@V2 := None ∗ mailbox.rx_page V2 p_rx2 ∗ ∃ mem_rx, memory_page p_rx2 mem_rx)%I in
    let program0 := rywu_program0 addr p_tx0imm in
    (* Disjoint pages *)
    (of_pid p_tx0 = p_tx0imm) ->
    (of_pid p_pg0 = p_pg0imm) ->
    (p_pg0 ∉ ({[(tpa addr); p_tx0; p_pg2; p_tx2; p_rx2]}:gset _)) ->
    tpa addr ≠ p_rx0 ->
    tpa addr ≠ p_pg0 ->
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
      VMProp V1 ((R0 @@ V0 ->r run_I ∗ R1 @@ V0 ->r encode_vmid V1) ∗
                    VMProp V0 ((R0 @@ V0 ->r yield_I ∗ R1 @@ V0 ->r encode_vmid V1) ∗
                                 VMProp V1 False%I (1/2)%Qp) (1/2)%Qp)%I (1/2)%Qp ∗
      (* Protocol for unknown vm *)
      VMProp V2 (VMProp_2 p_tx2 p_rx2) (1/2)%Qp ∗
      (* Pages for unknown VM *)            
      V2 -@{1/2}A> {[p_pg2;p_tx2;p_rx2]} ∗
      LB_auth ∅ ∗
      trans.fresh_handles 1 hs_all ∗
      (* RX states *)               
      RX0 ∗ RX1 ∗ RX2 
      ⊢ WP ExecI @ V0
            {{ (λ m,
                 ⌜m = HaltI⌝ ∗
                 (* program program0 (of_pid p_pg0) ∗ *)
                 addr ->a four ∗       
                 V0 -@A> {[p_pg0; (tpa addr)]} ∗
                 TX@ V0 := (tpa p_tx0) ∗
                 PC @@ V0 ->r ((of_pid p_pg0) ^+ (length program0))%f ∗
                 R0 @@ V0 ->r yield_I ∗
                 R1 @@ V0 ->r encode_vmid V1
                 )}}%I.
  Proof.
    rewrite /vmprop_unknown.
    iIntros (Htxeq Hpgeq HnIn_p HneAddr_RX0 HneAddr_PG0 HneTX0_RX0 HIn) "((p_1 & p_2 & p_3 & p_4 & p_5 & p_6 & p_7 
            & p_8 & p_9 & p_10 & p_11 & p_12 & p_13 & p_14 & p_15 & p_16 
            & p_17 & p_18 & p_19 & p_20 & p_21 & p_22 & p_23 & p_24 & p_25
            & p_26 & p_27 & p_28 & p_29 & p_30 & p_31 & p_32 & p_33 & p_34
            & p_35 & p_36 & p_37 & p_38 & p_39 & _) 
         & (%memv & mem) & (%txmemgm & txmem) & OE & acc & tx & PCz & (%r0 & R0z) & (%r1 & R1z) & (%r2 & R2z) 
         & (%r3 & R3z) & (%r4 & R4z) & (%r5 & R5z) 
         & prop0 & prop1 & prop2 & acc2 & LB_auth & hp & (RX0st & (RX0page & RX0own & RX0excl) & RX0mem) 
         & (RX1st & (RX1page & RX1own & RX1excl) & RX1mem) & (RX2st & (RX2page & RX2own & RX2excl) & RX2mem))".
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
    simpl.
    TODO: bug
  Abort.
    cbn in domtxmem.
    simpl in domtxmem.
    clear HnIn_p domtxmem.
    (* clear -HnIn_p HIn Hnottx. *)
    auto.
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
    iApply ((@add _ _ _ _ _ _ (add_I R5 R3) p_tx0imm one 1%Qp (tpa p_tx0) (((((((p_pg0 ^+ 1) ^+ 1) ^+ 1) ^+ 1) ^+ 1) ^+ 1) ^+ 1)%f R5 R3 ({[tpa addr]} ∪ {[p_pg0; tpa p_tx0]})) with "[p_8 PCz acc R5z R3z tx]").
    apply decode_encode_instruction.
    apply elem_of_union_r.
    apply elem_of_union_l.
    apply elem_of_singleton_2.
    rewrite HIn.
    reflexivity.
    set_solver +.
    rewrite HIn.
    rewrite to_pid_aligned_eq.
    assumption.
    set_solver +.
    iFrame.    
    iModIntro.
    iIntros "(PCz & _ & R5z & R3z & acc & tx) _".
    (* mov_word_I R4 zero *)
    rewrite wp_sswp.
    iApply ((@mov_word _ _ _ _ _ _ _ _ _ ({[tpa addr]} ∪ {[p_pg0; tpa p_tx0]}) (tpa p_tx0) ((((((((p_pg0 ^+ 1) ^+ 1) ^+ 1) ^+ 1) ^+ 1) ^+ 1) ^+ 1) ^+ 1)%f zero R4) with "[p_9 PCz acc tx R4z]").
    apply decode_encode_instruction.
    apply elem_of_union_r.
    apply elem_of_union_l.
    apply elem_of_singleton_2.
    rewrite HIn.
    reflexivity.
    set_solver +.    
    rewrite HIn.
    rewrite to_pid_aligned_eq.
    assumption.
    set_solver +.
    iFrame.
    iModIntro.
    iIntros "(PCz & _ & acc & tx & R4z) _".
    (* str_I R4 R5 *)
    rewrite wp_sswp.
    iApply ((@str _ _ _ _ _ _ _ zero w2 1%Qp p_rx0 (tpa p_tx0) ({[tpa addr]} ∪ {[p_pg0; tpa p_tx0]}) (((((((((p_pg0 ^+ 1) ^+ 1) ^+ 1) ^+ 1) ^+ 1) ^+ 1) ^+ 1) ^+ 1) ^+ 1)%f (p_tx0 ^+ 1)%f R4 R5) with "[p_10 PCz acc txmem2 RX0page tx R4z R5z]").
    apply decode_encode_instruction.
    apply union_subseteq_r'.
    apply union_least.
    rewrite singleton_subseteq_l.    
    apply elem_of_union_r.
    apply elem_of_singleton_2.
    {
      rewrite to_pid_aligned_eq.
      apply to_pid_aligned_in_page.
      unfold addr_in_page.
      split.
      apply Is_true_true_2.
      solve_finz.
      apply Is_true_true_2.
      solve_finz.
    }
    rewrite singleton_subseteq_l.
    apply elem_of_union_l.
    apply elem_of_singleton_2.
    apply HIn.
    set_solver +.
    rewrite HIn.
    rewrite to_pid_aligned_eq.
    assumption.
    set_solver +.
    assert (tpa (p_tx0 ^+ 1)%f = p_tx0) as ->.
    {
      apply to_pid_aligned_in_page.
      unfold addr_in_page.
      split.
      apply Is_true_true_2.
      solve_finz.
      apply Is_true_true_2.
      solve_finz.
    }
    assumption.
    rewrite Htxeq.
    iFrame.
    iModIntro.
    iIntros "(PCz & _ & R5z & txmem2 & R4z & acc & tx & RX0page) _".
    (* add_I R5 R3 *)
    rewrite wp_sswp.
    iApply (@add _ _ _ _ _ _ (add_I R5 R3) (p_tx0imm ^+ 1)%f one 1%Qp (tpa p_tx0)
              ((((((((((p_pg0 ^+ 1) ^+ 1) ^+ 1) ^+ 1) ^+ 1) ^+ 1) ^+ 1) ^+ 1) ^+ 1) ^+ 1)%f
              R5 R3 ({[tpa addr]} ∪ {[p_pg0; tpa p_tx0]}) with "[p_11 PCz acc R5z R3z tx]").
    apply decode_encode_instruction. 
    apply elem_of_union_r.
    apply elem_of_union_l.
    apply elem_of_singleton_2.
    {
      apply to_pid_aligned_in_page.
      unfold addr_in_page.
      split.
      apply Is_true_true_2.
      solve_finz.
      apply Is_true_true_2.
      solve_finz.
    }
    rewrite HIn.
    rewrite to_pid_aligned_eq.
    assumption.
    set_solver +.
    rewrite Htxeq.
    iFrame.
    iModIntro.
    iIntros "(PCz & _ & R5z & R3z & acc & tx) _".
    (* (* mov_word_I R4 one *) *)
    rewrite wp_sswp.
    iApply ((@mov_word _ _ _ _ _ _ _ _ _ ({[tpa addr]} ∪ {[p_pg0; tpa p_tx0]}) (tpa p_tx0)
               (((((((((((p_pg0 ^+ 1) ^+ 1) ^+ 1) ^+ 1) ^+ 1) ^+ 1) ^+ 1) ^+ 1) ^+ 1) ^+ 1) ^+ 1)%f
               one R4) with "[p_12 PCz acc tx R4z]").
    apply decode_encode_instruction.
    apply elem_of_union_r.
    apply elem_of_union_l.
    apply elem_of_singleton_2.
    {
      apply to_pid_aligned_in_page.
      unfold addr_in_page.
      split.
      apply Is_true_true_2.
      solve_finz.
      apply Is_true_true_2.
      solve_finz.
    }
    rewrite HIn.
    rewrite to_pid_aligned_eq.
    assumption.
    set_solver +.
    rewrite Htxeq.
    iFrame.
    iModIntro.
    iIntros "(PCz & _ & R5z & R3z & acc & tx) _".
    (* iApply ((mov_word _ one R4) with "[p_12 PCz acc tx R4z]"); iFrameAutoSolve. *)
    (* rewrite HIn. *)
    (* set_solver +. *)
    (* set_solver +. *)
    (* rewrite HIn. *)
    (* assumption. *)
    (* set_solver +. *)
    (* iModIntro. *)
    (* iIntros "(PCz & _ & acc & tx & R4z) _". *)
    (* (* str_I R4 R5 *) *)
    (* rewrite wp_sswp. *)
    (* iDestruct "txmem" as "(txmem3 & txmem)". *)
    (* iApply ((str _ ((p_tx0 ^+ 1) ^+ 1)%f R4 R5) with "[p_13 PCz acc txmem3 RX0page tx R4z R5z]"); iFrameAutoSolve. *)
    (* (* solvable *) *)
    (* admit. *)
    (* rewrite HIn. *)
    (* assumption. *)
    (* set_solver +. *)
    (* assert (tpa ((p_tx0 ^+ 1) ^+ 1)%f = tpa p_tx0) as ->. *)
    (* admit. *)
    (* assert (tpa p_tx0 ≠ p_rx0) as temp. *)
    (* admit. *)
    (* exact temp. *)
    (* iModIntro. *)
    (* iIntros "(PCz & _ & R5z & txmem3 & R4z & acc & tx & RX0page) _". *)
    (* (* add_I R5 R3 *) *)
    (* rewrite wp_sswp. *)
    (* iApply ((add _ R5 R3 _) with "[p_14 PCz acc R5z R3z tx]"); iFrameAutoSolve. *)
    (* apply elem_of_union_r. *)
    (* apply elem_of_union_l. *)
    (* apply elem_of_singleton_2. *)
    (* rewrite HIn. *)
    (* reflexivity. *)
    (* set_solver +. *)
    (* rewrite HIn. *)
    (* assumption. *)
    (* set_solver +. *)
    (* iModIntro. *)
    (* iIntros "(PCz & _ & R5z & R3z & acc & tx) _". *)
    (* (* mov_word_I R4 (encode_vmid V1) *) *)
    (* rewrite wp_sswp. *)
    (* iApply ((mov_word _ (encode_vmid V1) R4) with "[p_15 PCz acc tx R4z]"); iFrameAutoSolve. *)
    (* rewrite HIn. *)
    (* set_solver +. *)
    (* set_solver +. *)
    (* rewrite HIn. *)
    (* assumption. *)
    (* set_solver +. *)
    (* iModIntro. *)
    (* iIntros "(PCz & _ & acc & tx & R4z) _". *)
    (* (* str_I R4 R5 *) *)
    (* rewrite wp_sswp. *)
    (* iDestruct "txmem" as "(txmem4 & txmem)". *)
    (* iApply ((str _ (((p_tx0 ^+ 1) ^+ 1) ^+ 1)%f R4 R5) with "[p_16 PCz acc txmem4 RX0page tx R4z R5z]"); iFrameAutoSolve. *)
    (* (* solvable *) *)
    (* admit. *)
    (* rewrite HIn. *)
    (* assumption. *)
    (* set_solver +. *)
    (* assert (tpa (((p_tx0 ^+ 1) ^+ 1) ^+ 1)%f = tpa p_tx0) as ->. *)
    (* admit. *)
    (* assert (tpa p_tx0 ≠ p_rx0) as temp. *)
    (* admit. *)
    (* exact temp. *)
    (* iModIntro. *)
    (* iIntros "(PCz & _ & R5z & txmem4 & R4z & acc & tx & RX0page) _". *)
    (* (* add_I R5 R3 *) *)
    (* rewrite wp_sswp. *)
    (* iApply ((add _ R5 R3 _) with "[p_17 PCz acc R5z R3z tx]"); iFrameAutoSolve. *)
    (* apply elem_of_union_r. *)
    (* apply elem_of_union_l. *)
    (* apply elem_of_singleton_2. *)
    (* rewrite HIn. *)
    (* reflexivity. *)
    (* set_solver +. *)
    (* rewrite HIn. *)
    (* assumption. *)
    (* set_solver +. *)
    (* iModIntro. *)
    (* iIntros "(PCz & _ & R5z & R3z & acc & tx) _". *)
    (* (* mov_word_I R4 addr *) *)
    (* rewrite wp_sswp. *)
    (* iApply ((mov_word _ addr R4) with "[p_18 PCz acc tx R4z]"); iFrameAutoSolve. *)
    (* rewrite HIn. *)
    (* set_solver +. *)
    (* set_solver +. *)
    (* rewrite HIn. *)
    (* assumption. *)
    (* set_solver +. *)
    (* iModIntro. *)
    (* iIntros "(PCz & _ & acc & tx & R4z) _". *)
    (* (* str_I R4 R5 *) *)
    (* rewrite wp_sswp. *)
    (* iDestruct "txmem" as "(txmem5 & _)". *)
    (* iApply ((str _ ((((p_tx0 ^+ 1) ^+ 1) ^+ 1) ^+ 1)%f R4 R5) with "[p_19 PCz acc txmem5 RX0page tx R4z R5z]"); iFrameAutoSolve. *)
    (* (* solvable *) *)
    (* admit. *)
    (* rewrite HIn. *)
    (* assumption. *)
    (* set_solver +. *)
    (* assert (tpa ((((p_tx0 ^+ 1) ^+ 1) ^+ 1) ^+ 1)%f = tpa p_tx0) as ->. *)
    (* admit. *)
    (* assert (tpa p_tx0 ≠ p_rx0) as temp. *)
    (* admit. *)
    (* exact temp. *)
    (* iModIntro. *)
    (* iIntros "(PCz & _ & R5z & txmem5 & R4z & acc & tx & RX0page) _". *)
    (* (* mov_word_I R0 mem_lend_I *) *)
    (* rewrite wp_sswp. *)
    (* iApply ((mov_word _ mem_lend_I R0) with "[p_20 PCz acc tx R0z]"); iFrameAutoSolve. *)
    (* rewrite HIn. *)
    (* set_solver +. *)
    (* set_solver +. *)
    (* rewrite HIn. *)
    (* assumption. *)
    (* set_solver +. *)
    (* iModIntro. *)
    (* iIntros "(PCz & _ & acc & tx & R0z) _". *)
    (* (* mov_word_I R1 mem_descriptor_length *) *)
    (* rewrite wp_sswp. *)
    (* iApply ((mov_word _ mem_descriptor_length R1) with "[p_21 PCz acc tx R1z]"); iFrameAutoSolve. *)
    (* rewrite HIn. *)
    (* set_solver +. *)
    (* set_solver +. *)
    (* rewrite HIn. *)
    (* assumption. *)
    (* set_solver +. *)
    (* iModIntro. *)
    (* iIntros "(PCz & _ & acc & tx & R1z) _". *)
    (* (* lend *) *)
    (* rewrite wp_sswp. *)
    (* iApply ((mem_lend (p_tx := tpa p_tx0) (wi := hvc_I) (hvcf := Lend) *)
    (*            (sacc := ({[tpa addr]} ∪ {[p_pg0; tpa p_tx0]}))  *)
    (*            (r0 := mem_lend_I) (r1 := mem_descriptor_length) (r2 := r2) *)
    (*            (((((((((((((((((((((p_pg0 ^+ 1) ^+ 1) ^+ 1) ^+ 1) ^+ 1) ^+ 1) ^+ 1) ^+ 1) ^+ 1) ^+ 1) ^+ 1) ^+ 1) ^+ 1) ^+ 1) ^+ 1) ^+ 1) ^+ 1) ^+ 1) ^+ 1) ^+ 1) ^+ 1)%f *)
    (*            V1 ({[ of_imm p_tx0 := of_imm (encode_vmid V0); *)
    (*                           (p_tx0 ^+ 1)%f := of_imm zero; *)
    (*                           ((p_tx0 ^+ 1) ^+ 1)%f := of_imm one; *)
    (*                           (((p_tx0 ^+ 1) ^+ 1) ^+ 1)%f := of_imm (encode_vmid V1); *)
    (*                           ((((p_tx0 ^+ 1) ^+ 1) ^+ 1) ^+ 1)%f := of_imm addr ]} : gmap Addr Addr) *)
    (*            hs_all (singleton (tpa addr))) *)
    (*          with "[p_22 PCz acc R0z R1z R2z hp tx txmem1 txmem2 txmem3 txmem4 txmem5]"). *)
    (* { *)
    (*   apply elem_of_union_r. *)
    (*   apply elem_of_union_l. *)
    (*   apply elem_of_singleton_2. *)
    (*   rewrite HIn. *)
    (*   reflexivity. *)
    (*   set_solver +. *)
    (* } *)
    (* { *)
    (*   rewrite HIn. *)
    (*   assumption. *)
    (*   set_solver +. *)
    (* } *)
    (* { *)
    (*   apply decode_encode_instruction. *)
    (* } *)
    (* { *)
    (*   apply decode_encode_hvc_func. *)
    (* } *)
    (* { *)
    (*   reflexivity. *)
    (* } *)
    (* { *)
    (*   unfold mem_descriptor_length. *)
    (*   simpl. *)
    (*   lia. *)
    (* } *)
    (* { *)
    (*   (* clear. *) *)
    (*   (* unfold parse_transaction_descriptor. *) *)
    (*   (* unfold parse_list_of_Word. *) *)
    (*   (* unfold monad.List.sequence_a_list. *) *)
    (*   (* unfold sequence_a. *) *)
    (*   (* unfold List.traversable_list. *) *)
    (*   (* unfold monad.List.sequence_a_list. *) *)
    (*   admit. *)
    (* } *)
    (* { *)
    (*   auto. *)
    (* } *)
    (* { *)
    (*   set_solver +. *)
    (* } *)
    (* { *)
    (*   unfold hs_all. *)
    (*   clear. *)
    (*   apply non_empty_inhabited_L with W0. *)
    (*   apply elem_of_union_l. *)
    (*   apply elem_of_singleton_2. *)
    (*   reflexivity. *)
    (* } *)
    (* { *)
    (*   iFrame. *)
    (*   iSplitR "txmem1 txmem2 txmem3 txmem4 txmem5". *)
    (*   (* ([∗ set] p ∈ {[tpa addr]}, p -@O> V0 ∗ p -@E> true) *) *)
    (*   admit. *)
    (*   iNext. *)
    (*   unfold memory_page. *)
    (*   iSplit. *)
    (*   - admit. (* fix descriptor *) *)
    (*   - clear. *)
    (*     rewrite ->4big_opM_insert; *)
    (*       rewrite ?lookup_insert_None; *)
    (*       rewrite ?lookup_singleton_None; *)
    (*       rewrite ?lookup_empty. *)
    (*     rewrite big_opM_singleton. *)
    (*     iFrame. *)
    (*     all: destruct p_tx0 as [[a1 a2] b];           *)
    (*       simpl in b; *)
    (*       unfold finz.incr_default; *)
    (*       unfold finz.largest; *)
    (*       simpl; *)
    (*       intuition; *)
    (*       try solve_finz. *)
    (* } *)
    (* iModIntro. *)
    (* iIntros "(PCz & _ & OE & acc & R0z & R1z & (%wh & whin & R2z & whtans & whretri & whfresh) & tx & txmem) _". *)
    (* assert ((({[tpa addr]} ∪ {[p_pg0; tpa p_tx0]}) ∖ {[tpa addr]}) = {[p_pg0; tpa p_tx0]}) as ->. *)
    (* { *)
    (*   (* tpa addr ≠ p_pg0 *) *)
    (*   admit. *)
    (* } *)
    (* (* mov_word_I R5 p_tx0 *) *)
    (* rewrite wp_sswp. *)
    (* iApply ((mov_word _ p_tx0 R5) with "[p_23 PCz acc tx R5z]"); iFrameAutoSolve. *)
    (* rewrite HIn. *)
    (* set_solver +. *)
    (* set_solver +. *)
    (* rewrite HIn. *)
    (* assumption. *)
    (* set_solver +. *)
    (* iModIntro. *)
    (* iIntros "(PCz & _ & acc & tx & R5z) _". *)
    (* (* str_I R2 R5 *) *)
    (* rewrite wp_sswp.     *)
    (* iApply ((str _ _ R2 R5) with "[p_24 PCz acc txmem RX0page tx R2z R5z]"); iFrameAutoSolve. *)
    (* (* solvable *) *)
    (* admit. *)
    (* rewrite HIn. *)
    (* assumption. *)
    (* set_solver +. *)
    (* assert (tpa p_tx0 ≠ p_rx0) as temp. *)
    (* admit. *)
    (* exact temp. *)
    (* admit. *)
    (* iModIntro. *)
    (* iIntros "(PCz & _ & R5z & txmem & R2z & acc & tx & RX0page) _". *)
    (* rewrite wp_sswp. *)
    (* (* mov_reg_I R3 R3 *) *)
    (* iApply ((mov_reg _ _ R3 R2) with "[p_25 PCz acc tx R2z R3z]"); iFrameAutoSolve. *)
    (* admit. *)
    (* rewrite HIn. *)
    (* assumption. *)
    (* set_solver +. *)
    (* iModIntro. *)
    (* iIntros "(PCz & _ & acc & tx & R3z & R2z) _". *)
    (* (* mov_word_I R0 msg_send_I *) *)
    (* rewrite wp_sswp. *)
    (* iApply ((mov_word _ msg_send_I R0) with "[p_26 PCz acc tx R0z]"); iFrameAutoSolve. *)
    (* rewrite HIn. *)
    (* set_solver +. *)
    (* set_solver +. *)
    (* rewrite HIn. *)
    (* assumption. *)
    (* set_solver +. *)
    (* iModIntro. *)
    (* iIntros "(PCz & _ & acc & tx & R0z) _". *)
    (* (* mov_word_I R1 one *) *)
    (* rewrite wp_sswp. *)
    (* iApply ((mov_word _ (encode_vmid V1) R1) with "[p_27 PCz acc tx R1z]"); iFrameAutoSolve. *)
    (* rewrite HIn. *)
    (* set_solver +. *)
    (* set_solver +. *)
    (* rewrite HIn. *)
    (* assumption. *)
    (* set_solver +. *)
    (* iModIntro. *)
    (* iIntros "(PCz & _ & acc & tx & R1z) _". *)
    (* (* mov_word_I R2 one *) *)
    (* rewrite wp_sswp. *)
    (* iApply ((mov_word _ one R2) with "[p_28 PCz acc tx R2z]"); iFrameAutoSolve. *)
    (* rewrite HIn. *)
    (* set_solver +. *)
    (* set_solver +. *)
    (* rewrite HIn. *)
    (* assumption. *)
    (* set_solver +. *)
    (* iModIntro. *)
    (* iIntros "(PCz & _ & acc & tx & R2z) _". *)
    (* (* send *) *)
    (* rewrite wp_sswp. *)
    (* iApply ((msg_send_primary _ V1) with "[p_29 PCz acc R0z R1z R2z tx txmem RX1st RX1page RX1mem]"); iFrameAutoSolve. *)
    (* (* BP *) *)

    
    (* iDestruct (lb_update_alloc V2 {[p_pg0]} with "LB_auth") as ">[LB_auth LB2]";first done. *)
    (* rewrite wp_sswp. *)
    (* iApply ((run (((p_pg0 ^+ 1) ^+ 1))%f V2 (R := True%I) *)
    (*             (R' := PC @@ V0 ->r (((p_pg0 ^+ 1) ^+ 1) ^+ 1)%f *)
    (*                              ∗((p_pg0 ^+ 1) ^+ 1)%f ->a hvc_I ∗ V0 -@A> {[p_pg0]} ∗ TX@ V0 := p_tx0) *)
    (*             ) with "[PCz p_3 acc tx R0z R1z R2z prop0 prop2 acc2 LB2 hp R0 R1 R2]"); try rewrite HIn //; iFrameAutoSolve. *)
    (* { set_solver +. } *)
    (* { set_solver +. } *)
    (* { set_solver +. } *)
    (* { apply decode_encode_hvc_func. } *)
    (* { apply decode_encode_vmid. } *)
    (* { iSplitL "prop2". *)
    (*   iFrame. *)
    (*   iSplitL "prop0". *)
    (*   done. *)
    (*   iSplitR "";last done. *)
    (*   iNext. *)
    (*   iIntros "((PC & addr & acc & tx & R0' & R1') & _ & prop0)". *)
    (*   iFrame "PC addr R0' R1' acc tx". *)
    (*   iExists {[p_pg0]}, {[p_pg2;p_tx2;p_rx2]} , ∅, None. *)
    (*   iFrame "acc2 LB2". *)
    (*   iSplitL "". *)
    (*   iPureIntro. set_solver + HnIn_p. *)
    (*   iSplitL "hp". *)
    (*   { *)
    (*     iExists hs_all. *)
    (*     iSplitL "". *)
    (*     iPureIntro. *)
    (*     rewrite dom_empty_L union_empty_r_L //. *)
    (*     iFrame. *)
    (*     rewrite big_sepM_empty //. *)
    (*   } *)
    (*   iSplitL "". *)
    (*   { *)
    (*     rewrite /transaction_pagetable_entries_transferred. *)
    (*     rewrite /base_extra.big_sepFM. *)
    (*     rewrite map_filter_empty big_sepM_empty //. *)
    (*   } *)
    (*   iSplitL "". *)
    (*   { *)
    (*     rewrite /retrieval_entries_transferred. *)
    (*     rewrite /base_extra.big_sepFM. *)
    (*     rewrite map_filter_empty big_sepM_empty //. *)
    (*   } *)
    (*   iSplitL "". *)
    (*   { *)
    (*     rewrite /memory_transferred. *)
    (*     rewrite /trans_memory_in_trans /pages_in_trans. *)
    (*     rewrite map_filter_empty map_fold_empty. *)
    (*     iExists ∅. *)
    (*     iApply memory_pages_empty. *)
    (*   } *)
    (*   iDestruct "R2" as "(R1' & R2 & R3)". *)
    (*   iFrame "R1' R2 R3 prop0". *)
    (*   iSplitL "R2z"; first (iExists r2; done). *)
    (*   iSplitL "R0 R1". *)
    (*   { *)
    (*     rewrite /rx_pages. *)
    (*     rewrite /list_of_vmids. *)
    (*     rewrite /vm_count /rywu_vmconfig. *)
    (*     simpl. *)
    (*     rewrite /V2. *)
    (*     simpl. *)
    (*     assert (({[2%fin]} ∪ ∅) = {[2%fin]}) as ->. *)
    (*     { set_solver. } *)
    (*     assert (({[0%fin]} ∪ {[1%fin; 2%fin]}) = ({[2%fin]} ∪ {[0%fin; 1%fin]})) as ->. *)
    (*     { set_solver. } *)
    (*     rewrite difference_union_distr_l_L. *)
    (*     rewrite difference_diag_L. *)
    (*     set p := {[0%fin; 1%fin]}. *)
    (*     set q := {[2%fin]}. *)
    (*     assert ((∅ ∪ p ∖ q) = p) as ->. *)
    (*     { subst p q; set_solver. } *)
    (*     subst p. *)
    (*     clear q. *)
    (*     rewrite big_sepS_union; last set_solver. *)
    (*     iSplitL "R0". *)
    (*     - rewrite big_sepS_singleton. *)
    (*       iExists p_rx0. *)
    (*       iDestruct "R0" as "(R0 & R1 & R2)". *)
    (*       iFrame. *)
    (*       rewrite /mailbox.rx_page. *)
    (*       iDestruct "R1" as "(R1 & R2)". *)
    (*       iFrame. *)
    (*       iExists None. *)
    (*       rewrite mailbox.rx_state_split. *)
    (*       iDestruct "R0" as "(R0 & R0')". *)
    (*       iFrame. *)
    (*       done. *)
    (*     - rewrite big_sepS_singleton. *)
    (*       iExists p_rx1. *)
    (*       iDestruct "R1" as "(R0 & R1 & R2)". *)
    (*       iFrame. *)
    (*       rewrite /mailbox.rx_page. *)
    (*       iDestruct "R1" as "(R1 & R2)". *)
    (*       iFrame. *)
    (*       iExists None. *)
    (*       rewrite mailbox.rx_state_split. *)
    (*       iDestruct "R0" as "(R0 & R0')". *)
    (*       iFrame. *)
    (*       done. *)
    (*   } *)
    (*   iSplit. *)
    (*   iIntros;done. *)
    (*   iSplitL "". *)
    (*   iIntros;done. *)
    (*   iSplitL "". *)
    (*   iIntros;done. *)
    (*   { *)
    (*     rewrite /trans_memory_in_trans /pages_in_trans. *)
    (*     rewrite map_filter_empty map_fold_empty. *)
    (*     iIntros "[? _]". *)
    (*     rewrite difference_empty_L union_empty_r_L. *)
    (*     done. *)
    (*   } *)
    (* } *)
    (* iNext. *)
    (* iIntros "((PCz & p_3 & acc & tx) & Hprop0) Hholds0". *)
    (* iDestruct (VMProp_holds_agree with "[Hholds0 Hprop0]") as "[P' prop0]". *)
    (* iSplitR "Hprop0". *)
    (* 2: { iFrame "Hprop0". } *)
    (* iSimpl. *)
    (* iSimpl in "Hholds0". *)
    (* done. *)
    (* (* getting back resources *) *)
    (* iDestruct "P'" as ">[(% & % & % & ? & ? & % & ? & ? & ? & ? & ? & ? & ? & returnreg)|False]". *)
    (* 2: { (* V2 does not yield *) *)
    (* iExFalso. *)
    (* iExact "False". *)
    (* } *)
    (* (* mov_word_I R0 run *) *)
    (* rewrite wp_sswp. *)
    (* rewrite /return_reg_rx. *)
    (* iDestruct "returnreg" as "[returnreg | returnreg]". *)
    (* { *)
    (*   iDestruct "returnreg" as "(R0z & R1z & R2z)". *)
    (*   iDestruct "R0z" as "[R0z | R0z]". *)
    (*   { *)
    (*     iDestruct "R0z" as "(R0z & ?)". *)
    (*     iApply ((mov_word ((((of_pid p_pg0) ^+ 1) ^+ 1)^+ 1)%f run_I R0) with "[p_4 PCz acc tx R0z]");try rewrite HIn //; iFrameAutoSolve; try set_solver +. *)
    (*     iModIntro. *)
    (*     iIntros "(PCz & p_4 & acc & tx & R0z) _". *)
    (*     (* mov_word_I R1 V1 *) *)
    (*     rewrite wp_sswp. *)
    (*     iApply ((mov_word (((((of_pid p_pg0) ^+ 1) ^+ 1)^+ 1) ^+ 1)%f (encode_vmid V1) R1) with "[p_5 PCz acc tx R1z]"); try rewrite HIn //; iFrameAutoSolve; try set_solver +. *)
    (*     iModIntro. *)
    (*     iIntros "(PCz & p_5 & acc & tx & R1z) _". *)
    (*     (* hvc_I *) *)
    (*     rewrite wp_sswp. *)
    (*     iApply ((run ((((((of_pid p_pg0) ^+ 1) ^+ 1)^+ 1) ^+ 1) ^+ 1)%f V1 (R := True)) *)
    (*               with "[PCz p_6 acc tx R0z R1z prop0 prop1]"); try rewrite HIn //;iFrameAutoSolve. *)
    (*     { set_solver +. } *)
    (*     { set_solver +. } *)
    (*     { set_solver +. } *)
    (*     { apply decode_encode_hvc_func. } *)
    (*     { apply decode_encode_vmid. } *)
    (*     { *)
    (*       iSplitR "prop0". *)
    (*       - iModIntro. *)
    (*         iFrame "prop1". *)
    (*       - iSplitL "prop0". *)
    (*         iFrame "prop0". *)
    (*         iSplitR "";last done. *)
    (*         iNext. *)
    (*         iIntros "((PCz & p_6 & acc & tx & R0z & R1z) & _ & prop)". *)
    (*         iFrame "R0z R1z prop". *)
    (*         iCombine "PCz p_6 acc tx" as "R'". *)
    (*         iExact "R'". *)
    (*     } *)
    (*     iModIntro. *)
    (*     iIntros "[(PC & p_6 & acc & tx) prop0] Hholds". *)
    (*     iDestruct (VMProp_holds_agree with "[Hholds prop0]") as "[P' prop0]". *)
    (*     simpl. *)
    (*     iFrame "Hholds prop0". *)
    (*     (* getting back resources *) *)
    (*     iDestruct "P'" as "((>R0z & >R1z) & prop1)". *)
    (*     (* halt_I *) *)
    (*     rewrite wp_sswp. *)
    (*     iApply ((halt (((((((of_pid p_pg0) ^+ 1) ^+ 1) ^+ 1) ^+ 1) ^+ 1) ^+ 1)%f) with "[PC p_7 acc tx]"); *)
    (*       try rewrite HIn //; iFrameAutoSolve;try set_solver +. *)
    (*     iNext. *)
    (*     iIntros "( PCz & p_7 & acc & tx)". *)
    (*     iIntros "_". *)
    (*     iApply wp_terminated'; eauto. *)
    (*     assert ((((((((p_pg0 ^+ 1) ^+ 1) ^+ 1) ^+ 1) ^+ 1) ^+ 1) ^+ 1)%f = ((of_pid p_pg0) ^+ length rywu_program0)%f) as ->. *)
    (*     { *)
    (*       assert ( (Z.of_nat (length rywu_program0)) = 7%Z) as ->. by compute. *)
    (*       solve_finz. *)
    (*     } *)
    (*     iFrame. *)
    (*     iSplitR; first done. *)
    (*     done. *)
    (*   } *)
    (*   { *)
    (*     iDestruct "R0z" as "(R0z & ?)". *)
    (*     iApply ((mov_word ((((of_pid p_pg0) ^+ 1) ^+ 1)^+ 1)%f run_I R0) with "[p_4 PCz acc tx R0z]");try rewrite HIn //; iFrameAutoSolve; try set_solver +. *)
    (*     iModIntro. *)
    (*     iIntros "(PCz & p_4 & acc & tx & R0z) _". *)
    (*     (* mov_word_I R1 V1 *) *)
    (*     rewrite wp_sswp. *)
    (*     iApply ((mov_word (((((of_pid p_pg0) ^+ 1) ^+ 1)^+ 1) ^+ 1)%f (encode_vmid V1) R1) with "[p_5 PCz acc tx R1z]"); try rewrite HIn //; iFrameAutoSolve; try set_solver +. *)
    (*     iModIntro. *)
    (*     iIntros "(PCz & p_5 & acc & tx & R1z) _". *)
    (*     (* hvc_I *) *)
    (*     rewrite wp_sswp. *)
    (*     iApply ((run ((((((of_pid p_pg0) ^+ 1) ^+ 1)^+ 1) ^+ 1) ^+ 1)%f V1 (R := True)) *)
    (*               with "[PCz p_6 acc tx R0z R1z prop0 prop1]"); try rewrite HIn //;iFrameAutoSolve. *)
    (*     { set_solver +. } *)
    (*     { set_solver +. } *)
    (*     { set_solver +. } *)
    (*     { apply decode_encode_hvc_func. } *)
    (*     { apply decode_encode_vmid. } *)
    (*     { *)
    (*       iSplitR "prop0". *)
    (*       - iModIntro. *)
    (*         iFrame "prop1". *)
    (*       - iSplitL "prop0". *)
    (*         iFrame "prop0". *)
    (*         iSplitR "";last done. *)
    (*         iNext. *)
    (*         iIntros "((PCz & p_6 & acc & tx & R0z & R1z) & _ & prop)". *)
    (*         iFrame "R0z R1z prop". *)
    (*         iCombine "PCz p_6 acc tx" as "R'". *)
    (*         iExact "R'". *)
    (*     } *)
    (*     iModIntro. *)
    (*     iIntros "[(PC & p_6 & acc & tx) prop0] Hholds". *)
    (*     iDestruct (VMProp_holds_agree with "[Hholds prop0]") as "[P' prop0]". *)
    (*     simpl. *)
    (*     iFrame "Hholds prop0". *)
    (*     (* getting back resources *) *)
    (*     iDestruct "P'" as "((>R0z & >R1z) & prop1)". *)
    (*     (* halt_I *) *)
    (*     rewrite wp_sswp. *)
    (*     iApply ((halt (((((((of_pid p_pg0) ^+ 1) ^+ 1) ^+ 1) ^+ 1) ^+ 1) ^+ 1)%f) with "[PC p_7 acc tx]"); *)
    (*       try rewrite HIn //; iFrameAutoSolve;try set_solver +. *)
    (*     iNext. *)
    (*     iIntros "( PCz & p_7 & acc & tx)". *)
    (*     iIntros "_". *)
    (*     iApply wp_terminated'; eauto. *)
    (*     assert ((((((((p_pg0 ^+ 1) ^+ 1) ^+ 1) ^+ 1) ^+ 1) ^+ 1) ^+ 1)%f = ((of_pid p_pg0) ^+ length rywu_program0)%f) as ->. *)
    (*     { *)
    (*       assert ( (Z.of_nat (length rywu_program0)) = 7%Z) as ->. by compute. *)
    (*       solve_finz. *)
    (*     } *)
    (*     iFrame. *)
    (*     iSplitR; first done. *)
    (*     done. *)
    (*   }       *)
    (* } *)
    (* { *)
    (*   iDestruct "returnreg" as "(R0z & ? & R1z)". *)
    (*   iApply ((mov_word ((((of_pid p_pg0) ^+ 1) ^+ 1)^+ 1)%f run_I R0) with "[p_4 PCz acc tx R0z]");try rewrite HIn //; iFrameAutoSolve; try set_solver +. *)
    (*   iModIntro. *)
    (*   iIntros "(PCz & p_4 & acc & tx & R0z) _". *)
    (*   (* mov_word_I R1 V1 *) *)
    (*   rewrite wp_sswp. *)
    (*   iDestruct "R1z" as "(%j & %p_rx & %l & ? & ? & ? & R1z & R2z & ?)". *)
    (*   iDestruct "R1z" as "(%r3 & R1z & ?)". *)
    (*   iApply ((mov_word (((((of_pid p_pg0) ^+ 1) ^+ 1)^+ 1) ^+ 1)%f (encode_vmid V1) R1) with "[p_5 PCz acc tx R1z]"); try rewrite HIn //; iFrameAutoSolve; try set_solver +. *)
    (*   iModIntro. *)
    (*   iIntros "(PCz & p_5 & acc & tx & R1z) _". *)
    (*   (* hvc_I *) *)
    (*   rewrite wp_sswp. *)
    (*   iApply ((run ((((((of_pid p_pg0) ^+ 1) ^+ 1)^+ 1) ^+ 1) ^+ 1)%f V1 (R := True)) *)
    (*             with "[PCz p_6 acc tx R0z R1z prop0 prop1]"); try rewrite HIn //;iFrameAutoSolve. *)
    (*   { set_solver +. } *)
    (*   { set_solver +. } *)
    (*   { set_solver +. } *)
    (*   { apply decode_encode_hvc_func. } *)
    (*   { apply decode_encode_vmid. } *)
    (*   { *)
    (*     iSplitR "prop0". *)
    (*     - iModIntro. *)
    (*       iFrame "prop1". *)
    (*     - iSplitL "prop0". *)
    (*       iFrame "prop0". *)
    (*       iSplitR "";last done. *)
    (*       iNext. *)
    (*       iIntros "((PCz & p_6 & acc & tx & R0z & R1z) & _ & prop)". *)
    (*       iFrame "R0z R1z prop". *)
    (*       iCombine "PCz p_6 acc tx" as "R'". *)
    (*       iExact "R'". *)
    (*   } *)
    (*   iModIntro. *)
    (*   iIntros "[(PC & p_6 & acc & tx) prop0] Hholds". *)
    (*   iDestruct (VMProp_holds_agree with "[Hholds prop0]") as "[P' prop0]". *)
    (*   simpl. *)
    (*   iFrame "Hholds prop0". *)
    (*   (* getting back resources *) *)
    (*   iDestruct "P'" as "((>R0z & >R1z) & prop1)". *)
    (*   (* halt_I *) *)
    (*   rewrite wp_sswp. *)
    (*   iApply ((halt (((((((of_pid p_pg0) ^+ 1) ^+ 1) ^+ 1) ^+ 1) ^+ 1) ^+ 1)%f) with "[PC p_7 acc tx]"); *)
    (*     try rewrite HIn //; iFrameAutoSolve;try set_solver +. *)
    (*   iNext. *)
    (*   iIntros "( PCz & p_7 & acc & tx)". *)
    (*   iIntros "_". *)
    (*   iApply wp_terminated'; eauto. *)
    (*   assert ((((((((p_pg0 ^+ 1) ^+ 1) ^+ 1) ^+ 1) ^+ 1) ^+ 1) ^+ 1)%f = ((of_pid p_pg0) ^+ length rywu_program0)%f) as ->. *)
    (*   { *)
    (*     assert ( (Z.of_nat (length rywu_program0)) = 7%Z) as ->. by compute. *)
    (*     solve_finz. *)
    (*   } *)
    (*   iFrame. *)
    (*   iSplitR; first done. *)
    (*   done. *)
    (* } *)
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
