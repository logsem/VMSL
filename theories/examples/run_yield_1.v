From machine_program_logic.program_logic Require Import machine weakestpre.
From HypVeri Require Import RAs rule_misc lifting.
From HypVeri.rules Require Import rules_base mov ldr str halt run yield.
From iris.proofmode Require Import tactics.
From iris.base_logic.lib Require Export invariants.
Require Import iris.base_logic.lib.ghost_map iris.bi.big_op iris.algebra.lib.frac_agree.
Require Import stdpp.fin.

Section RunYield1.

  Definition mov_word_I ra w := encode_instruction (Mov ra (inl w)).
  Definition str_I ra rb := encode_instruction (Str ra rb).
  Definition halt_I := encode_instruction Halt.
  Definition hvc_I := encode_instruction Hvc.
  
  Definition run_I := encode_hvc_func Run.
  Definition yield_I := encode_hvc_func Yield.
  
  Definition r0 := R 0 ltac:(solveRegCount).
  Definition r1 := R 1 ltac:(solveRegCount).
  
  Definition program1 (i : vmid) (b : addr) : list (addr * word) :=
    [
    (b +w 0, mov_word_I r0 run_I);
    (b +w 1, mov_word_I r1 (encode_vmid i));
    (b +w 2, hvc_I);
    (b +w 3, halt_I)
    ].

  Definition program2 (b : addr) : list (addr * word) :=
    [
    (b +w 0, mov_word_I r0 yield_I);
    (b +w 1, hvc_I)
    ].
  
  Definition addrs_to_page (b : addr) (off : nat) (p : pid) :=
    Forall (fun n => mm_translation (b +w n) = p) (seq 0 off).

  Class tokG Σ := tok_G :> inG Σ (frac_agreeR (leibnizO vmid)).

  Context `{gen_VMG Σ, tokG Σ}.
  
  Definition tokI γ i := own γ (to_frac_agree (1/2)%Qp i).
  
  Definition tokN := nroot .@ "tok".
  
  Definition is_tok γ i :=
    inv tokN ((<<Fin.of_nat_lt vm_count_pos>>) ∨ ∃j, tokI γ j ∧ ⌜j = i⌝ ∗ <<i>>)%I.
  
  Lemma spec1 {γ z i q1 q2 pr1page pr2page pr1base pr2base} :
      addrs_to_page pr1base 6 pr1page ->
      addrs_to_page pr2base 4 pr2page ->
      fin_to_nat z = 0 ->
      z ≠ i ->
      ([∗ list] aw ∈ (program1 i pr1base), (aw.1 ->a aw.2))%I ∗
      ([∗ list] aw ∈ (program2 pr2base), (aw.1 ->a aw.2))%I ∗
      is_tok γ i ∗                                                           
      A@z :={q1} pr1page ∗ A@i :={q2} pr2page
            ∗ PC @@ z ->r pr1base ∗ PC @@ i ->r pr2base
                                                ⊢ (WP ExecI @ z {{ (λ m, ⌜m = HaltI⌝) }}%I)
                                                ∗ (WP ExecI @ i {{ (λ m, ⌜m = ExecI⌝) }}%I).
  Proof.
    iIntros (addrM1 addrM2 zP neH) "((p_1 & p_2 & p_3 & p_4 & _) & (p_1' & p_2' & _) & #Hinv & Hacc1 & Hacc2 & PCz & PCi)".
    simpl.
    iSplitL "p_1 p_2 p_3 p_4 Hacc1 PCz".
    - rewrite wp_sswp.
      iApply sswp_fupd_around.
      iInv tokN as "S" "HClose".
Admitted.

End RunYield1.
