From machine_program_logic.program_logic Require Import machine weakestpre.
From HypVeri Require Import reg_addr RAs rule_misc lifting.
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
  

   Definition program1 (i : VMID) : list Word :=
    [
    mov_word_I R0 run_I;
    mov_word_I R1 (encode_vmid i);
    hvc_I;
    halt_I
    ].

  Definition program2 : list Word :=
    [
    mov_word_I R0 yield_I;
    hvc_I
    ].
  
  Class tokG Σ := tok_G :> inG Σ (frac_agreeR (leibnizO vmid)).

  Context `{gen_VMG Σ, tokG Σ}.

  Definition program (instr: list Word) (b:Addr):=
    ([∗ list] a;w ∈ (finz.seq b (length instr));instr, (a ->a w))%I.

  Definition tokI γ i := own γ (to_frac_agree (1/2)%Qp i).
  
  Definition tokN := nroot .@ "tok".

  Definition is_tok γ (z i:VMID) :=
    inv tokN ((<<z>>) ∨ ∃j, tokI γ j ∗ ⌜j = i⌝ ∗ <<i>>)%I.

  (* Definition seq_in_a_page (b e: Addr) (p:PID) := *)
  (*   ((of_pid p) <=? b)%f ∧ (e <? ((of_pid p) ^+ page_size))%f. *)

  Lemma spec1 {γ z i q1 q2 prog1page prog2page r0_} :
      fin_to_nat z = 0 ->
      z ≠ i ->
      program (program1 i) (of_pid prog1page) ∗
      program (program2) (of_pid prog2page) ∗
      is_tok γ z i ∗
      A@z :={q1} prog1page ∗ A@i :={q2} prog2page
      ∗ PC @@ z ->r (of_pid prog1page) ∗ PC @@ i ->r (of_pid prog2page)
      ∗ R0 @@ z ->r r0_
      ⊢ (WP ExecI @ z {{ (λ m, ⌜m = HaltI⌝) }}%I)
       ∗ (WP ExecI @ i {{ (λ m, ⌜m = ExecI⌝) }}%I).
  Proof.
    iIntros (zP neH) "((p_1 & p_2 & p_3 & p_4 & _) & (p_1' & p_2' & _) & #Hinv & Hacc1 & Hacc2 & PCz & PCi & Hr0_)".
    iSplitL "p_1 p_2 p_3 p_4 Hacc1 PCz Hr0_".
    - rewrite wp_sswp.
      iApply (sswp_fupd_around ⊤ ⊤ ⊤).
      iInv tokN as ">S" "HClose".
      iDestruct "S" as "[S | S]".
      + iDestruct ((@mov_word _ _ (Mov R0 (inl run_I)) z (mov_word_I R0 run_I) r0_ q1 (of_pid prog1page) run_I R0) with "[> S]") as "J"; eauto.
        * by rewrite decode_encode_instruction.          
        * admit.
        * admit.
      + iDestruct "S" as "[%j (S1 & %S2 & S3)]".
        simplify_eq.
        iApply (sswp_mono z _ ExecI (λ _, False %I) _).
        * iIntros;iExFalso; done.
        * assert (neH' : i ≠ z).
          {
            intros contra.
            apply neH.
            symmetry.
            assumption.
          }
          iApply eliminate_wrong_token.
          (* TODO eliminate_wrong_token consumes the token, so we cannot close the invariant! *)
          apply neH'.
          iFrame.
          admit.
    - admit.
Admitted.

End RunYield1.
