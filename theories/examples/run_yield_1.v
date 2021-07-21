From machine_program_logic.program_logic Require Import machine weakestpre.
From HypVeri Require Import reg_addr RAs rule_misc lifting.
From HypVeri.rules Require Import rules_base mov ldr str halt run yield.
From iris.proofmode Require Import tactics.
From iris.base_logic.lib Require Import invariants na_invariants.
From iris.algebra Require Import excl.

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
  
  Class tokG Σ := tok_G :> inG Σ (exclR unitO).

  Context `{gen_VMG Σ, tokG Σ}.

  Definition program (instr: list Word) (b:Addr):=
    ([∗ list] a;w ∈ (finz.seq b (length instr));instr, (a ->a w))%I.

  Definition tokI γ := own γ (Excl ()).

  Lemma tokI_excl γ : tokI γ -∗ tokI γ -∗ False.
  Proof.
    iIntros "H1 H2".
    unfold tokI.
    iDestruct (own_valid_2 with "H1 H2") as "%HF".
    iPureIntro.
    inversion HF.
    Qed.

  Definition invN := nroot .@ "tok".

  Definition inv γ1  (z i:VMID) :=
    ((<<z>>)  ∨  <<i>> ∗ tokI γ1)%I.
  (* TODO: put R0@z and R1@z into the invariant *)

  Lemma mach_zero {γ1 z i q1 prog1page r0_ r1_} :
      fin_to_nat z = 0 ->
      z ≠ i ->
      seq_in_page (of_pid prog1page) (length (program1 i)) prog1page ->
      program (program1 i) (of_pid prog1page) ∗
      nainv invN (inv γ1 z i) ∗ tokI γ1 ∗
      nainv_closed ⊤ ∗
      A@z :={q1} prog1page
      ∗ PC @@ z ->r (of_pid prog1page)
      ∗ R0 @@ z ->r r0_
      ∗ R1 @@ z ->r r1_
      ⊢ (WP ExecI @ z
            {{ (λ m, ⌜m = HaltI⌝
            ∗ nainv_closed ⊤
            ∗ program (program1 i) (of_pid prog1page)
            ∗ A@z :={q1} prog1page
            ∗ PC @@ z ->r ((of_pid prog1page) ^+ (length (program1 i)))%f
            ∗ R0 @@ z ->r run_I
            ∗ R1 @@ z ->r (encode_vmid i)) }}%I).
  Proof.
    iIntros (zP neH HIn) "((p_1 & p_2 & p_3 & p_4 & _) & #Hinv  & Hgtok & Hown & Hacc & PCz & R0z &R1z)".
    apply seq_in_page_forall in HIn.
    (* mov_word_I R0 run_I *)
    rewrite wp_sswp.
    (* iApply (sswp_fupd_around z ⊤ (⊤ ∖ ↑invN) ⊤). *)
    iApply (sswp_fupd_around z ⊤ ⊤ ⊤).
    iMod (na_inv_acc with "Hinv Hown") as "(>S & Hown & HClose)";auto.
    iModIntro.
    iDestruct "S" as "[Htok | [Htok Hgtok2] ]".
    2: {
      iExFalso.
      iApply (tokI_excl with "Hgtok Hgtok2").
    }
    iDestruct
      ((mov_word (of_pid prog1page) run_I R0) with "[Htok p_1 PCz Hacc R0z]") as "J";eauto.
    3:{iFrame. }
    by rewrite decode_encode_instruction.
    by inversion HIn.
    iApply "J".
    iNext.
    iIntros "(Htok & PCz & p_1 & Hacc & R0z)".
    (* iDestruct ("HClose" with "[Htok]") as "HClose". *)
    (* iNext. *)
    (* iLeft. *)
    (* iFrame. *)
    (* iMod "HClose" as %_. *)
    iModIntro.
    (* mov_word_I R1 (encode_vmid i) *)
    rewrite wp_sswp.
    (* iApply (sswp_fupd_around z ⊤ (⊤ ∖ ↑invN) ⊤). *)
    (* iInv invN as ">S" "HClose". *)
    (* iModIntro. *)
    (* iDestruct "S" as "[Htok | [Htok Hgtok2] ]". *)
    (* 2: { *)
    (*   iExFalso. *)
    (*   iApply (tokI_excl with "Hgtok Hgtok2"). *)
    (* } *)
    iDestruct
      ((mov_word ((of_pid prog1page) ^+ 1)%f  (encode_vmid i) R1)
         with "[Htok p_2 PCz Hacc R1z]") as "J"; eauto.
    3:{iFrame. }
    by rewrite decode_encode_instruction.
    by inversion HIn;inversion H4.
    iApply "J".
    iNext.
    iIntros "(Htok & PCz & p_2 & Hacc & R1z)".
    (* iDestruct ("HClose" with "[Htok]") as "HClose". *)
    (* iNext. *)
    (* iLeft. *)
    (* iFrame. *)
    (* iMod "HClose" as %_. *)
    (* iModIntro. *)
    (* hvc_I *)
    rewrite wp_sswp.
    (* iApply (sswp_fupd_around z ⊤ (⊤ ∖ ↑invN) ⊤). *)
    (* iInv invN as ">S" "HClose". *)
    (* iModIntro. *)
    (* iDestruct "S" as "[Htok | [Htok Hgtok2] ]". *)
    (* 2: { *)
    (*    iExFalso. *)
    (*   iApply (tokI_excl with "Hgtok Hgtok2"). *)
    (* } *)
    iDestruct
      ((run (((of_pid prog1page) ^+ 1) ^+ 1)%f)
         with "[Htok PCz p_3 Hacc R0z R1z]") as "J"; eauto.
    5: { iFrame. }
    by rewrite decode_encode_instruction.
    by inversion HIn;inversion H4; inversion H8.
    by rewrite decode_encode_hvc_func.
    by rewrite decode_encode_vmid.
    iApply "J".
    iNext.
    iIntros "(Htok & PCz & p_3 & Hacc & R0z & R1z)".
    iDestruct ("HClose" with "[Htok Hgtok Hown]") as "Hown".
    iFrame.
    iNext.
    iRight.
    iFrame.
    (* iModIntro. *)
    (* halt_I *)
    rewrite wp_sswp.
    (* iApply (sswp_fupd_around z ⊤ (⊤ ∖ ↑invN) ⊤). *)
    iApply (sswp_fupd_around z ⊤ ⊤ ⊤).
    iMod "Hown".
    iMod (na_inv_acc with "Hinv Hown") as "(>S & Hown & HClose)";auto.
    (* iInv invN as ">S" "HClose". *)
    iModIntro.
    iDestruct "S" as "[Htok | [Htok Hgtok2] ]".
    2: {
      iDestruct (eliminate_wrong_token) as "J".
      assert (Hne: i ≠ z). { intro.  apply neH. symmetry. done. }
      apply Hne.
      iApply ("J" with "Htok").
      iNext.
      iIntros "(Htok & HFALSE)".
      iDestruct ("HClose" with "[Htok Hgtok2 Hown]") as "Hown".
      iFrame.
    iNext.
    iRight.
    iFrame.
    iModIntro.
    iExFalso.
    done.
    }
    iDestruct
      ((halt ((((of_pid prog1page) ^+ 1) ^+ 1) ^+1 )%f)
         with "[Htok PCz p_4 Hacc]") as "J"; eauto.
    3: { iFrame. }
    by rewrite decode_encode_instruction.
    by inversion HIn;inversion H4; inversion H8; inversion H12.
    iApply "J".
    iNext.
    iIntros "(Htok & PCz & p_4 & Hacc )".
    iDestruct ("HClose" with "[Htok Hown]") as "Hown".
    iFrame.
    iMod "Hown".
    iModIntro.
    iApply wp_terminated';eauto.
    assert (Hlen: (((((of_pid prog1page) ^+ 1) ^+ 1) ^+ 1) ^+ 1)%f = ((of_pid prog1page) ^+ length (program1 i))%f).
    {
    assert (Hlen4 : (Z.of_nat (length (program1 i))) = 4%Z). by compute.
    rewrite Hlen4;clear Hlen4.
    solve_finz.
    }
    rewrite Hlen.
    iFrame.
    iSplitL;done.
  Qed.

    Lemma mach_i {γ1 z i q1 prog2page r0_} :
      fin_to_nat z = 0 ->
      z ≠ i ->
      seq_in_page (of_pid prog2page) (length program2) prog2page ->
      program program2 (of_pid prog2page) ∗
      inv γ1 z i ∗
      A@i :={q1} prog2page
      ∗ PC @@ i ->r (of_pid prog2page)
      ∗ R0 @@ i ->r r0_
      ⊢ (WP ExecI @ i
            {{ (λ m, ⌜m = HaltI⌝
            ∗ program (program1 i) (of_pid prog2page)
            ∗ A@i :={q1} prog2page
            ∗ PC @@ i ->r ((of_pid prog2page) ^+ (length program2))%f
            ∗ R0 @@ i ->r yield_I)}}%I).
  Proof.
    iIntros (zP neH HIn) "((p_1 & p_2) & #Hinv & Hacc & PCi & R0i)".
    apply seq_in_page_forall in HIn.
    (* mov_word_I R0 yield_I *)
    rewrite wp_sswp.
    iApply (sswp_fupd_around i ⊤ (⊤ ∖ ↑invN) ⊤).
    iInv invN as ">S" "HClose".
    iModIntro.
    iDestruct "S" as "[Htok | [Htok Hgtok2] ]".
    1: {
       iDestruct (eliminate_wrong_token) as "J".
      apply neH.
      iApply ("J" with "Htok").
      iNext.
      iIntros "(Htok & HFALSE)".
      iDestruct ("HClose" with "[Htok]") as "HClose".
    iNext.
    iLeft.
    iFrame.
    iMod "HClose" as %_.
    iModIntro.
    iExFalso.
    done.
    }
    iDestruct
      ((mov_word (of_pid prog2page) yield_I R0) with "[Htok p_1 PCi Hacc R0i]") as "J";eauto.
    3:{iFrame. }
    by rewrite decode_encode_instruction.
    by inversion HIn.
    iApply "J".
    iNext.
    iIntros "(Htok & PCz & p_1 & Hacc & R0i)".
    iDestruct ("HClose" with "[Htok Hgtok2]") as "HClose".
    iNext.
    iRight.
    iFrame.
    iMod "HClose" as %_.
    iModIntro.
    (* hvc_I *)
    rewrite wp_sswp.
    iApply (sswp_fupd_around i ⊤ (⊤ ∖ ↑invN) ⊤).
    iInv invN as ">S" "HClose".
    iModIntro.
    iDestruct "S" as "[Htok | [Htok Hgtok2] ]".
   1: {
       iDestruct (eliminate_wrong_token) as "J".
      apply neH.
      iApply ("J" with "Htok").
      iNext.
      iIntros "(Htok & HFALSE)".
      iDestruct ("HClose" with "[Htok]") as "HClose".
    iNext.
    iLeft.
    iFrame.
    iMod "HClose" as %_.
    iModIntro.
    iExFalso.
    done.
    }
    (* iDestruct *)
    (*   ((yield ((of_pid prog1page) ^+ 1) %f) *)
    (*      with "[Htok PCz p_3 Hacc R0z R1z]") as "J"; eauto. *)
   (* TODO: need R0z and R1z *)




  Lemma spec1 {γ1 γ2 z i q1 q2 prog1page prog2page r0_} :
      fin_to_nat z = 0 ->
      z ≠ i ->
      program (program1 i) (of_pid prog1page) ∗
      program (program2) (of_pid prog2page) ∗
      inv γ1 γ2 z i ∗ tokI γ1 ∗ tokI γ2 ∗
      A@z :={q1} prog1page ∗ A@i :={q2} prog2page
      ∗ PC @@ z ->r (of_pid prog1page) ∗ PC @@ i ->r (of_pid prog2page)
      ∗ R0 @@ z ->r r0_
      ⊢ (WP ExecI @ z {{ (λ m, ⌜m = HaltI⌝) }}%I)
       ∗ (WP ExecI @ i {{ (λ m, ⌜m = ExecI⌝) }}%I).
  Proof.
    iIntros (zP neH) "((p_1 & p_2 & p_3 & p_4 & _) & (p_1' & p_2' & _) & #Hinv & Hgtok1 & Hgtok2 & Hacc1 & Hacc2 & PCz & PCi & Hr0_)".
    iSplitL "p_1 p_2 p_3 p_4 Hgtok2 Hacc1 PCz Hr0_".
    - rewrite wp_sswp.
      iApply (sswp_fupd_around ⊤ ⊤ ⊤).
      iInv invN as ">S" "HClose".
      iDestruct "S" as "[S | S]".
      + iDestruct ((@mov_word _ _ (Mov R0 (inl run_I)) z (mov_word_I R0 run_I) r0_ q1 (of_pid prog1page) run_I R0) with "[> S]") as "J"; eauto.
        * by rewrite decode_encode_instruction.          
        * admit.
        * admit.
      + iDestruct "S" as "(Hgtok & Htok)".
        iExFalso.
        iApply (tokI_excl with "Hgtok2 Hgtok").
    - admit.
Admitted.

End RunYield1.
