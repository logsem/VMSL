From machine_program_logic.program_logic Require Import machine weakestpre.
From HypVeri Require Import reg_addr RAs rule_misc lifting.
From HypVeri.rules Require Import rules_base mov halt run yield.
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

  Definition na_inv γ1 γ2 γ3 (z i:VMID) :=
    ((∃ w0 w1,   tokI γ1 ∗ tokI γ3 ∗ R0 @@ z ->r w0 ∗ R1 @@ z ->r w1) ∨
     ( tokI γ2 ∗ R0 @@ z ->r yield_I ∗ R1 @@ z ->r (encode_vmid i)) ∨
     ( tokI γ1 ∗ tokI γ2 ∗ R0 @@ z ->r run_I ∗ R1 @@ z ->r (encode_vmid i)))%I.

  Definition inv' :=
    ( (∃ i, <<i>>{ (1/2)%Qp }) ∨ nainv_closed ⊤ )%I.

  Lemma mach_zero {γ1 γ2 γ3 z i q1 prog1page ι ι1} :
      ι ## ι1 ->
      fin_to_nat z = 0 ->
      z ≠ i ->
      seq_in_page (of_pid prog1page) (length (program1 i)) prog1page ->
      <<z>>{ 1%Qp } ∗
      program (program1 i) (of_pid prog1page) ∗
      inv ι (inv') ∗
      nainv ι1 (na_inv γ1 γ2 γ3 z i) ∗ tokI γ2 ∗
      A@z :={q1} prog1page
      ∗ PC @@ z ->r (of_pid prog1page)
      ⊢ (WP ExecI @ z
            {{ (λ m, ⌜m = HaltI⌝
            ∗ nainv_closed ⊤ ∗ tokI γ3
            ∗ program (program1 i) (of_pid prog1page)
            ∗ A@z :={q1} prog1page
            ∗ PC @@ z ->r ((of_pid prog1page) ^+ (length (program1 i)))%f)}}%I).
  Proof.
    iIntros (Hdisj zP neH HIn) "(Htok & (p_1 & p_2 & p_3 & p_4 & _) & #Hinv & #Hnainv & Hgtok2 & Hacc & PCz )".
    apply seq_in_page_forall in HIn.
    rewrite wp_sswp.
    (* iApply (sswp_fupd_around z ⊤ (⊤ ∖ ↑ι) ⊤). *)
    iApply (sswp_fupd_around z ⊤ ⊤ _).
    iInv ι as ">Inv" "HClose".
    iDestruct "Inv" as "[Htok' | Hown ]".
    1: {
    iDestruct "Htok'" as (j) "Htok'".
    iExFalso.
    iDestruct (token_frag_valid with "Htok Htok'") as %[_ Hvalid].
    contradiction.
    }
    iDestruct ((token_frag_split z (1/2)%Qp (1/2)%Qp) with "Htok") as "[Htok Htok']";try done.
    compute_done.
    iDestruct ("HClose" with "[Htok']") as "HIClose".
    iNext;iLeft;iExists z;iFrame.
    iMod "HIClose" as %_.
    iModIntro.
    (* mov_word_I R0 run_I *)
    iApply (sswp_fupd_around z ⊤ ⊤ _).
    iMod (na_inv_acc with "Hnainv Hown") as "(>[HInv | [[Hgtok2' ?] | ( Hgtok1' & Hgtok2' & ?)]] & Hown & HClose)";auto.
    (* set_solver. *)
    iDestruct "HInv" as (w0 w1) "(  Hgtok1' & Hgtok3' & R0z & R1z )".
    2: {
      iExFalso.
      iApply (tokI_excl with "Hgtok2 Hgtok2'").
    }
    2: {
    iExFalso.
      iApply (tokI_excl with "Hgtok2 Hgtok2'").
    }
    iDestruct
      ((mov_word (of_pid prog1page) run_I R0) with "[Htok p_1 PCz Hacc R0z]") as "J";eauto.
    3:{iFrame. }
    by rewrite decode_encode_instruction.
    by inversion HIn.
    iApply "J".
    iModIntro.
    iNext.
    iIntros "(Htok & PCz & p_1 & Hacc & R0z)".
    iModIntro.
    iModIntro.
    (* mov_word_I R1 (encode_vmid i) *)
    rewrite wp_sswp.
    iDestruct
      ((mov_word ((of_pid prog1page) ^+ 1)%f  (encode_vmid i) R1)
         with "[Htok p_2 PCz Hacc R1z]") as "J"; eauto.
    3:{iFrame. }
    by rewrite decode_encode_instruction.
    by inversion HIn;inversion H4.
    iApply "J".
    iNext.
    iIntros "(Htok & PCz & p_2 & Hacc & R1z)".
    (* hvc_I *)
    rewrite wp_sswp.
    (* XXX:  to apply the rule for hvc run, a full token has to be provided. But to get it we need to
       close the na_inv and open the invariant. But after closing na_inv, we would lose the registers...
     *)
    iDestruct
      ((run (((of_pid prog1page) ^+ 1) ^+ 1)%f i)
         with "[Htok Htok' PCz p_3 Hacc R0z R1z]") as "J"; eauto.
    5: { iFrame. iNext. iApply ((token_frag_merge z (1/2)%Qp (1/2)%Qp) with "Htok Htok'"). compute_done. }
    by rewrite decode_encode_instruction.
    by inversion HIn;inversion H4; inversion H8.
    by rewrite decode_encode_hvc_func.
    by rewrite decode_encode_vmid.
    iApply "J".
    iNext.
    iIntros "(Htok & PCz & p_3 & Hacc & R0z & R1z)".
    iDestruct ((token_frag_split i (1/2)%Qp (1/2)%Qp) with "Htok") as "[Htok Htok']". compute_done.
    iDestruct ("HClose" with "[Htok Hgtok1' Hgtok2 R0z R1z Hown]") as "Hown".
    iFrame.
    iNext.
    iRight.
    iRight.
    iFrame.
    (* halt_I *)
    rewrite wp_sswp.
    iApply (sswp_fupd_around z  ⊤ ⊤ _).
    iMod "Hown".
    iMod (na_inv_acc with "Hnainv Hown") as "(>[HInv | [ (Htok & Hrest) | [Htok [Hgtok2 Hrest]]]] & Hown & HClose)";auto.
    iModIntro.
    1: {
      iDestruct "HInv" as (? ?) "(_ & Hgtok1' & Hgtok3 & _ )".
      iExFalso.
      iApply (tokI_excl with "Hgtok3 Hgtok3'").
    }
    2: {
      iDestruct (eliminate_wrong_token) as "J".
      assert (Hne: i ≠ z). { intro.  apply neH. symmetry. done. }
      apply Hne.
      iApply ("J" with "Htok").
      iModIntro.
      iNext.
      iIntros "(Htok & HFALSE)".
      iDestruct ("HClose" with "[Htok Hgtok2 Hrest Hown]") as "Hown".
      iFrame.
    iNext.
    iRight.
    iRight.
    iFrame.
    iModIntro.
    iExFalso.
    done.
    }
    iModIntro.
    iDestruct
      ((halt ((((of_pid prog1page) ^+ 1) ^+ 1) ^+1 )%f)
         with "[Htok PCz p_4 Hacc]") as "J"; eauto.
    3: { iFrame. }
    by rewrite decode_encode_instruction.
    by inversion HIn;inversion H4; inversion H8; inversion H12.
    iApply "J".
    iNext.
    iIntros "(Htok & PCz & p_4 & Hacc )".
    iDestruct ("HClose" with "[Htok Hrest Hown]") as "Hown".
    iFrame.
    iNext.
    iRight;iLeft.
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

    Lemma mach_i {γ1 γ2 γ3 z i q1 prog2page r0_} :
      fin_to_nat z = 0 ->
      z ≠ i ->
      seq_in_page (of_pid prog2page) (length program2) prog2page ->
      program program2 (of_pid prog2page) ∗
      nainv invN (inv γ1 γ2 γ3 z i) ∗
      nainv_closed ⊤ ∗
      A@i :={q1} prog2page
      ∗ PC @@ i ->r (of_pid prog2page)
      ∗ R0 @@ i ->r r0_
      ⊢ (WP ExecI @ i
            {{ (λ m, ⌜m = ExecI⌝
            ∗ nainv_closed ⊤
            ∗ program (program1 i) (of_pid prog2page)
            ∗ A@i :={q1} prog2page
            ∗ PC @@ i ->r ((of_pid prog2page) ^+ (length program2))%f
            ∗ R0 @@ i ->r yield_I)}}%I).
  Proof.
    iIntros (zP neH HIn) "((p_1 & p_2 & _) & #Hinv & Hown & Hacc & PCi & R0i)".
    apply seq_in_page_forall in HIn.
    (* mov_word_I R0 yield_I *)
    rewrite wp_sswp.
    iApply (sswp_fupd_around i ⊤ ⊤ ⊤).
    iMod (na_inv_acc with "Hinv Hown") as "(>[HInv | [[Htok Hrest] | (Htok & Hgtok1 & Hgtok2 & R0z & R1z)]] & Hown & HClose)";auto.
    iModIntro.
    1: { iDestruct "HInv" as (w0 w1) "( Htok & Hrest )".
         iDestruct (eliminate_wrong_token) as "J".
      apply neH.
      iApply ("J" with "Htok").
      iModIntro.
      iIntros "(Htok & HFALSE)".
      iDestruct ("HClose" with "[Htok Hrest Hown ]") as "HClose".
      iFrame.
    iNext.
    iLeft.
    iExists w0, w1.
    iFrame.
    iMod "HClose".
    iModIntro.
    iExFalso.
    done.
      }
    1: {
    iDestruct (eliminate_wrong_token) as "J".
      apply neH.
      iApply ("J" with "Htok").
      iModIntro.
      iNext.
      iIntros "(Htok & HFALSE)".
      iDestruct ("HClose" with "[Htok Hrest Hown ]") as "HClose".
      iFrame.
    iNext.
    iRight;iLeft.
    iFrame.
    iMod "HClose".
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
    iModIntro.
    iNext.
    iIntros "(Htok & PCi & p_1 & Hacc & R0i)".
    iModIntro.
    (* hvc_I *)
    rewrite wp_sswp.
    iDestruct
      ((yield ((of_pid prog2page) ^+ 1) %f)
         with "[Htok PCi p_2 Hacc R0i R0z R1z]") as "J"; eauto.
    4: { iFrame. }
    by rewrite decode_encode_instruction.
    by inversion HIn;inversion H4.
    by rewrite decode_encode_hvc_func.
    iApply "J".
    iNext.
    iIntros "(Htok & PCi & p_2 & Hacc & R0i & R0z & R1z)".
    iDestruct ("HClose" with "[Htok Hgtok2 R0z R1z Hown]") as "Hown".
    iFrame.
    iNext.
    iRight;iLeft.
    iFrame.
    rewrite wp_sswp.
    iApply (sswp_fupd_around i ⊤ ⊤ ⊤).
    iMod "Hown".
    iMod (na_inv_acc with "Hinv Hown") as "(>[HInv | [[Htok Hrest] | (Htok & Hgtok1' & Hrest)]] & Hown & HClose)";auto.
    iModIntro.
    1: { iDestruct "HInv" as (w0 w1) "( Htok & Hrest )".
         iDestruct (eliminate_wrong_token) as "J".
      apply neH.
      iApply ("J" with "Htok").
      iModIntro.
      iIntros "(Htok & HFALSE)".
      iDestruct ("HClose" with "[Htok Hrest Hown ]") as "HClose".
      iFrame.
    iNext.
    iLeft.
    iExists w0, w1.
    iFrame.
    iMod "HClose".
    iModIntro.
    iExFalso.
    done.
      }
    1: {
    iDestruct (eliminate_wrong_token) as "J".
      apply neH.
      iApply ("J" with "Htok").
      iModIntro.
      iNext.
      iIntros "(Htok & HFALSE)".
      iDestruct ("HClose" with "[Htok Hrest Hown ]") as "HClose".
      iFrame.
    iNext.
    iRight;iLeft.
    iFrame.
    iMod "HClose".
    iModIntro.
    iExFalso.
    done.
    }
    1: {
      iExFalso.
      iApply (tokI_excl with "Hgtok1 Hgtok1'").
    }
Qed.

  Lemma spec1 {γ1 γ2 γ3 z i q1 q2 prog1page prog2page r0_} :
      fin_to_nat z = 0 ->
      z ≠ i ->
      prog1page ≠ prog2page ->
      seq_in_page (of_pid prog1page) (length (program1 i)) prog1page ->
      seq_in_page (of_pid prog2page) (length program2) prog2page ->
      program (program1 i) (of_pid prog1page) ∗
      program (program2) (of_pid prog2page) ∗
      nainv invN (inv γ1 γ2 γ3 z i) ∗ tokI γ2 ∗
      nainv_closed ⊤ ∗
      A@z :={q1} prog1page ∗ A@i :={q2} prog2page ∗
      PC @@ z ->r (of_pid prog1page) ∗ PC @@ i ->r (of_pid prog2page) ∗
      R0 @@ i ->r r0_
        ⊢ (WP ExecI @ z {{ (λ m, ⌜m = HaltI⌝
            ∗ nainv_closed ⊤ ∗ tokI γ3
            ∗ program (program1 i) (of_pid prog1page)
            ∗ A@z :={q1} prog1page
            ∗ PC @@ z ->r ((of_pid prog1page) ^+ (length (program1 i)))%f) }}%I)
       ∗ (WP ExecI @ i {{ (λ m, ⌜m = ExecI⌝
            ∗ nainv_closed ⊤
            ∗ program (program1 i) (of_pid prog2page)
            ∗ A@i :={q1} prog2page
            ∗ PC @@ i ->r ((of_pid prog2page) ^+ (length program2))%f
            ∗ R0 @@ i ->r yield_I) }}%I).
  Proof.
    iIntros (Z Hvne Hpne HInz HIni) "(Hprogz & Hprogi & #Hinv &  Hgtok2 & Hown & Haccz & Hacci & PCz & PCi & R0i)".
 Admitted.

  (* XXX: na_invariants can only be opened by a single thread, so we have to switch back to regular invariants... *)
  (* we may need a new wp... *)
End RunYield1.
