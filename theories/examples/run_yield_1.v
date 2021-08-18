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

  Context `{gen_VMG Σ, tokG Σ} (N : namespace).

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

  Definition na_inv  γ2 γ3 (z i:VMID) :=
    ((∃ w0 w1,  tokI γ2  ∗ R0 @@ z ->r w0 ∗ R1 @@ z ->r w1) ∨
     ( tokI γ3  ∗ R0 @@ z ->r run_I ∗ R1 @@ z ->r (encode_vmid i)))%I.

  Definition inv' z i γ1 γ2 γ3 ι1 :=
    ( ( <<z>>{ 1%Qp } ∗ nainv_closed (⊤ ∖ ↑ι1) ∗ tokI γ1)
      ∨ <<z>>{ 1%Qp } ∗ nainv_closed ⊤ ∗ tokI γ3
      ∨ <<i>>{ 1%Qp } ∗ nainv_closed ⊤ ∗ tokI γ1 ∗ tokI γ2 )%I.

  Lemma machine_z_spec {γ1 γ2 γ3 z i q1 prog1page ι ι1} :
      ι ## ι1 ->
      fin_to_nat z = 0 ->
      z ≠ i ->
      seq_in_page (of_pid prog1page) (length (program1 i)) prog1page ->
      tokI γ1 ∗
      program (program1 i) (of_pid prog1page) ∗
      inv ι (inv' z i γ1 γ2 γ3 ι1) ∗
      nainv ι1 (na_inv γ2 γ3 z i) ∗
      A@z :={q1} prog1page
      ∗ PC @@ z ->r (of_pid prog1page)
      ⊢ (WP ExecI @ z
            {{ (λ m, ⌜m = HaltI⌝
            ∗ program (program1 i) (of_pid prog1page)
            ∗ A@z :={q1} prog1page
            ∗ PC @@ z ->r ((of_pid prog1page) ^+ (length (program1 i)))%f)}}%I).
  Proof.
    iIntros (Hdisj zP neH HIn) "(H△ & (p_1 & p_2 & p_3 & p_4 & _) & #Hinv & #Hnainv & Hacc & PCz )".
    apply seq_in_page_forall in HIn.
    rewrite wp_sswp.
    iApply (sswp_fupd_around z ⊤ (⊤ ∖ ↑ι) ⊤).
    iInv ι as ">Inv" "HIClose".
    iDestruct "Inv" as "[(? & ? & H△')|[ (Htok & Hown & H□ ) | (Htok & ?) ]]".
    1: {
    iExFalso.
    iDestruct (tokI_excl with "H△ H△'") as %[].
    }
    2: {
      iDestruct (eliminate_wrong_token) as "J".
      assert (Hne: i ≠ z). { intro.  apply neH. symmetry. done. }
      apply Hne.
      iApply ("J" with "Htok").
      iModIntro.
      iNext.
      iIntros "(_ & HFALSE)".
      iDestruct "HFALSE" as %[].
    }
    (* mov_word_I R0 run_I *)
    iMod (na_inv_acc with "Hnainv Hown") as "(>[HInv |  (  H□' &_ & _ )] & Hown & HClose)";auto.
    set_solver.
    iDestruct "HInv" as (w0 w1) "(H♢ & R0z & R1z )".
    2: {
      iExFalso.
      iApply (tokI_excl with "H□ H□'").
    }
    iDestruct
      ((mov_word (of_pid prog1page) run_I R0) with "[p_1 PCz Hacc R0z]") as "J";eauto.
    3:{iFrame. }
    by rewrite decode_encode_instruction.
    by inversion HIn.
    iApply "J".
    iModIntro.
    iNext.
    iIntros "( PCz & p_1 & Hacc & R0z)".
    iDestruct ("HIClose" with "[Htok Hown H△]") as "HIClose".
    iNext;iLeft;iFrame.
    iMod "HIClose" as %_.
    iModIntro.
    (* mov_word_I R1 (encode_vmid i) *)
    rewrite wp_sswp.
    iDestruct
      ((mov_word ((of_pid prog1page) ^+ 1)%f  (encode_vmid i) R1)
         with "[p_2 PCz Hacc R1z]") as "J"; eauto.
    3:{iFrame. }
    by rewrite decode_encode_instruction.
    by inversion HIn;inversion H4.
    iApply "J".
    iNext.
    iIntros "(PCz & p_2 & Hacc & R1z)".
    (* hvc_I *)
    rewrite wp_sswp.
    iApply (sswp_fupd_around z ⊤ (⊤ ∖ ↑ι) _).
    iInv ι as ">Inv" "HIClose".
    iDestruct "Inv" as "[(Htokz & Hown & H△)|[ (_ & _ & H□') | (Htok' & ?) ]]".
        2: {   iExFalso.
      iApply (tokI_excl with "H□ H□'").
    }
    2: {
      iDestruct (eliminate_wrong_token) as "J".
      assert (Hne: i ≠ z). { intro.  apply neH. symmetry. done. }
      apply Hne.
      iApply ("J" with "Htok'").
      iModIntro.
      iNext.
      iIntros "(_ & HFALSE)".
      iDestruct "HFALSE" as %[].
    }
    iDestruct
      ((run (((of_pid prog1page) ^+ 1) ^+ 1)%f i)
         with "[Htokz PCz p_3 Hacc R0z R1z]") as "J"; eauto.
    5: { iFrame. }
    by rewrite decode_encode_instruction.
    by inversion HIn;inversion H4; inversion H8.
    by rewrite decode_encode_hvc_func.
    by rewrite decode_encode_vmid.
    iApply "J".
    iModIntro.
    iNext.
    iIntros "(Htoki & PCz & p_3 & Hacc & R0z & R1z)".
    iDestruct ("HClose" with "[Hown R0z R1z H□]") as "Hown".
    iFrame.
    iNext.
    iRight.
    iFrame.
    iMod "Hown".
    iDestruct ("HIClose" with "[Htoki Hown H♢ H△]") as "HIClose".
    iNext;iRight;iRight;iFrame.
    iMod "HIClose" as %_.
    iModIntro.
    (* halt_I *)
    rewrite wp_sswp.
    iDestruct
      ((halt ((((of_pid prog1page) ^+ 1) ^+ 1) ^+1 )%f)
         with "[PCz p_4 Hacc]") as "J"; eauto.
    3: { iFrame. }
    by rewrite decode_encode_instruction.
    by inversion HIn;inversion H4; inversion H8; inversion H12.
    iApply "J".
    iNext.
    iIntros "( PCz & p_4 & Hacc )".
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

  Lemma machine_i_spec {γ1 γ2 γ3 z i q1 prog2page r0_ ι ι1} :
      ι ## ι1 ->
      fin_to_nat z = 0 ->
      z ≠ i ->
      seq_in_page (of_pid prog2page) (length program2) prog2page ->
      program program2 (of_pid prog2page) ∗
      inv ι (inv' z i γ1 γ2 γ3 ι1) ∗
      nainv ι1 (na_inv  γ2 γ3 z i) ∗
      A@i :={q1} prog2page
      ∗ PC @@ i ->r (of_pid prog2page)
      ∗ R0 @@ i ->r r0_
      ⊢ (WP ExecI @ i
            {{ (λ m, ⌜m = ExecI⌝
            ∗ tokI γ1
            ∗ program (program1 i) (of_pid prog2page)
            ∗ A@i :={q1} prog2page
            ∗ PC @@ i ->r ((of_pid prog2page) ^+ (length program2))%f
            ∗ R0 @@ i ->r yield_I)}}%I).
  Proof.
    iIntros (Hdisj zP neH HIn) "((p_1 & p_2 & _) & #Hinv & #Hnainv & Hacc & PCi & R0i)".
    apply seq_in_page_forall in HIn.
    (* mov_word_I R0 yield_I *)
    rewrite wp_sswp.
    iDestruct
      ((mov_word (of_pid prog2page) yield_I R0) with "[p_1 PCi Hacc R0i]") as "J";eauto.
    3:{iFrame. }
    by rewrite decode_encode_instruction.
    by inversion HIn.
    iApply "J".
    iModIntro.
    iIntros "(PCi & p_1 & Hacc & R0i)".
    (* hvc_I *)
    rewrite wp_sswp.
    iApply (sswp_fupd_around i ⊤ (⊤ ∖ ↑ι) _).
    iInv ι as ">Inv" "HIClose".
    iDestruct "Inv" as "[(Htokz & _ )|[ (Htokz & _ ) | (Htoki & Hown &  H△ & H♢) ]]".
     1: {
      iDestruct (eliminate_wrong_token) as "J".
      apply neH.
      iApply ("J" with "Htokz").
      iModIntro.
      iNext.
      iIntros "(Htok & HFALSE)".
      iDestruct "HFALSE" as %[].
    }
     1: {
      iDestruct (eliminate_wrong_token) as "J".
      apply neH.
      iApply ("J" with "Htokz").
      iModIntro.
      iNext.
      iIntros "(Htok & HFALSE)".
      iDestruct "HFALSE" as %[].
    }
    iMod (na_inv_acc with "Hnainv Hown") as "(>[ HInv | (H□ & R0z & R1z)] & Hown & HClose)";auto.
     set_solver.
     1: {
     iDestruct "HInv" as (w0 w1) "(H♢' & R0z & R1z )".
     iExFalso.
      iApply (tokI_excl with "H♢ H♢'").
      }
    iDestruct
      ((yield ((of_pid prog2page) ^+ 1) %f)
         with "[Htoki PCi p_2 Hacc R0i R0z R1z]") as "J"; eauto.
    4: { iFrame. }
    by rewrite decode_encode_instruction.
    by inversion HIn;inversion H4.
    by rewrite decode_encode_hvc_func.
    iApply "J".
    iModIntro.
    iNext.
    iIntros "(Htokz & PCi & p_2 & Hacc & R0i & R0z & R1z)".
    iDestruct ("HClose" with "[ H♢ R0z R1z Hown]") as "Hown".
    iFrame.
    iNext.
    iLeft.
    iExists (encode_hvc_func Yield), (encode_vmid i).
    iFrame.
    iMod "Hown".
    iDestruct ("HIClose" with "[H□ Htokz Hown]") as "HIClose".
    iNext;iRight;iLeft;iFrame.
    iMod "HIClose" as %_.
    iModIntro.
    rewrite wp_sswp.
    iApply (sswp_fupd_around i ⊤ (⊤ ∖ ↑ι) ⊤).
    iInv ι as ">Inv" "HIClose".
    iDestruct "Inv" as "[(Htokz & _ )|[ (Htokz & _ ) | (_ & _ &  H△' & _) ]]".
     1: {
      iDestruct (eliminate_wrong_token) as "J".
      apply neH.
      iApply ("J" with "Htokz").
      iModIntro.
      iNext.
      iIntros "(Htok & HFALSE)".
      iDestruct "HFALSE" as %[].
    }
     1: {
      iDestruct (eliminate_wrong_token) as "J".
      apply neH.
      iApply ("J" with "Htokz").
      iModIntro.
      iNext.
      iIntros "(Htok & HFALSE)".
      iDestruct "HFALSE" as %[].
    }
     iExFalso.
      iApply (tokI_excl with "H△ H△'").
  Qed.

  Lemma run_yield_1_spec' γ1 γ2 γ3 ι ι1 z i q1 q2 prog1page prog2page r0_:
      ι ## ι1 ->
      fin_to_nat z = 0 ->
      z ≠ i ->
      prog1page ≠ prog2page ->
      seq_in_page (of_pid prog1page) (length (program1 i)) prog1page ->
      seq_in_page (of_pid prog2page) (length program2) prog2page ->
      program (program1 i) (of_pid prog1page) ∗
      program (program2) (of_pid prog2page) ∗
      inv ι (inv' z i γ1 γ2 γ3 ι1) ∗
      nainv ι1 (na_inv  γ2 γ3 z i) ∗ tokI γ1 ∗
      A@z :={q1} prog1page ∗ A@i :={q2} prog2page ∗
      PC @@ z ->r (of_pid prog1page) ∗ PC @@ i ->r (of_pid prog2page) ∗
      R0 @@ i ->r r0_
        ⊢ (WP ExecI @ z {{ (λ m, ⌜m = HaltI⌝
            ∗ program (program1 i) (of_pid prog1page)
            ∗ A@z :={q1} prog1page
            ∗ PC @@ z ->r ((of_pid prog1page) ^+ (length (program1 i)))%f )}}%I)
       ∗ (WP ExecI @ i {{ (λ m, ⌜m = ExecI⌝
            ∗ tokI γ1
            ∗ program (program1 i) (of_pid prog2page)
            ∗ A@i :={q2} prog2page
            ∗ PC @@ i ->r ((of_pid prog2page) ^+ (length program2))%f
            ∗ R0 @@ i ->r yield_I) }}%I).
  Proof.
    iIntros (Hdisj Z Hvne Hpne HInz HIni) "(Hprogz & Hprogi & #Hinv & #Hnainv & H△ & Haccz & Hacci & PCz & PCi & R0i)".
    iSplitL  "Hprogz H△ Haccz PCz".
    - iApply machine_z_spec;eauto.
      iFrame.
      iSplitL;done.
    - iApply machine_i_spec;eauto.
      iFrame.
      iSplitL;done.
  Qed.

  Definition invN := N .@ "inv".

  Definition nainvN := N .@ "na".

  Lemma namespace_disjoint: invN ## nainvN.
  Proof.
    apply ndot_ne_disjoint.
    done.
  Qed.

  Lemma run_yield_1_spec z i q1 q2 prog1page prog2page r0_ r1_ r0_':
      fin_to_nat z = 0 ->
      z ≠ i ->
      prog1page ≠ prog2page ->
      seq_in_page (of_pid prog1page) (length (program1 i)) prog1page ->
      seq_in_page (of_pid prog2page) (length program2) prog2page ->
      program (program1 i) (of_pid prog1page) ∗
      program (program2) (of_pid prog2page) ∗
      nainv_closed ⊤ ∗
      <<z>>{ 1%Qp} ∗ R0 @@ z ->r r0_ ∗ R1 @@ z ->r r1_ ∗
      A@z :={q1} prog1page ∗ A@i :={q2} prog2page ∗
      PC @@ z ->r (of_pid prog1page) ∗ PC @@ i ->r (of_pid prog2page) ∗
      R0 @@ i ->r r0_'
        ⊢ |={⊤}=>
        (WP ExecI @ z {{ (λ m, ⌜m = HaltI⌝
            ∗ program (program1 i) (of_pid prog1page)
            ∗ A@z :={q1} prog1page
            ∗ PC @@ z ->r ((of_pid prog1page) ^+ (length (program1 i)))%f )}}%I)
       ∗ (WP ExecI @ i {{ (λ m, ⌜m = ExecI⌝
            ∗ program (program1 i) (of_pid prog2page)
            ∗ A@i :={q2} prog2page
            ∗ PC @@ i ->r ((of_pid prog2page) ^+ (length program2))%f
            ∗ R0 @@ i ->r yield_I) }}%I).
  Proof.
    iIntros ( Z Hvne Hpne HInz HIni) "(Hprogz & Hprogi & Hnatok & Hstok & R0z & R1z & Haccz & Hacci & PCz & PCi & R0i)".
    iMod (own_alloc (Excl ())) as (γ1) "Htok1". done.
    iMod (own_alloc (Excl ())) as (γ2) "Htok2". done.
    iMod (own_alloc (Excl ())) as (γ3) "Htok3". done.
    iMod ((nainv_alloc nainvN ⊤ (na_inv  γ2 γ3 z i)) with "[ R0z R1z Htok2 ]" ) as "Hnainv".
    { iNext. iLeft. iExists r0_, r1_. iFrame. }
    iMod (inv_alloc invN _ (inv' z i γ1 γ2 γ3 nainvN) with "[Hstok Hnatok Htok3]") as "Hinv".
    { iNext. iRight;iLeft. iFrame. }
    iModIntro.
    iDestruct (run_yield_1_spec' γ1 γ2 γ3 invN nainvN z i q1 q2 prog1page prog2page r0_'
                 with "[Hprogz Hprogi Haccz Hacci PCz PCi R0i Htok1 Hnainv Hinv]") as "[WP1 WP2]";eauto.
    { apply namespace_disjoint. }
    { iFrame. }
    iFrame.
    iApply (wp_mono with "WP2").
    iIntros (?) "(? & ? & ? & ? & ? & ? )".
    iFrame.
  Qed.


End RunYield1.
