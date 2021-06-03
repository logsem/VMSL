From machine_program_logic.program_logic Require Import machine weakestpre.
From HypVeri Require Export lang RAs.
From iris.proofmode Require Import tactics.
(* From iris_string_ident Require Import ltac2_string_ident. *)

Section lifting.

Lemma machine_mixin : MachineMixin terminated step.
Proof.
  refine {| mixin_terminated_stuck := terminated_stuck |}.
Qed.

Canonical Structure hyp_machine :=
  Machine terminated step (Some scheduler) machine_mixin.

Context `{_ : !irisG hyp_machine Σ}.

Lemma sswp_lift_step_fupd {i E Φ} m1 :
  machine.terminated m1 = false →
  (∀ σ1 , ⌜scheduled σ1 i⌝ -∗  state_interp σ1 ={E,∅}=∗
    ⌜reducible m1 σ1⌝ ∗
    ∀ m2 σ2 , ⌜step m1 σ1 m2 σ2 ⌝ ={∅}=∗ ▷ |={∅,E}=>
      state_interp σ2 ∗  Φ m2 )
  ⊢ SSWP m1 @ i; E {{ Φ }}.
Proof.
  by rewrite sswp_eq /sswp_def=>->.
Qed.

Lemma sswp_lift_step {i E Φ} m1 :
  machine.terminated m1 = false →
  (∀ σ1 , ⌜scheduled σ1 i⌝ -∗  state_interp σ1 ={E,∅}=∗
    ⌜reducible m1 σ1⌝ ∗
    ▷∀ m2 σ2 , ⌜step m1 σ1 m2 σ2 ⌝ ={∅,E}=∗
      state_interp σ2 ∗  Φ m2 )
  ⊢ SSWP m1 @ i; E {{ Φ }}.
Proof.
  iIntros (?) "H".
  iApply sswp_lift_step_fupd; [done |].
  iIntros (?) "Hsche Hσ".
  iMod ("H" $! σ1 with "Hsche Hσ") as "[ $ H]".
  iIntros "!> * % !> !>".
  by iApply "H".
Qed.


Lemma sswp_lift_atomic_step_fupd {i E1 E2 Φ} m1 :
  machine.terminated m1 = false →
  (∀ σ1 , ⌜scheduled σ1 i⌝ -∗  state_interp σ1 ={E1}=∗
    ⌜reducible m1 σ1⌝ ∗
    ∀ m2 σ2 , ⌜step m1 σ1 m2 σ2 ⌝ ={E1} [E2]▷=∗
      state_interp σ2 ∗  Φ m2 )
  ⊢ SSWP m1 @ i; E1 {{ Φ }}.
Proof.
  iIntros (?) "H".
  iApply (sswp_lift_step_fupd m1)=>//.
  iIntros (?) "Hsche Hσ".
  iMod ("H" $! σ1 with "Hsche Hσ") as "[$ H]".
  iApply fupd_mask_intro;first set_solver.
  iIntros "Hclose" (m2 σ2 ?).
  iMod "Hclose" as "_".
  iMod ("H" $! m2 σ2 with "[#]") as "H";[done|].
  iApply fupd_mask_intro;first set_solver.
  iIntros " Hclose !>".
  iMod "Hclose" as "_".
  by iApply "H".
Qed.

Lemma sswp_lift_atomic_step {i E Φ} m1 :
  machine.terminated m1 = false →
  (∀ σ1 , ⌜scheduled σ1 i⌝ -∗  state_interp σ1 ={E}=∗
    ⌜reducible m1 σ1⌝ ∗
    ▷ ∀ m2 σ2 , ⌜step m1 σ1 m2 σ2 ⌝ ={E}=∗
      state_interp σ2 ∗  Φ m2 )
  ⊢ SSWP m1 @ i; E {{ Φ }}.
Proof.
  iIntros (?) "H".
  iApply (@sswp_lift_atomic_step_fupd i E E Φ);[done|].
  iIntros (??) "Hσ".
  iMod ("H" $! σ1 H0 with "Hσ") as "[$ H]".
  iIntros "!> *".
  iIntros (Hstep).
  do 2 iModIntro.
  by iApply "H".
Qed.

End lifting.

Section rules.

Global Instance hyp_irisG `{gen_VMG Σ}: irisG hyp_machine Σ:=
  {
  iris_invG := gen_invG;
  state_interp := gen_vm_interp
  }.

Context `{vmG: !gen_VMG Σ}.
Implicit Type a : addr.
Implicit Type i : vmid.
Implicit Type ra rb : reg_name.
Implicit Type w: word.
Implicit Type q : Qp.




Lemma mov_word {i w1 w3 q} a w2 ra :
  decode_instruction w1 = Some(Mov ra (inl w2)) ->
  PC @@ i ->r a ∗ a ->a w1 ∗ A@i:={q} (mm_translation a) ∗ ra @@ i ->r w3  ⊢ SSWP ExecI @ i {{ (λ m, True) }}%I.
Proof.
  iIntros (Hdecode) "(Hpc & Hapc & Hacc & Hra)".
  iApply (sswp_lift_atomic_step ExecI);[done|].
  iIntros (σ1) "%Hsche Hσ".
  inversion Hsche.
  subst i0 σ1.
  iModIntro.
  iDestruct "Hσ" as "(? & Hmem & Hreg & ? )".
  Check gen_reg_valid_Sep.
  iDestruct ((gen_reg_valid_Sep σ (get_current_vm σ) (<[(PC,i):=a]>{[(ra,i):=w3]}))
               with "Hreg [Hpc Hra]") as "Hreg".
  done.
  (* iApply (big_sepM_delete _ _ (PC,i) a). *)
  (* simplify_map_eq. *)
  (* done. *)
  (* iFrame. *)
  (* iApply (big_sepM_delete _ _ (ra,i) w3). *)
  (* simplify_map_eq. *)
  (* apply lookup_delete_Some. *)
  (* split. *)
  (* iFrame. *)

  (*TODO:  need some helper lemmas ...*)
  Admitted.
