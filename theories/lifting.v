From machine_program_logic.program_logic Require Import machine weakestpre.
From HypVeri Require Import lang.
From iris.proofmode Require Import tactics.


Lemma machine_mixin : MachineMixin terminated step.
Proof.
  refine {| mixin_terminated_stuck := terminated_stuck |}.
Qed.

Canonical Structure hyp_machine :=
  Machine terminated step (Some scheduler) machine_mixin.

Section lifting.

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
