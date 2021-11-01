From machine_program_logic.program_logic Require Import machine weakestpre.
From HypVeri Require Import lang.
From iris.proofmode Require Import tactics.


Section lifting.

Context `{HyperConst : !HypervisorConstants}.
Context `{HyperParams : !HypervisorParameters}.
Lemma machine_mixin : MachineMixin terminated step.
Proof.
  refine {| mixin_terminated_stuck := terminated_stuck |}.
Qed.

Global Canonical Structure hyp_machine :=
  Machine terminated step (Some scheduler) machine_mixin.

Context `{_ : !irisG hyp_machine Σ}.

Lemma sswp_lift_step_fupd {i E Φ} m1 :
  machine.terminated m1 = false →
  (∀ n σ1 , ⌜scheduled σ1 i⌝ -∗  state_interp n σ1 ={E,∅}=∗
    ⌜reducible m1 σ1⌝ ∗
    ∀ m2 σ2 , (∃ P, VMPropAuth i P) -∗
    ⌜step m1 σ1 m2 σ2⌝ ={∅}=∗ ▷ |={∅,E}=>
    (∃ P, VMPropAuth i P) ∗ state_interp n σ2 ∗
    ([∗ list] vmid ∈ just_scheduled_vms n σ1 σ2, VMProp_holds vmid) ∗
    Φ (negb (scheduled σ2 i) && negb (terminated m2), m2))
  ⊢ SSWP m1 @ i; E {{ Φ }}.
Proof.
  by rewrite sswp_eq /sswp_def=>->.
Qed.

Lemma sswp_lift_step {i E Φ} m1 :
  machine.terminated m1 = false →
  (∀ n σ1 , ⌜scheduled σ1 i⌝ -∗  state_interp n σ1 ={E,∅}=∗
    ⌜reducible m1 σ1⌝ ∗
    ▷ ∀ m2 σ2 , (∃ P, VMPropAuth i P) -∗ ⌜step m1 σ1 m2 σ2 ⌝ ={∅,E}=∗
      (∃ P, VMPropAuth i P) ∗ state_interp n σ2 ∗
    ([∗ list] vmid ∈ just_scheduled_vms n σ1 σ2, VMProp_holds vmid) ∗
    Φ (negb (scheduled σ2 i) && negb (terminated m2), m2)) 
  ⊢ SSWP m1 @ i; E {{ Φ }}.
Proof.
  iIntros (?) "H".
  iApply sswp_lift_step_fupd; [done |].
  iIntros (? ?) "Hsche Hσ".
  iMod ("H" $! n σ1 with "Hsche Hσ") as "[ $ H]".
  iIntros "!> * [% HpropA] % !> !>". 
  iApply ("H" with "[HpropA]");auto.
Qed.

Lemma sswp_lift_atomic_step_fupd {i E1 E2 Φ} m1 :
  machine.terminated m1 = false →
  (∀ n σ1 , ⌜scheduled σ1 i⌝ -∗  state_interp n σ1 ={E1}=∗
    ⌜reducible m1 σ1⌝ ∗
    ∀ m2 σ2 , (∃ P, VMPropAuth i P) -∗ ⌜step m1 σ1 m2 σ2 ⌝ ={E1} [E2]▷=∗
      (∃ P, VMPropAuth i P) ∗ state_interp n σ2 ∗
    ([∗ list] vmid ∈ just_scheduled_vms n σ1 σ2, VMProp_holds vmid) ∗
    Φ (negb (scheduled σ2 i) && negb (terminated m2), m2)) 
  ⊢ SSWP m1 @ i; E1 {{ Φ }}.
Proof.
  iIntros (?) "H".
  iApply (sswp_lift_step_fupd m1)=>//.
  iIntros (? ?) "Hsche Hσ".
  iMod ("H" $! n σ1 with "Hsche Hσ") as "[$ H]".
  iApply fupd_mask_intro;first set_solver.
  iIntros "Hclose" (m2 σ2).
  iMod "Hclose" as "_".
  iIntros "[% Hprop] %".
  iDestruct ("H" $! m2 σ2 with "[Hprop]") as "H";[eauto|]. 
  iMod ("H" $! H0) as "H". 
  iApply fupd_mask_intro;first set_solver.
  iIntros " Hclose !>".
  iMod "Hclose" as "_".
  by iApply "H".
Qed.

Lemma sswp_lift_atomic_step {i E Φ} m1 :
  machine.terminated m1 = false →
  (∀ n σ1 , ⌜scheduled σ1 i⌝ -∗  state_interp n σ1 ={E}=∗
    ⌜reducible m1 σ1⌝ ∗
    ▷ ∀ m2 σ2 , (∃ P, VMPropAuth i P) -∗ ⌜step m1 σ1 m2 σ2 ⌝ ={E}=∗
      (∃ P, VMPropAuth i P) ∗ state_interp n σ2 ∗
    ([∗ list] vmid ∈ just_scheduled_vms n σ1 σ2, VMProp_holds vmid) ∗
    Φ (negb (scheduled σ2 i) && negb (terminated m2), m2))
  ⊢ SSWP m1 @ i; E {{ Φ }}.
Proof.
  iIntros (?) "H".
  iApply (@sswp_lift_atomic_step_fupd i E E Φ);[done|].
  iIntros (? ? Hsche) "Hσ".
  iMod ("H" $! n σ1 Hsche with "Hσ") as "[$ H]".
  iIntros "!> * [% Hprop] %Hstep". 
  do 2 iModIntro.
  iApply ("H" with "[Hprop]");auto.
Qed.

End lifting.
