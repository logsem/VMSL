From machine_program_logic.program_logic Require Import machine weakestpre.
From HypVeri Require Export lang RAs.

Lemma machine_mixin : MachineMixin terminated HypVeri.lang.step.
Proof.
  refine {| mixin_terminated_stuck := terminated_stuck |}.
Qed.

Canonical Structure hyp_machine := Machine terminated step (Some scheduler) machine_mixin.

Context `{_ : irisG hyp_machine Σ}.


Lemma mov_reg_rule (i : nat) : True ⊢ WP ExecI @ i {{ (λ m, True) }}%I.
