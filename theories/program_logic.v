From machine_program_logic.program_logic Require Export machine weakestpre.
From HypVeri Require Export lang RAs.

Lemma machine_mixin : MachineMixin terminated HypVeri.lang.step.
Proof.
  refine {| mixin_terminated_stuck := terminated_stuck |}.
Qed.

Canonical Structure hyp_machine := Machine terminated step (Some scheduler) machine_mixin.

Context `{vmG : !gen_VMG Σ}.

Lemma hyp_irisG : irisG hyp_machine Σ.
Proof.
  refine {| iris_invG := gen_invG;
            state_interp σ := (gen_vm_interp σ)%I;
         |}.
Qed.

Lemma mov_reg_rule (i : nat) : WP ExecI @ i {{ True }}.
