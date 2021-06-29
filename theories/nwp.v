From machine_program_logic.program_logic Require Import machine weakestpre.
From HypVeri Require Import RAs rule_base lifting.
From iris.proofmode Require Import tactics.

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

Lemma why_we_need_a_new_wp {i ai j}:
  j ≠ i ->
  << j >> ∗ PC @@i ->r ai ⊢ WP ExecI @ i {{ (λ m, ⌜m = ExecI ⌝ ∗ << i >> ∗ PC @@ i ->r (ai +w 1))}}.
Proof.
  intros.
  iLöb as "IH".
  iIntros "[Htok HPC]".
  iApply wp_unfold. rewrite /wp_pre.
  simpl.
  iIntros (σ1) "%Hsche Hσ".
  iApply fupd_mask_intro; first set_solver.
  iIntros "Hmask".
  iDestruct "Hσ" as "(Hstate & ?)".
  iDestruct (gen_token_valid_neq j i with "Htok Hstate") as "%Hnsche";eauto.
  apply Hnsche in Hsche.
  done.
Qed.
