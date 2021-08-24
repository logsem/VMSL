From machine_program_logic.program_logic Require Import weakestpre.
From HypVeri.algebra Require Import base token reg pagetable.
From HypVeri Require Import lifting.
From HypVeri.lang Require Import lang_extra.
Require Import stdpp.fin.


Global Instance hyp_irisG `{gen_VMG Σ}: irisG hyp_machine Σ:=
  {
  iris_invG := gen_invG;
  state_interp := gen_vm_interp
  }.

Section rules_base.

Context `{vmG: !gen_VMG Σ}.
Implicit Type a : Addr.
Implicit Type i : VMID.
Implicit Type ra rb : reg_name.
Implicit Type w: Word.
Implicit Type q : Qp.
  

Lemma not_valid_pc {a i s} :
  (to_pid_aligned a) ∉ s ->
  {SS{{ ▷ (PC @@ i ->r a) ∗ ▷ A@i:={1}[s] }}} ExecI @ i {{{ RET FailI; PC @@ i ->r a ∗ A@i:={1}[s] }}}.
Proof.
  simpl.
  iIntros (Hmm ϕ) "(>Hpc & >Ha) Hϕ".
  iApply (sswp_lift_atomic_step ExecI);[done|].
  iIntros (σ1) "%Hsche Hσ1".
  inversion Hsche as [ Hcur ]; clear Hsche.
  apply fin_to_nat_inj in Hcur.
  iModIntro.
  iDestruct "Hσ1" as "(? & ? & Hreg & ? & ? & ? & ? & Haccess & ?)".
  iDestruct (gen_reg_valid1 PC i a Hcur with "Hreg Hpc") as "%Hpc".
  iDestruct (gen_access_valid_not (to_pid_aligned a) s Hmm with "Haccess Ha") as "%Hnacc".
  iSplit.
  - iPureIntro.
    rewrite /reducible.
    exists FailI, σ1.
    apply step_exec_fail.
    rewrite /is_valid_PC Hpc Hcur.
    simpl.
    rewrite check_access_page_mem_eq in Hnacc.
    rewrite Hnacc.
    done.
  - iModIntro.
    iIntros (m2 σ2) "%HstepP".
    iModIntro.
    inversion HstepP; subst.
    + simpl.
      rewrite /gen_vm_interp.
      iFrame.
      iApply "Hϕ".
      iFrame.
    + simplify_eq.
      rewrite /is_valid_PC Hpc in H.      
      simpl in H.
      rewrite check_access_page_mem_eq in Hnacc.
      rewrite Hnacc in H.
      inversion H.
Qed.

Lemma eliminate_wrong_token {i j q E} :
  j ≠ i ->
  {SS{{ ▷ (<<j>>{ q })}}} ExecI @ i ; E {{{ RET ExecI ; <<j>>{ q } ∗ False }}}.
Proof.
  iIntros (Hne Φ ) "> Htok HΦ".
  iApply (sswp_lift_atomic_step ExecI) ;[done|].
  iIntros (σ1) "%Hsche Hσ".
  iDestruct "Hσ" as "(Htokown & ? & ? & ? & ? & ? & ? & ?)".
  iDestruct (gen_token_valid_neq j i Hne with "Htok Htokown") as "%Hnsch".
  iExFalso.
  iPureIntro.
  done.
Qed.


End rules_base.
