From machine_program_logic.program_logic Require Import machine weakestpre.
From HypVeri Require Import RAs rule_misc lifting.
From iris.proofmode Require Import tactics.
Require Import iris.base_logic.lib.ghost_map.
Require Import stdpp.fin.

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


Ltac rewrite_reg_all :=
  match goal with
  | |- _ =>
    try rewrite -> update_offset_PC_preserve_current_vm; try rewrite -> update_reg_global_preserve_current_vm;
    try rewrite -> update_offset_PC_preserve_mem ; try rewrite -> update_reg_global_preserve_mem;
    try rewrite -> update_offset_PC_preserve_tx ; try rewrite -> update_reg_global_preserve_tx;
    try rewrite -> update_offset_PC_preserve_rx ; try rewrite  -> update_reg_global_preserve_rx;
    try rewrite -> update_offset_PC_preserve_owned  ; try rewrite -> update_reg_global_preserve_owned;
    try rewrite -> update_offset_PC_preserve_access  ; try rewrite -> update_reg_global_preserve_access;
    try rewrite -> update_offset_PC_preserve_trans  ; try rewrite -> update_reg_global_preserve_trans;
    try rewrite -> update_offset_PC_preserve_receivers  ; try rewrite -> update_reg_global_preserve_receivers
  end.


Ltac rewrite_mem_all :=
  match goal with
  | |- _ =>
    try rewrite -> update_memory_unsafe_preserve_current_vm;
    try rewrite -> update_reg_global_preserve_mem;
    try rewrite -> update_memory_unsafe_preserve_tx;
    try rewrite -> update_memory_unsafe_preserve_rx;
    try rewrite -> update_memory_unsafe_preserve_owned;
    try rewrite -> update_memory_unsafe_preserve_access;
    try rewrite -> update_memory_unsafe_preserve_trans;
    try rewrite -> update_memory_unsafe_preserve_receivers
  end.

Ltac solve_reg_lookup :=
  match goal with
  | _ : get_reg ?σ ?r = Some ?w |- get_reg_gmap ?σ !! (?r, ?i) = Some ?w => rewrite get_reg_gmap_get_reg_Some;eauto
  | _ : get_reg ?σ ?r = Some ?w |- is_Some (get_reg_gmap ?σ !! (?r, ?i)) => eexists;rewrite get_reg_gmap_get_reg_Some;eauto
  | _ : get_reg ?σ ?r1 = Some ?w, _ : ?r1 ≠ ?r2 |- <[(?r2, ?i):= ?w2]>(get_reg_gmap ?σ) !! (?r1, ?i) = Some ?w =>
    rewrite lookup_insert_ne; eauto
  end.
  

Lemma check_access_page_mem_eq {σ i a} :
  check_access_page σ i (mm_translation a) =
  check_access_addr σ i a.
Proof.
  rewrite /check_access_addr; done.
Qed.

Lemma not_valid_pc {a i s} :
  (mm_translation a) ∉ s ->
  {SS{{ ▷ (PC @@ i ->r a) ∗ ▷ A@i:={1}[s] }}} ExecI @ i {{{ RET FailI; PC @@ i ->r a ∗ A@i:={1}[s] }}}.
Proof.
  simpl.
  iIntros (Hmm ϕ) "(>Hpc & >Ha) Hϕ".
  iApply (sswp_lift_atomic_step ExecI);[done|].
  iIntros (σ1) "%Hsche Hσ1".
  inversion Hsche as [ Hcur ]; clear Hsche.
  apply fin_to_nat_inj in Hcur.
  iModIntro.
  iDestruct "Hσ1" as "(? & ? & Hreg & ? & ? & ? & Haccess & ?)".
  iDestruct (gen_reg_valid1 σ1 PC i a Hcur with "Hreg Hpc") as "%Hpc".
  iDestruct (gen_no_access_valid σ1 i (mm_translation a) s Hmm with "Haccess Ha") as "%Hnacc".
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

Lemma eliminate_wrong_token {i j E} :
  j ≠ i ->
  {SS{{ ▷ <<j>> }}} ExecI @ i; E {{{ m, RET m; False }}}.
Proof.
  iIntros (Hne ϕ) ">Htok Hϕ".
  iApply (sswp_lift_atomic_step ExecI) ;[done|].
  iIntros (σ1) "%Hsche Hσ".
  iDestruct "Hσ" as "(Htokown & ? & ? & ? & ? & ? & ? & ?)".
  iDestruct (gen_token_valid_neq j i Hne with "Htok Htokown") as "%Hnsch".
  iExFalso.
  iPureIntro.
  done.
Qed.

