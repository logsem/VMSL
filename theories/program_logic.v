From machine_program_logic.program_logic Require Import machine weakestpre.
From HypVeri Require Export lang RAs.
From iris.proofmode Require Import tactics.
Require Import iris.base_logic.lib.ghost_map.
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
  PC ≠ ra ->
  NZ ≠ ra ->
  PC @@ i ->r a ∗ a ->a w1 ∗ A@i:={q} (mm_translation a) ∗ ra @@ i ->r w3
    ⊢ SSWP ExecI @ i {{ (λ m, ⌜m = ExecI ⌝ (* TODO : PC @@ i ->r a+1, need a helper function... *)∗ a ->a w1 ∗ A@i:={q} (mm_translation a) ∗ ra @@ i ->r w2) }}%I.

Proof.
  iIntros (Hdecode HneqPC HneqNZ) "(Hpc & Hapc & Hacc & Hra)".
  iApply (sswp_lift_atomic_step ExecI);[done|].
  iIntros (σ1) "%Hsche Hσ".
  inversion Hsche as [ Hcur ]; clear Hsche.
  apply fin_to_nat_inj in Hcur.
  iModIntro.
  iDestruct "Hσ" as "(H1 & Hmem & Hreg & ? & ? & ? & Haccess & H2)".
  iDestruct ((gen_reg_valid_Sep σ1 (get_current_vm σ1) (<[(PC,i):=a]>{[(ra,i):=w3]}))
               with "Hreg [Hpc Hra]") as "%Hreg".
  done.
  iApply (big_sepM_delete _ _ (PC,i) a).
  simplify_map_eq.
  done.
  iFrame.
  iApply (big_sepM_delete _ _ (ra,i) w3).
  simplify_map_eq.
  apply lookup_delete_Some.
  split.
  intros P; inversion P; contradiction.
  rewrite lookup_insert_Some.
  right.
  split.
  intros P; inversion P; contradiction.
  simplify_map_eq; done.
  iFrame.
  rewrite delete_insert.
  rewrite delete_insert; auto using lookup_empty.
  apply lookup_insert_None; split; auto using lookup_empty.
  intros P; by inversion P.
  iDestruct (gen_access_valid σ1 i q (mm_translation a) with "Haccess Hacc") as %Hacc .
  assert (HPC : get_reg σ1 PC = Some a).
  {
    by apply (Hreg (PC, i) a (lookup_insert _ (PC, i) a)).
  }
  assert (Hra : get_reg σ1 ra = Some w3).
  {
    apply (Hreg (ra, i) w3).
    rewrite lookup_insert_Some.
    right.
    split.
    intros P; inversion P; contradiction.
    by apply (lookup_insert _ (ra, i) w3).
    done.
  }
  assert (Haccess: (check_access_addr σ1 i a) = true).
  {
    by unfold check_access_addr.
  }
  iDestruct (gen_mem_valid σ1 a w1 with "Hmem Hapc") as "%Hmem".
  iSplit.
  iPureIntro.
  remember (exec (Mov ra (inl w2)) σ1) as ex.
  exists ex.1, ex.2.
  unfold prim_step.
  apply step_exec_normal with a w1 (Mov ra (inl w2)).
  - rewrite /is_valid_PC HPC /=.
    subst i.
    by rewrite Haccess.
  - by apply (Hreg (PC, i) a (lookup_insert _ (PC, i) a)).
  - unfold get_memory.
    subst i.
    by rewrite Haccess.
  - done.
  - by symmetry.
  - iModIntro.
    iIntros (m2 σ2) "%HstepP".
    iModIntro.
    inversion HstepP as
        [ σ1' Hnotvalid
        | σ1'  ? ? ? ? Hvalid Hreg2 Hmem2 Hdecode2 Hexec Hcontrol];
      simplify_eq /=;[| remember (get_current_vm σ1) as i eqn: Heqi].
    + (*Fail*)
      rewrite /is_valid_PC /= in Hnotvalid.
      by rewrite -> HPC ,Haccess in Hnotvalid.
    + (* Normal. *)
      (* eliminate Hmem2 *)
      rewrite /get_memory -Heqi Haccess /get_memory_unsafe Hmem in Hmem2 .
      inversion Hmem2;subst; clear Hmem2.
      (* eliminate Hdecode2 *)
      rewrite Hdecode in Hdecode2;inversion Hdecode2;subst; clear Hdecode2.
      remember (exec (Mov ra (inl w2)) σ1) as c2 eqn:Heqc2.
      destruct ra eqn:Heqra;[contradiction|contradiction| rewrite <- Heqra].
      rewrite /gen_vm_interp.
      (* eliminate option_state_unpack *)
      rewrite /exec /mov_word /update_incr_PC in Heqc2.
      rewrite <- (option_state_unpack_preserve_state_Some
                  σ1 (update_offset_PC (update_reg σ1 (R n fin) w2) true 1)) in Heqc2;[|done].
      rewrite /update_reg in Heqc2.
      simplify_eq /=.
      (* unchanged part *)
      rewrite -> update_offset_PC_preserve_mem , -> update_reg_global_preserve_mem.
      rewrite -> update_offset_PC_preserve_tx , -> update_reg_global_preserve_tx.
      rewrite -> update_offset_PC_preserve_rx , -> update_reg_global_preserve_rx.
      rewrite -> update_offset_PC_preserve_owned , -> update_reg_global_preserve_owned.
      rewrite -> update_offset_PC_preserve_access , -> update_reg_global_preserve_access.
      rewrite -> update_offset_PC_preserve_trans , -> update_reg_global_preserve_trans.
      rewrite -> update_offset_PC_preserve_receivers , -> update_reg_global_preserve_receivers.
      iFrame.
      (* TODO : almost done! the last step is to update PC and ra*)
      Admitted.
