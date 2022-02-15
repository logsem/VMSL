From machine_program_logic.program_logic Require Import weakestpre.
From HypVeri Require Import lifting rules.rules_base.
From HypVeri.algebra Require Import base reg mem pagetable mailbox.
From HypVeri.lang Require Import lang_extra reg_extra current_extra mailbox_extra.
Require Import stdpp.fin.

Section msg_poll.

Context `{hypparams: HypervisorParameters}.
Context `{vmG: !gen_VMG Σ}.
  
Lemma msg_poll_full {E i w1 r0 q s l j r1 r2 p_tx} ai:
  tpa ai ∈ s ->
  tpa ai ≠ p_tx ->
  decode_instruction w1 = Some Hvc ->
  decode_hvc_func r0 = Some Poll ->
  {SS{{ ▷ (PC @@ i ->r ai)
          ∗ ▷ (ai ->a w1)
          ∗ ▷ (TX@ i := p_tx)
          ∗ ▷ (i -@{q}A> s)
          ∗ ▷ (R0 @@ i ->r r0)
          ∗ ▷ (R1 @@ i ->r r1)
          ∗ ▷ (R2 @@ i ->r r2)
          ∗ ▷ (RX_state@ i := Some (l, j))}}}
    ExecI @ i ;E
    {{{ RET (false,ExecI); PC @@ i ->r (ai ^+ 1)%f
                     ∗ ai ->a w1
                     ∗ TX@ i := p_tx
                     ∗ i -@{q}A> s
                     ∗ R0 @@ i ->r (encode_hvc_func Send)
                     ∗ R1 @@ i ->r l
                     ∗ R2 @@ i ->r (encode_vmid j)
                     ∗ RX_state@ i := None}}}.
Proof.
  Admitted.
(*   iIntros (Hdecinstr Hdechvc Haddr Hins ϕ) "(>HPC & >HR0 & >HR1 & >HR2 & >Hai & >Hacc & >Hrx) Hϕ". *)
(*   iApply (sswp_lift_atomic_step ExecI); [done|]. *)
(*   iIntros (σ1) "%Hsche Hσ". *)
(*   inversion Hsche as [ Hcur ]; clear Hsche. *)
(*   apply fin_to_nat_inj in Hcur. *)
(*   iModIntro. *)
(*   iDestruct "Hσ" as "(Htokown & Hmemown & Hregown & Htx & Hrx1 & Hrx2 & Hown & Haccessown & Hrest)". *)
(*   (* valid regs *) *)
(*   iDestruct (gen_reg_valid1 PC i ai Hcur with "Hregown HPC") as "%HPC". *)
(*   iDestruct (gen_reg_valid1 R0 i r0 Hcur with "Hregown HR0") as "%HR0". *)
(*   iDestruct (gen_reg_valid1 R1 i r1 Hcur with "Hregown HR1") as "%HR1". *)
(*   iDestruct (gen_reg_valid1 R2 i r2 Hcur with "Hregown HR2") as "%HR2". *)
(*   (* valid pt *) *)
(*   iDestruct ((gen_access_valid_addr_Set ai s) with "Haccessown Hacc") as %Hacc;eauto. *)
(*   rewrite (to_pid_aligned_in_page _ p); auto. *)
(*   (* valid mem *) *)
(*   iDestruct (gen_mem_valid ai w1 with "Hmemown Hai") as "%Hmem". *)
(*   (* valid rx *) *)
(*   iDestruct (gen_rx_valid_some i l j with "Hrx Hrx2") as %Hrx. *)
(*   iSplit. *)
(*   - (* reducible *) *)
(*     iPureIntro. *)
(*     apply (reducible_normal i Hvc ai w1);eauto. *)
(*   - iModIntro. *)
(*     iIntros (m2 σ2 Hstep). *)
(*     apply (step_ExecI_normal i Hvc ai w1) in Hstep; eauto. *)
(*     remember (exec Hvc σ1) as c2 eqn:Heqc2. *)
(*     rewrite /exec /hvc in Heqc2; eauto. *)
(*     rewrite  HR0 Hdechvc /poll in Heqc2. *)
(*     rewrite /is_rx_ready in Heqc2. *)
(*     rewrite /is_rx_ready_global in Heqc2. *)
(*     rewrite /get_rx_length /get_rx_sender /get_rx_length_global /get_rx_sender_global in Heqc2. *)
(*     destruct (get_vm_mail_box σ1 (get_current_vm σ1)) as [tx rx] eqn:Heqmb. *)
(*     destruct rx as [rxaddr rxstatus] eqn:Heqrx. *)
(*     rewrite Hcur in Heqmb. *)
(*     rewrite (surjective_pairing (get_vm_mail_box σ1 i)) in Heqmb. *)
(*     rewrite (surjective_pairing ((get_vm_mail_box σ1 i).2)) in Heqmb. *)
(*     rewrite Hrx in Heqmb. *)
(*     inversion Heqmb. *)
(*     subst rxstatus. *)
(*     simpl in Heqc2. *)
(*     destruct Hstep as [Hstep1 Hstep2]. *)
(*     simplify_eq. *)
(*     simpl. *)
(*     rewrite /gen_vm_interp /update_incr_PC. *)
(*     rewrite_reg_pc. *)
(*     rewrite /update_reg. *)
(*     do 3 rewrite_reg_global. *)
(*     rewrite /empty_rx. *)
(*     rewrite_empty_rx_global. *)
(*     iFrame "Hrest Htx Hrx1 Hmemown Haccessown Hown Htokown". *)
(*     iDestruct ((gen_reg_update4_global PC (get_current_vm σ1) (ai ^+ 1)%f *)
(*                                        R2 (get_current_vm σ1) (encode_vmid j) *)
(*                                        R1 (get_current_vm σ1) l *)
(*                                        R0 (get_current_vm σ1) (encode_hvc_func Send)) *)
(*                  with "Hregown HPC HR2 HR1 HR0") as ">[Hregown [PC [R2 [R1 R0]]]]"; eauto. *)
(*     rewrite ->(update_offset_PC_update_PC1 _ (get_current_vm σ1) ai 1). *)
(*     rewrite !update_reg_global_update_reg. *)
(*     rewrite empty_rx_global_preserve_regs. *)
(*     iFrame. *)
(*     iDestruct (gen_rx_gmap_update_empty_global_Some (get_current_vm σ1) with "Hrx2 Hrx") as "Hrx'". *)
(*     iMod "Hrx'". *)
(*     iDestruct "Hrx'" as "[? ?]". *)
(*     iModIntro. *)
(*     rewrite empty_rx_global_update_mailbox. *)
(*     iFrame. *)
(*     iApply "Hϕ". *)
(*     by iFrame. *)
(*     exists r0. *)
(*     rewrite empty_rx_global_preserve_regs. *)
(*     apply get_reg_gmap_get_reg_Some; auto. *)
(*     exists r1. *)
(*     rewrite lookup_insert_ne; [|done]. *)
(*     rewrite empty_rx_global_preserve_regs. *)
(*     apply get_reg_gmap_get_reg_Some; auto. *)
(*     exists r0. *)
(*     rewrite empty_rx_global_preserve_regs. *)
(*     apply get_reg_gmap_get_reg_Some; auto. *)
(*     exists r2. *)
(*     do 2 (rewrite lookup_insert_ne; [|done]). *)
(*     rewrite empty_rx_global_preserve_regs.     *)
(*     apply get_reg_gmap_get_reg_Some; auto. *)
(*     exists r0. *)
(*     rewrite empty_rx_global_preserve_regs. *)
(*     apply get_reg_gmap_get_reg_Some; auto. *)
(*     exists r1. *)
(*     rewrite lookup_insert_ne; [|done]. *)
(*     rewrite empty_rx_global_preserve_regs. *)
(*     apply get_reg_gmap_get_reg_Some; auto. *)
(*     exists r0. *)
(*     rewrite empty_rx_global_preserve_regs. *)
(*     apply get_reg_gmap_get_reg_Some; auto. *)
(*     by rewrite !update_reg_global_preserve_current_vm empty_rx_global_preserve_current_vm. *)
(*     rewrite !update_reg_global_update_reg empty_rx_global_preserve_regs;try solve_reg_lookup. *)
(*     do 3 (rewrite lookup_insert_ne; [|done]). *)
(*     apply get_reg_gmap_get_reg_Some; auto. *)
(*     exists r1. *)
(*     rewrite lookup_insert_ne. *)
(*     solve_reg_lookup. *)
(*     done. *)
(*     exists r2. *)
(*     do 2 (rewrite lookup_insert_ne; [|done]). *)
(*     solve_reg_lookup. *)
(*     exists r1. *)
(*     rewrite lookup_insert_ne; [|done]. *)
(*     solve_reg_lookup. *)
(* Qed. *)

Lemma msg_poll_empty {E i w1 r0 q s r2 p_tx} ai:
  tpa ai ∈ s ->
  tpa ai ≠ p_tx ->
  decode_instruction w1 = Some Hvc ->
  decode_hvc_func r0 = Some Poll ->
  {SS{{ ▷ (PC @@ i ->r ai)
          ∗ ▷ (ai ->a w1)
          ∗ ▷ (TX@ i := p_tx)
          ∗ ▷ (i -@{q}A> s)
          ∗ ▷ (R0 @@ i ->r r0)
          ∗ ▷ (R2 @@ i ->r r2)
          ∗ ▷ (RX_state@ i := None)}}}
    ExecI @ i ;E
    {{{ RET (false,ExecI); PC @@ i ->r (ai ^+ 1)%f
                     ∗ ai ->a w1
                     ∗ TX@ i := p_tx
                     ∗ i -@{q}A> s
                     ∗ R0 @@ i ->r (encode_hvc_ret_code Error)
                     ∗ R2 @@ i ->r (encode_hvc_error Denied)
                     ∗ RX_state@ i := None}}}.
Proof.
  Admitted.

End msg_poll.
