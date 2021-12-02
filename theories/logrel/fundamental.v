From iris.proofmode Require Import tactics.
From machine_program_logic.program_logic Require Import weakestpre.
From HypVeri.lang Require Import lang.
From HypVeri.algebra Require Import base.
From HypVeri.rules Require Import rules_base.
From HypVeri.logrel Require Import logrel.
Import uPred.

Section fundamental.
  Context `{hypconst:HypervisorConstants}.
  Context `{hypparams:!HypervisorParameters}.
  Context `{vmG: !gen_VMG Σ}.

  Lemma ftlr (i:VMID) (pgt:page_table) (regs: reg_file):
    interp_access i pgt regs ⊢ interp_execute i.
  Proof.
    rewrite /interp_access /=.
    iIntros "((%Hreg_full & regs) & %Hpgt_full & VMProp) Hnotp VMProp_holds".
    iDestruct (VMProp_holds_agree i with "[VMProp_holds VMProp]") as "[Hres VMProp]".
    { iFrame. }
    iDestruct( later_or with "Hres") as "Hres".
    iDestruct "Hres" as "[Hres| >False]";last done.
    (* the vm is scheduled *)
    rewrite !later_sep.
    (* we have to do this because VMProp is not(?) timeless *)
    iDestruct "Hres" as "(>R0z & >R1z & (VMPropz & >excl_pages & >shared_pages))".
    (* getting the PC *)
    pose proof (Hlookup_PC:= (Hreg_full PC)).
    simpl in Hlookup_PC.
    destruct Hlookup_PC as [ai Hlookup_PC].
    rewrite (big_opM_delete _ _ PC ai Hlookup_PC).
    iDestruct ("regs") as "[PC regs]".
    (* getting sacc from pgt *)
    pose proof (Hpgt_full (to_pid_aligned ai)) as Hlookup_ai.
    simpl in Hlookup_ai.
    destruct Hlookup_ai as [[? sacc] Hlookup_ai].
    (* sswp *)
    rewrite wp_sswp.
    destruct (decide (i ∈ sacc)).
    {
      (* i has access *)
      destruct (decide (sacc = {[i]})).
      { (* i has exclusive access *)
        iEval(rewrite /exclusive_access_pages) in "excl_pages".
        rewrite (big_opM_delete _ _ (to_pid_aligned ai) _ Hlookup_ai).
        iDestruct ("excl_pages") as "[pi excl_pages]".
        simpl.
        iDestruct ("pi" with "[]") as "[pi pi_mem]";first done.
        rewrite /unknown_mem_page.
        pose proof (in_page_to_pid_aligned ai) as Hinpage_ai.
        pose proof (addr_of_page_NoDup (tpa ai)) as HNoDup_ai.
        rewrite -big_opS_list_to_set; last exact HNoDup_ai.
        admit.
      }
      {
        (* i has shared access *)
      admit.
      }
    }
    { (* i doesn't have access *)
      iClear "VMProp VMPropz".
      rewrite /shared_or_noaccess_pages.
      rewrite (big_opM_delete _ _ (to_pid_aligned ai) _ Hlookup_ai).
      iDestruct ("shared_pages") as "[[pi _] shared_pages]".
      simpl.
      iDestruct ("pi" with "[]") as "pi"; first done.
      iApply (not_valid_pc with "[PC pi]");
      [exact n|iFrame|].
      iNext;simpl.
      iIntros "? _".
      by iApply wp_terminated.
    }
Admitted.

End fundamental.
