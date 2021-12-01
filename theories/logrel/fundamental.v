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

  (* Global Instance VMProp_timeless id Q q: Timeless (VMProp id Q q). *)
  (* Proof. rewrite /VMProp. admit.  Admitted. *)

  Lemma ftlr (i:VMID) (pgt:page_table) (regs: reg_file):
    interp_access i pgt regs⊢ interp_execute i.
  Proof.
    rewrite /interp_access /=.
    iIntros "((%Hreg_full & regs) & VMProp) Hnotp VMProp_holds".
    iDestruct (VMProp_holds_agree i with "[VMProp_holds VMProp]") as "[Hres VMProp]".
    { iFrame. }
    iDestruct( later_or with "Hres") as "Hres".
    iDestruct "Hres" as "[Hres| >False]";last done.
    { (* the vm is scheduled *)
      rewrite !later_sep.
      (* we have to do this because VMProp is not(?) timeless *)
      iDestruct "Hres" as "(>R0z & >R1z & VMPropz)".
      (* getting the PC *)
      pose proof (Hlookup_PC:= (Hreg_full PC)).
      simpl in Hlookup_PC.
      destruct Hlookup_PC as [ai Hlookup_PC].
      rewrite (big_opM_delete _ _ PC ai Hlookup_PC).
      iDestruct ("regs") as "[PC regs]".

    }

End fundamental.
