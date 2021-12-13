From iris.proofmode Require Import tactics.
From machine_program_logic.program_logic Require Import weakestpre.
From HypVeri.lang Require Import lang.
From HypVeri.algebra Require Import base.
From HypVeri.rules Require Import rules_base nop mov ldr str.
From HypVeri.logrel Require Import logrel logrel_extra.
From HypVeri Require Import proofmode.
Import uPred.

Section fundamental.
  Context `{hypconst:HypervisorConstants}.
  Context `{hypparams:!HypervisorParameters}.
  Context `{vmG: !gen_VMG Σ}.


  (* TODO:
   - [x] fix iIntros
   - [] fix pgt accessor
   - [x] new lemmas for updating VMProp (not necessary)
   - [x] fix nop
   - [x] fix mov
   - [] str
   - [] ldr *)

  (* TODO: separate into helper lemmas *)
  Lemma ftlr (i:VMID)  :
   ∀ pgt, interp_access i pgt ⊢ interp_execute i.
  Proof.
    rewrite /interp_access /=.
    iLöb as "IH".
    iIntros (pgt) "(%regs & (#Htotal_regs & regs) & rx & tx & VMProp) Hnotp VMProp_holds".
    iDestruct (VMProp_holds_agree i with "[$VMProp_holds $VMProp]") as "[Hres VMProp]".
    iDestruct( later_exist with "Hres") as (mem) "Hres".
    iDestruct (later_or with "Hres") as "Hres".
    iDestruct "Hres" as "[Hres| >False]";last done.
    (* the vm is scheduled *)
    rewrite !later_sep.
    (* we have to do this because VMProp is not(?) timeless *)
    iDestruct "Hres" as "(>#Htotal_pgt & >#Htotal_mem & >R0z & >R1z & (VMPropz & >excl_pages & >shared_pages & >mem & >rx_status))".
    (* we don't really need to get the resource of PC, but just the value *)
    iPoseProof ("Htotal_regs" $! PC) as "%Hlookup_PC".
    destruct Hlookup_PC as [ai Hlookup_PC].
    (* getting sacc from pgt *)
    iPoseProof ("Htotal_pgt" $! (to_pid_aligned ai)) as "%Hlookup_ai".
    destruct Hlookup_ai as [[? sacc] Hlookup_ai].
    (* sswp *)
    rewrite ->wp_sswp.
    destruct (decide (i ∈ sacc)).
    { (* i has access *)
      destruct (decide (sacc = {[i]})) as [->Heqs | Heqs].
      { (* i has exclusive access *)
        iEval(rewrite /exclusive_access_pages) in "excl_pages".
        iPoseProof ("Htotal_mem" $! ai) as "[%instr %Hlookup_instr]".
        destruct (decode_instruction instr) as [instr'|] eqn:Heqn.
        { (* valid instruction *)
          destruct instr'.
          { (* NOP *)
            (* getting the PC *)
            iDestruct (reg_big_sepM_split_upd regs i Hlookup_PC with "[$Htotal_regs $regs]")
              as "[PC Hacc_regs]".
            (* getting pgt *)
            (* we don't update pagetable *)
            iDestruct (pgt_big_sepM_split pgt Hlookup_ai with "[$excl_pages]")
                       as "[pi Hacc_pgt]".
            iDestruct ("pi" with "[]") as "pi";first done.
            (* getting mem *)
            rewrite /accessible_memory.
            (* we don't update memory *)
            iDestruct (mem_big_sepM_split mem Hlookup_instr with "[$mem]")
                      as "[instrm Hacc_mem]".
            iDestruct ("instrm" with "[]") as "instrm".
            { iPureIntro. exists (v,{[i]}).  split;first done. simpl;set_solver +. }
            iApply (nop ai (w1 := instr) (s := {[i]}) (q := 1%Qp) with "[PC pi instrm]"); iFrameAutoSolve.
            iNext.
            iIntros "(PC & instrm & pi) _".
            iDestruct ("Hacc_regs" $! (ai ^+ 1)%f with "PC") as "[#Htotal_regs' regs]".
            iDestruct ("Hacc_mem" with "[instrm]") as "mem".
            { iIntros "_". iFrame "instrm". }
            iDestruct ("Hacc_pgt" with "[pi]") as "pgt".
            { iIntros "_". iFrame "pi". }
            (* NOTE: accessor doesn't work on pagetable, since we could update it. need to extend interp_access *)
            iDestruct (VMProp_split with "VMProp") as "[VMProp1 VMProp2]".
            iSpecialize ("IH" $! pgt with "[regs $rx $tx VMProp1]").
            iExists (<[PC:= (ai ^+ 1)%f]> regs).
            iFrame.
            iFrame "Htotal_regs'".
            iSpecialize ("IH" with "Hnotp").
            iApply "IH".
            set Pred := (X in VMProp i X _).
            iExists Pred.
            iFrame.
            iNext.
            iExists mem.
            iLeft.
            iFrame.
            iFrame "#".
          }
          { (* MOV *)
            destruct src as [imm | srcreg].
            { (* mov imm *)
              destruct dst.
              {
                apply decode_instruction_valid in Heqn.
                inversion Heqn.
                unfold reg_valid_cond in *.
                exfalso.
                naive_solver.
              }
              {
                apply decode_instruction_valid in Heqn.
                inversion Heqn.
                unfold reg_valid_cond in *.
                exfalso.
                naive_solver.
              }
              {
                iPoseProof ("Htotal_regs" $! (R n fin)) as (w) "%Hlookup_R".
                (* getting regs *)
                iDestruct ((reg_big_sepM_split_upd2 regs i _ Hlookup_PC Hlookup_R)
                            with "[$Htotal_regs $regs]") as "(PC & R & Hacc_regs)".
                (* getting mem *)
                rewrite /accessible_memory.
                (* we don't update memory *)
                iDestruct (mem_big_sepM_split mem Hlookup_instr with "[$mem]")
                  as "[instrm Hacc_mem]".
                iDestruct ("instrm" with "[]") as "instrm".
                { iPureIntro. exists (v,{[i]}).  split;first done. simpl;set_solver +. }
                (* getting pgt *)
                (* we don't update pagetable *)
                iDestruct (pgt_big_sepM_split pgt Hlookup_ai with "[$excl_pages]")
                  as "[pi Hacc_pgt]".
                iDestruct ("pi" with "[]") as "pi";first done.
                iApply (mov_word (w3 := w) _ imm (R n fin) with "[PC pi instrm R]"); iFrameAutoSolve.
                iNext.
                iIntros "(PC & instrm & pi & R) _".
                iDestruct ("Hacc_regs" with "[$PC $R]") as (regs') "[#Htotal_regs' regs]";iFrame.
                iDestruct ("Hacc_mem" with "[instrm]") as "mem".
                { iIntros "_". iFrame "instrm". }
                iDestruct ("Hacc_pgt" with "[pi]") as "pgt".
                { iIntros "_". iFrame "pi". }
                iDestruct (VMProp_split with "VMProp") as "[VMProp1 VMProp2]".
                iSpecialize ("IH" $! pgt with "[regs Htotal_regs' rx tx VMProp1]").
                iExists regs'.
                iFrame.
                iFrame "#".
                iSpecialize ("IH" with "Hnotp").
                iApply "IH".
                set Pred := (X in VMProp i X _).
                iExists Pred.
                iFrame.
                iNext.
                iExists mem.
                iLeft.
                iFrame.
                iFrame "#".
              }
            }
            { (* mov reg *)
              admit.
            }
          }
          {(* ldr *)
            pose proof Heqn as Hdecode.
            apply decode_instruction_valid in Heqn.
            inversion Heqn as [| | ? ? Hvalid_dst Hvalid_src Hvalid_neq | | | | | | | | | ].
            subst dst0 src0.
            unfold reg_valid_cond in Hvalid_dst, Hvalid_src.
            iPoseProof ("Htotal_regs" $! src) as (src_a) "%Hlookup_src".
            iPoseProof ("Htotal_regs" $! dst) as (dst_w) "%Hlookup_dst".
            iPoseProof ("Htotal_pgt" $! (tpa src_a)) as (src_perm) "%Hlookup_src_a".
            iDestruct "tx" as (tx_p) "tx".
            (* case analysis on src  *)
            destruct (decide (i ∈ src_perm.2)).
            { (* access to the page, more cases.. *)
              admit.
            }
            { (* no access to the page, apply ldr_error *)
               iDestruct ((reg_big_sepM_split_upd3 regs i _ _ _ Hlookup_PC Hlookup_src Hlookup_dst)
                            with "[$Htotal_regs $regs]") as "(PC & r_src & r_dst & Hacc_regs)".
              (* getting mem *)
               rewrite /accessible_memory.
               (* we don't update memory *)
               iDestruct (mem_big_sepM_split mem Hlookup_instr with "[$mem]")
                 as "[instrm Hacc_mem]".
               iDestruct ("instrm" with "[]") as "a_instr".
               { iPureIntro. exists (v,{[i]}).  split;first done. simpl;set_solver +. }
               (* getting pgt *)
               (* we don't update pagetable *)
               iDestruct (pgt_big_sepM_split pgt Hlookup_ai  with "[$excl_pages]")
                 as "(p_instr & Hacc_excl_pgt)".
               iDestruct ("p_instr" with "[]") as "p_instr";first done.
               iDestruct (pgt_big_sepM_split pgt Hlookup_src_a  with "[$shared_pages]")
                 as "([p_src _] & Hacc__shared_pgt)".
               iDestruct ("p_src" with "[]") as "p_src";first done.
               iApply (ldr_error ai src_a dst src with "[PC p_instr a_instr r_src r_dst tx p_src]"); iFrameAutoSolve.
               { left;done. }
               iNext.
               iIntros "(tx & PC & a_instr & r_src & p_src & r_dst) _".
               by iApply wp_terminated.
            }

            admit.
          }
          {(* str *)
            admit.
          }
          all: admit.
        }
        { (*invalid instruction *)
          iDestruct (reg_big_sepM_split regs i Hlookup_PC with "[$regs]") as "[PC _]".
           (* getting pgt *)
          (* we don't update pagetable *)
          iDestruct (pgt_big_sepM_split pgt Hlookup_ai with "[$excl_pages]")
            as "[pi Hacc_pgt]".
          iDestruct ("pi" with "[]") as "pi";first done.
          (* getting mem *)
          rewrite /accessible_memory.
          (* we don't update memory *)
          iDestruct (mem_big_sepM_split mem Hlookup_instr with "[$mem]")
            as "[instrm Hacc_mem]".
          iDestruct ("instrm" with "[]") as "instrm".
          { iPureIntro. exists (v,{[i]}).  split;first done. simpl;set_solver +. }
          iApply (not_valid_instr (s := {[i]}) (q := 1%Qp) _ ai instr with "[PC pi instrm]"); iFrameAutoSolve.
          iNext.
          iIntros "? _".
          by iApply wp_terminated.
        }
      }
      { (* i has shared access *)
      admit.
      }
    }
    { (* i doesn't have access *)
      iClear "VMProp VMPropz".
      rewrite /shared_or_noaccess_pages.
      iEval (rewrite (big_opM_delete _ _ (to_pid_aligned ai) _ Hlookup_ai)) in "shared_pages".
      iDestruct ("shared_pages") as "[[pi _] shared_pages]".
      simpl.
      iDestruct ("pi" with "[]") as "pi"; first done.
      iDestruct (reg_big_sepM_split regs i Hlookup_PC with "[$regs]") as "[PC _]".
      iApply (not_valid_pc with "[PC pi]");
      [exact n|iFrame|].
      iNext;simpl.
      iIntros "? _".
      by iApply wp_terminated.
    }
  Admitted.

End fundamental.
