From iris.proofmode Require Import tactics.
From machine_program_logic.program_logic Require Import weakestpre.
From HypVeri.lang Require Import lang.
From HypVeri.algebra Require Import base.
From HypVeri.rules Require Import rules_base nop mov.
From HypVeri.logrel Require Import logrel.
From HypVeri Require Import proofmode.
Import uPred.

(* 
For memory chunks
TODO: move to iris.algebra.big_op 
*)
Section sep_map.
  Context `{Countable K} {A : Type}.
  Context {PROP : bi}.
  Implicit Types m : gmap K A.
  Implicit Types Φ Ψ : K → A → PROP.
  
  Lemma big_sepM_union_acc Φ m m' :
    m' ⊆ m ->
    ([∗ map] k↦y ∈ m, Φ k y) ⊢ ([∗ map] k↦y ∈ m', Φ k y) ∗ (([∗ map] k↦y ∈ m', Φ k y) -∗ [∗ map] k↦y ∈ m, Φ k y).
  Proof.
    iIntros (subseteq) "Hmap".
    pose proof (map_difference_union m' m subseteq) as Hrewrite.
    rewrite <-Hrewrite.
    iDestruct (big_sepM_union with "Hmap") as "[Hmap1 Hmap2]".
    apply map_disjoint_difference_r; auto.
    iSplitL "Hmap1"; first iFrame.
    iIntros "Hmap1".
    iCombine "Hmap1 Hmap2" as "Hmap".
    rewrite <-(big_opM_union _ m' (m ∖ m')).
    done.
    apply map_disjoint_difference_r; auto.
  Qed.
  
End sep_map.

Section fundamental.
  Context `{hypconst:HypervisorConstants}.
  Context `{hypparams:!HypervisorParameters}.
  Context `{vmG: !gen_VMG Σ}.

  (* TODO: separate into helper lemmas *)
  Lemma ftlr (i:VMID) (pgt:page_table) :
    interp_access i pgt ⊢ interp_execute i.
  Proof.
    rewrite /interp_access /=.
    iLöb as "IH". 
    iIntros "((%reg & %Hreg_full & regs) & %Hpgt_full & VMProp) Hnotp VMProp_holds".
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
      destruct (decide (sacc = {[i]})) as [Heqs | Heqs].
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
        rewrite big_opS_delete.
        Unshelve.
        3 : { exact ai. }
        2 : {
          apply elem_of_list_to_set.
          apply tpa_addr_of_page.
          (* apply of_pid_tpa_addr_of_page. *)
        }
        iDestruct "pi_mem" as "((%instr & instrp) & pi_mem)".
        destruct (decode_instruction instr) as [instr'|] eqn:Heqn.
        {
          destruct instr'.
          (* NOP *)
          {            
            iApply (nop ai (w1 := instr) (s := sacc) (q := 1%Qp) with "[PC pi instrp]"); auto.
            rewrite Heqs.
            iFrame.
            iSimpl.            
            iNext.
            iIntros "(PC & instrp & pi) _".
            iAssert ((∃ regs : reg_file, full_reg_map regs ∗ ([∗ map] r↦w ∈ regs, r @@ i ->r w)))%I with "[PC regs]" as "HRegs".
            {
              iCombine "PC regs" as "regs".
              pose proof (big_opM_fn_insert (o := bi_sep) (fun k v _ => (k @@ i ->r v)%I) (fun _ => True) (delete PC reg) PC (ai ^+ 1)%f) as Hrewrite.
              simpl in Hrewrite.
              specialize (Hrewrite True (ltac:(apply lookup_delete))).
              rewrite <-Hrewrite.
              rewrite insert_delete_insert.
              iExists (<[PC := (ai ^+ 1)%f]> reg).
              iFrame.
              unfold full_reg_map.
              iIntros (r).
              iPureIntro.
              specialize (Hreg_full r).
              simpl in Hreg_full.
              destruct Hreg_full as [v' Hreg_full].
              destruct (decide (r = PC)).
              - subst r.
                simplify_map_eq /=.
                done.
              - simplify_map_eq /=.
                exists v'.
                rewrite lookup_insert_Some.
                right.
                split; first done.
                done.                
            }
            iAssert (full_pgt_map pgt ∗ exclusive_access_pages i pgt)%I with "[pi_mem instrp excl_pages pi]" as "[Hpt Hexcl]".
            {              
              pose proof (big_opS_insert (fun x => (∃ w, x ->a w)%I) (list_to_set (addr_of_page (tpa ai)) ∖ {[ai]}) ai) as Hrewrite.
              cbv beta in Hrewrite.
              iAssert (∃ w : Addr, ai ->a w)%I with "[instrp]" as "instrp".
              {
                by iExists instr.                
              }
              iCombine "instrp pi_mem" as "instrp".
              rewrite <-Hrewrite.
              - unfold full_pgt_map.
                iSplit.
                iIntros (p).
                iPureIntro.
                specialize (Hpgt_full p).
                by simpl in Hpgt_full.
                unfold exclusive_access_pages.
                unfold unknown_mem_page.
                pose proof (big_opM_fn_insert (o := bi_sep) (fun k y _ => (⌜{[i]} = y.2⌝ -∗ k -@EA> i ∗ ([∗ list] a ∈ addr_of_page k, ∃ w : Addr, a ->a w))%I) (fun _ => True) (delete (tpa ai) pgt) (tpa ai) (v, sacc)) as Hrewrite'.
                specialize (Hrewrite' True).
                feed specialize Hrewrite'.
                unfold page_table in *.
                apply lookup_delete.
                cbn in Hrewrite'.
                set s := list_to_set (addr_of_page (tpa ai)) : gset Addr.
                assert (({[ai]} ∪ s ∖ {[ai]}) = s) as ->.
                {
                  symmetry.
                  apply union_difference_singleton_L.
                  subst s.
                  apply elem_of_list_to_set.
                  apply tpa_addr_of_page.
                }
                subst s.
                iAssert (⌜{[i]} = sacc⌝ -∗ tpa ai -@EA> i ∗ ([∗ list] a ∈ addr_of_page (tpa ai), ∃ w : Addr, a ->a w))%I with "[pi instrp]" as "H2".
                {
                  iIntros.
                  rewrite Heqs.
                  iFrame.
                  rewrite <-big_opS_list_to_set; last exact HNoDup_ai.
                  iFrame.
                }
                iCombine "H2 excl_pages" as "excl_pages".
                rewrite <-Hrewrite'.
                rewrite insert_delete_insert.
                assert (<[tpa ai := (v, sacc)]> pgt = pgt) as H1.
                {
                  rewrite insert_id; auto.
                }
                rewrite H1.
                iFrame.
              - intros c.
                rewrite ->elem_of_difference in c.
                destruct c as [_ c].
                apply c.
                by apply elem_of_singleton_2.
            }
            iDestruct (VMProp_split with "VMProp") as "[VMProp1 VMProp2]".
            iSpecialize ("IH" with "[HRegs Hpt VMProp1]").
            iFrame.
            iSpecialize ("IH" with "Hnotp").
            iEval (rewrite <-wp_sswp) in "IH".
            iApply "IH".
            set Pred := (X in VMProp i X _).
            iExists Pred.
            iFrame.
            iNext.
            iLeft.
            iFrame.
          }
          {
            (* MOV *)
            destruct src as [imm | srcreg].
            {
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
                (* getting the R *)
                assert (is_Some (delete PC reg !! (R n fin))) as [Rval Hlookup_R].
                {
                  pose proof (Hlookup_R':= (Hreg_full (R n fin))).
                  simpl in Hlookup_R'.
                  destruct Hlookup_R' as [temp Hlookup_R'].
                  exists temp.                
                  rewrite lookup_delete_Some.
                  done.
                }                
                iDestruct (big_sepM_insert_acc _ _ (R n fin) Rval with "regs") as "[R regs]"; auto.
                iApply (mov_word (w3 := Rval) _ imm (R n fin) with "[PC pi instrp R]"); iFrameAutoSolve.
                set_solver.
                iSimpl.            
                iNext.
                iIntros "(PC & instrp & pi & R) _".
                iDestruct ("regs" with "R") as "regs".
                iAssert ((∃ regs : reg_file, full_reg_map regs ∗ ([∗ map] r↦w ∈ regs, r @@ i ->r w)))%I with "[PC regs]" as "HRegs".
                {
                  iCombine "PC regs" as "regs".
                  pose proof (big_opM_fn_insert (o := bi_sep) (fun k v _ => (k @@ i ->r v)%I) (fun _ => True) (<[R n fin := (of_imm imm)]> (delete PC reg)) PC (ai ^+ 1)%f) as Hrewrite.
                  simpl in Hrewrite.
                  specialize (Hrewrite True).
                  feed specialize Hrewrite.
                  rewrite lookup_insert_None; split; [apply lookup_delete | done].
                  rewrite <-Hrewrite.
                  rewrite insert_commute; last done.
                  rewrite insert_delete_insert.
                  iExists (<[R n fin := (of_imm imm)]> (<[PC := (ai ^+ 1)%f]> reg)).
                  iFrame.
                  unfold full_reg_map.
                  iIntros (r).
                  iPureIntro.
                  specialize (Hreg_full r).
                  simpl in Hreg_full.
                  destruct Hreg_full as [v' Hreg_full].
                  destruct (decide (r = PC)).
                  - subst r.
                    simplify_map_eq /=.
                    exists (v' ^+ 1)%f.
                    apply lookup_insert_Some.
                    right.
                    split; first done.
                    apply lookup_insert.
                  - simplify_map_eq /=.
                    destruct (decide (r = R n fin)).
                    + subst r.
                      simplify_map_eq /=.
                      done.
                    + exists v'.
                      rewrite lookup_insert_Some.
                      right.
                      split; first done.
                      apply lookup_insert_Some.
                      right.
                      split; first done.
                      done.
                }
                iAssert (full_pgt_map pgt ∗ exclusive_access_pages i pgt)%I with "[pi_mem instrp excl_pages pi]" as "[Hpt Hexcl]".
                {              
                  pose proof (big_opS_insert (fun x => (∃ w, x ->a w)%I) (list_to_set (addr_of_page (tpa ai)) ∖ {[ai]}) ai) as Hrewrite.
                  cbv beta in Hrewrite.
                  iAssert (∃ w : Addr, ai ->a w)%I with "[instrp]" as "instrp".
                  {
                    by iExists instr.                
                  }
                  iCombine "instrp pi_mem" as "instrp".
                  rewrite <-Hrewrite.
                  - unfold full_pgt_map.
                    iSplit.
                    iIntros (p).
                    iPureIntro.
                    specialize (Hpgt_full p).
                    by simpl in Hpgt_full.
                    unfold exclusive_access_pages.
                    unfold unknown_mem_page.
                    pose proof (big_opM_fn_insert (o := bi_sep) (fun k y _ => (⌜{[i]} = y.2⌝ -∗ k -@EA> i ∗ ([∗ list] a ∈ addr_of_page k, ∃ w : Addr, a ->a w))%I) (fun _ => True) (delete (tpa ai) pgt) (tpa ai) (v, sacc)) as Hrewrite'.
                    specialize (Hrewrite' True).
                    feed specialize Hrewrite'.
                    unfold page_table in *.
                    apply lookup_delete.
                    cbn in Hrewrite'.
                    set s := list_to_set (addr_of_page (tpa ai)) : gset Addr.
                    assert (({[ai]} ∪ s ∖ {[ai]}) = s) as ->.
                    {
                      symmetry.
                      apply union_difference_singleton_L.
                      subst s.
                      apply elem_of_list_to_set.
                      apply tpa_addr_of_page.
                    }
                    subst s.
                    iAssert (⌜{[i]} = sacc⌝ -∗ tpa ai -@EA> i ∗ ([∗ list] a ∈ addr_of_page (tpa ai), ∃ w : Addr, a ->a w))%I with "[pi instrp]" as "H2".
                    {
                      iIntros.
                      iFrame.
                      rewrite <-big_opS_list_to_set; last exact HNoDup_ai.
                      iFrame.
                    }
                    iCombine "H2 excl_pages" as "excl_pages".
                    rewrite <-Hrewrite'.
                    rewrite insert_delete_insert.
                    assert (<[tpa ai := (v, sacc)]> pgt = pgt) as H1.
                    {
                      rewrite insert_id; auto.
                    }
                    rewrite H1.
                    iFrame.
                  - intros c.
                    rewrite ->elem_of_difference in c.
                    destruct c as [_ c].
                    apply c.
                    by apply elem_of_singleton_2.
                }
                iDestruct (VMProp_split with "VMProp") as "[VMProp1 VMProp2]".
                iSpecialize ("IH" with "[HRegs Hpt VMProp1]").
                iFrame.
                iSpecialize ("IH" with "Hnotp").
                iEval (rewrite <-wp_sswp) in "IH".
                iApply "IH".
                set Pred := (X in VMProp i X _).
                iExists Pred.
                iFrame.
                iNext.
                iLeft.
                iFrame.
              }
            }
          admit.
          }
          all: admit.
        }
        {
          iApply (not_valid_instr (s := sacc) (q := 1%Qp) _ ai instr with "[PC pi instrp]"); auto.
          {
            rewrite Heqs.
            iFrame.
          }
          iNext.
          iIntros "? _".
          by iApply wp_terminated.
        }
      }
      {
        (* i has shared access *)
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
      iApply (not_valid_pc with "[PC pi]");
      [exact n|iFrame|].
      iNext;simpl.
      iIntros "? _".
      by iApply wp_terminated.
    }
  Admitted.

End fundamental.
