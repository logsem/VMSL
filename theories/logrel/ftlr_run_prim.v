From iris.proofmode Require Import tactics.
From machine_program_logic.program_logic Require Import weakestpre.
From HypVeri.lang Require Import lang trans_extra.
From HypVeri.algebra Require Import base pagetable mem trans mailbox.
From HypVeri.rules Require Import run.
From HypVeri.logrel Require Import logrel_prim logrel_prim_extra.
From HypVeri Require Import stdpp_extra proofmode.
Import uPred.

Section ftlr_run_prim.
  Context `{hypconst:HypervisorConstants}.
  Context `{hypparams:!HypervisorParameters}.
  Context `{vmG: !gen_VMG Σ}.

Lemma ftlr_run_prim {Φ_t Φ_r mem_acc_tx ai regs rxs ps_acc p_tx p_rx instr trans r0}:
  let i := V0 in
  base_extra.is_total_gmap regs ->
  base_extra.is_total_gmap rxs ->
  {[p_tx; p_rx]} ⊆ ps_acc ->
  currently_accessible_in_trans_memory_pages i trans ⊆ ps_acc ∖ {[p_tx; p_rx]} ->
  p_rx ∉ ps_acc ∖ {[p_rx; p_tx]} ∪ accessible_in_trans_memory_pages i trans ->
  p_tx ∉ ps_acc ∖ {[p_rx; p_tx]} ∪ accessible_in_trans_memory_pages i trans ->
  regs !! PC = Some ai ->
  tpa ai ∈ ps_acc ->
  tpa ai ≠ p_tx ->
  dom (gset Addr) mem_acc_tx = set_of_addr (ps_acc ∖ {[p_tx]}) ->
  tpa ai ∈ ps_acc ∖ {[p_tx]} ->
  mem_acc_tx !! ai = Some instr ->
  decode_instruction instr = Some Hvc ->
  regs !! R0 = Some r0 ->
  decode_hvc_func r0 = Some Run ->
  p_tx ≠ p_rx ->
  SliceTransWf Φ_t ->
  SliceRxsWf Φ_r ->
  (∀ (i0 j : VMID) (trans0 : gmap Addr transaction), i0 = V0 ∨ j = V0 → Φ_t trans0 i0 j ⊣⊢ slice_transfer_all trans0 i0 j) ->
  (∀ (i0 : VMID) (os : option (Addr * VMID)), match os with
                                                    | Some (_, j) => j = V0
                                                    | None => True
                                                    end → Φ_r i0 os i0 ⊣⊢ slice_rx_state i0 os) ->
  (∀ (i0 : VMID) (os : option (Addr * VMID)), match os with
                                                    | Some (_, k) => k = V0
                                                    | None => True
                                                    end → Φ_r i0 os i0 ⊣⊢ Φ_r i0 os V0) ->
  (∀ (i0 j : VMID) (os : option (Addr * VMID)), match os with
                                                      | Some (_, j0) => j0 = V0
                                                      | None => True
                                                      end → j ≠ i0 → j ≠ V0 → Φ_r i0 os j ⊣⊢ True) ->
  (∀ i0 : option (Addr * VMID), Φ_r V0 i0 V0 ⊣⊢ slice_rx_state V0 i0) ->
  ⊢ ▷ (∀ (a : gmap reg_name Addr) (a0 : gset PID) (a1 : gmap Addr transaction) (a2 : gmap VMID (option (Addr * VMID))),
              ⌜base_extra.is_total_gmap a2⌝ -∗
              ⌜base_extra.is_total_gmap a⌝ -∗
              ⌜{[p_tx; p_rx]} ⊆ a0⌝ -∗
              ⌜currently_accessible_in_trans_memory_pages i a1 ⊆ a0 ∖ {[p_tx; p_rx]}⌝ -∗
              ⌜p_rx ∉ a0 ∖ {[p_rx; p_tx]} ∪ accessible_in_trans_memory_pages i a1⌝ -∗
              ⌜p_tx ∉ a0 ∖ {[p_rx; p_tx]} ∪ accessible_in_trans_memory_pages i a1⌝ -∗
              ([∗ map] r↦w ∈ a, r @@ i ->r w) -∗
              TX@i:=p_tx -∗
              p_tx -@O> - ∗ p_tx -@E> true -∗
              mailbox.rx_page i p_rx -∗
              i -@A> a0 -∗
              pagetable_entries_excl_owned i (a0 ∖ {[p_rx; p_tx]} ∖ currently_accessible_in_trans_memory_pages i a1) -∗
              transaction_hpool_global_transferred a1 -∗
              transaction_pagetable_entries_transferred i a1 -∗
              retrievable_transaction_transferred i a1 -∗
              rx_state_get i a2 -∗
              rx_states_global (delete i a2) -∗
              transaction_pagetable_entries_owned i a1 -∗
              retrieved_transaction_owned i a1 -∗
              (∃ mem : lang.mem, memory_pages (a0 ∪ (accessible_in_trans_memory_pages i a1)) mem) -∗
              ((∃ P0 : iProp Σ, VMProp i P0 1) ∗ ([∗ set] y ∈ (set_of_vmids ∖ {[i]}), ▷ VMProp (y:VMID) (vmprop_unknown y Φ_t Φ_r) (1 / 2)) ∗
               ▷ (big_sepSS_except set_of_vmids i (Φ_t a1) ∗ rx_states_transferred Φ_r (delete i a2))) -∗
              WP ExecI @ i {{ _, True }}) -∗
   ([∗ map] r↦w ∈ regs, r @@ i ->r w) -∗
   TX@i:=p_tx -∗
   p_tx -@O> - ∗ p_tx -@E> true -∗
   i -@A> ps_acc -∗
   pagetable_entries_excl_owned i (ps_acc ∖ {[p_rx; p_tx]} ∖ (currently_accessible_in_trans_memory_pages i trans)) -∗
   transaction_hpool_global_transferred trans -∗
   transaction_pagetable_entries_transferred i trans -∗
   retrievable_transaction_transferred i trans -∗
   rx_state_get i rxs -∗
   mailbox.rx_page i p_rx -∗
   rx_states_global (delete i rxs) -∗
   transaction_pagetable_entries_owned i trans -∗
   retrieved_transaction_owned i trans -∗
   (∃ mem1 : mem, memory_pages ((ps_acc ∪ (accessible_in_trans_memory_pages i trans)) ∖ ps_acc) mem1) -∗
   ([∗ map] k↦v ∈ mem_acc_tx, k ->a v) -∗
   (∃ mem2 : mem, memory_page p_tx mem2) -∗
   ((∃ P0 : iProp Σ, VMProp i P0 1) ∗ ([∗ set] y ∈ (set_of_vmids ∖ {[i]}), ▷ VMProp (y:VMID) (vmprop_unknown y Φ_t Φ_r) (1 / 2)) ∗
               ▷ (big_sepSS_except set_of_vmids i (Φ_t trans) ∗ rx_states_transferred Φ_r (delete i rxs))) -∗
   SSWP ExecI @ i {{ bm, (if bm.1 then VMProp_holds i (1 / 2) else True) -∗ WP bm.2 @ i {{ _, True }} }}.
Proof.
  iIntros (i Htotal_regs Htotal_rxs Hsubset_mb Hsubset_acc Hnin_rx Hnin_tx Hlookup_PC Hin_ps_acc Hneq_ptx Hdom_mem_acc_tx Hin_ps_acc_tx
             Hlookup_mem_ai Hdecode_instr Hlookup_reg_R0).
  iIntros (Hdecode_hvc Hneq_mb SliceTransWf0 SliceRxsWf0 HΦt HΦr1 HΦr2 HΦr3 HΦr4) "IH regs tx pgt_tx pgt_acc pgt_owned trans_hpool_global tran_pgt_transferred retri rx_state rx rxs_global tran_pgt_owned
                 retri_owned mem_rest mem_acc_tx mem_tx Running".
  pose proof (Htotal_regs R1) as [r1 Hlookup_reg_R1].
  destruct (decode_vmid r1) as [v |] eqn:Hdecode_r1.
  {
    destruct (decide (v = V0)).
    { (* run_primary *)
      iDestruct (reg_big_sepM_split_upd3 i Hlookup_PC Hlookup_reg_R0 Hlookup_reg_R1 with "[$regs]")
        as "(PC & R0 & R1 & Hacc_regs)";eauto.
      iDestruct (mem_big_sepM_split mem_acc_tx Hlookup_mem_ai with "mem_acc_tx") as "[mem_instr Hacc_mem_acc]".

      iApply (run_primary ai with "[PC R0 R1 pgt_acc tx mem_instr]"); iFrameAutoSolve.
      subst v. done.
      iNext. iIntros "(PC & mem_instr & pgt_acc & tx & R0 & R1) _".
      iDestruct ("Hacc_regs" $! (ai ^+ 1)%f _ _ with "[$PC $R0 $R1]") as "[%regs' [%Htotal_regs' regs]]".
      iDestruct ("Hacc_mem_acc" with "[$mem_instr]") as "mem_acc_tx".
      iApply ("IH" $! regs' ps_acc trans rxs Htotal_rxs Htotal_regs' Hsubset_mb Hsubset_acc Hnin_rx Hnin_tx with
               "regs tx pgt_tx rx pgt_acc pgt_owned  trans_hpool_global tran_pgt_transferred retri rx_state rxs_global
                              tran_pgt_owned retri_owned [mem_rest mem_acc_tx mem_tx] [Running]").
      {
        iDestruct (memory_pages_split_singleton' p_tx ps_acc with "[mem_acc_tx $mem_tx]") as "mem_acc". set_solver + Hsubset_mb.
        iExists mem_acc_tx;by iFrame "mem_acc_tx".
        iApply (memory_pages_split_diff' _ ps_acc with "[$mem_rest $mem_acc]").
        set_solver +.
      }
      { iDestruct "Running" as "($&?&$&$)". rewrite <-big_sepS_later. iFrame. }
    }
    {
      pose proof (Htotal_regs R2) as [r2 Hlookup_reg_R2].
      iDestruct (reg_big_sepM_split_upd4 i Hlookup_PC Hlookup_reg_R0 Hlookup_reg_R1 Hlookup_reg_R2 with "[$regs]")
        as "(PC & R0 & R1 & R2 & Hacc_regs)";eauto.
      pose proof (union_split_difference_intersection_L (ps_acc∖ {[p_tx]}) ({[p_rx]} ∪ (transferred_memory_pages i trans)))
        as [Heq_ps_acc_tx Hdisj_ps_acc_tx].
      rewrite Heq_ps_acc_tx in Hdom_mem_acc_tx.
      rewrite set_of_addr_union in Hdom_mem_acc_tx;last auto.
      apply dom_union_inv_L in Hdom_mem_acc_tx;last apply set_of_addr_disj;auto.
      destruct Hdom_mem_acc_tx as (mem_oea & mem_inters & Heq_mem_acc_tx' & Hdisj_mem_oea_inters & Hdom_mem_oea & Hdom_mem_inters).
      rewrite Heq_mem_acc_tx'.
      iDestruct (big_sepM_union with "mem_acc_tx") as "[mem_oea mem_inters]";auto.

      iDestruct (get_trans_ps_disj with "trans_hpool_global") as %Htrans_disj.
      iDestruct (get_trans_neq with "trans_hpool_global") as %Htrans_neq.

      (* for simplication *)
      set ps_mem_in_trans := accessible_in_trans_memory_pages i trans.
      assert (Heq_inter_diff_union: (ps_acc ∖ {[p_tx]}) ∩ ({[p_rx]} ∪ (transferred_memory_pages i trans)) ∪
                                      ((ps_acc ∪ (ps_mem_in_trans)) ∖ ps_acc)
                                    = {[p_rx]} ∪ (transferred_memory_pages i trans)).
      {
        assert ((ps_acc ∪ ps_mem_in_trans) ∖ ps_acc = ps_mem_in_trans ∖ (ps_acc∖ {[p_tx]})) as ->.
        {
          assert ((ps_acc ∪ ps_mem_in_trans) ∖ ps_acc = ps_mem_in_trans ∖ ps_acc) as ->.
          set_solver +.
          set_solver + Hnin_tx.
        }
        rewrite intersection_union_l_L.
        rewrite -union_assoc_L.
        rewrite intersection_comm_L.
        rewrite subseteq_intersection_1_L.
        2: { apply subseteq_difference_r. set_solver. set_solver + Hsubset_mb. }
        pose proof (union_split_difference_intersection_L (transferred_memory_pages i trans) (ps_acc∖ {[p_tx]})) as [Heq _].
        rewrite union_comm_L intersection_comm_L in Heq.
        f_equal.
        rewrite (accessible_retrieved_lending_memory_pages_difference i trans).
        rewrite union_intersection_r_L.
        rewrite union_comm_L difference_union_L.
        assert(ps_mem_in_trans ∖ retrieved_lending_memory_pages i trans ∪ ps_mem_in_trans ∖ (ps_acc ∖ {[p_tx]})=
                 ps_mem_in_trans ∖ retrieved_lending_memory_pages i trans) as H.
        rewrite union_comm_L.
        apply subseteq_union_1_L.
        pose proof (retrieved_lending_currently_accessible_memory_pages_subseteq i trans).
        set_solver + Hsubset_acc H.
        rewrite H.
        set_solver +.
        done.
      }

      iDestruct (get_valid_accessible_in_trans_memory_pages with "[$trans_hpool_global $pgt_owned]") as %Hvalid_acc_in_tran.
      set_solver + Hsubset_acc.

      (* we have this annoying case anlaysis because we need to know if the instruction is in the memory pages required by VMProp 0 *)
      destruct (decide ((tpa ai) ∈ ((ps_acc∖ {[p_tx]}) ∖ ({[p_rx]} ∪ transferred_memory_pages i trans)))) as [Hin_ps_oea | Hnin_ps_oea].
      { (* instruction is in ps_oea *)
        (* in this case, we don't need to transfer instruction *)
        assert (Hsubseteq_mem_acc: mem_oea ⊆ mem_acc_tx).
        rewrite Heq_mem_acc_tx'.
        apply map_union_subseteq_l.
        rewrite map_subseteq_spec in Hsubseteq_mem_acc.
        apply elem_of_set_of_addr_tpa in Hin_ps_oea.
        rewrite -Hdom_mem_oea in Hin_ps_oea.
        rewrite elem_of_dom in Hin_ps_oea.
        destruct Hin_ps_oea as [? Hlookup_mem_ai'].
        specialize (Hsubseteq_mem_acc ai _ Hlookup_mem_ai').
        rewrite Hlookup_mem_ai in Hsubseteq_mem_acc.
        inversion Hsubseteq_mem_acc.
        subst x. clear Hsubseteq_mem_acc.

        iAssert (memory_pages ((ps_acc ∖ {[p_tx]}) ∩ ({[p_rx]} ∪ (transferred_memory_pages i trans))) mem_inters)%I  with "[mem_inters]" as "mem_inters".
        { rewrite /memory_pages. iSplitL "";first done. iFrame. }

        (* merge [mem_inters] and [mem_rest] into [mem_trans] (including [mem_rx]) *)
        iDestruct (memory_pages_split_union'
                     ((ps_acc∖ {[p_tx]}) ∩ ({[p_rx]} ∪ (transferred_memory_pages i trans))) with "[mem_inters mem_rest]") as "mem_tran".
        2:{ iSplitL "mem_inters". iExists mem_inters. iFrame "mem_inters". iExact "mem_rest". }
        { set_solver +. }
        rewrite Heq_inter_diff_union.

        iDestruct (memory_pages_split_singleton' p_rx with "mem_tran") as "[mem_transferred mem_rx]".
        set_solver +.
        replace (({[p_rx]} ∪ transferred_memory_pages i trans) ∖ {[p_rx]}) with (transferred_memory_pages i trans).
        2:{
          pose proof (transferred_retrieved_lending_memory_pages_union i trans).
          set_solver + H Hnin_rx.
        }

        (* organizing big_sepSS: merging i and splitting v *)
        iDestruct (transferred_only_equiv with "[$tran_pgt_transferred $retri $mem_transferred]") as "transferred_only";eauto.
        rewrite /big_sepSS_except.
        assert (Hvmids_eq: set_of_vmids = (set_of_vmids ∖ {[i]} ∪ {[i]})).
        {
          pose proof (elem_of_set_of_vmids i).
          rewrite union_comm_L.
          apply union_difference_L.
          set_solver + H.
        }

        iDestruct "Running" as "([% VMProp] & VMProps & transferred_except & rxs_transferred)".
        iDestruct (big_sepSS_union_singleton (set_of_vmids ∖ {[i]}) i with "[transferred_except transferred_only]") as "transferred";auto.
        set_solver +. rewrite -Hvmids_eq. rewrite big_sepSS_later. iDestruct (later_intro with "transferred_only") as "transferred_only".
        rewrite big_sepSS_singleton_later. iFrame.
        rewrite -Hvmids_eq.
        iDestruct (big_sepSS_difference_singleton _ v with "transferred") as "[transferred_except transferred_only]";eauto.
        apply elem_of_set_of_vmids.

        (* organizing rx_states: merging i and splitting v *)
        iAssert(RX@i := p_rx)%I  with "[rx]"  as "#rx'".
        iDestruct "rx" as "[$ _]".
        iDestruct (rx_state_merge_zero_later with "[$rxs_global $rxs_transferred rx_state mem_rx]") as "[rxs_global rxs_transferred]";auto.
        iFrame "rx_state". iExists p_rx. iFrame "rx' mem_rx".
        iDestruct (rx_states_split_later v with "[$rxs_global $rxs_transferred]") as "(rxs_global & rxs_transferred & rx_state_v)";auto.
        Unshelve. 2: exact SliceRxsWf0.

        (* split VMProp v *)
        iDestruct (big_sepS_elem_of_acc _ _ v with "VMProps") as "[VMProp_v VMProps_acc]".
        pose proof (elem_of_set_of_vmids v). set_solver + H n i.

        (* getting instruction from [mem_oea] *)
        iDestruct (mem_big_sepM_split mem_oea Hlookup_mem_ai' with "mem_oea") as "[mem_instr Hacc_mem]".
        iDestruct ("tx") as "#tx".

        iApply (run ai v (transaction_hpool_global_transferred trans ∗
                            big_sepSS_singleton set_of_vmids v (Φ_t trans) ∗
                            rx_states_global (delete v rxs) ∗
                            (∀ rs : option (Addr * VMID), ⌜rxs !! v = Some rs⌝ -∗ rx_state_match v rs ∗ Φ_r v rs v)
                  )%I (vmprop_zero v Φ_t Φ_r trans rxs)
                 with "[PC R0 R1 R2 pgt_acc $tx mem_instr rxs_global VMProp VMProp_v
                           trans_hpool_global transferred_only rx_state_v]"); iFrameAutoSolve.
        {
          iSplitL "VMProp_v". iNext. iExact "VMProp_v".
          iSplitL "VMProp". iNext. iExact "VMProp".
          iSplitL "R2".
          {
            iNext. iIntros "((PC & instr & pgt_acc & _ & R0 & R1) & (trans_hpool_global & trans_transferred & rxs_global
                      & rx_state_v) & vmprop0)".
            rewrite vmprop_unknown_eq.
            iSplitR "PC instr pgt_acc".
            iExists trans, rxs.
            iFrame "trans_hpool_global trans_transferred rx_state_v rxs_global vmprop0".
            iSplitL "R0". iExists _. iSplitL. iExact "R0". done.
            iSplitL "R1". iExists _. iSplitL. iExact "R1". done.
            iSplitL "R2". iExists _. iExact "R2". done.
            iCombine "PC instr pgt_acc" as "R". iExact "R".
          }
          {
            rewrite -big_sepSS_singleton_later.
            iNext. iFrame "trans_hpool_global transferred_only". iFrame.
          }
        }
        iNext. iIntros "[(PC & instr & pgt_acc) VMProp] HHolds". simpl.
        iDestruct (VMProp_holds_agree i with "[$HHolds $VMProp]") as "[Hres VMProp]".
        iEval (rewrite /vmprop_zero /vmprop_zero_pre) in "Hres".
        iEval (rewrite later_exist) in "Hres". iDestruct "Hres" as (trans') "Hres".
        iEval (rewrite later_exist) in "Hres". iDestruct "Hres" as (rx_state_v') "Hres".
        iEval (rewrite 5!later_sep) in "Hres".
        iDestruct "Hres" as "(>%Hdisj & >trans_hpool_global & transferred_only & >rx_state_v & rx_transferred & regs_rx & VMProp_v)".
        iDestruct (slice_preserve_except _ _ (except v trans) with "transferred_except") as "transferred_except".
        symmetry. apply except_idemp.
        rewrite big_sepSS_singleton_later.
        iDestruct (slice_trans_unify (λ trans i j , (▷ Φ_t trans i j)%I) with "[$transferred_only transferred_except]") as "transferred".
        rewrite -except_idemp. done.
        iApply big_sepSS_except_later. iNext;done.

        iDestruct (big_sepSS_difference_singleton _ V0 with "transferred") as "[transferred_except transferred_only]";eauto.
        apply elem_of_set_of_vmids.
        rewrite -big_sepSS_except_later.
        iDestruct (get_trans_ps_disj with "trans_hpool_global") as %Htrans_disj'.
        iDestruct (get_trans_neq with "trans_hpool_global") as %Htrans_neq'.
        iDestruct (transferred_only_equiv_later with "transferred_only") as "(>tran_pgt_transferred & >retri & >mem_transferred)";eauto.
        iDestruct ("Hacc_mem" with "instr") as "mem_oea".

        iDestruct (get_trans_rel_secondary with "[$trans_hpool_global $retri $tran_pgt_owned $retri_owned]") as "%trans_rel".
        erewrite (trans_rel_secondary_currently_accessible_memory_pages);eauto.
        erewrite (trans_rel_secondary_currently_accessible_memory_pages) in Hsubset_acc;eauto.
        iDestruct (trans_rel_secondary_transaction_pagetable_entries_owned with "tran_pgt_owned") as "tran_pgt_owned";eauto.
        iDestruct (trans_rel_secondary_retrieved_transaction_owned with "retri_owned") as "retri_owned";eauto.

        set trans'' := (only v trans' ∪ (except v trans)).

        iAssert (⌜(ps_acc ∖ {[p_tx]} ∖ ({[p_rx]} ∪ transferred_memory_pages i trans)
                   = ps_acc ∖ {[p_rx; p_tx]} ∖ transferred_memory_pages i trans'')⌝)%I as "%H".
        {
          iDestruct (get_valid_accessible_in_trans_memory_pages with "[$trans_hpool_global $pgt_owned]") as %Hvalid_acc_in_tran'.
          set_solver + Hsubset_acc.
          iPureIntro.
          rewrite difference_difference_L.
          rewrite union_assoc_L (union_comm_L {[p_tx]}).
          rewrite -(difference_difference_L _ {[p_rx; p_tx]}).
          apply acc_transferred_memory_pages_difference;auto.
          erewrite <-(trans_rel_secondary_currently_accessible_memory_pages _ trans trans'') in Hsubset_acc;eauto.
          rewrite union_comm_L.
          exact Hsubset_acc.
        }
        iAssert (∃ mem_all : mem, memory_pages (ps_acc ∖ {[p_rx; p_tx]} ∪ accessible_in_trans_memory_pages i trans'') mem_all)%I
          with "[mem_oea mem_transferred]" as (?) "mem".
        {
          iAssert(∃ m: mem, memory_pages (ps_acc ∖ {[p_tx]} ∖ ({[p_rx]} ∪ transferred_memory_pages i trans)) m)%I with "[mem_oea]" as "mem_oea".
          iExists _. iSplit; done.
          rewrite H.
          iDestruct(memory_pages_union' with "[$mem_oea $mem_transferred]") as "mem". iFrame.
          rewrite acc_accessible_in_trans_memory_pages_union;auto.
          rewrite union_comm_L //.
        }

        clear Htrans_disj Htrans_neq.
        iDestruct ("VMProps_acc" with "VMProp_v") as "VMProps".

        iEval(rewrite /return_reg_rx later_or !later_sep) in "regs_rx".
        iDestruct ("regs_rx") as "[(>[R0| [R0 %Hrxstate_eq]] & >rxs_global & >R1 & >[% R2])
                            | (>R0 & regs_rx)]".
        { (* yield *)
          iDestruct ("Hacc_regs" $! (ai ^+ 1)%f _ _ _ with "[PC R0 R1 R2]") as "[%regs' [%Htotal_regs' regs'']]"; iFrameAutoSolve.
          iDestruct (rx_states_merge_yield with "[$rxs_global $rxs_transferred $rx_state_v $rx_transferred]") as
            "(rxs_global & rxs_transferred)";auto.
          Unshelve. 2: exact SliceRxsWf0.
          pose proof (base_extra.is_total_gmap_insert rxs v rx_state_v' Htotal_rxs) as Htotal_rxs'.
          iDestruct (rx_states_split_zero_later with "[$rxs_global $rxs_transferred]") as "(rxs_global & rxs_transferred
                                 & (>rx_state & >[% (#rx'' & [% mem_rx])]))";auto.
          iAssert (⌜p_rx0 = p_rx⌝%I) with "[rx' rx'']" as %Hrx_eq. iApply (rx_agree with "rx'' rx'").
          iClear "rx''". subst p_rx0.

          set ps_mem_in_trans' := (accessible_in_trans_memory_pages i trans'').

          iDestruct (memory_pages_disj_singleton with "[$mem $mem_rx]") as %Hnin_rx'.
          iDestruct "mem_tx" as "[%mem_tx mem_tx]".
          iDestruct (memory_pages_disj_singleton with "[$mem $mem_tx]") as %Hnin_tx'.

          (* merge all memory pages together *)
          iDestruct (memory_pages_merge_mb with "[$mem mem_rx mem_tx]") as "mem";auto.
          iCombine "mem_tx mem_rx" as "mem". iExact "mem".
          clear mem_rx mem_tx mem_all; subst ps_mem_in_trans.

          set rxs' := (<[v:=rx_state_v']> rxs).
          iApply ("IH" $! regs' ps_acc trans'' rxs' Htotal_rxs' Htotal_regs' Hsubset_mb Hsubset_acc Hnin_rx' Hnin_tx' with
                   "regs'' tx pgt_tx rx pgt_acc pgt_owned  trans_hpool_global tran_pgt_transferred retri rx_state rxs_global
                              tran_pgt_owned retri_owned mem [$transferred_except $rxs_transferred VMProp $VMProps]").
          { iExists _. iExact "VMProp". }
        }
        { (* wait, same *)
          iDestruct ("Hacc_regs" $! (ai ^+ 1)%f _ _ _ with "[PC R0 R1 R2]") as "[%regs' [%Htotal_regs' regs'']]"; iFrameAutoSolve.
          iDestruct (rx_states_merge_yield with "[$rxs_global $rxs_transferred $rx_state_v $rx_transferred]") as
            "(rxs_global & rxs_transferred)";auto.
          Unshelve. 2: exact SliceRxsWf0.
          pose proof (base_extra.is_total_gmap_insert rxs v rx_state_v' Htotal_rxs) as Htotal_rxs'.
          iDestruct (rx_states_split_zero_later with "[$rxs_global $rxs_transferred]") as "(rxs_global & rxs_transferred
                                 & (>rx_state & >[% (#rx'' & [% mem_rx])]))";auto.
          iAssert (⌜p_rx0 = p_rx⌝%I) with "[rx' rx'']" as %Hrx_eq. iApply (rx_agree with "rx'' rx'").
          iClear "rx''". subst p_rx0.

          set ps_mem_in_trans' := (accessible_in_trans_memory_pages i trans'').

          iDestruct (memory_pages_disj_singleton with "[$mem $mem_rx]") as %Hnin_rx'.
          iDestruct "mem_tx" as "[%mem_tx mem_tx]".
          iDestruct (memory_pages_disj_singleton with "[$mem $mem_tx]") as %Hnin_tx'.

          (* merge all memory pages together *)
          iDestruct (memory_pages_merge_mb with "[$mem mem_rx mem_tx]") as "mem";auto.
          iCombine "mem_tx mem_rx" as "mem". iExact "mem".
          clear mem_rx mem_tx mem_all; subst ps_mem_in_trans.

          set rxs' := (<[v:=rx_state_v']> rxs).
          iApply ("IH" $! regs' ps_acc trans'' rxs' Htotal_rxs' Htotal_regs' Hsubset_mb Hsubset_acc Hnin_rx' Hnin_tx' with
                   "regs'' tx pgt_tx rx pgt_acc pgt_owned  trans_hpool_global tran_pgt_transferred retri rx_state rxs_global
                              tran_pgt_owned retri_owned mem [$transferred_except $rxs_transferred VMProp $VMProps]").
          { iExists _. iExact "VMProp". }
        }
        { (* send *)
          (* FIXME: Inhabited?? *)
          iDestruct (later_exist with "regs_rx") as "[%l regs_rx]".
          Unshelve. 2: { split. exists W0. solve_finz. solve_finz. }
                  iDestruct (later_exist with "regs_rx") as "[%j regs_rx]".
          Unshelve. 2: { split. exact V0. }
                  iEval(rewrite !later_sep) in "regs_rx".
          iDestruct ("regs_rx") as "(Φjv & >rxs_global & >%Hlookup_rxs & >(%& R1 & %Hdecode_r1') & >R2)".
          iDestruct ("Hacc_regs" $! (ai ^+ 1)%f _ _ _ with "[PC R0 R1 R2]") as "[%regs' [%Htotal_regs' regs'']]"; iFrameAutoSolve.
          iDestruct (rx_states_merge_send with "[$rxs_global $rxs_transferred $rx_state_v $rx_transferred $Φjv]") as
            "(rxs_global & rxs_transferred)";auto.

          assert (Htotal_rxs': base_extra.is_total_gmap (<[j:= Some (l,v)]>(<[v := rx_state_v']> rxs))).
          by repeat apply base_extra.is_total_gmap_insert.
          iDestruct (rx_states_split_zero_later with "[$rxs_global $rxs_transferred]") as "(rxs_global & rxs_transferred
                                 & (>rx_state & >[% (#rx'' & [% mem_rx])]))";auto.

          iAssert (⌜p_rx0 = p_rx⌝%I) with "[rx' rx'']" as %Hrx_eq. iApply (rx_agree with "rx'' rx'").
          iClear "rx''". subst p_rx0.

          set ps_mem_in_trans' := (accessible_in_trans_memory_pages i trans'').

          iDestruct (memory_pages_disj_singleton with "[$mem $mem_rx]") as %Hnin_rx'.
          iDestruct "mem_tx" as "[%mem_tx mem_tx]".
          iDestruct (memory_pages_disj_singleton with "[$mem $mem_tx]") as %Hnin_tx'.

          (* merge all memory pages together *)
          iDestruct (memory_pages_merge_mb with "[$mem mem_rx mem_tx]") as "mem";auto.
          iCombine "mem_tx mem_rx" as "mem". iExact "mem".
          clear mem_rx mem_tx mem_all; subst ps_mem_in_trans.

          set rxs' := (<[j:= Some (l,v)]>(<[v:=rx_state_v']> rxs)).
          iApply ("IH" $! regs' ps_acc trans'' rxs' Htotal_rxs' Htotal_regs' Hsubset_mb Hsubset_acc Hnin_rx' Hnin_tx' with
                   "regs'' tx pgt_tx rx pgt_acc pgt_owned  trans_hpool_global tran_pgt_transferred retri rx_state rxs_global
                              tran_pgt_owned retri_owned mem [$transferred_except $rxs_transferred VMProp $VMProps]").
          { iExists _. iExact "VMProp". }
        }
      }
      { (* instruction is in rx *)
        (* spliting rx from mem_inters *)
        assert (Hsplit_rx: ((ps_acc ∖ {[p_tx]}) ∩ ({[p_rx]} ∪ transferred_memory_pages i trans))
                           = {[p_rx]} ∪ ((ps_acc ∖ {[p_tx]} ∖ {[p_rx]}) ∩ (transferred_memory_pages i trans))).
        rewrite intersection_union_l_L.
        assert ((ps_acc ∖ {[p_tx]}) ∩ {[p_rx]} = {[p_rx]}) as ->. set_solver + Hneq_mb Hsubset_mb.
        f_equal.
        pose proof (transferred_accessible_memory_pages_subseteq i trans).
        set_solver + H Hnin_rx.

        rewrite Hsplit_rx in Hdom_mem_inters.

        assert (Hnin_rx' : {[p_rx]} ## transferred_memory_pages i trans).
        pose proof (transferred_accessible_memory_pages_subseteq i trans).
        set_solver + H Hnin_rx.
        iPoseProof (memory_pages_split_union {[p_rx]} ((ps_acc ∖ {[p_tx]} ∖ {[p_rx]}) ∩ transferred_memory_pages i trans))as "[Ht _]".
        set_solver + Hnin_rx'.

        iDestruct ("Ht" with "[mem_inters]") as "(%mem_rx & %mem_inters' & mem_rx & mem_inters & %Heq_mem_inters)".
        iSplit. iPureIntro. exact Hdom_mem_inters. iFrame "mem_inters".
        iClear "Ht". subst mem_inters.

        destruct (decide (tpa ai = p_rx)).
        { (* in rx *)
          assert (Hsubseteq_mem_acc: mem_rx ⊆ mem_acc_tx).
          rewrite Heq_mem_acc_tx'.
          apply map_union_subseteq_r'. done.
          apply map_union_subseteq_l.
          rewrite map_subseteq_spec in Hsubseteq_mem_acc.
          assert (Hin_ps_rx: tpa ai ∈ ({[p_rx]} :gset _)). set_solver +e.
          apply elem_of_set_of_addr_tpa in Hin_ps_rx.
          iDestruct "mem_rx" as "[%Hdom_mem_rx mem_rx]".
          rewrite -Hdom_mem_rx in Hin_ps_rx.
          rewrite elem_of_dom in Hin_ps_rx.
          destruct Hin_ps_rx as [? Hlookup_mem_ai'].
          specialize (Hsubseteq_mem_acc ai _ Hlookup_mem_ai').
          rewrite Hlookup_mem_ai in Hsubseteq_mem_acc.
          inversion Hsubseteq_mem_acc.
          subst x. clear Hsubseteq_mem_acc.

          (* merge [mem_inters] and [mem_rest] into [mem_trans] (including [mem_rx]) *)
          iDestruct (memory_pages_split_union'
                       ((ps_acc∖ {[p_tx]} ∖ {[p_rx]}) ∩ ( (transferred_memory_pages i trans))) with "[mem_inters mem_rest]") as "mem_transferred".
          2:{ iSplitL "mem_inters". iExists mem_inters'. iFrame "mem_inters". iExact "mem_rest". }
          { set_solver +. }

          assert ((ps_acc ∖ {[p_tx]} ∖ {[p_rx]}) ∩ transferred_memory_pages i trans ∪ (ps_acc ∪ ps_mem_in_trans) ∖ ps_acc
                  = transferred_memory_pages i trans) as ->.
          {
            assert ((ps_acc ∪ ps_mem_in_trans) ∖ ps_acc = ps_mem_in_trans ∖ (ps_acc∖ {[p_tx]} ∖ {[p_rx]})) as ->.
            {
              assert ((ps_acc ∪ ps_mem_in_trans) ∖ ps_acc = ps_mem_in_trans ∖ ps_acc) as ->.
              set_solver +.
              set_solver + Hnin_tx Hnin_rx.
            }
            pose proof (union_split_difference_intersection_L (transferred_memory_pages i trans) (ps_acc∖ {[p_tx]})) as [Heq _].
            rewrite union_comm_L intersection_comm_L in Heq.
            f_equal.
            rewrite (accessible_retrieved_lending_memory_pages_difference i trans).
            rewrite union_intersection_r_L.
            rewrite union_comm_L difference_union_L.
            assert(ps_mem_in_trans ∖ retrieved_lending_memory_pages i trans ∪ ps_mem_in_trans ∖ (ps_acc ∖ {[p_tx]}∖ {[p_rx]})=
                     ps_mem_in_trans ∖ retrieved_lending_memory_pages i trans) as H.
            rewrite union_comm_L.
            apply subseteq_union_1_L.
            pose proof (retrieved_lending_currently_accessible_memory_pages_subseteq i trans).
            set_solver + Hsubset_acc H.
            rewrite H.
            set_solver +.
            done.
          }

          (* organizing big_sepSS: merging i and splitting v *)
          iDestruct (transferred_only_equiv with "[$tran_pgt_transferred $retri $mem_transferred]") as "transferred_only";eauto.
          rewrite /big_sepSS_except.
          assert (Hvmids_eq: set_of_vmids = (set_of_vmids ∖ {[i]} ∪ {[i]})).
          {
            pose proof (elem_of_set_of_vmids i).
            rewrite union_comm_L.
            apply union_difference_L.
            set_solver + H.
          }

          iDestruct "Running" as "([% VMProp] & VMProps & transferred_except & rxs_transferred)".
          iDestruct (big_sepSS_union_singleton (set_of_vmids ∖ {[i]}) i with "[transferred_except transferred_only]") as "transferred";auto.
          set_solver +. rewrite -Hvmids_eq. rewrite big_sepSS_later. iDestruct (later_intro with "transferred_only") as "transferred_only".
          rewrite big_sepSS_singleton_later. iFrame.
          rewrite -Hvmids_eq.
          iDestruct (big_sepSS_difference_singleton _ v with "transferred") as "[transferred_except transferred_only]";eauto.
          apply elem_of_set_of_vmids.

          (* organizing rx_states: merging i and splitting v *)
          iAssert(RX@i := p_rx)%I  with "[rx]"  as "#rx'".
          iDestruct "rx" as "[$ _]".

          (* split VMProp v *)
          iDestruct (big_sepS_elem_of_acc _ _ v with "VMProps") as "[VMProp_v VMProps_acc]".
          pose proof (elem_of_set_of_vmids v). set_solver + H n i.

          (* getting instruction from [mem_oea] *)
          iDestruct (mem_big_sepM_split mem_rx Hlookup_mem_ai' with "mem_rx") as "[mem_instr Hacc_mem]".
          iDestruct ("tx") as "#tx".

          iApply (run ai v (transaction_hpool_global_transferred trans ∗
                              big_sepSS_singleton set_of_vmids v (Φ_t trans) ∗
                              rx_states_global (delete i rxs) ∗
                              rx_states_transferred Φ_r (delete i rxs) ∗
                              rx_state_get i rxs ∗
                              (ai ->a instr -∗ [∗ map] k↦y ∈ mem_rx, k ->a y)
                    )%I (vmprop_zero v Φ_t Φ_r trans rxs)
                   with "[PC R0 R1 R2 pgt_acc $tx mem_instr rxs_global VMProp VMProp_v
                           trans_hpool_global transferred_only rxs_transferred rx_state Hacc_mem]"); iFrameAutoSolve.
          {
            iSplitL "VMProp_v". iNext. iExact "VMProp_v".
            iSplitL "VMProp". iNext. iExact "VMProp".
            iSplitL "R2".
            {
              iNext. iIntros "((PC & instr & pgt_acc & _ & R0 & R1) & (trans_hpool_global & trans_transferred & rxs_global
                      & rxs_transferred & rx_state & Hacc_mem) & vmprop0)".
              rewrite vmprop_unknown_eq.
              iDestruct ("Hacc_mem" with "instr") as "mem_rx".
              iDestruct (rx_state_merge_zero with "[$rxs_global $rxs_transferred rx_state mem_rx]") as "[rxs_global rxs_transferred]";auto.
              iFrame "rx_state". iExists p_rx. iFrame "rx'".  iExists mem_rx. rewrite -memory_pages_singleton. iSplit. iPureIntro. done. iFrame "mem_rx".
              iDestruct (rx_states_split v with "[$rxs_global $rxs_transferred]") as "(rxs_global & rxs_transferred & rx_state)";auto.
              Unshelve. 2,4: exact SliceRxsWf0.
              iSplitR "PC pgt_acc rxs_transferred".
              iExists trans, rxs.
              iFrame "trans_hpool_global trans_transferred rxs_global vmprop0".
              iSplitL "R0". iExists _. iSplitL. iExact "R0". done.
              iSplitL "R1". iExists _. iSplitL. iExact "R1". done.
              iSplitL "R2". iExists _. iExact "R2". iSplitL "rx_state". done. done.
              iCombine "PC pgt_acc rxs_transferred" as "R". iExact "R".
            }
            {
              rewrite -big_sepSS_singleton_later.
              iNext. iFrame "trans_hpool_global transferred_only". iFrame.
            }
          }
          iNext. iIntros "[(PC & pgt_acc & rxs_transferred) VMProp] HHolds". simpl.
          iDestruct (VMProp_holds_agree i with "[$HHolds $VMProp]") as "[Hres VMProp]".
          iEval (rewrite /vmprop_zero /vmprop_zero_pre) in "Hres".
          iEval (rewrite later_exist) in "Hres". iDestruct "Hres" as (trans') "Hres".
          iEval (rewrite later_exist) in "Hres". iDestruct "Hres" as (rx_state_v') "Hres".
          iEval (rewrite 5!later_sep) in "Hres".
          iDestruct "Hres" as "(>%Hdisj & >trans_hpool_global & transferred_only & >rx_state_v & rx_transferred & regs_rx & VMProp_v)".
          iDestruct (slice_preserve_except _ _ (except v trans) with "transferred_except") as "transferred_except".
          symmetry. apply except_idemp.
          rewrite big_sepSS_singleton_later.
          iDestruct (slice_trans_unify (λ trans i j , (▷ Φ_t trans i j)%I) with "[$transferred_only transferred_except]") as "transferred".
          rewrite -except_idemp. done.
          iApply big_sepSS_except_later. iNext;done.

          iDestruct (big_sepSS_difference_singleton _ V0 with "transferred") as "[transferred_except transferred_only]";eauto.
          apply elem_of_set_of_vmids.
          rewrite -big_sepSS_except_later.
          iDestruct (get_trans_ps_disj with "trans_hpool_global") as %Htrans_disj'.
          iDestruct (get_trans_neq with "trans_hpool_global") as %Htrans_neq'.
          iDestruct (transferred_only_equiv_later with "transferred_only") as "(>tran_pgt_transferred & >retri & >mem_transferred)";eauto.

          iDestruct (get_trans_rel_secondary with "[$trans_hpool_global $retri $tran_pgt_owned $retri_owned]") as "%trans_rel".
          erewrite (trans_rel_secondary_currently_accessible_memory_pages);eauto.
          erewrite (trans_rel_secondary_currently_accessible_memory_pages) in Hsubset_acc;eauto.
          iDestruct (trans_rel_secondary_transaction_pagetable_entries_owned with "tran_pgt_owned") as "tran_pgt_owned";eauto.
          iDestruct (trans_rel_secondary_retrieved_transaction_owned with "retri_owned") as "retri_owned";eauto.

          set trans'' := (only v trans' ∪ (except v trans)).

          iAssert (⌜(ps_acc ∖ {[p_tx]} ∖ ({[p_rx]} ∪ transferred_memory_pages i trans)
                     = ps_acc ∖ {[p_rx; p_tx]} ∖ transferred_memory_pages i trans'')⌝)%I as "%H".
          {
            iDestruct (get_valid_accessible_in_trans_memory_pages with "[$trans_hpool_global $pgt_owned]") as %Hvalid_acc_in_tran'.
            set_solver + Hsubset_acc.
            iPureIntro.
            rewrite difference_difference_L.
            rewrite union_assoc_L (union_comm_L {[p_tx]}).
            rewrite -(difference_difference_L _ {[p_rx; p_tx]}).
            apply acc_transferred_memory_pages_difference;auto.
            erewrite <-(trans_rel_secondary_currently_accessible_memory_pages _ trans trans'') in Hsubset_acc;eauto.
            rewrite union_comm_L.
            exact Hsubset_acc.
          }
          iAssert (∃ mem_all : mem, memory_pages (ps_acc ∖ {[p_rx; p_tx]} ∪ accessible_in_trans_memory_pages i trans'') mem_all)%I
            with "[mem_oea mem_transferred]" as (?) "mem".
          {
            iAssert(∃ m: mem, memory_pages (ps_acc ∖ {[p_tx]} ∖ ({[p_rx]} ∪ transferred_memory_pages i trans)) m)%I with "[mem_oea]" as "mem_oea".
            iExists _. iSplit; done.
            rewrite H.
            iDestruct(memory_pages_union' with "[$mem_oea $mem_transferred]") as "mem". iFrame.
            rewrite acc_accessible_in_trans_memory_pages_union;auto.
            rewrite union_comm_L //.
          }

          clear Htrans_disj Htrans_neq.
          iDestruct ("VMProps_acc" with "VMProp_v") as "VMProps".

          iEval(rewrite /return_reg_rx later_or !later_sep) in "regs_rx".
          iDestruct ("regs_rx") as "[(>[R0| [R0 %Hrxstate_eq]] & >rxs_global & >R1 & >[% R2])
                            | (>R0 & regs_rx)]".
          { (* yield *)
            iDestruct ("Hacc_regs" $! (ai ^+ 1)%f _ _ _ with "[PC R0 R1 R2]") as "[%regs' [%Htotal_regs' regs'']]"; iFrameAutoSolve.
            iDestruct (rx_states_merge_yield with "[$rxs_global $rxs_transferred $rx_state_v $rx_transferred]") as
              "(rxs_global & rxs_transferred)";auto.
            Unshelve. 2: exact SliceRxsWf0.
            pose proof (base_extra.is_total_gmap_insert rxs v rx_state_v' Htotal_rxs) as Htotal_rxs'.
            iDestruct (rx_states_split_zero_later with "[$rxs_global $rxs_transferred]") as "(rxs_global & rxs_transferred
                                 & (>rx_state & >[% (#rx'' & [% mem_rx])]))";auto.
            iAssert (⌜p_rx0 = p_rx⌝%I) with "[rx' rx'']" as %Hrx_eq. iApply (rx_agree with "rx'' rx'").
            iClear "rx''". subst p_rx0.

            set ps_mem_in_trans' := (accessible_in_trans_memory_pages i trans'').

            iDestruct (memory_pages_disj_singleton with "[$mem $mem_rx]") as %Hnin_rx''.
            iDestruct "mem_tx" as "[%mem_tx mem_tx]".
            iDestruct (memory_pages_disj_singleton with "[$mem $mem_tx]") as %Hnin_tx''.

            (* merge all memory pages together *)
            iDestruct (memory_pages_merge_mb with "[$mem mem_rx mem_tx]") as "mem";auto.
            iCombine "mem_tx mem_rx" as "mem". iExact "mem".
            clear Hlookup_mem_ai' Hdom_mem_inters Hdom_mem_rx Heq_mem_acc_tx' Hdisj_mem_oea_inters mem_rx mem_tx mem_all; subst ps_mem_in_trans.

            set rxs' := (<[v:=rx_state_v']> rxs).
            iApply ("IH" $! regs' ps_acc trans'' rxs' Htotal_rxs' Htotal_regs' Hsubset_mb Hsubset_acc Hnin_rx'' Hnin_tx'' with
                     "regs'' tx pgt_tx rx pgt_acc pgt_owned  trans_hpool_global tran_pgt_transferred retri rx_state rxs_global
                              tran_pgt_owned retri_owned mem [$transferred_except $rxs_transferred VMProp $VMProps]").
            { iExists _. iExact "VMProp". }
          }
          { (* wait, same *)
            iDestruct ("Hacc_regs" $! (ai ^+ 1)%f _ _ _ with "[PC R0 R1 R2]") as "[%regs' [%Htotal_regs' regs'']]"; iFrameAutoSolve.
            iDestruct (rx_states_merge_yield with "[$rxs_global $rxs_transferred $rx_state_v $rx_transferred]") as
              "(rxs_global & rxs_transferred)";auto.
            Unshelve. 2: exact SliceRxsWf0.
            pose proof (base_extra.is_total_gmap_insert rxs v rx_state_v' Htotal_rxs) as Htotal_rxs'.
            iDestruct (rx_states_split_zero_later with "[$rxs_global $rxs_transferred]") as "(rxs_global & rxs_transferred
                                 & (>rx_state & >[% (#rx'' & [% mem_rx])]))";auto.
            iAssert (⌜p_rx0 = p_rx⌝%I) with "[rx' rx'']" as %Hrx_eq. iApply (rx_agree with "rx'' rx'").
            iClear "rx''". subst p_rx0.

            set ps_mem_in_trans' := (accessible_in_trans_memory_pages i trans'').

            iDestruct (memory_pages_disj_singleton with "[$mem $mem_rx]") as %Hnin_rx''.
            iDestruct "mem_tx" as "[%mem_tx mem_tx]".
            iDestruct (memory_pages_disj_singleton with "[$mem $mem_tx]") as %Hnin_tx''.

            (* merge all memory pages together *)
            iDestruct (memory_pages_merge_mb with "[$mem mem_rx mem_tx]") as "mem";auto.
            iCombine "mem_tx mem_rx" as "mem". iExact "mem".
            clear Hlookup_mem_ai' Hdom_mem_inters Hdom_mem_rx Heq_mem_acc_tx' Hdisj_mem_oea_inters mem_rx mem_tx mem_all; subst ps_mem_in_trans.

            set rxs' := (<[v:=rx_state_v']> rxs).
            iApply ("IH" $! regs' ps_acc trans'' rxs' Htotal_rxs' Htotal_regs' Hsubset_mb Hsubset_acc Hnin_rx'' Hnin_tx'' with
                     "regs'' tx pgt_tx rx pgt_acc pgt_owned  trans_hpool_global tran_pgt_transferred retri rx_state rxs_global
                              tran_pgt_owned retri_owned mem [$transferred_except $rxs_transferred VMProp $VMProps]").
            { iExists _. iExact "VMProp". }
          }
          { (* send *)
            (* FIXME: Inhabited?? *)
            iDestruct (later_exist with "regs_rx") as "[%l regs_rx]".
            Unshelve. 2: { split. exists W0. solve_finz. solve_finz. }
                    iDestruct (later_exist with "regs_rx") as "[%j regs_rx]".
            Unshelve. 2: { split. exact V0. }
                    iEval(rewrite !later_sep) in "regs_rx".
            iDestruct ("regs_rx") as "(Φjv & >rxs_global & >%Hlookup_rxs & >(%& R1 & %Hdecode_r1') & >R2)".
            iDestruct ("Hacc_regs" $! (ai ^+ 1)%f _ _ _ with "[PC R0 R1 R2]") as "[%regs' [%Htotal_regs' regs'']]"; iFrameAutoSolve.
            iDestruct (rx_states_merge_send with "[$rxs_global $rxs_transferred $rx_state_v $rx_transferred $Φjv]") as
              "(rxs_global & rxs_transferred)";auto.

            assert (Htotal_rxs': base_extra.is_total_gmap (<[j:= Some (l,v)]>(<[v := rx_state_v']> rxs))).
            by repeat apply base_extra.is_total_gmap_insert.
            iDestruct (rx_states_split_zero_later with "[$rxs_global $rxs_transferred]") as "(rxs_global & rxs_transferred
                                 & (>rx_state & >[% (#rx'' & [% mem_rx])]))";auto.

            iAssert (⌜p_rx0 = p_rx⌝%I) with "[rx' rx'']" as %Hrx_eq. iApply (rx_agree with "rx'' rx'").
            iClear "rx''". subst p_rx0.

            set ps_mem_in_trans' := (accessible_in_trans_memory_pages i trans'').

            iDestruct (memory_pages_disj_singleton with "[$mem $mem_rx]") as %Hnin_rx''.
            iDestruct "mem_tx" as "[%mem_tx mem_tx]".
            iDestruct (memory_pages_disj_singleton with "[$mem $mem_tx]") as %Hnin_tx''.

            (* merge all memory pages together *)
            iDestruct (memory_pages_merge_mb with "[$mem mem_rx mem_tx]") as "mem";auto.
            iCombine "mem_tx mem_rx" as "mem". iExact "mem".
            clear Hlookup_mem_ai' Hdom_mem_inters Hdom_mem_rx Heq_mem_acc_tx' Hdisj_mem_oea_inters mem_rx mem_tx mem_all; subst ps_mem_in_trans.

            set rxs' := (<[j:= Some (l,v)]>(<[v:=rx_state_v']> rxs)).
            iApply ("IH" $! regs' ps_acc trans'' rxs' Htotal_rxs' Htotal_regs' Hsubset_mb Hsubset_acc Hnin_rx'' Hnin_tx'' with
                     "regs'' tx pgt_tx rx pgt_acc pgt_owned  trans_hpool_global tran_pgt_transferred retri rx_state rxs_global
                              tran_pgt_owned retri_owned mem [$transferred_except $rxs_transferred VMProp $VMProps]").
            { iExists _. iExact "VMProp". }
          }
        }
        { (* not in rx, two cases *)
          assert (Hin_ps_inters : tpa ai ∈ (ps_acc ∖ {[p_tx]} ∖ {[p_rx]}) ∩ (transferred_memory_pages i trans)).
          {
            rewrite Heq_ps_acc_tx in Hin_ps_acc_tx.
            rewrite elem_of_union in Hin_ps_acc_tx.
            destruct Hin_ps_acc_tx.
            set_solver + H Hnin_ps_oea.
            set_solver + H n0.
          }

          assert (ps_acc ∪ ps_mem_in_trans = ps_acc ∪ (transferred_memory_pages i trans)) as ->.
          {
            rewrite -acc_accessible_in_trans_memory_pages_union;auto.
            rewrite difference_union_L //.
            set_solver + Hsubset_acc Hnin_rx Hnin_tx.
          }
          rewrite (difference_union_cancel_L_l ps_acc).

          pose proof (transferred_memory_pages_split_only i v trans) as [Hsplit_trans Hsplit_trans_disj];auto.
          iEval (rewrite Hsplit_trans intersection_union_l_L) in "mem_inters".

          rewrite Hsplit_trans in Hin_ps_inters.

          iEval (rewrite /ps_mem_in_trans Hsplit_trans) in "mem_rest".

          rewrite difference_union_distr_l_L.
          iDestruct (memory_pages_split_union' with "mem_rest") as "[mem_rest_a mem_rest_b]".
          { set_solver + Hsplit_trans_disj. }

          assert(∀ trans_sub,
                   trans_sub ⊆ trans ->
                   (ps_acc ∖ {[p_tx]} ∖ {[p_rx]}) ∩ (transferred_memory_pages i trans_sub) ∪ (transferred_memory_pages i trans_sub) ∖ ps_acc =
                     transferred_memory_pages i trans_sub).
          {
            intros ? Hsubset_trans.
            rewrite intersection_comm_L.
            pose proof (transferred_memory_pages_subseteq i trans_sub trans Hsubset_trans) as H.
            pose proof (union_split_difference_intersection_L (transferred_memory_pages i trans_sub) ps_acc) as [Heq _].
            assert (transferred_memory_pages i trans_sub ∩ (ps_acc ∖ {[p_tx]} ∖ {[p_rx]})
                    = transferred_memory_pages i trans_sub ∩ ps_acc) as ->.
            {
              assert (Hnin_tx' : {[p_tx]} ## transferred_memory_pages i trans).
              pose proof (transferred_accessible_memory_pages_subseteq i trans).
              set_solver + H0 Hnin_tx.
              set_solver + H Hnin_tx' Hnin_rx'.
            }
            rewrite Heq. set_solver +.
          }

          iAssert (⌜mem_rx ##ₘ mem_inters'⌝%I )with "[mem_rx mem_inters]" as "%Hdisj_rx_inters'".
          {
            iDestruct "mem_rx" as "[%Hdom_mem_rx _]".
            iDestruct "mem_inters" as "[%Hdom_mem_inters' _]".
            iPureIntro.
            apply map_disjoint_dom.
            rewrite Hdom_mem_inters' Hdom_mem_rx.
            apply set_of_addr_disj.
            set_solver +.
          }

          iPoseProof (memory_pages_split_union ((ps_acc ∖ {[p_tx]} ∖ {[p_rx]}) ∩ transferred_memory_pages i (only v trans))
                        ((ps_acc ∖ {[p_tx]} ∖ {[p_rx]}) ∩ transferred_memory_pages i (except v trans))
                     )as "[Ht _]".
          set_solver + Hsplit_trans_disj.

          iDestruct ("Ht" with "[mem_inters]") as "(%mem_inters_a & %mem_inters_b & mem_inters_a & mem_inters_b & %Heq_mem_inters)".
          iExact "mem_inters".
          iClear "Ht". subst mem_inters'.

          iDestruct (transaction_pagetable_entries_transferred_split _ v with "tran_pgt_transferred") as "[tran_pgt_transferred_only_v tran_pgt_transferred_except_v]";auto.
          iDestruct (retrievable_transaction_transferred_split _ v with "retri") as "[retri_transferred_only_v retri_transferred_except_v]";auto.

          iDestruct "Running" as "([% VMProp] & VMProps & transferred_except & rxs_transferred)".
          iDestruct (big_sepSS_difference_singleton _ v with "transferred_except") as "[transferred_except_v transferred_only_v]";eauto.
          pose proof (elem_of_set_of_vmids v). set_solver + H0 n.

          (* organizing rx_states: merging i and splitting v *)
          iAssert(RX@i := p_rx)%I  with "[rx]"  as "#rx'".
          iDestruct "rx" as "[$ _]".
          iDestruct (rx_state_merge_zero_later with "[$rxs_global $rxs_transferred rx_state mem_rx]") as "[rxs_global rxs_transferred]"; auto.
          iFrame "rx_state". iExists p_rx. iFrame "rx'". iExists mem_rx. rewrite memory_pages_singleton. iFrame "mem_rx".
          iDestruct (rx_states_split_later v with "[$rxs_global $rxs_transferred]") as "(rxs_global & rxs_transferred & rx_state_v)";auto.

          (* split VMProp v *)
          iDestruct (big_sepS_elem_of_acc _ _ v with "VMProps") as "[VMProp_v VMProps_acc]".
          pose proof (elem_of_set_of_vmids v). set_solver + H0 n i.

          iDestruct ("tx") as "#tx".

          rewrite intersection_union_l_L in Hin_ps_inters.
          apply elem_of_union in Hin_ps_inters.
          destruct Hin_ps_inters as [Hin_ps_only | Hnin_ps_only].
          {
            assert (Hsubseteq_mem_acc: mem_inters_a ⊆ mem_acc_tx).
            rewrite Heq_mem_acc_tx'.
            apply map_union_subseteq_r'. done.
            apply map_union_subseteq_r'. done.
            apply map_union_subseteq_l.
            rewrite map_subseteq_spec in Hsubseteq_mem_acc.
            apply elem_of_set_of_addr_tpa in Hin_ps_only.
            iDestruct "mem_inters_a" as "[%Hdom_mem_inters_a mem_inters_a]".
            rewrite -Hdom_mem_inters_a in Hin_ps_only.
            rewrite elem_of_dom in Hin_ps_only.
            destruct Hin_ps_only as [? Hlookup_mem_ai'].
            specialize (Hsubseteq_mem_acc ai _ Hlookup_mem_ai').
            rewrite Hlookup_mem_ai in Hsubseteq_mem_acc.
            inversion Hsubseteq_mem_acc.
            subst x. clear Hsubseteq_mem_acc.

            iDestruct (memory_pages_union' with "[mem_inters_b $mem_rest_b]") as "mem_b".
            { iExists mem_inters_b. iExact "mem_inters_b". }
            iEval (rewrite union_comm_L) in "mem_b".
            rewrite (H (except v trans)). 2: apply except_subseteq.

            (* getting instruction from [mem_inters_a] *)
            iDestruct (mem_big_sepM_split mem_inters_a Hlookup_mem_ai' with "mem_inters_a") as "[mem_instr Hacc_mem]".

            iApply (run ai v (transaction_hpool_global_transferred trans ∗
                                big_sepSS_singleton (set_of_vmids ∖ {[i]}) v (Φ_t trans) ∗
                                transaction_pagetable_entries_transferred i (only v trans) ∗
                                retrievable_transaction_transferred i (only v trans) ∗
                                (∃ mem1 : mem, memory_pages (transferred_memory_pages i (only v trans) ∖ ps_acc) mem1) ∗
                                (ai ->a instr -∗ [∗ map] k↦y ∈ mem_inters_a, k ->a y) ∗
                                rx_states_global (delete v rxs) ∗
                                (∀ rs : option (Addr * VMID), ⌜rxs !! v = Some rs⌝ -∗ rx_state_match v rs ∗ Φ_r v rs v)
                      )%I (vmprop_zero v Φ_t Φ_r trans rxs)
                     with "[PC R0 R1 R2 pgt_acc $tx mem_instr rxs_global VMProp VMProp_v
                           trans_hpool_global tran_pgt_transferred_only_v retri_transferred_only_v Hacc_mem mem_rest_a transferred_only_v rx_state_v]"); iFrameAutoSolve.
            {
              iSplitL "VMProp_v". iNext. iExact "VMProp_v".
              iSplitL "VMProp". iNext. iExact "VMProp".
              iSplitL "R2".
              {
                iNext. iIntros "((PC & instr & pgt_acc & _ & R0 & R1) & (trans_hpool_global & transferred_only_v &
                      tran_pgt_transferred_only_v & retri_transferred_only_v & mem_rest & Hacc_inters & rxs_global
                      & rx_state_v) & vmprop0)".
                rewrite vmprop_unknown_eq.
                iSplitR "PC pgt_acc".
                iExists trans, rxs.
                iFrame "trans_hpool_global rx_state_v rxs_global vmprop0".
                iSplitL "transferred_only_v tran_pgt_transferred_only_v retri_transferred_only_v mem_rest Hacc_inters instr".
                rewrite /big_sepSS_singleton.
                case_decide. 2:{ pose proof (elem_of_set_of_vmids v). set_solver + H0 H1 n. }
                           case_decide. 2:{ pose proof (elem_of_set_of_vmids v). set_solver + H0 H1 n. }
                                      iDestruct "transferred_only_v" as "[$ transferred_only_v]".
                iApply (big_sepS_delete _ _ i).
                pose proof (elem_of_set_of_vmids i). set_solver + H2 n. clear H0 H1.
                assert (set_of_vmids ∖ {[v]} ∖ {[i]} = set_of_vmids ∖ {[i]} ∖ {[v]}) as ->. set_solver + n.
                iFrame "transferred_only_v".
                rewrite 2?HΦt. 2: left;done. 2: right;done.
                rewrite /slice_transfer_all.
                iDestruct (transaction_pagetable_entries_transferred_only_equiv with "tran_pgt_transferred_only_v") as "[$ $]";auto.
                iDestruct (retrievable_transaction_transferred_only_equiv with "retri_transferred_only_v") as "[$ $]";auto.
                iDestruct ("Hacc_inters" with "instr") as "mem_inters".
                iApply (transferred_memory_only_equiv). auto. auto. auto.
                iDestruct (memory_pages_union' with "[$mem_rest mem_inters]") as "mem".
                iExists mem_inters_a. iSplit. iPureIntro. exact Hdom_mem_inters_a. iFrame.
                rewrite (union_comm_L (transferred_memory_pages i (only v trans) ∖ ps_acc)).
                rewrite H. iFrame "mem". apply only_subseteq.
                iSplitL "R0". iExists _. iSplitL. iExact "R0". done.
                iSplitL "R1". iExists _. iSplitL. iExact "R1". done.
                iSplitL "R2". iExists _. iExact "R2". done.
                iCombine "PC pgt_acc" as "R". iExact "R".
              }
              {
                iNext. iFrame "trans_hpool_global rxs_global rx_state_v". iFrame.
              }
            }
            iNext. iIntros "([PC pgt_acc] & VMProp) HHolds". iSimpl in "HHolds".

            iDestruct (VMProp_holds_agree i with "[$HHolds $VMProp]") as "[Hres VMProp]".
            iEval (rewrite /vmprop_zero /vmprop_zero_pre) in "Hres".
            iEval (rewrite later_exist) in "Hres". iDestruct "Hres" as (trans') "Hres".
            iEval (rewrite later_exist) in "Hres". iDestruct "Hres" as (rx_state_v') "Hres".
            iEval (rewrite 5!later_sep) in "Hres".
            iDestruct "Hres" as "(>%Hdisj' & >trans_hpool_global & transferred_only & >rx_state_v & rx_transferred & regs_rx & VMProp_v)".
            iDestruct (slice_preserve_except v _ (only v trans' ∪ except v trans) trans with "transferred_except_v") as "transferred_except_v".
            symmetry. rewrite -(except_only_union v (except v trans) trans'). apply except_idemp.
            rewrite -except_idemp;done.

            iDestruct (big_sepSS_singletion_union _ i with "transferred_only") as "[transferred_only_v transferred_i_v]".
            apply elem_of_set_of_vmids.

            assert (Htemp: (set_of_vmids ∖ {[i]}) = (set_of_vmids ∖ {[i]} ∖ {[v]} ∪ {[v]})).
            rewrite difference_union_L.
            pose proof (elem_of_set_of_vmids v).
            set_solver + i n H0.
            iDestruct (big_sepSS_union_singleton with "[transferred_except_v transferred_only_v]") as "transferred".
            2:{
              iSplitL "transferred_except_v".
              iDestruct (later_intro with "transferred_except_v") as "transferred_except_v".
              rewrite big_sepSS_except_later.
              iExact "transferred_except_v".
              iEval (rewrite Htemp) in "transferred_only_v".
              rewrite big_sepSS_singleton_later.
              iExact "transferred_only_v".
            } set_solver +.
            iDestruct (get_trans_ps_disj with "trans_hpool_global") as %Htrans_disj'.
            iDestruct (get_trans_neq with "trans_hpool_global") as %Htrans_neq'.

            rewrite -Htemp.

            iEval (rewrite big_sepSS_singleton_later /big_sepSS_singleton ) in "transferred_i_v".
            case_decide. set_solver + i n H0.
            assert (({[i]} ∖ {[v]}) = ({[i]}:gset _)) as ->. set_solver + i n H0.
            rewrite big_sepS_singleton.
            rewrite 2?HΦt. 2: left;done. 2: right;done.
            iDestruct "transferred_i_v" as "[>(tran_pgt_transferred_i_v & retri_transferred_i_v & transferred_mem_i_v) >(tran_pgt_transferred_v_i & retri_transferred_v_i & transferred_mem_v_i)]".
            iCombine "tran_pgt_transferred_v_i tran_pgt_transferred_i_v" as "tran_pgt_transferred".
            pose proof (except_only_union v (except v trans) trans') as Htemp'.
            feed specialize Htemp'. rewrite -except_idemp //.
            iDestruct (transaction_pagetable_entries_transferred_only_equiv i with "tran_pgt_transferred") as "tran_pgt_transferred_only_v";auto.
            iEval(rewrite except_idemp Htemp') in "tran_pgt_transferred_except_v".
            iDestruct(transaction_pagetable_entries_transferred_split with "[$tran_pgt_transferred_only_v $tran_pgt_transferred_except_v ]") as "tran_pgt_transferred".

            iCombine "retri_transferred_v_i retri_transferred_i_v" as "retri_transferred".
            iDestruct (retrievable_transaction_transferred_only_equiv i with "retri_transferred") as "retri_transferred_only_v"; auto.
            iEval(rewrite except_idemp Htemp') in "retri_transferred_except_v".
            iDestruct(retrievable_transaction_transferred_split with "[$retri_transferred_only_v $retri_transferred_except_v ]") as "retri_transferred".

            iCombine "transferred_mem_i_v transferred_mem_v_i" as "transferred_mem".
            iDestruct (transferred_memory_only_equiv i v with "transferred_mem") as "transferred_memory_only_v";auto.
            iEval(rewrite except_idemp Htemp') in "mem_b".
            iDestruct (transferred_memory_split i with "[mem_b transferred_memory_only_v]") as "mem_transferred";auto.
            3: { iSplitR "mem_b". iExact "transferred_memory_only_v". iExact "mem_b". }
            auto. auto.

            iDestruct (get_trans_rel_secondary with "[$trans_hpool_global $retri_transferred $tran_pgt_owned $retri_owned]") as "%trans_rel".
            erewrite (trans_rel_secondary_currently_accessible_memory_pages);eauto.
            erewrite (trans_rel_secondary_currently_accessible_memory_pages) in Hsubset_acc;eauto.
            iDestruct (trans_rel_secondary_transaction_pagetable_entries_owned with "tran_pgt_owned") as "tran_pgt_owned";eauto.
            iDestruct (trans_rel_secondary_retrieved_transaction_owned with "retri_owned") as "retri_owned";eauto.

            set trans'' := (only v trans' ∪ (except v trans)).

            iAssert (⌜(ps_acc ∖ {[p_tx]} ∖ ({[p_rx]} ∪ transferred_memory_pages i trans)
                       = ps_acc ∖ {[p_rx; p_tx]} ∖ transferred_memory_pages i trans'')⌝)%I as "%H'".
            {
              iDestruct (get_valid_accessible_in_trans_memory_pages with "[$trans_hpool_global $pgt_owned]") as %Hvalid_acc_in_tran'.
              set_solver + Hsubset_acc.
              iPureIntro.
              rewrite difference_difference_L.
              rewrite union_assoc_L (union_comm_L {[p_tx]}).
              rewrite -(difference_difference_L _ {[p_rx; p_tx]}).
              apply acc_transferred_memory_pages_difference;auto.
              erewrite <-(trans_rel_secondary_currently_accessible_memory_pages _ trans trans'') in Hsubset_acc;eauto.
              rewrite union_comm_L.
              exact Hsubset_acc.
            }
            iAssert (∃ mem_all : mem, memory_pages (ps_acc ∖ {[p_rx; p_tx]} ∪ accessible_in_trans_memory_pages i trans'') mem_all)%I
              with "[mem_oea mem_transferred]" as (?) "mem".
            {
              iAssert(∃ m: mem, memory_pages (ps_acc ∖ {[p_tx]} ∖ ({[p_rx]} ∪ transferred_memory_pages i trans)) m)%I with "[mem_oea]" as "mem_oea".
              iExists _. iSplit; done.
              rewrite H'.
              iDestruct(memory_pages_union' with "[$mem_oea $mem_transferred]") as "mem". iFrame.
              rewrite acc_accessible_in_trans_memory_pages_union;auto.
              rewrite union_comm_L //.
            }

            clear Htrans_disj Htrans_neq H'.
            iDestruct ("VMProps_acc" with "VMProp_v") as "VMProps".
            rewrite -big_sepSS_later.
            iEval(rewrite /return_reg_rx later_or !later_sep) in "regs_rx".
            iDestruct ("regs_rx") as "[(>[R0| [R0 %Hrxstate_eq]] & >rxs_global & >R1 & >[% R2])
                            | (>R0 & regs_rx)]".
            { (* yield *)
              iDestruct ("Hacc_regs" $! (ai ^+ 1)%f _ _ _ with "[PC R0 R1 R2]") as "[%regs' [%Htotal_regs' regs'']]"; iFrameAutoSolve.
              iDestruct (rx_states_merge_yield with "[$rxs_global $rxs_transferred $rx_state_v $rx_transferred]") as
                "(rxs_global & rxs_transferred)";auto.
              Unshelve. 2: exact SliceRxsWf0.
              pose proof (base_extra.is_total_gmap_insert rxs v rx_state_v' Htotal_rxs) as Htotal_rxs'.
              iDestruct (rx_states_split_zero_later with "[$rxs_global $rxs_transferred]") as "(rxs_global & rxs_transferred
                                 & (>rx_state & >[% (#rx'' & [% mem_rx])]))";auto.
              iAssert (⌜p_rx0 = p_rx⌝%I) with "[rx' rx'']" as %Hrx_eq. iApply (rx_agree with "rx'' rx'").
              iClear "rx''". subst p_rx0.

              set ps_mem_in_trans' := (accessible_in_trans_memory_pages i trans'').

              iDestruct (memory_pages_disj_singleton with "[$mem $mem_rx]") as %Hnin_rx''.
              iDestruct "mem_tx" as "[%mem_tx mem_tx]".
              iDestruct (memory_pages_disj_singleton with "[$mem $mem_tx]") as %Hnin_tx''.

              (* merge all memory pages together *)
              iDestruct (memory_pages_merge_mb with "[$mem mem_rx mem_tx]") as "mem";auto.
              iCombine "mem_tx mem_rx" as "mem". iExact "mem".
              clear Hdisj_rx_inters' Hdom_mem_inters Hdisj_mem_oea_inters Heq_mem_acc_tx' mem_rx mem_tx mem_all; subst ps_mem_in_trans.

              set rxs' := (<[v:=rx_state_v']> rxs).
              iApply ("IH" $! regs' ps_acc trans'' rxs' Htotal_rxs' Htotal_regs' Hsubset_mb Hsubset_acc Hnin_rx'' Hnin_tx'' with
                       "regs'' tx pgt_tx rx pgt_acc pgt_owned  trans_hpool_global tran_pgt_transferred retri_transferred rx_state rxs_global
                              tran_pgt_owned retri_owned mem [$transferred $rxs_transferred VMProp $VMProps]").
              { iExists _. iExact "VMProp". }
              exact SliceRxsWf0.
              exact SliceRxsWf0.
            }
            { (* wait, same *)
              iDestruct ("Hacc_regs" $! (ai ^+ 1)%f _ _ _ with "[PC R0 R1 R2]") as "[%regs' [%Htotal_regs' regs'']]"; iFrameAutoSolve.
              iDestruct (rx_states_merge_yield with "[$rxs_global $rxs_transferred $rx_state_v $rx_transferred]") as
                "(rxs_global & rxs_transferred)";auto.
              Unshelve. 2: exact SliceRxsWf0.
              pose proof (base_extra.is_total_gmap_insert rxs v rx_state_v' Htotal_rxs) as Htotal_rxs'.
              iDestruct (rx_states_split_zero_later with "[$rxs_global $rxs_transferred]") as "(rxs_global & rxs_transferred
                                 & (>rx_state & >[% (#rx'' & [% mem_rx])]))";auto.
              iAssert (⌜p_rx0 = p_rx⌝%I) with "[rx' rx'']" as %Hrx_eq. iApply (rx_agree with "rx'' rx'").
              iClear "rx''". subst p_rx0.

              set ps_mem_in_trans' := (accessible_in_trans_memory_pages i trans'').

              iDestruct (memory_pages_disj_singleton with "[$mem $mem_rx]") as %Hnin_rx''.
              iDestruct "mem_tx" as "[%mem_tx mem_tx]".
              iDestruct (memory_pages_disj_singleton with "[$mem $mem_tx]") as %Hnin_tx''.

              (* merge all memory pages together *)
              iDestruct (memory_pages_merge_mb with "[$mem mem_rx mem_tx]") as "mem";auto.
              iCombine "mem_tx mem_rx" as "mem". iExact "mem".
              clear Hdisj_rx_inters' Hdom_mem_inters Hdisj_mem_oea_inters Heq_mem_acc_tx' mem_rx mem_tx mem_all; subst ps_mem_in_trans.

              set rxs' := (<[v:=rx_state_v']> rxs).
              iApply ("IH" $! regs' ps_acc trans'' rxs' Htotal_rxs' Htotal_regs' Hsubset_mb Hsubset_acc Hnin_rx'' Hnin_tx'' with
                       "regs'' tx pgt_tx rx pgt_acc pgt_owned  trans_hpool_global tran_pgt_transferred retri_transferred rx_state rxs_global
                              tran_pgt_owned retri_owned mem [$transferred $rxs_transferred VMProp $VMProps]").
              { iExists _. iExact "VMProp". }
            }
            { (* send *)
              (* FIXME: Inhabited?? *)
              iDestruct (later_exist with "regs_rx") as "[%l regs_rx]".
              Unshelve. 2: { split. exists W0. solve_finz. solve_finz. }
                      iDestruct (later_exist with "regs_rx") as "[%j regs_rx]".
              Unshelve. 2: { split. exact V0. }
                      iEval(rewrite !later_sep) in "regs_rx".
              iDestruct ("regs_rx") as "(Φjv & >rxs_global & >%Hlookup_rxs & >(%& R1 & %Hdecode_r1') & >R2)".
              iDestruct ("Hacc_regs" $! (ai ^+ 1)%f _ _ _ with "[PC R0 R1 R2]") as "[%regs' [%Htotal_regs' regs'']]"; iFrameAutoSolve.
              iDestruct (rx_states_merge_send with "[$rxs_global $rxs_transferred $rx_state_v $rx_transferred $Φjv]") as
                "(rxs_global & rxs_transferred)";auto.

              assert (Htotal_rxs': base_extra.is_total_gmap (<[j:= Some (l,v)]>(<[v := rx_state_v']> rxs))).
              by repeat apply base_extra.is_total_gmap_insert.
              iDestruct (rx_states_split_zero_later with "[$rxs_global $rxs_transferred]") as "(rxs_global & rxs_transferred
                                 & (>rx_state & >[% (#rx'' & [% mem_rx])]))";auto.

              iAssert (⌜p_rx0 = p_rx⌝%I) with "[rx' rx'']" as %Hrx_eq. iApply (rx_agree with "rx'' rx'").
              iClear "rx''". subst p_rx0.

              set ps_mem_in_trans' := (accessible_in_trans_memory_pages i trans'').

              iDestruct (memory_pages_disj_singleton with "[$mem $mem_rx]") as %Hnin_rx''.
              iDestruct "mem_tx" as "[%mem_tx mem_tx]".
              iDestruct (memory_pages_disj_singleton with "[$mem $mem_tx]") as %Hnin_tx''.

              (* merge all memory pages together *)
              iDestruct (memory_pages_merge_mb with "[$mem mem_rx mem_tx]") as "mem";auto.
              iCombine "mem_tx mem_rx" as "mem". iExact "mem".
              clear Hdisj_rx_inters' Hdom_mem_inters Hdisj_mem_oea_inters Heq_mem_acc_tx' mem_rx mem_tx mem_all; subst ps_mem_in_trans.

              set rxs' := (<[j:= Some (l,v)]>(<[v:=rx_state_v']> rxs)).
              iApply ("IH" $! regs' ps_acc trans'' rxs' Htotal_rxs' Htotal_regs' Hsubset_mb Hsubset_acc Hnin_rx'' Hnin_tx'' with
                       "regs'' tx pgt_tx rx pgt_acc pgt_owned  trans_hpool_global tran_pgt_transferred retri_transferred rx_state rxs_global
                              tran_pgt_owned retri_owned mem [$transferred $rxs_transferred VMProp $VMProps]").
              { iExists _. iExact "VMProp". }
            }
          }
          {

            iAssert (⌜mem_inters_a ##ₘ mem_inters_b⌝%I )with "[mem_inters_a mem_inters_b]" as "%Hdisj_inters_ab".
            {
              iDestruct "mem_inters_a" as "[%Hdom_mem_inters_a _]".
              iDestruct "mem_inters_b" as "[%Hdom_mem_inters_b _]".
              iPureIntro.
              apply map_disjoint_dom.
              rewrite Hdom_mem_inters_a Hdom_mem_inters_b.
              apply set_of_addr_disj.
              set_solver + Hsplit_trans_disj.
            }
            assert (Hsubseteq_mem_acc: mem_inters_b ⊆ mem_acc_tx).
            rewrite Heq_mem_acc_tx'.
            apply map_union_subseteq_r'. done.
            apply map_union_subseteq_r'. done.
            apply map_union_subseteq_r. done.
            rewrite map_subseteq_spec in Hsubseteq_mem_acc.
            apply elem_of_set_of_addr_tpa in Hnin_ps_only.
            iDestruct "mem_inters_b" as "[%Hdom_mem_inters_b mem_inters_b]".
            rewrite -Hdom_mem_inters_b in Hnin_ps_only.
            rewrite elem_of_dom in Hnin_ps_only.
            destruct Hnin_ps_only as [? Hlookup_mem_ai'].
            specialize (Hsubseteq_mem_acc ai _ Hlookup_mem_ai').
            rewrite Hlookup_mem_ai in Hsubseteq_mem_acc.
            inversion Hsubseteq_mem_acc.
            subst x. clear Hsubseteq_mem_acc.

            iDestruct (memory_pages_union' with "[mem_inters_a $mem_rest_a]") as "mem_a".
            { iExists mem_inters_a. iExact "mem_inters_a". }
            iEval (rewrite union_comm_L) in "mem_a".
            rewrite (H (only v trans)). 2: apply only_subseteq.

            (* getting instruction from [mem_inters_b] *)
            iDestruct (mem_big_sepM_split mem_inters_b Hlookup_mem_ai' with "mem_inters_b") as "[mem_instr Hacc_mem]".

            iApply (run ai v (transaction_hpool_global_transferred trans ∗
                                big_sepSS_singleton (set_of_vmids ∖ {[i]}) v (Φ_t trans) ∗
                                transaction_pagetable_entries_transferred i (only v trans) ∗
                                retrievable_transaction_transferred i (only v trans) ∗
                                (∃ mem1 : mem, memory_pages (transferred_memory_pages i (only v trans)) mem1) ∗
                                rx_states_global (delete v rxs) ∗
                                (∀ rs : option (Addr * VMID), ⌜rxs !! v = Some rs⌝ -∗ rx_state_match v rs ∗ Φ_r v rs v)
                      )%I (vmprop_zero v Φ_t Φ_r trans rxs)
                     with "[PC R0 R1 R2 pgt_acc $tx mem_instr rxs_global VMProp VMProp_v
                           trans_hpool_global tran_pgt_transferred_only_v retri_transferred_only_v mem_a transferred_only_v rx_state_v]"); iFrameAutoSolve.
            {
              iSplitL "VMProp_v". iNext. iExact "VMProp_v".
              iSplitL "VMProp". iNext. iExact "VMProp".
              iSplitL "R2".
              {
                iNext. iIntros "((PC & instr & pgt_acc & _ & R0 & R1) & (trans_hpool_global & transferred_only_v &
                      tran_pgt_transferred_only_v & retri_transferred_only_v & mem_a & rxs_global
                      & rx_state_v) & vmprop0)".
                rewrite vmprop_unknown_eq.
                iSplitR "PC pgt_acc instr".
                iExists trans, rxs.
                iFrame "trans_hpool_global rx_state_v rxs_global vmprop0".
                iSplitL "transferred_only_v tran_pgt_transferred_only_v retri_transferred_only_v mem_a".
                rewrite /big_sepSS_singleton.
                case_decide. 2:{ pose proof (elem_of_set_of_vmids v). set_solver + H0 H1 n. }
                case_decide. 2:{ pose proof (elem_of_set_of_vmids v). set_solver + H0 H1 n. }
                iDestruct "transferred_only_v" as "[$ transferred_only_v]".
                iApply (big_sepS_delete _ _ i).
                pose proof (elem_of_set_of_vmids i). set_solver + H2 n. clear H0 H1.
                assert (set_of_vmids ∖ {[v]} ∖ {[i]} = set_of_vmids ∖ {[i]} ∖ {[v]}) as ->. set_solver + n.
                iFrame "transferred_only_v".
                rewrite 2?HΦt. 2: left;done. 2: right;done.
                rewrite /slice_transfer_all.
                iDestruct (transaction_pagetable_entries_transferred_only_equiv with "tran_pgt_transferred_only_v") as "[$ $]";auto.
                iDestruct (retrievable_transaction_transferred_only_equiv with "retri_transferred_only_v") as "[$ $]";auto.
                iDestruct ("mem_a") as "mem".
                iApply (transferred_memory_only_equiv). auto. auto. auto.
                iFrame "mem".
                iSplitL "R0". iExists _. iSplitL. iExact "R0". done.
                iSplitL "R1". iExists _. iSplitL. iExact "R1". done.
                iSplitL "R2". iExists _. iExact "R2". done.
                iCombine "PC pgt_acc instr" as "R". iExact "R".
              }
              {
                iNext. iFrame "trans_hpool_global rxs_global rx_state_v". iFrame.
              }
            }
            iNext. iIntros "((PC & pgt_acc & instr) & VMProp) HHolds". iSimpl in "HHolds".

            iDestruct (VMProp_holds_agree i with "[$HHolds $VMProp]") as "[Hres VMProp]".
            iEval (rewrite /vmprop_zero /vmprop_zero_pre) in "Hres".
            iEval (rewrite later_exist) in "Hres". iDestruct "Hres" as (trans') "Hres".
            iEval (rewrite later_exist) in "Hres". iDestruct "Hres" as (rx_state_v') "Hres".
            iEval (rewrite 5!later_sep) in "Hres".
            iDestruct "Hres" as "(>%Hdisj' & >trans_hpool_global & transferred_only & >rx_state_v & rx_transferred & regs_rx & VMProp_v)".

            iDestruct (slice_preserve_except v _ (only v trans' ∪ except v trans) trans with "transferred_except_v") as "transferred_except_v".
            symmetry. rewrite -(except_only_union v (except v trans) trans'). apply except_idemp.
            rewrite -except_idemp;done.

            iDestruct (big_sepSS_singletion_union _ i with "transferred_only") as "[transferred_only_v transferred_i_v]".
            apply elem_of_set_of_vmids.

            assert (Htemp: (set_of_vmids ∖ {[i]}) = (set_of_vmids ∖ {[i]} ∖ {[v]} ∪ {[v]})).
            rewrite difference_union_L.
            pose proof (elem_of_set_of_vmids v).
            set_solver + i n H0.
            iDestruct (big_sepSS_union_singleton with "[transferred_except_v transferred_only_v]") as "transferred".
            2:{
              iSplitL "transferred_except_v".
              iDestruct (later_intro with "transferred_except_v") as "transferred_except_v".
              rewrite big_sepSS_except_later.
              iExact "transferred_except_v".
              iEval (rewrite Htemp) in "transferred_only_v".
              rewrite big_sepSS_singleton_later.
              iExact "transferred_only_v".
            } set_solver +.
            iDestruct (get_trans_ps_disj with "trans_hpool_global") as %Htrans_disj'.
            iDestruct (get_trans_neq with "trans_hpool_global") as %Htrans_neq'.

            rewrite -Htemp.

            iEval (rewrite big_sepSS_singleton_later /big_sepSS_singleton ) in "transferred_i_v".
            case_decide. set_solver + i n H0.
            assert (({[i]} ∖ {[v]}) = ({[i]}:gset _)) as ->. set_solver + i n H0.
            rewrite big_sepS_singleton.
            rewrite 2?HΦt. 2: left;done. 2: right;done.
            iDestruct "transferred_i_v" as "[>(tran_pgt_transferred_i_v & retri_transferred_i_v & transferred_mem_i_v) >(tran_pgt_transferred_v_i & retri_transferred_v_i & transferred_mem_v_i)]".
            iCombine "tran_pgt_transferred_v_i tran_pgt_transferred_i_v" as "tran_pgt_transferred".
            pose proof (except_only_union v (except v trans) trans') as Htemp'.
            feed specialize Htemp'. rewrite -except_idemp //.
            iDestruct (transaction_pagetable_entries_transferred_only_equiv i with "tran_pgt_transferred") as "tran_pgt_transferred_only_v";auto.
            iEval(rewrite except_idemp Htemp') in "tran_pgt_transferred_except_v".
            iDestruct(transaction_pagetable_entries_transferred_split with "[$tran_pgt_transferred_only_v $tran_pgt_transferred_except_v ]") as "tran_pgt_transferred".

            iCombine "retri_transferred_v_i retri_transferred_i_v" as "retri_transferred".
            iDestruct (retrievable_transaction_transferred_only_equiv i with "retri_transferred") as "retri_transferred_only_v"; auto.
            iEval(rewrite except_idemp Htemp') in "retri_transferred_except_v".
            iDestruct(retrievable_transaction_transferred_split with "[$retri_transferred_only_v $retri_transferred_except_v ]") as "retri_transferred".

            iCombine "transferred_mem_i_v transferred_mem_v_i" as "transferred_mem".
            iDestruct (transferred_memory_only_equiv i v with "transferred_mem") as "transferred_memory_only_v";auto.
            iDestruct ("Hacc_mem" with "instr") as "mem_inters_b".
            iDestruct (memory_pages_union' with "[mem_inters_b $mem_rest_b]") as "mem_b".
            { iExists mem_inters_b.
              iSplit.
              iPureIntro;done. iFrame.
            }
            iEval (rewrite union_comm_L) in "mem_b".
            rewrite (H (except v trans)). 2: apply except_subseteq.

            iEval (rewrite except_idemp Htemp') in "mem_b".

            iDestruct (transferred_memory_split i with "[mem_b $transferred_memory_only_v]") as "mem_transferred";auto.

            iDestruct (get_trans_rel_secondary with "[$trans_hpool_global $retri_transferred $tran_pgt_owned $retri_owned]") as "%trans_rel".
            erewrite (trans_rel_secondary_currently_accessible_memory_pages);eauto.
            erewrite (trans_rel_secondary_currently_accessible_memory_pages) in Hsubset_acc;eauto.
            iDestruct (trans_rel_secondary_transaction_pagetable_entries_owned with "tran_pgt_owned") as "tran_pgt_owned";eauto.
            iDestruct (trans_rel_secondary_retrieved_transaction_owned with "retri_owned") as "retri_owned";eauto.

            set trans'' := (only v trans' ∪ (except v trans)).

            iAssert (⌜(ps_acc ∖ {[p_tx]} ∖ ({[p_rx]} ∪ transferred_memory_pages i trans)
                       = ps_acc ∖ {[p_rx; p_tx]} ∖ transferred_memory_pages i trans'')⌝)%I as "%H'".
            {
              iDestruct (get_valid_accessible_in_trans_memory_pages with "[$trans_hpool_global $pgt_owned]") as %Hvalid_acc_in_tran'.
              set_solver + Hsubset_acc.
              iPureIntro.
              rewrite difference_difference_L.
              rewrite union_assoc_L (union_comm_L {[p_tx]}).
              rewrite -(difference_difference_L _ {[p_rx; p_tx]}).
              apply acc_transferred_memory_pages_difference;auto.
              erewrite <-(trans_rel_secondary_currently_accessible_memory_pages _ trans trans'') in Hsubset_acc;eauto.
              rewrite union_comm_L.
              exact Hsubset_acc.
            }
            iAssert (∃ mem_all : mem, memory_pages (ps_acc ∖ {[p_rx; p_tx]} ∪ accessible_in_trans_memory_pages i trans'') mem_all)%I
              with "[mem_oea mem_transferred]" as (?) "mem".
            {
              iAssert(∃ m: mem, memory_pages (ps_acc ∖ {[p_tx]} ∖ ({[p_rx]} ∪ transferred_memory_pages i trans)) m)%I with "[mem_oea]" as "mem_oea".
              iExists _. iSplit; done.
              rewrite H'.
              iDestruct(memory_pages_union' with "[$mem_oea $mem_transferred]") as "mem". iFrame.
              rewrite acc_accessible_in_trans_memory_pages_union;auto.
              rewrite union_comm_L //.
            }

            clear Htrans_disj Htrans_neq H'.
            iDestruct ("VMProps_acc" with "VMProp_v") as "VMProps".
            rewrite -big_sepSS_later.
            iEval(rewrite /return_reg_rx later_or !later_sep) in "regs_rx".
            iDestruct ("regs_rx") as "[(>[R0| [R0 %Hrxstate_eq]] & >rxs_global & >R1 & >[% R2])
                            | (>R0 & regs_rx)]".
            { (* yield *)
              iDestruct ("Hacc_regs" $! (ai ^+ 1)%f _ _ _ with "[PC R0 R1 R2]") as "[%regs' [%Htotal_regs' regs'']]"; iFrameAutoSolve.
              iDestruct (rx_states_merge_yield with "[$rxs_global $rxs_transferred $rx_state_v $rx_transferred]") as
                "(rxs_global & rxs_transferred)";auto.
              Unshelve. 2: exact SliceRxsWf0.
              pose proof (base_extra.is_total_gmap_insert rxs v rx_state_v' Htotal_rxs) as Htotal_rxs'.
              iDestruct (rx_states_split_zero_later with "[$rxs_global $rxs_transferred]") as "(rxs_global & rxs_transferred
                                 & (>rx_state & >[% (#rx'' & [% mem_rx])]))";auto.
              iAssert (⌜p_rx0 = p_rx⌝%I) with "[rx' rx'']" as %Hrx_eq. iApply (rx_agree with "rx'' rx'").
              iClear "rx''". subst p_rx0.

              set ps_mem_in_trans' := (accessible_in_trans_memory_pages i trans'').

              iDestruct (memory_pages_disj_singleton with "[$mem $mem_rx]") as %Hnin_rx''.
              iDestruct "mem_tx" as "[%mem_tx mem_tx]".
              iDestruct (memory_pages_disj_singleton with "[$mem $mem_tx]") as %Hnin_tx''.

              (* merge all memory pages together *)
              iDestruct (memory_pages_merge_mb with "[$mem mem_rx mem_tx]") as "mem";auto.
              iCombine "mem_tx mem_rx" as "mem". iExact "mem".
              clear Hdisj_rx_inters' Hdom_mem_inters Hdisj_mem_oea_inters Heq_mem_acc_tx' mem_rx mem_tx mem_all; subst ps_mem_in_trans.

              set rxs' := (<[v:=rx_state_v']> rxs).
              iApply ("IH" $! regs' ps_acc trans'' rxs' Htotal_rxs' Htotal_regs' Hsubset_mb Hsubset_acc Hnin_rx'' Hnin_tx'' with
                       "regs'' tx pgt_tx rx pgt_acc pgt_owned  trans_hpool_global tran_pgt_transferred retri_transferred rx_state rxs_global
                              tran_pgt_owned retri_owned mem [$transferred $rxs_transferred VMProp $VMProps]").
              { iExists _. iExact "VMProp". }
              exact SliceRxsWf0.
            }
            { (* wait, same *)
              iDestruct ("Hacc_regs" $! (ai ^+ 1)%f _ _ _ with "[PC R0 R1 R2]") as "[%regs' [%Htotal_regs' regs'']]"; iFrameAutoSolve.
              iDestruct (rx_states_merge_yield with "[$rxs_global $rxs_transferred $rx_state_v $rx_transferred]") as
                "(rxs_global & rxs_transferred)";auto.
              Unshelve. 2: exact SliceRxsWf0.
              pose proof (base_extra.is_total_gmap_insert rxs v rx_state_v' Htotal_rxs) as Htotal_rxs'.
              iDestruct (rx_states_split_zero_later with "[$rxs_global $rxs_transferred]") as "(rxs_global & rxs_transferred
                                 & (>rx_state & >[% (#rx'' & [% mem_rx])]))";auto.
              iAssert (⌜p_rx0 = p_rx⌝%I) with "[rx' rx'']" as %Hrx_eq. iApply (rx_agree with "rx'' rx'").
              iClear "rx''". subst p_rx0.

              set ps_mem_in_trans' := (accessible_in_trans_memory_pages i trans'').

              iDestruct (memory_pages_disj_singleton with "[$mem $mem_rx]") as %Hnin_rx''.
              iDestruct "mem_tx" as "[%mem_tx mem_tx]".
              iDestruct (memory_pages_disj_singleton with "[$mem $mem_tx]") as %Hnin_tx''.

              (* merge all memory pages together *)
              iDestruct (memory_pages_merge_mb with "[$mem mem_rx mem_tx]") as "mem";auto.
              iCombine "mem_tx mem_rx" as "mem". iExact "mem".
              clear Hdisj_rx_inters' Hdom_mem_inters Hdisj_mem_oea_inters Heq_mem_acc_tx' mem_rx mem_tx mem_all; subst ps_mem_in_trans.

              set rxs' := (<[v:=rx_state_v']> rxs).
              iApply ("IH" $! regs' ps_acc trans'' rxs' Htotal_rxs' Htotal_regs' Hsubset_mb Hsubset_acc Hnin_rx'' Hnin_tx'' with
                       "regs'' tx pgt_tx rx pgt_acc pgt_owned  trans_hpool_global tran_pgt_transferred retri_transferred rx_state rxs_global
                              tran_pgt_owned retri_owned mem [$transferred $rxs_transferred VMProp $VMProps]").
              { iExists _. iExact "VMProp". }
            }
            { (* send *)
              (* FIXME: Inhabited?? *)
              iDestruct (later_exist with "regs_rx") as "[%l regs_rx]".
              Unshelve. 2: { split. exists W0. solve_finz. solve_finz. }
                      iDestruct (later_exist with "regs_rx") as "[%j regs_rx]".
              Unshelve. 2: { split. exact V0. }
                      iEval(rewrite !later_sep) in "regs_rx".
              iDestruct ("regs_rx") as "(Φjv & >rxs_global & >%Hlookup_rxs & >(%& R1 & %Hdecode_r1') & >R2)".
              iDestruct ("Hacc_regs" $! (ai ^+ 1)%f _ _ _ with "[PC R0 R1 R2]") as "[%regs' [%Htotal_regs' regs'']]"; iFrameAutoSolve.
              iDestruct (rx_states_merge_send with "[$rxs_global $rxs_transferred $rx_state_v $rx_transferred $Φjv]") as
                "(rxs_global & rxs_transferred)";auto.

              assert (Htotal_rxs': base_extra.is_total_gmap (<[j:= Some (l,v)]>(<[v := rx_state_v']> rxs))).
              by repeat apply base_extra.is_total_gmap_insert.
              iDestruct (rx_states_split_zero_later with "[$rxs_global $rxs_transferred]") as "(rxs_global & rxs_transferred
                                 & (>rx_state & >[% (#rx'' & [% mem_rx])]))";auto.

              iAssert (⌜p_rx0 = p_rx⌝%I) with "[rx' rx'']" as %Hrx_eq. iApply (rx_agree with "rx'' rx'").
              iClear "rx''". subst p_rx0.

              set ps_mem_in_trans' := (accessible_in_trans_memory_pages i trans'').

              iDestruct (memory_pages_disj_singleton with "[$mem $mem_rx]") as %Hnin_rx''.
              iDestruct "mem_tx" as "[%mem_tx mem_tx]".
              iDestruct (memory_pages_disj_singleton with "[$mem $mem_tx]") as %Hnin_tx''.

              (* merge all memory pages together *)
              iDestruct (memory_pages_merge_mb with "[$mem mem_rx mem_tx]") as "mem";auto.
              iCombine "mem_tx mem_rx" as "mem". iExact "mem".
              clear Hdisj_rx_inters' Hdom_mem_inters Hdisj_mem_oea_inters Heq_mem_acc_tx' mem_rx mem_tx mem_all; subst ps_mem_in_trans.

              set rxs' := (<[j:= Some (l,v)]>(<[v:=rx_state_v']> rxs)).
              iApply ("IH" $! regs' ps_acc trans'' rxs' Htotal_rxs' Htotal_regs' Hsubset_mb Hsubset_acc Hnin_rx'' Hnin_tx'' with
                       "regs'' tx pgt_tx rx pgt_acc pgt_owned  trans_hpool_global tran_pgt_transferred retri_transferred rx_state rxs_global
                              tran_pgt_owned retri_owned mem [$transferred $rxs_transferred VMProp $VMProps]").
              { iExists _. iExact "VMProp". }
            }
          }
        }
      }
    }
  }

  pose proof (Htotal_regs R2) as [r2 Hlookup_reg_R2].
  iDestruct (reg_big_sepM_split_upd4 i Hlookup_PC Hlookup_reg_R0 Hlookup_reg_R1 Hlookup_reg_R2 with "[$regs]")
    as "(PC & R0 & R1 & R2 & Hacc_regs)";eauto.
  iDestruct (mem_big_sepM_split mem_acc_tx Hlookup_mem_ai with "mem_acc_tx") as "[mem_instr Hacc_mem_acc]".

  iApply (run_invalid_vmid ai with "[PC R0 R1 R2 pgt_acc tx mem_instr]"); iFrameAutoSolve.
  iNext. iIntros "(PC & mem_instr & pgt_acc & tx & R0 & R1 & R2) _".
  iDestruct ("Hacc_regs" $! (ai ^+ 1)%f _ _ with "[$PC $R0 $R1 $R2]") as "[%regs' [%Htotal_regs' regs]]".
  iDestruct ("Hacc_mem_acc" with "[$mem_instr]") as "mem_acc_tx".
  iApply ("IH" $! regs' ps_acc trans rxs Htotal_rxs Htotal_regs' Hsubset_mb Hsubset_acc Hnin_rx Hnin_tx with
           "regs tx pgt_tx rx pgt_acc pgt_owned  trans_hpool_global tran_pgt_transferred retri rx_state rxs_global
                              tran_pgt_owned retri_owned [mem_rest mem_acc_tx mem_tx] [Running]").
  {
    iDestruct (memory_pages_split_singleton' p_tx ps_acc with "[mem_acc_tx $mem_tx]") as "mem_acc". set_solver + Hsubset_mb.
    iExists mem_acc_tx;by iFrame "mem_acc_tx".
    iApply (memory_pages_split_diff' _ ps_acc with "[$mem_rest $mem_acc]").
    set_solver +.
  }
  { iDestruct "Running" as "($&?&$&$)". rewrite <-big_sepS_later. iFrame. }
  Unshelve. exact SliceRxsWf0.
Qed.

End ftlr_run_prim.
