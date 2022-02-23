From iris.proofmode Require Import tactics.
From machine_program_logic.program_logic Require Import weakestpre.
From HypVeri.lang Require Import lang trans_extra.
From HypVeri.algebra Require Import base pagetable mem trans.
From HypVeri.rules Require Import mem_send.
From HypVeri.logrel Require Import logrel logrel_extra.
From HypVeri Require Import proofmode.
Import uPred.

Section ftlr_share.
  Context `{hypconst:HypervisorConstants}.
  Context `{hypparams:!HypervisorParameters}.
  Context `{vmG: !gen_VMG Σ}.

Lemma ftlr_share {i trans' mem_acc_tx ai regs ps_acc p_tx p_rx ps_na instr trans rx_state r0}:
  base_extra.is_total_gmap regs ->
  {[p_tx; p_rx]} ⊆ ps_acc ->
  i ≠ V0 ->
  ps_na ## ps_acc ∪ pages_in_trans (trans_memory_in_trans i trans) ->
  p_rx ∉ ps_acc ∖ {[p_rx; p_tx]} ∪ pages_in_trans (trans_memory_in_trans i trans) ->
  p_tx ∉ ps_acc ∖ {[p_rx; p_tx]} ∪ pages_in_trans (trans_memory_in_trans i trans) ->
  regs !! PC = Some ai ->
  tpa ai ∈ ps_acc ->
  tpa ai ≠ p_tx ->
  dom (gset Addr) mem_acc_tx = set_of_addr (ps_acc ∖ {[p_tx]}) ->
  tpa ai ∈ ps_acc ∖ {[p_tx]} ->
  mem_acc_tx !! ai = Some instr ->
  decode_instruction instr = Some Hvc ->
  regs !! R0 = Some r0 ->
  decode_hvc_func r0 = Some Share ->
  p_tx ≠ p_rx ->
  ⊢
  ▷ (∀ (a : gmap reg_name Addr) (a0 : gset PID) (a1 : gmap Addr transaction) (a2 : option (Addr * VMID)),
          ⌜base_extra.is_total_gmap a⌝
            → ⌜{[p_tx; p_rx]} ⊆ a0⌝
              → ⌜ps_na ## a0 ∪ pages_in_trans (trans_memory_in_trans i a1)⌝
                → ⌜p_rx ∉ a0 ∖ {[p_rx; p_tx]} ∪ pages_in_trans (trans_memory_in_trans i a1)⌝
                  → ⌜p_tx ∉ a0 ∖ {[p_rx; p_tx]} ∪ pages_in_trans (trans_memory_in_trans i a1)⌝
                    → ([∗ map] r↦w ∈ a, r @@ i ->r w) -∗
                      TX@i:=p_tx -∗
                      p_tx -@O> - ∗ p_tx -@E> true -∗
                      i -@{1 / 2}A> a0 -∗
                      i -@{1 / 2}A> a0 -∗
                      LB@ i := [ps_na] -∗
                      transaction_hpool_global_transferred a1 -∗
                      transaction_pagetable_entries_transferred i a1 -∗
                      retrieval_entries_transferred i a1 -∗
                      R0 @@ V0 ->r encode_hvc_func Run -∗
                      R1 @@ V0 ->r encode_vmid i -∗
                      (∃ r2 : Addr, R2 @@ V0 ->r r2) -∗
                      RX_state@i:= a2 -∗
                      mailbox.rx_page i p_rx -∗
                      rx_pages (list_to_set list_of_vmids ∖ {[i]}) -∗
                      ▷ VMProp V0 (vmprop_zero i p_rx) (1 / 2) -∗
                      VMProp i (vmprop_unknown i p_tx p_rx trans') 1 -∗
                      transaction_pagetable_entries_owned i a1 -∗
                      pagetable_entries_excl_owned i (a0 ∖ {[p_rx; p_tx]} ∖ pages_in_trans a1) -∗
                      retrieval_entries_owned i a1 -∗
                      (∃ mem : lang.mem, memory_pages (a0 ∪ pages_in_trans (trans_memory_in_trans i a1)) mem) -∗
                      WP ExecI @ i {{ _, True }}) -∗
   ([∗ map] r↦w ∈ regs, r @@ i ->r w) -∗
   TX@i:=p_tx -∗
   p_tx -@O> - ∗ p_tx -@E> true -∗
   i -@{1 / 2}A> ps_acc -∗
   i -@{1 / 2}A> ps_acc -∗
   LB@ i := [ps_na] -∗
   transaction_hpool_global_transferred trans -∗
   transaction_pagetable_entries_transferred i trans -∗
   retrieval_entries_transferred i trans -∗
   R0 @@ V0 ->r encode_hvc_func Run -∗
   R1 @@ V0 ->r encode_vmid i -∗
   (∃ r2 : Addr, R2 @@ V0 ->r r2) -∗
   RX_state@i:= rx_state -∗
   mailbox.rx_page i p_rx -∗
   rx_pages (list_to_set list_of_vmids ∖ {[i]}) -∗
   ▷ VMProp V0 (vmprop_zero i p_rx) (1 / 2) -∗
   VMProp i (vmprop_unknown i p_tx p_rx trans') 1 -∗
   transaction_pagetable_entries_owned i trans -∗
   pagetable_entries_excl_owned i (ps_acc ∖ {[p_rx; p_tx]} ∖ pages_in_trans trans) -∗
   retrieval_entries_owned i trans -∗
   (∃ mem1 : mem, memory_pages ((ps_acc ∪ (pages_in_trans (trans_memory_in_trans i trans))) ∖ ps_acc) mem1) -∗
   ([∗ map] k↦v ∈ mem_acc_tx, k ->a v) -∗
   (∃ mem2 : mem, memory_page p_tx mem2) -∗
   SSWP ExecI @ i {{ bm, (if bm.1 then VMProp_holds i (1 / 2) else True) -∗ WP bm.2 @ i {{ _, True }} }}.
  Proof.
    iIntros (Htotal_regs Hsubset_mb Hneq_0 Hdisj_na Hnin_rx Hnin_tx Hlookup_PC Hin_ps_acc Hneq_ptx Hdom_mem_acc_tx Hin_ps_acc_tx
                         Hlookup_mem_ai Heqn  Hlookup_reg_R0 Hdecode_hvc).
    iIntros (Hneq_mb) "IH regs tx pgt_tx pgt_acc pgt_acc' LB trans_hpool_global tran_pgt_transferred retri R0z R1z R2z rx_state rx other_rx prop0
             propi tran_pgt_owned pgt_owned retri_owned mem_rest mem_acc_tx mem_tx".
    set ps_mem_in_trans := (pages_in_trans (trans_memory_in_trans i trans)).
    pose proof (Htotal_regs R1) as[r1 Hlookup_reg_R1].
    pose proof (Htotal_regs R2) as[r2 Hlookup_reg_R2].
    iDestruct (reg_big_sepM_split_upd4 i Hlookup_PC Hlookup_reg_R0 Hlookup_reg_R1 Hlookup_reg_R2 with "[$regs]")
      as "(PC & R0 & R1 & R2 & Hacc_regs)";eauto.
    iDestruct (mem_big_sepM_split mem_acc_tx Hlookup_mem_ai with "mem_acc_tx") as "[mem_instr Hacc_mem_acc_tx]".

    destruct (decide (page_size < r1)%Z).
    { (* the length of msg exceeds [page_size] *)
      iApply (mem_send_invalid_len ai with "[PC mem_instr pgt_acc' R0 R1 R2 tx]");iFrameAutoSolve.
      exact Hdecode_hvc.
      simpl; reflexivity.
      iNext.
      iIntros "(PC & mem_instr & pgt_acc' & R0 & R1 & R2 & tx) _".
      iDestruct ("Hacc_regs" $! (ai ^+ 1)%f with "[$ PC $ R0 $ R1 $ R2]") as (regs') "[%Htotal_regs' regs]".

      iDestruct ("Hacc_mem_acc_tx" with "[$mem_instr]") as "mem_acc_tx".
      iApply ("IH" $! _ ps_acc trans _ Htotal_regs' Hsubset_mb Hdisj_na Hnin_rx Hnin_tx with "regs tx pgt_tx pgt_acc pgt_acc' LB trans_hpool_global
                            tran_pgt_transferred retri R0z R1z R2z rx_state rx other_rx prop0 propi tran_pgt_owned pgt_owned retri_owned [mem_rest mem_acc_tx mem_tx]
                            ").
      {
        iDestruct (memory_pages_split_singleton' p_tx ps_acc with "[mem_acc_tx $mem_tx]") as "mem_acc". set_solver + Hsubset_mb.
        iExists mem_acc_tx;by iFrame "mem_acc_tx".
        iApply (memory_pages_split_diff' _ ps_acc with "[$mem_rest $mem_acc]").
        set_solver +.
      }
    }
    iDestruct "mem_tx" as (mem_tx) "mem_tx".
    destruct (parse_transaction_descriptor mem_tx p_tx (Z.to_nat r1))  as [tran_des|] eqn:Heq_parse_tran.
    2:{ (* cannot parse the msg as a descriptor *)
      iApply (mem_send_invalid_msg ai with "[PC mem_instr pgt_acc' R0 R1 R2 tx mem_tx]");iFrameAutoSolve.
      exact Hdecode_hvc.
      simpl; reflexivity.
      lia.
      exact Heq_parse_tran.
      iFrame.
      iNext.
      iIntros "(PC & mem_instr & pgt_acc' & R0 & R1 & R2 & tx & mem_tx) _".
      iDestruct ("Hacc_regs" $! (ai ^+ 1)%f with "[$ PC $ R0 $ R1 $ R2]") as (regs') "[%Htotal_regs' regs]".

      iDestruct ("Hacc_mem_acc_tx" with "[$mem_instr]") as "mem_acc_tx".
      iApply ("IH" $! _ ps_acc trans _ Htotal_regs' Hsubset_mb Hdisj_na Hnin_rx Hnin_tx with "regs tx pgt_tx pgt_acc pgt_acc' LB trans_hpool_global
                            tran_pgt_transferred retri R0z R1z R2z rx_state rx other_rx prop0 propi tran_pgt_owned pgt_owned retri_owned [mem_rest mem_acc_tx mem_tx] ").
      {
        iDestruct (memory_pages_split_singleton' p_tx ps_acc with "[mem_acc_tx mem_tx]") as "mem_acc". set_solver + Hsubset_mb.
        iSplitL "mem_acc_tx".
        iExists mem_acc_tx;by iFrame "mem_acc_tx".
        iExists mem_tx;by iFrame "mem_tx".
        iApply (memory_pages_split_diff' _ ps_acc with "[$mem_rest $mem_acc]").
        set_solver +.
      }
    }

    destruct (validate_transaction_descriptor i tran_des) eqn:Hvalid_tran_des.
    2:{ (* validation of descriptor fails, apply [mem_send_invalid_des] *)
      iApply (mem_send_invalid_des ai with "[PC mem_instr pgt_acc' R0 R1 R2 tx mem_tx]");iFrameAutoSolve.
      exact Hdecode_hvc.
      simpl; reflexivity.
      lia.
      exact Heq_parse_tran.
      done.
      iFrame.
      iNext.
      iIntros "(PC & mem_instr & pgt_acc' & R0 & R1 & R2 & tx & mem_tx) _".
      iDestruct ("Hacc_regs" $! (ai ^+ 1)%f with "[$ PC $ R0 $ R1 $ R2]") as (regs') "[%Htotal_regs' regs]".

      iDestruct ("Hacc_mem_acc_tx" with "[$mem_instr]") as "mem_acc_tx".
      iApply ("IH" $! _ ps_acc trans _ Htotal_regs' Hsubset_mb Hdisj_na Hnin_rx Hnin_tx with "regs tx pgt_tx pgt_acc pgt_acc' LB trans_hpool_global
                            tran_pgt_transferred retri R0z R1z R2z rx_state rx other_rx prop0 propi tran_pgt_owned pgt_owned retri_owned [mem_rest mem_acc_tx mem_tx]").
      {
        iDestruct (memory_pages_split_singleton' p_tx ps_acc with "[mem_acc_tx mem_tx]") as "mem_acc". set_solver + Hsubset_mb.
        iSplitL "mem_acc_tx".
        iExists mem_acc_tx;by iFrame "mem_acc_tx".
        iExists mem_tx;by iFrame "mem_tx".
        iApply (memory_pages_split_diff' _ ps_acc with "[$mem_rest $mem_acc]").
        set_solver +.
      }
    }
    pose proof (Hvalid_tran_des) as Hvalid_trans_des'.
    apply validate_descriptor in Hvalid_tran_des as [j [ps_share [-> Hneq_sr]]].
    destruct (decide (ps_share ⊆ ps_acc)) as [Hsubseteq_share | Hnsubseteq_share].
    2:{ (* no access to at least one page in ps_share, apply [mem_send_not_acc] *)
      apply not_subseteq in Hnsubseteq_share as [p [Hin_p_share Hnin_p_acc]].
      iDestruct (access_split with "[$ pgt_acc $ pgt_acc' ]") as "pgt_acc".
      iApply (mem_send_not_acc ai p with "[PC mem_instr pgt_acc R0 R1 R2 tx mem_tx]");iFrameAutoSolve.
      exact Hdecode_hvc.
      simpl; reflexivity.
      lia.
      exact Heq_parse_tran.
      done.
      simpl; exact Hin_p_share.
      iFrame.
      iNext.
      iIntros "(PC & mem_instr  & R0 & R1 & R2 & tx & mem_tx & pgt_acc) _".
      iDestruct ("Hacc_regs" $! (ai ^+ 1)%f with "[$ PC $ R0 $ R1 $ R2]") as (regs') "[%Htotal_regs' regs]".
      iDestruct ("Hacc_mem_acc_tx" with "[$mem_instr]") as "mem_acc_tx".
      iDestruct (access_split with "pgt_acc") as "[pgt_acc pgt_acc']".

      iApply ("IH" $! _ ps_acc trans _ Htotal_regs' Hsubset_mb Hdisj_na Hnin_rx Hnin_tx with "regs tx pgt_tx pgt_acc pgt_acc' LB trans_hpool_global
                            tran_pgt_transferred retri R0z R1z R2z rx_state rx other_rx prop0 propi tran_pgt_owned pgt_owned retri_owned [mem_rest mem_acc_tx mem_tx]").
      {
        iDestruct (memory_pages_split_singleton' p_tx ps_acc with "[mem_acc_tx mem_tx]") as "mem_acc". set_solver + Hsubset_mb.
        iSplitL "mem_acc_tx".
        iExists mem_acc_tx;by iFrame "mem_acc_tx".
        iExists mem_tx;by iFrame "mem_tx".
        iApply (memory_pages_split_diff' _ ps_acc with "[$mem_rest $mem_acc]").
        set_solver +.
      }
    }
    destruct (decide (p_tx ∈ ps_share)) as [Hin_ptx_share | Hnin_ptx_share].
    { (* tx is not owned by i, apply [mem_send_not_owned] *)
      iDestruct "pgt_tx" as "[own_tx excl_tx]".
      iApply (mem_send_not_owned ai _ (p_tx -@O> -)%I with "[PC mem_instr pgt_acc' R0 R1 R2 tx mem_tx own_tx]");iFrameAutoSolve.
      exact Hdecode_hvc.
      simpl; reflexivity.
      lia.
      exact Heq_parse_tran.
      done.
      simpl; exact Hin_ptx_share.
      iFrame.
      iNext.
      iIntros "?".
      iLeft;done.
      iNext.
      iIntros "(PC & mem_instr & pgt_acc' & R0 & R1 & R2 & tx & mem_tx & own_tx) _".
      iDestruct ("Hacc_regs" $! (ai ^+ 1)%f with "[$ PC $ R0 $ R1 $ R2]") as (regs') "[%Htotal_regs' regs]".

      iDestruct ("Hacc_mem_acc_tx" with "[$mem_instr]") as "mem_acc_tx".
      iApply ("IH" $! _ ps_acc trans _ Htotal_regs' Hsubset_mb Hdisj_na Hnin_rx Hnin_tx with "regs tx [$own_tx $excl_tx] pgt_acc pgt_acc' LB trans_hpool_global
                            tran_pgt_transferred retri R0z R1z R2z rx_state rx other_rx prop0 propi tran_pgt_owned pgt_owned retri_owned [mem_rest mem_acc_tx mem_tx]").
      {
        iDestruct (memory_pages_split_singleton' p_tx ps_acc with "[mem_acc_tx mem_tx]") as "mem_acc". set_solver + Hsubset_mb.
        iSplitL "mem_acc_tx".
        iExists mem_acc_tx;by iFrame "mem_acc_tx".
        iExists mem_tx;by iFrame "mem_tx".
        iApply (memory_pages_split_diff' _ ps_acc with "[$mem_rest $mem_acc]").
        set_solver +.
      }
    }

    destruct (decide (p_rx ∈ ps_share)) as [Hin_prx_share | Hnin_prx_share].
    { (* rx is not owned by i, apply [mem_send_not_owned] *)
      iDestruct "rx" as "[rx [own_rx excl_rx]]".
      iApply (mem_send_not_owned ai _ (p_rx -@O> -)%I with "[PC mem_instr pgt_acc' R0 R1 R2 tx mem_tx own_rx]");iFrameAutoSolve.
      exact Hdecode_hvc.
      simpl; reflexivity.
      lia.
      exact Heq_parse_tran.
      done.
      simpl; exact Hin_prx_share.
      iFrame.
      iNext.
      iIntros "?".
      iLeft;done.
      iNext.
      iIntros "(PC & mem_instr & pgt_acc' & R0 & R1 & R2 & tx & mem_tx & own_rx) _".
      iDestruct ("Hacc_regs" $! (ai ^+ 1)%f with "[$ PC $ R0 $ R1 $ R2]") as (regs') "[%Htotal_regs' regs]".

      iDestruct ("Hacc_mem_acc_tx" with "[$mem_instr]") as "mem_acc_tx".
      iApply ("IH" $! _ ps_acc trans _ Htotal_regs' Hsubset_mb Hdisj_na Hnin_rx Hnin_tx with "regs tx pgt_tx pgt_acc pgt_acc' LB trans_hpool_global
                            tran_pgt_transferred retri R0z R1z R2z rx_state [$rx $own_rx $excl_rx] other_rx prop0 propi tran_pgt_owned pgt_owned retri_owned [mem_rest mem_acc_tx mem_tx]").
      {
        iDestruct (memory_pages_split_singleton' p_tx ps_acc with "[mem_acc_tx mem_tx]") as "mem_acc". set_solver + Hsubset_mb.
        iSplitL "mem_acc_tx".
        iExists mem_acc_tx;by iFrame "mem_acc_tx".
        iExists mem_tx;by iFrame "mem_tx".
        iApply (memory_pages_split_diff' _ ps_acc with "[$mem_rest $mem_acc]").
        set_solver +.
      }
    }

    assert (Hsubseteq_share' : ps_share ⊆ ps_acc ∖ {[p_rx;p_tx]}).
    { set_solver + Hsubseteq_share Hnin_ptx_share Hnin_prx_share. }
    clear Hsubseteq_share Hnin_ptx_share Hnin_prx_share.

    iDestruct "trans_hpool_global" as (hpool) "(%Heq_hsall & fresh_handles & %Htrans_ps_disj & trans)".
    destruct (decide (ps_share ⊆ ps_acc ∖ {[p_rx; p_tx]} ∖ (pages_in_trans trans))) as [Hsubseteq_share'' | Hnsubseteq_share].
    { (* all pages are exclusively owned, ok to perceed *)
      assert (ps_share ⊆ ps_acc ∖ {[p_rx; p_tx]} ∖ ps_mem_in_trans) as Hsubseteq.
      {
        assert (ps_mem_in_trans ⊆ (pages_in_trans trans)).
        {
          rewrite /ps_mem_in_trans.
          apply pages_in_trans_subseteq.
          apply map_filter_subseteq.
        }
        set_solver + H Hsubseteq_share''.
      }
      iDestruct (fresh_handles_disj with "[$fresh_handles $trans]") as "%Hdisj_hpool".
      iDestruct (access_split with "[$ pgt_acc $ pgt_acc' ]") as "pgt_acc".
      iDestruct (big_sepS_sep with "pgt_owned") as "pgt_owned".
      iDestruct (big_sepS_union_acc _ ps_share with "pgt_owned") as "[pgt_oe_share Hacc_pgt_oe]";auto.
      destruct (decide (hpool = ∅)).
      { (* no avaiable fresh handles, apply [mem_share_no_fresh_handles] *)
        iApply (mem_send_no_fresh_handles ai hpool j mem_tx ps_share with "[PC mem_instr pgt_acc pgt_oe_share R0 R1 R2 fresh_handles tx mem_tx]");iFrameAutoSolve.
        exact Hdecode_hvc.
        simpl; reflexivity.
        lia.
        intro;apply Hneq_sr,symmetry;done.
        set_solver + Hsubseteq_share'.
        iFrame.
        iNext. iIntros "(PC & mem_instr & pgt_oe_share & pgt_acc & R0 & R1 & R2 & fresh_handles & tx & mem_tx ) _".
        iDestruct ("Hacc_pgt_oe" $! ps_share with "[] pgt_oe_share") as "pgt_owned".
        { iPureIntro;set_solver +. }

        iDestruct ("Hacc_regs" $! (ai ^+ 1)%f _ _ _ with "[$ PC $ R0 $ R1 $ R2]") as (regs') "[%Htotal_regs' regs]".
        iDestruct ("Hacc_mem_acc_tx" with "[$mem_instr]") as "mem_acc_tx".
        iDestruct (access_split with "pgt_acc") as "[pgt_acc pgt_acc']".
        iApply ("IH" $! _ ps_acc trans _ Htotal_regs' Hsubset_mb Hdisj_na Hnin_rx Hnin_tx with "regs tx pgt_tx pgt_acc pgt_acc' LB [fresh_handles trans]
                            tran_pgt_transferred retri R0z R1z R2z rx_state rx other_rx prop0 propi tran_pgt_owned [pgt_owned] retri_owned [mem_rest mem_acc_tx mem_tx]").
        iExists hpool. by iFrame.
        pose proof (union_split_difference_intersection_subseteq_L _ _ Hsubseteq_share'') as [<- _].
        iApply (big_sepS_sep with "pgt_owned").
        {
          iDestruct (memory_pages_split_singleton' p_tx ps_acc with "[mem_acc_tx mem_tx]") as "mem_acc". set_solver + Hsubset_mb.
          iSplitL "mem_acc_tx".
          iExists mem_acc_tx;by iFrame "mem_acc_tx".
          iExists mem_tx;by iFrame "mem_tx".
          iApply (memory_pages_split_diff' _ ps_acc with "[$mem_rest $mem_acc]").
          set_solver +.
        }
      }
      iApply (mem_share ai j mem_tx hpool ps_share with "[PC mem_instr pgt_acc pgt_oe_share R0 R1 R2 fresh_handles tx mem_tx]");iFrameAutoSolve.
      exact Hdecode_hvc.
      simpl; reflexivity.
      lia.
      intro;apply Hneq_sr,symmetry;done.
      set_solver + Hsubseteq_share'.
      iFrame.
      iNext. iIntros "(PC & mem_instr & pgt_oe_share & pgt_acc & R0 & R1 & (%wh & %Hin_wh & R2 & tran_share & retri_share & fresh_handles) & tx & mem_tx ) _".
      iDestruct ("Hacc_pgt_oe" $! ∅ with "[] []") as "pgt_owned".
      { iPureIntro. set_solver +. }
      { rewrite big_sepS_empty //. }

      iDestruct ("Hacc_regs" $! (ai ^+ 1)%f _ _ _ with "[$ PC $ R0 $ R1 $ R2]") as (regs') "[%Htotal_regs' regs]".
      iDestruct ("Hacc_mem_acc_tx" with "[$mem_instr]") as "mem_acc_tx".
      iDestruct (access_split with "pgt_acc") as "[pgt_acc pgt_acc']".

      (* we will specialize IH with the new [trans'] *)
      pose (<[wh := (i, j, ps_share, Sharing, false)]>trans) as trans''.
      assert (Hlookup_wh_None: trans !! wh = None).
      rewrite -not_elem_of_dom.
      set_solver + Hin_wh Hdisj_hpool.

      assert (ps_share ∪ pages_in_trans (trans_memory_in_trans i trans) = pages_in_trans (trans_memory_in_trans i trans'')) as Hrewrite.
      {
        rewrite /trans'' /trans_memory_in_trans.
        rewrite map_filter_insert_True.
        rewrite /pages_in_trans map_fold_insert_L /=.
        f_equal.
        intros.
        set_solver +.
        rewrite map_filter_lookup_None.
        eauto.
        simpl.
        left.
        split;auto.
        intro.
        destruct H as [H []].
        inversion H.
      }

      iDestruct (trans_split with "tran_share") as "[tran_share tran_share']".

      iApply ("IH" $! _ ps_acc trans'' _ Htotal_regs' Hsubset_mb with "[] [] [] regs tx pgt_tx pgt_acc pgt_acc' LB
                [fresh_handles tran_share trans] [tran_pgt_transferred] [retri retri_share] R0z R1z R2z
                rx_state rx other_rx prop0 propi [tran_pgt_owned tran_share' pgt_oe_share] [pgt_owned] [retri_owned] [mem_rest mem_acc_tx mem_tx]").
      {
        rewrite -Hrewrite.
        rewrite union_assoc_L.
        assert (ps_acc ∪ ps_share = ps_acc) as ->.
        symmetry.
        rewrite union_comm_L.
        rewrite subseteq_union_1_L;auto.
        set_solver + Hsubseteq_share'.
        done.
      }
      {
        rewrite -Hrewrite.
        rewrite union_assoc_L.
        assert (ps_acc ∖ {[p_rx; p_tx]} ∪ ps_share = ps_acc ∖ {[p_rx; p_tx]}) as ->.
        rewrite union_comm_L.
        rewrite subseteq_union_1_L;auto.
        done.
      }
      {
        rewrite -Hrewrite.
        rewrite union_assoc_L.
        assert (ps_acc ∖ {[p_rx; p_tx]} ∪ ps_share = ps_acc ∖ {[p_rx; p_tx]}) as ->.
        rewrite union_comm_L.
        rewrite subseteq_union_1_L;auto.
        done.
      }
      {
        iExists (hpool ∖ {[wh]}).
        iSplit.
        iPureIntro.
        rewrite dom_insert_L.
        rewrite union_assoc_L.
        rewrite -Heq_hsall.
        f_equal.
        rewrite difference_union_L.
        set_solver + Hin_wh.
        rewrite big_sepM_insert;auto.
        iFrame.
        simpl.
        iPureIntro.
        apply trans_ps_disj_insert;auto.
        simpl.
        set_solver + Hsubseteq_share' Hsubseteq_share''.
      }
      {
        rewrite /transaction_pagetable_entries_transferred.
        iApply (big_sepFM_lookup_None_False with "tran_pgt_transferred"); auto.
        simpl.
        intros [H _];inversion H.
      }
      {
        rewrite /retrieval_entries_transferred.
        iDestruct (retri_split with "retri_share") as "[retri_share retri_share']".
        iDestruct "retri" as "[retri1 retri2]".
        iSplitL "retri1 retri_share".
        iApply (big_sepFM_lookup_None_True with "retri1"); auto.
        simpl;eauto.
        iApply (big_sepFM_lookup_None_True with "retri2"); auto.
        simpl;eauto.
      }
      {
        rewrite /transaction_pagetable_entries_owned.
        iApply (big_sepFM_lookup_None_True with "tran_pgt_owned"); auto.
        simpl;eauto.
        case_bool_decide.
        simpl in H. done.
        iFrame.
        iApply (big_sepS_sep with "pgt_oe_share").
      }
      {
        rewrite union_empty_r_L.
        rewrite /pagetable_entries_excl_owned /pgt.
        rewrite (pages_in_trans_insert Hlookup_wh_None) /=.
        rewrite (union_comm_L ps_share).
        rewrite difference_difference_L.
        iApply (big_sepS_sep with "pgt_owned").
      }
      {
        rewrite /retrieval_entries_owned.
        rewrite -big_sepFM_lookup_None_False;auto.
        simpl.
        intro. destruct H;contradiction.
      }
      {
        iDestruct (memory_pages_split_singleton' p_tx ps_acc with "[mem_acc_tx mem_tx]") as "mem_acc". set_solver + Hsubset_mb.
        iSplitL "mem_acc_tx".
        iExists mem_acc_tx;by iFrame "mem_acc_tx".
        iExists mem_tx;by iFrame "mem_tx".
        iApply (memory_pages_split_diff' _ ps_acc with "[mem_rest $mem_acc]").
        set_solver +.
        (* TODO: simplify *)
        assert ((ps_acc ∪ pages_in_trans (trans_memory_in_trans i trans'') ) ∖ ps_acc = pages_in_trans (trans_memory_in_trans i trans'')∖ (ps_acc∖ {[p_tx]})) as ->.
        {
          assert ((ps_acc ∪ pages_in_trans (trans_memory_in_trans i trans'') ) ∖ ps_acc = pages_in_trans (trans_memory_in_trans i trans'') ∖ ps_acc) as ->.
          set_solver +.
          rewrite -Hrewrite.
          set_solver + Hnin_tx Hsubseteq_share'.
        }
        assert ((ps_acc ∪ ps_mem_in_trans ) ∖ ps_acc = ps_mem_in_trans ∖ (ps_acc∖ {[p_tx]})) as ->.
        {
          assert ((ps_acc ∪ ps_mem_in_trans ) ∖ ps_acc = ps_mem_in_trans ∖ ps_acc) as ->.
          set_solver +.
          set_solver + Hnin_tx.
        }
        rewrite -Hrewrite.
        rewrite difference_union_distr_l_L.
        assert (ps_share ∖ (ps_acc ∖ {[p_tx]}) = ∅) as ->.
        set_solver + Hsubseteq_share'.
        rewrite union_empty_l_L //.
      }
    }
    { (* at least one page is not exclusively owned by i (i.e. is involved in a transaction) *)
      assert (∃ p, p ∈ ps_share ∧ p ∈ pages_in_trans trans) as [p [Hin_p_share Hin_p_mem_in_trans]].
      { apply (not_subseteq_diff _ (ps_acc ∖ {[p_rx; p_tx]}));auto. }
      apply elem_of_pages_in_trans in  Hin_p_mem_in_trans as [h [tran [Hlookup_tran Hin_p_tran]]].
      iDestruct (big_sepM_lookup_acc with "trans") as "[tran_tran Hacc_trans]";first exact Hlookup_tran.
      iApply (mem_send_in_trans ai p h with "[PC mem_instr pgt_acc' R0 R1 R2 tx mem_tx tran_tran]");iFrameAutoSolve.
      exact Hdecode_hvc.
      simpl; reflexivity.
      lia.
      exact Heq_parse_tran.
      done.
      simpl; exact Hin_p_share.
      iFrame.
      iNext.
      iIntros "(PC & mem_instr & pgt_acc' & R0 & R1 & R2 & tx & mem_tx & tran_tran) _".
      iDestruct ("Hacc_regs" $! (ai ^+ 1)%f with "[$ PC $ R0 $ R1 $ R2]") as (regs') "[%Htotal_regs' regs]".
      iDestruct ("Hacc_mem_acc_tx" with "[$mem_instr]") as "mem_acc_tx".
      iDestruct ("Hacc_trans" with "[$ tran_tran]") as "trans".

      iApply ("IH" $! _ ps_acc trans _ Htotal_regs' Hsubset_mb  Hdisj_na Hnin_rx Hnin_tx with "regs tx pgt_tx pgt_acc pgt_acc' LB [fresh_handles trans]
                            tran_pgt_transferred retri R0z R1z R2z rx_state rx other_rx prop0 propi tran_pgt_owned pgt_owned retri_owned [mem_rest mem_acc_tx mem_tx] ").
      iExists hpool;by iFrame.
      {
        iDestruct (memory_pages_split_singleton' p_tx ps_acc with "[mem_acc_tx mem_tx]") as "mem_acc". set_solver + Hsubset_mb.
        iSplitL "mem_acc_tx".
        iExists mem_acc_tx;by iFrame "mem_acc_tx".
        iExists mem_tx;by iFrame "mem_tx".
        iApply (memory_pages_split_diff' _ ps_acc with "[$mem_rest $mem_acc]").
        set_solver +.
      }
    }
  Qed.

End ftlr_share.
