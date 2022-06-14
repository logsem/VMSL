From iris.proofmode Require Import tactics.
From machine_program_logic.program_logic Require Import weakestpre.
From HypVeri.algebra Require Import base pagetable mem trans mailbox.
From HypVeri.rules Require Import msg_send.
From HypVeri.logrel Require Import logrel_prim_extra.
From HypVeri Require Import proofmode.
Import uPred.

Section ftlr_msg_send_prim.
  Context `{hypconst:HypervisorConstants}.
  Context `{hypparams:!HypervisorParameters}.
  Context `{vmG: !gen_VMG Σ}.

  Lemma ftlr_msg_send_prim {Φ_t Φ_r mem_acc_tx ai regs ps_acc p_tx p_rx instr trans rxs r0}:
    let i := V0 in
    (∀ i os, (match os with
                 | None => True
                 | Some (_,j) => j = V0
                end) -> Φ_r i os i ⊣⊢ slice_rx_state i os) ->
    (∀ i os, match os with
               | None => True
               | Some (_ ,k) => k = V0
               end -> Φ_r i os i ⊣⊢ Φ_r i os V0) ->
    base_extra.is_total_gmap regs ->
    base_extra.is_total_gmap rxs ->
    {[p_tx; p_rx]} ⊆ ps_acc ->
    currently_accessible_in_trans_memory_pages i trans ⊆ ps_acc ∖ {[p_tx; p_rx]} ->
    p_rx ∉ ps_acc ∖ {[p_rx; p_tx]} ∪ accessible_in_trans_memory_pages i trans ->
    p_tx ∉ ps_acc ∖ {[p_rx; p_tx]} ∪ accessible_in_trans_memory_pages i trans ->
    regs !! PC = Some ai ->
    tpa ai ∈ ps_acc ->
    tpa ai ≠ p_tx ->
    dom mem_acc_tx = set_of_addr (ps_acc ∖ {[p_tx]}) ->
    tpa ai ∈ ps_acc ∖ {[p_tx]} ->
    mem_acc_tx !! ai = Some instr ->
    decode_instruction instr = Some Hvc ->
    regs !! R0 = Some r0 ->
    decode_hvc_func r0 = Some Send ->
    p_tx ≠ p_rx ->
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
    iIntros (i HΦr1 HΦr2 Htotal_regs Htotal_rxs Hsubset_mb Hsubset_acc Hnin_rx Hnin_tx Hlookup_PC Hin_ps_acc Hneq_ptx Hdom_mem_acc_tx Hin_ps_acc_tx).
    iIntros (Hlookup_mem_ai Heqn Hlookup_reg_R0 Hdecode_hvc Hneq_mb) "IH regs tx pgt_tx pgt_acc pgt_owned trans_hpool_global tran_pgt_transferred retri rx_state rx other_rx
             tran_pgt_owned retri_owned mem_rest mem_acc_tx mem_tx P".
    set ps_mem_in_trans := accessible_in_trans_memory_pages i trans.
    pose proof (Htotal_regs R1) as[r1 Hlookup_reg_R1].
    pose proof (Htotal_regs R2) as[r2 Hlookup_reg_R2].
    iDestruct (reg_big_sepM_split_upd4 i Hlookup_PC Hlookup_reg_R0 Hlookup_reg_R1 Hlookup_reg_R2 with "[$regs]")
      as "(PC & R0 & R1 & R2 & Hacc_regs)";eauto.

    iDestruct (mem_big_sepM_split mem_acc_tx Hlookup_mem_ai with "mem_acc_tx") as "[mem_instr Hacc_mem_acc_tx]".
    destruct (decode_vmid r1) eqn:Heq_decode.
    2:{ (* apply [msg_send_invalid_receiver] *)
      iApply (msg_send_invalid_receiver ai with "[PC mem_instr pgt_acc R0 R1 R2 tx]");iFrameAutoSolve.
      iNext. iIntros "(PC & mem_instr & pgt_acc  & tx & R0 & R1 & R2) _".
      iDestruct ("Hacc_regs" $! (ai ^+ 1)%f with "[$ PC $ R0 $ R1 $ R2]") as (regs') "[%Htotal_regs' regs]".

      iDestruct ("Hacc_mem_acc_tx" with "[$mem_instr]") as "mem_acc_tx".
      iApply ("IH" $! _ ps_acc trans _ Htotal_rxs Htotal_regs' Hsubset_mb Hsubset_acc Hnin_rx Hnin_tx with "regs tx pgt_tx rx pgt_acc pgt_owned trans_hpool_global
                            tran_pgt_transferred retri rx_state other_rx tran_pgt_owned retri_owned [mem_rest mem_acc_tx mem_tx]
                            [P]").
      {
        iDestruct (memory_pages_split_singleton' p_tx ps_acc with "[mem_acc_tx $mem_tx]") as "mem_acc". set_solver + Hsubset_mb.
        iExists mem_acc_tx;by iFrame "mem_acc_tx".
        iApply (memory_pages_split_diff' _ ps_acc with "[$mem_rest $mem_acc]").
        set_solver +.
      }
      {
        iDestruct "P" as "($ & ? & $ & $)".
        rewrite -big_sepS_later.
        iFrame.
      }
    }

    destruct (decide (v = i)).
    { (* apply [msg_send_to_self] *)
      iApply (msg_send_to_self ai with "[PC mem_instr pgt_acc R0 R1 R2 tx]");iFrameAutoSolve.
      exact Heq_decode. done.
      iNext. iIntros "(PC & mem_instr & pgt_acc  & tx & R0 & R1 & R2) _".
      iDestruct ("Hacc_regs" $! (ai ^+ 1)%f with "[$ PC $ R0 $ R1 $ R2]") as (regs') "[%Htotal_regs' regs]".

      iDestruct ("Hacc_mem_acc_tx" with "[$mem_instr]") as "mem_acc_tx".
      iApply ("IH" $! _ ps_acc trans _ Htotal_rxs Htotal_regs' Hsubset_mb Hsubset_acc Hnin_rx Hnin_tx with "regs tx pgt_tx rx pgt_acc pgt_owned trans_hpool_global
                            tran_pgt_transferred retri rx_state other_rx tran_pgt_owned retri_owned [mem_rest mem_acc_tx mem_tx]
                            [P]").
      {
        iDestruct (memory_pages_split_singleton' p_tx ps_acc with "[mem_acc_tx $mem_tx]") as "mem_acc". set_solver + Hsubset_mb.
        iExists mem_acc_tx;by iFrame "mem_acc_tx".
        iApply (memory_pages_split_diff' _ ps_acc with "[$mem_rest $mem_acc]").
        set_solver +.
      }
      {
        iDestruct "P" as "($ & ? & $ & $)".
        rewrite -big_sepS_later.
        iFrame.
      }
    }

    destruct (decide (page_size < r2)%Z).
    { (*apply [msg_send_invalid_length]*)
      iApply (msg_send_invalid_length ai with "[PC mem_instr pgt_acc R0 R1 R2 tx]");iFrameAutoSolve.
      exact Heq_decode. done. lia.
      iNext. iIntros "(PC & mem_instr & pgt_acc  & tx & R0 & R1 & R2) _".
      iDestruct ("Hacc_regs" $! (ai ^+ 1)%f with "[$ PC $ R0 $ R1 $ R2]") as (regs') "[%Htotal_regs' regs]".

      iDestruct ("Hacc_mem_acc_tx" with "[$mem_instr]") as "mem_acc_tx".
      iApply ("IH" $! _ ps_acc trans _ Htotal_rxs Htotal_regs' Hsubset_mb Hsubset_acc Hnin_rx Hnin_tx with "regs tx pgt_tx rx pgt_acc pgt_owned trans_hpool_global
                            tran_pgt_transferred retri rx_state other_rx tran_pgt_owned retri_owned [mem_rest mem_acc_tx mem_tx]
                            [P]").
      {
        iDestruct (memory_pages_split_singleton' p_tx ps_acc with "[mem_acc_tx $mem_tx]") as "mem_acc". set_solver + Hsubset_mb.
        iExists mem_acc_tx;by iFrame "mem_acc_tx".
        iApply (memory_pages_split_diff' _ ps_acc with "[$mem_rest $mem_acc]").
        set_solver +.
      }
      {
        iDestruct "P" as "($ & ? & $ & $)".
        rewrite -big_sepS_later.
        iFrame.
      }
    }

    assert (is_Some((delete i rxs)!! v)) as Hin_v.
    {
      pose proof (Htotal_rxs v) as [? ?].
      exists x.
      rewrite lookup_delete_ne //.
    }

    destruct Hin_v as [rx_state_v Hin_v].
    iDestruct (big_sepM_delete with "other_rx") as "[rx_state_v other_rx]".
    exact Hin_v.

    destruct (rx_state_v).
    { (* apply [msg_send_full_rx] *)
      iEval (rewrite /rx_state_match /=) in "rx_state_v".
      iApply (msg_send_full_rx ai with "[PC mem_instr pgt_acc R0 R1 R2 tx rx_state_v]");iFrameAutoSolve.
      exact Heq_decode. done. lia. 2: { iDestruct "rx_state_v" as "[$ ?]". done. } done.
      iNext. iIntros "(PC & mem_instr & pgt_acc  & tx & R0 & R1 & R2 & rx_state_v ) _".
      iDestruct ("Hacc_regs" $! (ai ^+ 1)%f with "[$ PC $ R0 $ R1 $ R2]") as (regs') "[%Htotal_regs' regs]".

      iDestruct ("Hacc_mem_acc_tx" with "[$mem_instr]") as "mem_acc_tx".
      iApply ("IH" $! _ ps_acc trans _ Htotal_rxs Htotal_regs' Hsubset_mb Hsubset_acc Hnin_rx Hnin_tx with "regs tx pgt_tx rx pgt_acc pgt_owned trans_hpool_global
                            tran_pgt_transferred retri rx_state [other_rx rx_state_v] tran_pgt_owned retri_owned [mem_rest mem_acc_tx mem_tx]
                            [P]").
      {
        iApply (big_sepM_delete with "[other_rx rx_state_v]").
        exact Hin_v.
        simpl. iFrame "other_rx".
        iFrame.
      }
      {
        iDestruct (memory_pages_split_singleton' p_tx ps_acc with "[mem_acc_tx $mem_tx]") as "mem_acc". set_solver + Hsubset_mb.
        iExists mem_acc_tx;by iFrame "mem_acc_tx".
        iApply (memory_pages_split_diff' _ ps_acc with "[$mem_rest $mem_acc]").
        set_solver +.
      }
      {
        iDestruct "P" as "($ & ? & $ & $)".
        rewrite -big_sepS_later.
        iFrame.
      }
    }

    iDestruct "mem_tx" as "[% mem_tx]".
    iDestruct "rx_state_v" as "[rx_state_v [%p_rx_v [rx_v [%mem_rx_v mem_rx_v]]]]".
    iAssert (RX@i := p_rx)%I  with "[rx]" as "#rx'". iDestruct "rx" as "[$ ?]".
    iApply (msg_send_primary ai v
             with "[PC R0 R1 R2 pgt_acc tx mem_tx mem_instr rx_v rx_state_v mem_rx_v]"); iFrameAutoSolve.
    { solve_finz + n0. }
    {
        iSplitL "mem_tx". iFrame "mem_tx". iFrame "mem_rx_v".
    }
    iNext. iIntros "(PC & mem_instr & pgt_acc & R0 & R1 & R2 & tx & rx_v & rx_state_v & mem_tx & mem_rx_v) _".
    iDestruct ("Hacc_regs" $! (ai ^+ 1)%f r0 r1 r2 with "[PC R0 R1 R2]") as "[%regs' [%Htotal_regs' regs'']]"; iFrameAutoSolve.
    iDestruct ("Hacc_mem_acc_tx" with "mem_instr") as "mem_acc_tx".
    iDestruct (rx_state_split with "rx_state_v") as "[rx_state_v rx_state_v']".
    set rxs' := (<[v:= Some (r2, V0)]>rxs).
    iApply ("IH" $! _ ps_acc trans rxs' with "[] [] [] [] [] [] regs'' tx pgt_tx rx pgt_acc pgt_owned
                        trans_hpool_global tran_pgt_transferred retri [rx_state] [other_rx rx_state_v]
                           tran_pgt_owned retri_owned [mem_rest mem_acc_tx mem_tx] [P rx_state_v' rx_v mem_rx_v]");auto.
    {
      iPureIntro.
      intros k. destruct (decide (k = v)).
      subst k. exists (Some (r2,V0)). rewrite /rxs' lookup_insert //.
      pose proof (Htotal_rxs k).
      rewrite /rxs' lookup_insert_ne //.
    }
    {
      rewrite /rx_state_get.
      rewrite /rxs'. rewrite lookup_insert_ne //.
    }
    {
      rewrite /rx_states_global.
      iApply big_sepM_delete.
      rewrite /rxs' lookup_delete_ne.
      apply lookup_insert. done.
      rewrite /rxs'.
      rewrite delete_insert_ne //.
      rewrite delete_insert_delete.
      iFrame.
    }
    {
      iDestruct (memory_pages_split_singleton' p_tx ps_acc with "[mem_acc_tx mem_tx]") as "mem_acc". set_solver + Hsubset_mb.
      iSplitL "mem_acc_tx".
      iExists mem_acc_tx; by iFrame "mem_acc_tx".
      iExists mem2. iFrame "mem_tx".
      iApply (memory_pages_split_diff' _ ps_acc with "[$mem_rest $mem_acc]").
      set_solver +.
    }
    {
      iDestruct "P" as "($ & ? & $ & rxs)".
      rewrite -big_sepS_later.
      iFrame.
      rewrite /rx_states_transferred.
      iApply big_sepM_delete.
      rewrite /rxs' lookup_delete_ne.
      apply lookup_insert. done.
      simpl. iDestruct (big_sepM_delete with "rxs") as "[_ rxs]".
      exact Hin_v.
      rewrite /rxs'.
      rewrite delete_insert_ne //.
      rewrite delete_insert_delete.
      iFrame.
      iApply HΦr2. done.
      iApply HΦr1. done.
      rewrite /slice_rx_state.
      iFrame.
      iExists p_rx_v. iFrame.
      iDestruct "mem_rx_v" as "(% & _ & _ & mem)".
      iExists _. iExact "mem".
    }
  Qed.

End ftlr_msg_send_prim.
