From machine_program_logic.program_logic Require Import weakestpre.
From HypVeri Require Import lifting rules.rules_base stdpp_extra.
From HypVeri.algebra Require Import base mem reg pagetable mailbox trans base_extra.
From HypVeri.lang Require Import lang_extra reg_extra mem_extra mailbox_extra pagetable_extra trans_extra.

Section retrieve.

Context `{hypparams: HypervisorParameters}.
Context `{vmG: !gen_VMG Σ}.

Lemma mem_retrieve_donate {E i wi sacc p_tx r0 sh j mem_rx p_rx} {ps: gset PID} ai wh:
  (* has access to the page which the instruction is in *)
  tpa ai ≠ p_tx ->
  (tpa ai) ∈ sacc ->
  (* the current instruction is hvc *)
  (* the decoding of wi is correct *)
  decode_instruction wi = Some(Hvc) ->
  (* the hvc call to invoke is retrieve *)
  decode_hvc_func r0 = Some(Retrieve) ->
  {SS{{(* the encoding of instruction wi is stored in location ai *)
       ▷ (PC @@ i ->r ai) ∗ ▷ ai ->a wi ∗
       (* registers *)
       ▷ (R0 @@ i ->r r0) ∗
       ▷ (R1 @@ i ->r wh) ∗
       (* the pagetable *)
       ▷ ([∗ set] p ∈ ps, p -@O> j) ∗
       ▷ i -@A> sacc ∗
       ▷ TX@i := p_tx ∗
       (* the transaction hasn't been retrieved *)
       ▷ wh ->re false ∗ ▷ wh -{1}>t (j, i, ps, Donation) ∗
       (* the rx page and locations that the rx descriptor will be at *)
       ▷ RX@ i := p_rx ∗ ▷ RX_state@ i := None ∗
       ▷ memory_page p_rx mem_rx ∗
       (* the handle pool *)
       ▷ fresh_handles 1 sh}}}
   ExecI @ i; E
   {{{ RET (false, ExecI) ;
       (* PC is incremented *)
       PC @@ i ->r (ai ^+ 1)%f ∗ ai ->a wi ∗
       (* return Succ to R0 *)
       R0 @@ i ->r (encode_hvc_ret_code Succ) ∗
       R1 @@ i ->r wh ∗
       (* gain exclusive access and ownership *)
       ([∗ set] p ∈ ps, p -@O> i) ∗
       i -@A> (ps ∪ sacc) ∗
       TX@i := p_tx ∗
       (* new descriptor in rx *)
       RX@ i := p_rx ∗
       (∃ l des, RX_state@ i := Some(l, i) ∗ ⌜((Z.to_nat (finz.to_z l)) = (length des))%nat⌝ ∗
       (* XXX: not sure if it is useful *)
       (⌜des = ([of_imm (encode_vmid j); wh; encode_transaction_type Donation ;(l ^- 4)%f] ++ map of_pid (elements ps))⌝ ∗
                 memory_page p_rx ((list_to_map (zip (finz.seq p_rx (length des)) des)) ∪ mem_rx))) ∗
       (* the transaction is completed, deallocate it and release the handle *)
       fresh_handles 1 (sh ∪ {[wh]}) }}}.
Proof.
Admitted.

Lemma mem_retrieve_donate_rx {E i wi sacc r0 sh j mem_rx p_tx} {ps: gset PID} ai wh:
  tpa ai ≠ p_tx ->
  (* the current instruction is hvc *)
  (* the decoding of wi is correct *)
  decode_instruction wi = Some(Hvc) ->
  (* the hvc call to invoke is retrieve *)
  decode_hvc_func r0 = Some(Retrieve) ->
  {SS{{(* the encoding of instruction wi is stored in location ai *)
       ▷ (PC @@ i ->r ai) ∗ ▷ ai ->a wi ∗
       (* registers *)
       ▷ (R0 @@ i ->r r0) ∗
       ▷ (R1 @@ i ->r wh) ∗
       (* the pagetable *)
       ▷ ([∗ set] p ∈ ps, p -@O> j) ∗
       ▷ i -@A> sacc ∗
       ▷ TX@i := p_tx ∗
       (* the transaction hasn't been retrieved *)
       ▷ wh ->re false ∗ ▷ wh -{1}>t (j, i, ps, Donation) ∗
       (* the rx page and locations that the rx descriptor will be at *)
       ▷ RX@ i := (tpa ai) ∗ ▷ RX_state@ i := None ∗
       ▷ (ai ->a wi -∗ memory_page (tpa ai) mem_rx) ∗
       (* the handle pool *)
       ▷ fresh_handles 1 sh}}}
   ExecI @ i; E
   {{{ RET (false, ExecI) ;
       (* PC is incremented *)
       PC @@ i ->r (ai ^+ 1)%f ∗
       (* return Succ to R0 *)
       R0 @@ i ->r (encode_hvc_ret_code Succ) ∗
       R1 @@ i ->r wh ∗
       (* gain exclusive access and ownership *)
       ([∗ set] p ∈ ps, p -@O> i) ∗
       i -@A> (ps ∪ sacc) ∗
       TX@i := p_tx ∗
       (* new descriptor in rx *)
       RX@ i := (tpa ai) ∗
       (∃ l des, RX_state@ i := Some(l, i) ∗ ⌜((Z.to_nat (finz.to_z l)) = (length des))%nat⌝ ∗
       (* XXX: not sure if it is useful *)
       (⌜des = ([of_imm (encode_vmid j); wh; encode_transaction_type Donation ;(l ^- 4)%f] ++ map of_pid (elements ps))⌝ ∗
                 memory_page (tpa ai) ((list_to_map (zip (finz.seq (tpa ai) (length des)) des)) ∪ mem_rx))) ∗
       (* the transaction is completed, deallocate it and release the handle *)
       fresh_handles 1 (sh ∪ {[wh]}) }}}.
Proof.
Admitted.

Lemma mem_retrieve_invalid_handle {E i wi sacc r0 r2 wh p_tx} ai:
  tpa ai ≠ p_tx ->
  (tpa ai) ∈ sacc ->
  (* the current instruction is hvc *)
  (* the decoding of wi is correct *)
  decode_instruction wi = Some(Hvc) ->
  (* the hvc call to invoke is retrieve *)
  decode_hvc_func r0 = Some(Retrieve) ->
  wh ∉ hs_all ->
  {SS{{(* the encoding of instruction wi is stored in location ai *)
       ▷ (PC @@ i ->r ai) ∗ ▷ ai ->a wi ∗
       (* registers *)
       ▷ (R0 @@ i ->r r0) ∗
       ▷ (R1 @@ i ->r wh) ∗
       ▷ (R2 @@ i ->r r2) ∗
       ▷ i -@A> sacc ∗
       ▷ TX@i := p_tx
  }}}
   ExecI @ i; E
   {{{ RET (false, ExecI) ;
       (* PC is incremented *)
       PC @@ i ->r (ai ^+ 1)%f ∗ ai ->a wi ∗
       R0 @@ i ->r (encode_hvc_ret_code Error) ∗
       R1 @@ i ->r wh ∗
       R2 @@ i ->r (encode_hvc_error InvParam) ∗
       i -@A> sacc ∗
       TX@i := p_tx
   }}}.
Proof.
Admitted.

Lemma mem_retrieve_fresh_handle {E i wi sacc r0 r2 wh sh q p_tx} ai:
  tpa ai ≠ p_tx ->
  (tpa ai) ∈ sacc ->
  decode_instruction wi = Some(Hvc) ->
  decode_hvc_func r0 = Some(Retrieve) ->
  wh ∈ sh ->
  {SS{{▷ (PC @@ i ->r ai) ∗ ▷ ai ->a wi ∗
       ▷ (R0 @@ i ->r r0) ∗
       ▷ (R1 @@ i ->r wh) ∗
       ▷ (R2 @@ i ->r r2) ∗
       ▷ i -@A> sacc ∗
       ▷ TX@i := p_tx ∗
       ▷ fresh_handles q sh}}}
   ExecI @ i; E
   {{{ RET (false, ExecI) ;
       PC @@ i ->r (ai ^+ 1)%f ∗ ai ->a wi ∗
       R0 @@ i ->r (encode_hvc_ret_code Error) ∗
       R1 @@ i ->r wh ∗
       R2 @@ i ->r (encode_hvc_error InvParam) ∗
       i -@A> sacc ∗
       TX@i := p_tx ∗
       fresh_handles q sh
   }}}.
Proof.
Admitted.

Lemma mem_retrieve_invalid_trans {E i wi sacc r0 r2 wh meta q p_tx} ai:
  tpa ai ≠ p_tx ->
  (tpa ai) ∈ sacc ->
  decode_instruction wi = Some(Hvc) ->
  decode_hvc_func r0 = Some(Retrieve) ->
  meta.1.1.2 ≠ i ->
  {SS{{▷ (PC @@ i ->r ai) ∗ ▷ ai ->a wi ∗
       ▷ (R0 @@ i ->r r0) ∗
       ▷ (R1 @@ i ->r wh) ∗
       ▷ (R2 @@ i ->r r2) ∗
       ▷ i -@A> sacc ∗
       ▷ TX@i := p_tx ∗
       ▷ wh -{q}>t meta
       }}}
   ExecI @ i; E
   {{{ RET (false, ExecI) ;
       PC @@ i ->r (ai ^+ 1)%f ∗ ai ->a wi ∗
       R0 @@ i ->r (encode_hvc_ret_code Error) ∗
       R1 @@ i ->r wh ∗
       R2 @@ i ->r (encode_hvc_error Denied) ∗
       i -@A> sacc ∗
       TX@i := p_tx ∗
       wh -{q}>t meta
   }}}.
Proof.
Admitted.

Lemma mem_retrieve_retrieved{E i wi sacc r0 r2 wh q p_tx} ai:
  tpa ai ≠ p_tx ->
  (tpa ai) ∈ sacc ->
  decode_instruction wi = Some(Hvc) ->
  decode_hvc_func r0 = Some(Retrieve) ->
  {SS{{▷ (PC @@ i ->r ai) ∗ ▷ ai ->a wi ∗
       ▷ (R0 @@ i ->r r0) ∗
       ▷ (R1 @@ i ->r wh) ∗
       ▷ (R2 @@ i ->r r2) ∗
       ▷ i -@A> sacc ∗
       ▷ TX@i := p_tx ∗
       ▷ wh -{q}>re true
       }}}
   ExecI @ i; E
   {{{ RET (false, ExecI) ;
       PC @@ i ->r (ai ^+ 1)%f ∗ ai ->a wi ∗
       R0 @@ i ->r (encode_hvc_ret_code Error) ∗
       R1 @@ i ->r wh ∗
       R2 @@ i ->r (encode_hvc_error Denied) ∗
       i -@A> sacc ∗
       TX@i := p_tx ∗
       wh -{q}>re true
   }}}.
Proof.
Admitted.

Lemma mem_retrieve_rx_full{E i wi sacc r0 r2 q1 q2 j tt rx_state p_tx} {ps: gset PID} ai wh:
  tpa ai ≠ p_tx ->
  (tpa ai) ∈ sacc ->
  decode_instruction wi = Some(Hvc) ->
  decode_hvc_func r0 = Some(Retrieve) ->
  is_Some (rx_state) ->
  {SS{{▷ (PC @@ i ->r ai) ∗ ▷ ai ->a wi ∗
       ▷ (R0 @@ i ->r r0) ∗
       ▷ (R1 @@ i ->r wh) ∗
       ▷ (R2 @@ i ->r r2) ∗
       ▷ i -@A> sacc ∗
       ▷ TX@i := p_tx ∗
       ▷ wh -{q1}>re false ∗
       ▷ wh -{q2}>t (j, i, ps, tt) ∗
       ▷ RX_state@i := rx_state
       }}}
   ExecI @ i; E
   {{{ RET (false, ExecI) ;
       PC @@ i ->r (ai ^+ 1)%f ∗ ai ->a wi ∗
       R0 @@ i ->r (encode_hvc_ret_code Error) ∗
       R1 @@ i ->r wh ∗
       R2 @@ i ->r (encode_hvc_error Busy) ∗
       i -@A> sacc ∗
       TX@i := p_tx ∗
       wh -{q1}>re false ∗
       wh -{q2}>t (j, i, ps, tt) ∗
       RX_state@i := rx_state
   }}}.
Proof.
Admitted.

Lemma mem_retrieve_lend{E i wi sacc r0 j mem_rx p_rx q p_tx} {ps: gset PID} ai wh:
  (* has access to the page which the instruction is in *)
  tpa ai ≠ p_tx ->
  (tpa ai) ∈ sacc ->
  (* the current instruction is hvc *)
  (* the decoding of wi is correct *)
  decode_instruction wi = Some(Hvc) ->
  (* the hvc call to invoke is retrieve *)
  decode_hvc_func r0 = Some(Retrieve) ->
  {SS{{(* the encoding of instruction wi is stored in location ai *)
       ▷ (PC @@ i ->r ai) ∗ ▷ ai ->a wi ∗
       (* registers *)
       ▷ (R0 @@ i ->r r0) ∗
       ▷ (R1 @@ i ->r wh) ∗
       (* the pagetable *)
       ▷ i -@A> sacc ∗
       ▷ TX@i := p_tx ∗
       (* the transaction hasn't been retrieved *)
       ▷ wh ->re false ∗ ▷ wh -{q}>t (j,  i, ps, Lending) ∗
       (* the rx page and locations that the rx descriptor will be at *)
       ▷ RX@ i := p_rx ∗ ▷ RX_state@ i := None ∗
       ▷ memory_page p_rx mem_rx}}}
   ExecI @ i; E
   {{{ RET (false, ExecI) ;
       (* PC is incremented *)
       PC @@ i ->r (ai ^+ 1)%f ∗ ai ->a wi ∗
       (* return Succ to R0 *)
       R0 @@ i ->r (encode_hvc_ret_code Succ) ∗
       R1 @@ i ->r wh ∗
       (* gain exclusive access and ownership *)
       i -@A> (ps ∪ sacc) ∗
       TX@i := p_tx ∗
       wh ->re true ∗ wh -{q}>t (j, i, ps, Lending) ∗
       (* new descriptor in rx *)
       RX@ i := p_rx ∗
       (∃ l des, RX_state@ i := Some(l, i) ∗ ⌜((Z.to_nat (finz.to_z l)) = (length des))%nat⌝ ∗
       (* XXX: not sure if it is useful *)
       (⌜des = ([of_imm (encode_vmid j); wh; encode_transaction_type Donation ;(l ^- 4)%f] ++ map of_pid (elements ps))⌝ ∗
                 memory_page p_rx ((list_to_map (zip (finz.seq p_rx (length des)) des)) ∪ mem_rx)))
        }}}.
Proof.
  iIntros (Hneq_tx Hin_acc Hdecode_i Hdecode_f Φ)
          "(>PC & >mem_ins & >R0 & >R1 & >acc & >tx & >re & >tran & >rx & >rx_s & >mem_rx) HΦ".
  iApply (sswp_lift_atomic_step ExecI);[done|].
  iIntros (n σ1) "%Hsche state".
  rewrite /scheduled /= /scheduler in Hsche.
  assert (σ1.1.1.2 = i) as Heq_cur. { case_bool_decide;last done. by apply fin_to_nat_inj. }
  clear Hsche.
  iModIntro.
  iDestruct "state" as "(Hnum & mem & regs & mb & rx_state & pgt_owned & pgt_acc & pgt_excl &
                            trans & hpool & retri & %Hwf & %Hdisj & %Hconsis )".
  (* valid regs *)
  iDestruct ((gen_reg_valid3 i PC ai R0 r0 R1 wh Heq_cur) with "regs PC R0 R1")
    as "(%Hlookup_PC & %Hlookup_R0 & %Hlookup_R1)";eauto.
  (* valid pt *)
  iDestruct (access_agree_check_true (tpa ai) i with "pgt_acc acc") as %Hcheckpg_ai;eauto.
  (* valid mem *)
  iDestruct (gen_mem_valid ai wi with "mem mem_ins") as %Hlookup_ai.
  iDestruct (gen_mem_valid_SepM_subseteq with "mem [mem_rx]") as %Hsubseteq_mem_rx.
  { iDestruct "mem_rx" as "[% mem_rx]". iExact "mem_rx". }
  (* valid tx rx *)
  iDestruct (mb_valid_tx i p_tx with "mb tx") as %Heq_tx.
  iDestruct (mb_valid_rx i p_rx with "mb rx") as %Heq_rx.
  iDestruct (rx_state_valid_None with "rx_state rx_s") as %Heq_rx_state.
  (* valid trans *)
  iDestruct (trans_valid_Some with "trans tran") as %[re Hlookup_tran].
  iDestruct (retri_valid_Some with "retri re") as %[meta Hlookup_tran'].
  rewrite Hlookup_tran in Hlookup_tran'.
  inversion Hlookup_tran'. subst re. clear meta Hlookup_tran' H1.
  iSplit.
  - (* reducible *)
    iPureIntro.
    apply (reducible_normal i Hvc ai wi);eauto.
    rewrite Heq_tx //.
  - iModIntro.
    iIntros (m2 σ2) "vmprop_auth %HstepP".
    iFrame "vmprop_auth".
    apply (step_ExecI_normal i Hvc ai wi) in HstepP;eauto.
    2: rewrite Heq_tx //.
    remember (exec Hvc σ1) as c2 eqn:Heqc2.
    rewrite /exec /hvc Hlookup_R0 /= Hdecode_f /retrieve Hlookup_R1 /get_transaction /= Hlookup_tran Heq_cur /=  in Heqc2.
    case_bool_decide;last done. clear H0.
    assert (is_Some(finz.of_z (finz_bound := word_size) (Z.of_nat (size ps + 4)%nat))) as [l Heq_l].
    {
      destruct Hwf as [Hub _].
      specialize (Hub wh _ Hlookup_tran).
      simpl in Hub.
      rewrite Z.leb_le in Hub.
      apply finz_of_z_is_Some.
      lia. lia.
    }
    rewrite Heq_l Heq_rx in Heqc2.
    rewrite /fill_rx in Heqc2.
    assert (Heq_mb: (σ1.1.1.1.1.2 !!! i) = (p_tx, (p_rx, None))).
    rewrite -Heq_tx -Heq_rx -Heq_rx_state. rewrite -2!surjective_pairing //.
    rewrite p_wr_mem_mb Heq_mb /= in Heqc2.
    destruct HstepP;subst m2 σ2; subst c2; simpl.
    rewrite /gen_vm_interp.
    (* unchanged part *)
    set σ_fill := (fill_rx_unsafe (write_mem_segment σ1 p_rx _) l i i p_tx p_rx).
    rewrite (preserve_get_mb_gmap σ_fill (update_incr_PC _)).
    2:  rewrite p_upd_pc_mb p_upd_reg_mb p_grnt_acc_mb p_upd_tran_mb //.
    rewrite p_fill_rx_mb. all : try rewrite p_wr_mem_mb //.
    rewrite (preserve_get_mb_gmap σ1).
    2: rewrite p_wr_mem_mb //.
    iFrame "Hnum mb".
    (* upd mem *)
    rewrite p_upd_pc_mem p_upd_reg_mem p_grnt_acc_mem p_upd_tran_mem p_fill_rx_mem u_wr_mem_mem.
    iDestruct "mem_rx" as "[%Hdom_mem_rx mem_rx]".
    set des := (list_to_map _).
    iDestruct (gen_mem_update_SepM _ (des ∪ mem_rx) with "mem mem_rx") as ">[mem mem_rx]".
    { symmetry. apply dom_wr_mem_subseteq.
      destruct Hwf as [Hub _].
      specialize (Hub wh _ Hlookup_tran).
      simpl in Hub.
      rewrite Z.leb_le in Hub.
      rewrite /= map_length .
      rewrite /size /set_size /= in Hub. lia.
      simpl. lia.
      done.
    }
    rewrite -map_union_assoc.
    assert (mem_rx ∪ σ1.1.2 = σ1.1.2). apply map_subseteq_union. done.
    iEval (rewrite H0) in "mem". clear H0. iFrame "mem". 
    (* upd regs *)
    rewrite (u_upd_pc_regs _ i ai). 2: done.
    2: { rewrite u_upd_reg_regs p_grnt_acc_current_vm p_upd_tran_current_vm /σ_fill.
         rewrite (preserve_get_reg_gmap σ1). rewrite lookup_insert_ne. solve_reg_lookup. done. f_equal.
    }
    rewrite u_upd_reg_regs p_grnt_acc_current_vm p_upd_tran_current_vm p_fill_rx_current_vm p_wr_mem_current_vm Heq_cur.
    rewrite (preserve_get_reg_gmap σ1);last done.
    iDestruct ((gen_reg_update2_global PC i _ (ai ^+ 1)%f R0 i _ (encode_hvc_ret_code Succ)) with "regs PC R0")
      as ">[$ [PC R0]]";eauto.
    (* upd pgt *)
    rewrite (preserve_get_own_gmap (update_page_table_global grant_access (update_transaction σ_fill wh (j, i, ps, Lending, true)) i ps) (update_incr_PC _)).
    2: rewrite p_upd_pc_pgt p_upd_reg_pgt //.
    rewrite p_grnt_acc_own. rewrite (preserve_get_own_gmap σ1);last done.
    iFrame "pgt_owned".
    rewrite (preserve_get_access_gmap (update_page_table_global grant_access (update_transaction σ_fill wh (j, i, ps, Lending, true)) i ps) (update_incr_PC _)).
    2: rewrite p_upd_pc_pgt p_upd_reg_pgt //.
    iDestruct (access_agree with "pgt_acc acc") as %Hlookup_pgt_acc.
    rewrite (u_grnt_acc_acc _ _ _ sacc).
    2: {
      rewrite p_upd_tran_pgt p_fill_rx_pgt p_wr_mem_pgt.
      intros p Hin_p.
      specialize (Hconsis wh _ Hlookup_tran p Hin_p).
      simpl in Hconsis.
      exists (Some j, true, ∅).
      done.
    }
    2: rewrite (preserve_get_access_gmap σ1);done.
    rewrite (preserve_get_access_gmap σ1);last done.
    iDestruct (access_update (ps ∪ sacc) with "pgt_acc acc") as ">[$ acc]". done.
    rewrite (preserve_get_excl_gmap (update_page_table_global grant_access (update_transaction σ_fill wh (j, i, ps, Lending, true)) i ps) (update_incr_PC _)).
    2: rewrite p_upd_pc_pgt p_upd_reg_pgt //.
    rewrite p_grnt_acc_excl.
    2: { rewrite p_upd_tran_pgt p_fill_rx_pgt p_wr_mem_pgt. specialize (Hconsis wh _ Hlookup_tran).
         intros p Hin.
         specialize (Hconsis p Hin).
         simpl in Hdisj.
         exists (Some j, true, ∅).
         split;done.
    }
    rewrite (preserve_get_excl_gmap σ1);last done.
    iFrame "pgt_excl".
    (* upd rx_state *)
    rewrite (preserve_get_rx_gmap σ_fill (update_incr_PC _)).
    2: rewrite p_upd_pc_mb p_upd_reg_mb p_grnt_acc_mb //.
    rewrite u_fill_rx_rx_state.
    rewrite (preserve_get_rx_gmap σ1); last done.
    iDestruct (rx_state_update with "rx_state rx_s") as ">[$ rx_s]".
    (* upd tran *)
    rewrite (preserve_get_trans_gmap (update_transaction σ_fill wh (j, i, ps, Lending, true)) (update_incr_PC _)).
    2: rewrite p_upd_pc_trans p_upd_reg_trans //.
    rewrite u_upd_tran_trans (preserve_get_trans_gmap σ1);last done.
    rewrite insert_id.
    2: rewrite /get_trans_gmap /get_transactions_gmap lookup_fmap Hlookup_tran //=.
    iFrame "trans".
    (* upd hp *)
    rewrite (preserve_get_hpool_gset (update_transaction σ_fill wh (j, i, ps, Lending, true)) (update_incr_PC _)).
    2: rewrite p_upd_pc_trans p_upd_reg_trans //. rewrite p_upd_tran_hp.
    iFrame "hpool".
    (* upd retri *)
    rewrite (preserve_get_retri_gmap (update_transaction σ_fill wh (j, i, ps, Lending, true)) (update_incr_PC _)).
    2: rewrite p_upd_pc_trans p_upd_reg_trans //.
    2: { rewrite p_fill_rx_trans p_wr_mem_trans. exists (Some (j, i, ps, Lending, false)). split;eauto. }
    rewrite u_upd_tran_retri.
    iDestruct (retri_update_flip with "retri re") as ">[$ re]".
    (* TODO *)
Admitted.

Lemma mem_retrieve_lend_rx{E i wi sacc r0 j mem_rx q p_tx} {ps: gset PID} ai wh:
  tpa ai ≠ p_tx ->
  (* the current instruction is hvc *)
  (* the decoding of wi is correct *)
  decode_instruction wi = Some(Hvc) ->
  (* the hvc call to invoke is retrieve *)
  decode_hvc_func r0 = Some(Retrieve) ->
  (* l is the number of involved pages, of type word *)
  {SS{{(* the encoding of instruction wi is stored in location ai *)
       ▷ (PC @@ i ->r ai) ∗ ▷ ai ->a wi ∗
       (* registers *)
       ▷ (R0 @@ i ->r r0) ∗
       ▷ (R1 @@ i ->r wh) ∗
       (* the pagetable *)
       ▷ i -@A> sacc ∗
       ▷ TX@i := p_tx ∗
       (* the transaction hasn't been retrieved *)
       ▷ wh ->re false ∗ ▷ wh -{q}>t (j, i, ps, Lending) ∗
       (* the rx page and locations that the rx descriptor will be at *)
       ▷ RX@ i := (tpa ai) ∗ ▷ RX_state@ i := None ∗
       ▷ (ai ->a wi -∗ memory_page (tpa ai) mem_rx)}}}
   ExecI @ i; E
   {{{ RET (false, ExecI) ;
       (* PC is incremented *)
       PC @@ i ->r (ai ^+ 1)%f ∗ ai ->a wi ∗
       (* return Succ to R0 *)
       R0 @@ i ->r (encode_hvc_ret_code Succ) ∗
       R1 @@ i ->r wh ∗
       (* gain exclusive access and ownership *)
       i -@A> (ps ∪ sacc) ∗
       TX@i := p_tx ∗
       wh ->re true ∗ wh -{q}>t (j, i, ps, Lending) ∗
       (* new descriptor in rx *)
       RX@ i := (tpa ai) ∗
       (∃ l des, RX_state@ i := Some(l, i) ∗ ⌜((Z.to_nat (finz.to_z l)) = (length des))%nat⌝ ∗
       (* XXX: not sure if it is useful *)
       (⌜des = ([of_imm (encode_vmid j); wh; encode_transaction_type Donation ;(l ^- 4)%f] ++ map of_pid (elements ps))⌝ ∗
                 memory_page (tpa ai) ((list_to_map (zip (finz.seq (tpa ai) (length des)) des)) ∪ mem_rx)))
        }}}.
Proof.
Admitted.


Lemma mem_retrieve_share{E i wi sacc r0 j mem_rx p_rx q p_tx} {ps: gset PID} ai wh:
  (* has access to the page which the instruction is in *)
  tpa ai ≠ p_tx ->
  (tpa ai) ∈ sacc ->
  (* the current instruction is hvc *)
  (* the decoding of wi is correct *)
  decode_instruction wi = Some(Hvc) ->
  (* the hvc call to invoke is retrieve *)
  decode_hvc_func r0 = Some(Retrieve) ->
  (* l is the number of involved pages, of type word *)
  {SS{{(* the encoding of instruction wi is stored in location ai *)
       ▷ (PC @@ i ->r ai) ∗ ▷ ai ->a wi ∗
       (* registers *)
       ▷ (R0 @@ i ->r r0) ∗
       ▷ (R1 @@ i ->r wh) ∗
       (* the pagetable *)
       ▷ i -@A> sacc ∗
       ▷ TX@i := p_tx ∗
       (* the transaction hasn't been retrieved *)
       ▷ wh ->re false ∗ ▷ wh -{q}>t (j, i, ps, Sharing) ∗
       (* the rx page and locations that the rx descriptor will be at *)
       ▷ RX@ i := p_rx ∗ ▷ RX_state@ i := None ∗
       ▷ memory_page p_rx mem_rx}}}
   ExecI @ i; E
   {{{ RET (false, ExecI) ;
       (* PC is incremented *)
       PC @@ i ->r (ai ^+ 1)%f ∗ ai ->a wi ∗
       (* return Succ to R0 *)
       R0 @@ i ->r (encode_hvc_ret_code Succ) ∗
       R1 @@ i ->r wh ∗
       (* gain exclusive access and ownership *)
       i -@A> (ps ∪ sacc) ∗
       TX@i := p_tx ∗
       wh ->re true ∗ wh -{q}>t (j, i, ps, Sharing) ∗
       (* new descriptor in rx *)
       RX@ i := p_rx ∗
       (∃ l des, RX_state@ i := Some(l, i) ∗ ⌜((Z.to_nat (finz.to_z l)) = (length des))%nat⌝ ∗
       (* XXX: not sure if it is useful *)
       (⌜des = ([of_imm (encode_vmid j); wh; encode_transaction_type Donation ;(l ^- 4)%f] ++ map of_pid (elements ps))⌝ ∗
                 memory_page p_rx ((list_to_map (zip (finz.seq p_rx (length des)) des)) ∪ mem_rx)))
        }}}.
Proof.
Admitted.

Lemma mem_retrieve_share_rx{E i wi sacc r0 j mem_rx q p_tx} {ps: gset PID} ai wh:
  tpa ai ≠ p_tx ->
  (* the current instruction is hvc *)
  (* the decoding of wi is correct *)
  decode_instruction wi = Some(Hvc) ->
  (* the hvc call to invoke is retrieve *)
  decode_hvc_func r0 = Some(Retrieve) ->
  (* l is the number of involved pages, of type word *)
  {SS{{(* the encoding of instruction wi is stored in location ai *)
       ▷ (PC @@ i ->r ai) ∗ ▷ ai ->a wi ∗
       (* registers *)
       ▷ (R0 @@ i ->r r0) ∗
       ▷ (R1 @@ i ->r wh) ∗
       (* the pagetable *)
       ▷ i -@A> sacc ∗
       ▷ TX@i := p_tx ∗
       (* the transaction hasn't been retrieved *)
       ▷ wh ->re false ∗ ▷ wh -{q}>t (j, i, ps, Sharing) ∗
       (* the rx page and locations that the rx descriptor will be at *)
       ▷ RX@ i := (tpa ai) ∗ ▷ RX_state@ i := None ∗
       ▷ (ai ->a wi -∗ memory_page (tpa ai) mem_rx)}}}
   ExecI @ i; E
   {{{ RET (false, ExecI) ;
       (* PC is incremented *)
       PC @@ i ->r (ai ^+ 1)%f ∗ ai ->a wi ∗
       (* return Succ to R0 *)
       R0 @@ i ->r (encode_hvc_ret_code Succ) ∗
       R1 @@ i ->r wh ∗
       (* gain exclusive access and ownership *)
       i -@A> (ps ∪ sacc) ∗
       TX@i := p_tx ∗
       wh ->re true ∗ wh -{q}>t (j, i, ps, Sharing) ∗
       (* new descriptor in rx *)
       RX@ i := (tpa ai) ∗
       (∃ l des, RX_state@ i := Some(l, i) ∗ ⌜((Z.to_nat (finz.to_z l)) = (length des))%nat⌝ ∗
       (* XXX: not sure if it is useful *)
       (⌜des = ([of_imm (encode_vmid j); wh; encode_transaction_type Donation ;(l ^- 4)%f] ++ map of_pid (elements ps))⌝ ∗
                 memory_page (tpa ai) ((list_to_map (zip (finz.seq (tpa ai) (length des)) des)) ∪ mem_rx)))
        }}}.
Proof.
Admitted.


End retrieve.
