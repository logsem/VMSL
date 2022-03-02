From machine_program_logic.program_logic Require Import weakestpre.
From HypVeri Require Import lifting rules.rules_base machine_extra.
From HypVeri.algebra Require Import base mem reg pagetable mailbox trans base_extra.
From HypVeri.lang Require Import lang_extra reg_extra mem_extra pagetable_extra trans_extra.

Section mem_send.

Context `{hypparams: HypervisorParameters}.
Context `{vmG: !gen_VMG Σ}.

Lemma parse_transaction_descriptor_tx mem_tx mem p_tx len tran:
 parse_transaction_descriptor mem_tx (of_pid p_tx) len = Some tran ->
 map_Forall (λ k v, mem !! k = Some v) mem_tx ->
 parse_transaction_descriptor mem (of_pid p_tx) len = Some tran.
Proof.
  rewrite /parse_transaction_descriptor.
  rewrite /parse_list_of_Word.
  intros Hparse Hforall.
  destruct (sequence_a (map (λ v : Addr, mem_tx !! v) (finz.seq p_tx len))) eqn:Heqn;last done.
  assert (sequence_a (map (λ v : Addr, mem !! v) (finz.seq p_tx len)) = Some l) as ->.
  {
    apply (sequence_a_map_subseteq _ _ _ mem_tx). done.
    rewrite map_subseteq_spec.
    intros.
    apply Hforall.
    done.
  }
  done.
Qed.

Lemma mem_send_invalid_len {i wi r0 r1 r2 hvcf tt q sacc p_tx} ai :
  (tpa ai) ∈ sacc ->
  (tpa ai) ≠ p_tx ->
  let len := (finz.to_z r1) in
  decode_instruction wi = Some(Hvc) ->
  decode_hvc_func r0 = Some(hvcf) ->
  hvcf_to_tt hvcf = Some tt ->
  (page_size < len)%Z ->
  {SS{{ ▷(PC @@ i ->r ai) ∗
      ▷ ai ->a wi ∗
      ▷ (i -@{q}A> sacc) ∗
      ▷ (R0 @@ i ->r r0) ∗
      ▷ (R1 @@ i ->r r1) ∗
      ▷ (R2 @@ i ->r r2) ∗
      ▷ TX@ i := p_tx
       }}}
   ExecI @ i {{{ RET (false, ExecI) ;
                 PC @@ i ->r (ai ^+ 1)%f ∗
                 ai ->a wi ∗
                 i -@{q}A> sacc ∗
                 R0 @@ i ->r (encode_hvc_ret_code Error) ∗
                 R1 @@ i ->r r1 ∗
                 R2 @@ i ->r (encode_hvc_error InvParam) ∗
                 TX@ i := p_tx}}}.
Proof.
Admitted.

Lemma mem_send_invalid_msg {i wi r0 r1 r2 hvcf tt p_tx q sacc} ai mem_tx :
  (tpa ai) ∈ sacc ->
  (tpa ai) ≠ p_tx ->
  let len := (Z.to_nat (finz.to_z r1)) in
  decode_instruction wi = Some(Hvc) ->
  decode_hvc_func r0 = Some(hvcf) ->
  hvcf_to_tt hvcf = Some tt ->
  (len <= page_size)%Z ->
  parse_transaction_descriptor mem_tx (of_pid p_tx) len = None ->
  {SS{{ ▷(PC @@ i ->r ai) ∗
      ▷ ai ->a wi ∗
      ▷ (i -@{q}A> sacc) ∗
      ▷ (R0 @@ i ->r r0) ∗
      ▷ (R1 @@ i ->r r1) ∗
      ▷ (R2 @@ i ->r r2) ∗
      ▷ (TX@ i := p_tx) ∗
      ▷ (memory_page p_tx mem_tx)
       }}}
   ExecI @ i {{{ RET (false, ExecI) ;
                 PC @@ i ->r (ai ^+ 1)%f ∗
                 ai ->a wi ∗
                 i -@{q}A> sacc ∗
                 R0 @@ i ->r (encode_hvc_ret_code Error) ∗
                 R1 @@ i ->r r1 ∗
                 R2 @@ i ->r (encode_hvc_error InvParam) ∗
                 TX@ i := p_tx ∗
                 memory_page p_tx mem_tx
    }}}.
Proof.
Admitted.

Lemma mem_send_invalid_des {i wi r0 r1 r2 hvcf p_tx tt q sacc} ai mem_tx tran :
  (tpa ai) ∈ sacc ->
  (tpa ai) ≠ p_tx ->
  let len := (Z.to_nat (finz.to_z r1)) in
  decode_instruction wi = Some(Hvc) ->
  decode_hvc_func r0 = Some(hvcf) ->
  hvcf_to_tt hvcf = Some tt ->
  (len <= page_size)%Z ->
  parse_transaction_descriptor mem_tx (of_pid p_tx) len = Some tran ->
  validate_transaction_descriptor i tran = false ->
  {SS{{ ▷(PC @@ i ->r ai) ∗
      ▷ ai ->a wi ∗
      ▷ i -@{q}A> sacc ∗
      ▷ (R0 @@ i ->r r0) ∗
      ▷ (R1 @@ i ->r r1) ∗
      ▷ (R2 @@ i ->r r2) ∗
      ▷ (TX@ i := p_tx) ∗
      ▷ (memory_page p_tx mem_tx)
       }}}
   ExecI @ i {{{ RET (false, ExecI) ;
                 PC @@ i ->r (ai ^+ 1)%f ∗
                 ai ->a wi ∗
                 i -@{q}A> sacc ∗
                 R0 @@ i ->r (encode_hvc_ret_code Error) ∗
                 R1 @@ i ->r r1 ∗
                 R2 @@ i ->r (encode_hvc_error InvParam) ∗
                 TX@ i := p_tx ∗
                 memory_page p_tx mem_tx
    }}}.
Proof.
Admitted.

Lemma mem_send_not_owned {i wi r0 r1 r2 hvcf p_tx tt q sacc} ai p O mem_tx tran :
  (tpa ai) ∈ sacc ->
  (tpa ai) ≠ p_tx ->
  let len := (Z.to_nat (finz.to_z r1)) in
  decode_instruction wi = Some(Hvc) ->
  decode_hvc_func r0 = Some(hvcf) ->
  hvcf_to_tt hvcf = Some tt ->
  (len <= page_size)%Z ->
  parse_transaction_descriptor mem_tx (of_pid p_tx) len = Some tran ->
  validate_transaction_descriptor i tran = true ->
  p ∈ tran.2 ->
  {SS{{ ▷(PC @@ i ->r ai) ∗
      ▷ ai ->a wi ∗
      ▷ i -@{q}A> sacc ∗
      ▷ (R0 @@ i ->r r0) ∗
      ▷ (R1 @@ i ->r r1) ∗
      ▷ (R2 @@ i ->r r2) ∗
      ▷ (TX@ i := p_tx) ∗
      ▷ (memory_page p_tx mem_tx) ∗
      ▷ O ∗
      ▷ (O -∗ (p -@O> - ∨ (∃j, p -@O> j ∗ ⌜j ≠ i⌝)))
       }}}
   ExecI @ i {{{ RET (false, ExecI) ;
                 PC @@ i ->r (ai ^+ 1)%f ∗
                 ai ->a wi ∗
                 i -@{q}A> sacc ∗
                 R0 @@ i ->r (encode_hvc_ret_code Error) ∗
                 R1 @@ i ->r r1 ∗
                 R2 @@ i ->r (encode_hvc_error Denied) ∗
                 TX@ i := p_tx ∗
                 memory_page p_tx mem_tx ∗
                 O
    }}}.
Proof.
Admitted.

Lemma mem_send_not_excl {i wi r0 r1 r2 hvcf p_tx tt q sacc} ai p mem_tx tran :
  (tpa ai) ∈ sacc ->
  (tpa ai) ≠ p_tx ->
  let len := (Z.to_nat (finz.to_z r1)) in
  decode_instruction wi = Some(Hvc) ->
  decode_hvc_func r0 = Some(hvcf) ->
  hvcf_to_tt hvcf = Some tt ->
  (len <= page_size)%Z ->
  parse_transaction_descriptor mem_tx (of_pid p_tx) len = Some tran ->
  validate_transaction_descriptor i tran = true ->
  p ∈ tran.2 ->
  {SS{{ ▷(PC @@ i ->r ai) ∗
      ▷ ai ->a wi ∗
      ▷ i -@{q}A> sacc ∗
      ▷ (R0 @@ i ->r r0) ∗
      ▷ (R1 @@ i ->r r1) ∗
      ▷ (R2 @@ i ->r r2) ∗
      ▷ (TX@ i := p_tx) ∗
      ▷ (memory_page p_tx mem_tx) ∗
      ▷ (p -@E> false)
       }}}
   ExecI @ i {{{ RET (false, ExecI) ;
                 PC @@ i ->r (ai ^+ 1)%f ∗
                 ai ->a wi ∗
                 i -@{q}A> sacc ∗
                 R0 @@ i ->r (encode_hvc_ret_code Error) ∗
                 R1 @@ i ->r r1 ∗
                 R2 @@ i ->r (encode_hvc_error Denied) ∗
                 TX@ i := p_tx ∗
                 memory_page p_tx mem_tx ∗
                 p -@E> false
    }}}.
Proof.
Admitted.

Lemma mem_send_not_acc {i wi r0 r1 r2 hvcf p_tx tt sacc} ai p mem_tx tran:
  (tpa ai) ∈ sacc ->
  (tpa ai) ≠ p_tx ->
  let len := (Z.to_nat (finz.to_z r1)) in
  decode_instruction wi = Some(Hvc) ->
  decode_hvc_func r0 = Some(hvcf) ->
  hvcf_to_tt hvcf = Some tt ->
  (len <= page_size)%Z ->
  parse_transaction_descriptor mem_tx (of_pid p_tx) len = Some tran ->
  validate_transaction_descriptor i tran = true ->
  p ∈ tran.2 ->
  p ∉ sacc ->
  {SS{{ ▷(PC @@ i ->r ai) ∗
      ▷ ai ->a wi ∗
      ▷ (R0 @@ i ->r r0) ∗
      ▷ (R1 @@ i ->r r1) ∗
      ▷ (R2 @@ i ->r r2) ∗
      ▷ (TX@ i := p_tx) ∗
      ▷ (memory_page p_tx mem_tx) ∗
      ▷ (i -@A> sacc)
       }}}
   ExecI @ i {{{ RET (false, ExecI) ;
                 PC @@ i ->r (ai ^+ 1)%f ∗
                 ai ->a wi ∗
                 R0 @@ i ->r (encode_hvc_ret_code Error) ∗
                 R1 @@ i ->r r1 ∗
                 R2 @@ i ->r (encode_hvc_error Denied) ∗
                 TX@ i := p_tx ∗
                 memory_page p_tx mem_tx ∗
                 i -@A> sacc
    }}}.
Proof.
Admitted.

Lemma mem_send_in_trans {i wi r0 r1 r2 hvcf p_tx tt tran q tran' q' sacc} ai p wh mem_tx:
  (tpa ai) ∈ sacc ->
  (tpa ai) ≠ p_tx ->
  let len := (Z.to_nat (finz.to_z r1)) in
  decode_instruction wi = Some(Hvc) ->
  decode_hvc_func r0 = Some(hvcf) ->
  hvcf_to_tt hvcf = Some tt ->
  (len <= page_size)%Z ->
  parse_transaction_descriptor mem_tx (of_pid p_tx) len = Some tran ->
  validate_transaction_descriptor i tran = true ->
  p ∈ tran.2 ->
  p ∈ tran'.1.2 ->
  {SS{{ ▷(PC @@ i ->r ai) ∗
      ▷ ai ->a wi ∗
      ▷ i -@{q'}A> sacc ∗
      ▷ (R0 @@ i ->r r0) ∗
      ▷ (R1 @@ i ->r r1) ∗
      ▷ (R2 @@ i ->r r2) ∗
      ▷ (TX@ i := p_tx) ∗
      ▷ (memory_page p_tx mem_tx) ∗
      ▷ (wh -{q}>t tran')
       }}}
   ExecI @ i {{{ RET (false, ExecI) ;
                 PC @@ i ->r (ai ^+ 1)%f ∗
                 ai ->a wi ∗
                 i -@{q'}A> sacc ∗
                 R0 @@ i ->r (encode_hvc_ret_code Error) ∗
                 R1 @@ i ->r r1 ∗
                 R2 @@ i ->r (encode_hvc_error Denied) ∗
                 TX@ i := p_tx ∗
                 memory_page p_tx mem_tx ∗
                 wh -{q}>t tran'
    }}}.
Proof.
Admitted.

Lemma mem_send_no_fresh_handles {i wi r0 r1 r2 hvcf tt p_tx sacc} ai sh j mem_tx (ps: gset PID):
  (tpa ai) ∈ sacc ->
  (tpa ai) ≠ p_tx ->
  let len := (Z.to_nat (finz.to_z r1)) in
  decode_instruction wi = Some(Hvc) ->
  decode_hvc_func r0 = Some(hvcf) ->
  hvcf_to_tt hvcf = Some tt ->
  (len <= page_size)%Z ->
  parse_transaction_descriptor mem_tx (of_pid p_tx) len = Some (i, None, j, ps) ->
  i ≠ j ->
  ps ⊆ sacc ->
  sh = ∅ ->
  {SS{{ ▷(PC @@ i ->r ai) ∗
      ▷ ai ->a wi ∗
      ▷ ([∗ set] p ∈ ps, p -@O> i ∗ p -@E> true) ∗
      ▷ (i -@A> sacc) ∗
      ▷ (R0 @@ i ->r r0) ∗
      ▷ (R1 @@ i ->r r1) ∗
      ▷ (R2 @@i ->r r2) ∗
      ▷ (fresh_handles 1 sh) ∗
      ▷ TX@ i := p_tx ∗
      ▷ memory_page p_tx mem_tx
       }}}
   ExecI @ i {{{ RET (false, ExecI) ;
                 PC @@ i ->r (ai ^+ 1)%f ∗
                 ai ->a wi ∗
                 ([∗ set] p ∈ ps, p -@O> i ∗ p -@E> true) ∗
                 i -@A> sacc ∗
                 R0 @@ i ->r (encode_hvc_ret_code Error) ∗
                 R1 @@ i ->r r1 ∗
                 R2 @@ i ->r (encode_hvc_error NoMem) ∗
                 fresh_handles 1 sh ∗
                 TX@ i := p_tx ∗
                 memory_page p_tx mem_tx}}}.
Proof.
Admitted.

Lemma mem_share {i wi r0 r1 r2 hvcf p_tx sacc} ai j mem_tx sh (ps: gset PID) :
  (tpa ai) ∈ sacc ->
  (tpa ai) ≠ p_tx ->
  (* len is the length of the msg *)
  let len := (Z.to_nat (finz.to_z r1)) in
  (* the decoding of wi is correct *)
  decode_instruction wi = Some(Hvc) ->
  (* the decoding of R0 is a FFA mem_share *)
  decode_hvc_func r0 = Some(hvcf) ->
  hvcf_to_tt hvcf = Some Sharing ->
  (* the whole descriptor resides in the TX page *)
  (len <= page_size)%Z ->
  (* the descriptor *)
  parse_transaction_descriptor mem_tx (of_pid p_tx) len = Some (i, None, j, ps) ->
  (* caller is not the receiver *)
  i ≠ j ->
  ps ⊆ sacc ->
  (* there is at least one free handle in the hpool *)
  sh ≠ ∅ ->
  {SS{{ ▷(PC @@ i ->r ai) ∗
      ▷ ai ->a wi ∗
      (* VM i exclusively owns pages in ps *)
      ▷ ([∗ set] p ∈ ps, p -@O> i ∗ p -@E> true) ∗
      ▷ (i -@A> sacc) ∗
      ▷ (R0 @@ i ->r r0) ∗
      ▷ (R1 @@ i ->r r1) ∗
      ▷ (R2 @@i ->r r2) ∗
      ▷ (fresh_handles 1 sh) ∗
      ▷ TX@ i := p_tx ∗
      ▷ memory_page p_tx mem_tx
       }}}
   ExecI @ i {{{ RET (false, ExecI) ;
                 PC @@ i ->r (ai ^+ 1)%f ∗
                 ai ->a wi ∗
                 ([∗ set] p ∈ ps, p -@O> i ∗ p -@E> false) ∗
                 i -@A> sacc ∗
                 R0 @@ i ->r (encode_hvc_ret_code Succ) ∗
                 R1 @@ i ->r r1 ∗
                 (∃ (wh: Word), ⌜wh ∈ sh⌝ ∗
                 R2 @@ i ->r wh ∗
                 wh ->t (i, j, ps, Sharing) ∗
                 wh ->re false ∗
                 fresh_handles 1 (sh∖{[wh]})) ∗
                 TX@ i := p_tx ∗
                 memory_page p_tx mem_tx}}}.
Proof.
  iIntros (Hin_acc Hneq_tx len Hdecode_i Hdecode_f Htt Hle_ps Hparse Hneq_vmid Hsubseteq_acc Hneq_hp Φ)
          "(>PC & >mem_ins & >oe & >acc & >R0 & >R1 & >R2 & >[hp handles] & >tx & >mem_tx) HΦ".
  iApply (sswp_lift_atomic_step ExecI);[done|].
  iIntros (n σ1) "%Hsche state".
  rewrite /scheduled /= /scheduler in Hsche.
  assert (σ1.1.1.2 = i) as Heq_cur. { case_bool_decide;last done. by apply fin_to_nat_inj. }
  clear Hsche.
  iModIntro.
  iDestruct "state" as "(Hnum & mem & regs & mb & rx_state & pgt_owned & pgt_acc & pgt_excl &
                            trans & hpool & retri & %Hwf & %Hconsis & %Hdisj)".
  (* valid regs *)
  iDestruct ((gen_reg_valid4 i PC ai R0 r0 R1 r1 R2 r2 Heq_cur) with "regs PC R0 R1 R2")
    as "(%Hlookup_PC & %Hlookup_R0 & %Hlookup_R1 & %Hlookup_R2)";eauto.
  (* valid pt *)
  iDestruct (access_agree_check_true (tpa ai) i with "pgt_acc acc") as %Hcheckpg_ai;eauto.
  iDestruct (access_agree_check_true_forall with "pgt_acc acc") as %Hcheckpg_acc;eauto.
  iDestruct (big_sepS_sep with "oe") as "[own excl]".
  iDestruct (excl_agree_Some_check_true_bigS with "pgt_excl excl") as %Hcheckpg_excl;eauto.
  iDestruct (own_agree_Some_check_true_bigS with "pgt_owned own") as %Hcheckpg_own;eauto.
  (* valid mem *)
  iDestruct (gen_mem_valid ai wi with "mem mem_ins") as %Hlookup_ai.
  iDestruct (gen_mem_valid_SepM with "mem [mem_tx]") as %Hlookup_mem_tx.
  { iDestruct "mem_tx" as "[% mem_tx]". iExact "mem_tx". }
  (* valid tx *)
  iDestruct (mb_valid_tx i p_tx with "mb tx") as %Heq_tx.
  (* valid hpool *)
  iDestruct (hpool_valid with "hpool hp") as %Heq_hp.
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
    destruct hvcf; inversion Htt.
    rewrite /exec /hvc Hlookup_R0 /= Hdecode_f /mem_send Hlookup_R1 /= in Heqc2.
    case_bool_decide;first lia.
    rewrite -Heq_tx -Heq_cur /len in Hparse.
    apply (parse_transaction_descriptor_tx _ σ1.1.2) in Hparse;last done.
    rewrite Hparse //= in Heqc2.
    case_bool_decide.
    2: { destruct H1. split;auto. split;eauto. rewrite Heq_cur //. }
    case_bool_decide.
    2: { destruct H2. intros s Hin.
         rewrite Heq_cur.
         rewrite andb_true_iff. split.
         rewrite /check_excl_access_page.
         rewrite andb_true_iff. split.
         apply Hcheckpg_acc.
         set_solver + Hsubseteq_acc Hin.
         by apply Hcheckpg_excl.
         by apply Hcheckpg_own.
    }
    rewrite /new_transaction /= /fresh_handle /= -Heq_hp in Heqc2.
    destruct (elements sh) as [| h fhs] eqn:Hfhs.
    { exfalso. rewrite -elements_empty in Hfhs.  apply Hneq_hp. apply set_eq.
      intro. rewrite -elem_of_elements Hfhs elem_of_elements. split;intro;set_solver. }
    destruct HstepP;subst m2 σ2; subst c2; simpl.
    rewrite /gen_vm_interp.
    (* unchanged part *)
    rewrite (preserve_get_mb_gmap σ1).
    rewrite (preserve_get_rx_gmap σ1).
    all: try rewrite p_upd_pc_mb //.
    rewrite p_upd_pc_mem 2!p_upd_reg_mem p_flip_excl_mem p_alloc_trans_mem.
    iFrame "Hnum mem rx_state mb".
    (* upd regs *)
    rewrite Heq_cur.
    rewrite (u_upd_pc_regs _ i ai) //.
    2: { rewrite 2!u_upd_reg_regs.
         rewrite (preserve_get_reg_gmap σ1). rewrite lookup_insert_ne //.  rewrite lookup_insert_ne //. solve_reg_lookup. done.
    }
    rewrite u_upd_reg_regs p_upd_reg_current_vm p_flip_excl_current_vm p_alloc_trans_current_vm  Heq_cur.
    rewrite u_upd_reg_regs p_flip_excl_current_vm p_alloc_trans_current_vm  Heq_cur.
    rewrite (preserve_get_reg_gmap σ1) //.
    iDestruct ((gen_reg_update3_global PC i (ai ^+ 1)%f R2 i h R0 i (encode_hvc_ret_code Succ)) with "regs PC R2 R0")
      as ">[$ [PC [R2 R0]]]";eauto.
    (* upd pgt *)
    rewrite (preserve_get_own_gmap (update_page_table_global flip_excl (alloc_transaction σ1 h (i, j, ps, Sharing, false)) i ps) (update_incr_PC _)).
    2: rewrite p_upd_pc_pgt !p_upd_reg_pgt //.
    rewrite p_flip_excl_own. rewrite (preserve_get_own_gmap σ1) //.
    iFrame "pgt_owned".
    rewrite (preserve_get_access_gmap (update_page_table_global flip_excl (alloc_transaction σ1 h (i, j, ps, Sharing, false)) i ps) (update_incr_PC _)).
    2: rewrite p_upd_pc_pgt p_upd_reg_pgt //.
    rewrite p_flip_excl_acc. rewrite (preserve_get_access_gmap σ1) //.
    iFrame "pgt_acc".
    rewrite (preserve_get_excl_gmap (update_page_table_global flip_excl (alloc_transaction σ1 h (i, j, ps, Sharing, false)) i ps) (update_incr_PC _)).
    2: rewrite p_upd_pc_pgt p_upd_reg_pgt //.

    (* rewrite (preserve_get_excl_gmap σ1) //. *)
    (* iFrame "pgt_excl". *)
Admitted.

Lemma mem_lend {i wi r0 r1 r2 hvcf p_tx sacc} ai j mem_tx sh (ps: gset PID) :
  (tpa ai) ∈ sacc ->
  (tpa ai) ≠ p_tx ->
  (* len is the length of the msg *)
  let len := (Z.to_nat (finz.to_z r1)) in
  (* the decoding of wi is correct *)
  decode_instruction wi = Some(Hvc) ->
  (* the decoding of R0 is a FFA mem_share *)
  decode_hvc_func r0 = Some(hvcf) ->
  hvcf_to_tt hvcf = Some Lending ->
  (* the whole descriptor resides in the TX page *)
  (len <= page_size)%Z ->
  (* the descriptor *)
  parse_transaction_descriptor mem_tx (of_pid p_tx) len = Some (i, None, j, ps) ->
  (* caller is not the receiver *)
  i ≠ j ->
  ps ⊆ sacc ->
  (* there is at least one free handle in the hpool *)
  sh ≠ ∅ ->
  {SS{{ ▷(PC @@ i ->r ai) ∗
      ▷ ai ->a wi ∗
      (* VM i exclusively owns pages in ps *)
      ▷ ([∗ set] p ∈ ps, p -@O> i ∗ p -@E> true) ∗
      ▷ (i -@A> sacc) ∗
      ▷ (R0 @@ i ->r r0) ∗
      ▷ (R1 @@ i ->r r1) ∗
      ▷ (R2 @@i ->r r2) ∗
      ▷ (fresh_handles 1 sh) ∗
      ▷ TX@ i := p_tx ∗
      ▷ memory_page p_tx mem_tx
       }}}
   ExecI @ i {{{ RET (false, ExecI) ;
                 PC @@ i ->r (ai ^+ 1)%f ∗
                 ai ->a wi ∗
                 ([∗ set] p ∈ ps, p -@O> i ∗ p -@E> true) ∗
                 i -@A> (sacc ∖ ps) ∗
                 R0 @@ i ->r (encode_hvc_ret_code Succ) ∗
                 R1 @@ i ->r r1 ∗
                 (∃ (wh: Word), ⌜wh ∈ sh⌝ ∗
                 R2 @@ i ->r wh ∗
                 wh ->t (i, j, ps, Lending) ∗
                 wh ->re false ∗
                 fresh_handles 1 (sh∖{[wh]})) ∗
                 TX@ i := p_tx ∗
                 memory_page p_tx mem_tx}}}.
Proof.
Admitted.

Lemma mem_donate {i wi r0 r1 r2 hvcf p_tx sacc} ai j mem_tx sh (ps: gset PID) :
  (tpa ai) ∈ sacc ->
  (tpa ai) ≠ p_tx ->
  (* len is the length of the msg *)
  let len := (Z.to_nat (finz.to_z r1)) in
  (* the decoding of wi is correct *)
  decode_instruction wi = Some(Hvc) ->
  (* the decoding of R0 is a FFA mem_share *)
  decode_hvc_func r0 = Some(hvcf) ->
  hvcf_to_tt hvcf = Some Donation ->
  (* the whole descriptor resides in the TX page *)
  (len <= page_size)%Z ->
  (* the descriptor *)
  parse_transaction_descriptor mem_tx (of_pid p_tx) len = Some (i, None, j, ps) ->
  (* caller is not the receiver *)
  i ≠ j ->
  ps ⊆ sacc ->
  (* there is at least one free handle in the hpool *)
  sh ≠ ∅ ->
  {SS{{ ▷(PC @@ i ->r ai) ∗
      ▷ ai ->a wi ∗
      (* VM i exclusively owns pages in ps *)
      ▷ ([∗ set] p ∈ ps, p -@O> i ∗ p -@E> true) ∗
      ▷ (i -@A> sacc) ∗
      ▷ (R0 @@ i ->r r0) ∗
      ▷ (R1 @@ i ->r r1) ∗
      ▷ (R2 @@i ->r r2) ∗
      ▷ (fresh_handles 1 sh) ∗
      ▷ TX@ i := p_tx ∗
      ▷ memory_page p_tx mem_tx
       }}}
   ExecI @ i {{{ RET (false, ExecI) ;
                 PC @@ i ->r (ai ^+ 1)%f ∗
                 ai ->a wi ∗
                 ([∗ set] p ∈ ps, p -@O> i ∗ p -@E> true) ∗
                 i -@A> (sacc ∖ ps) ∗
                 R0 @@ i ->r (encode_hvc_ret_code Succ) ∗
                 R1 @@ i ->r r1 ∗
                 (∃ (wh: Word), ⌜wh ∈ sh⌝ ∗
                 R2 @@ i ->r wh ∗
                 wh ->t (i, j, ps, Donation) ∗
                 wh ->re false ∗
                 fresh_handles 1 (sh∖{[wh]})) ∗
                 TX@ i := p_tx ∗
                 memory_page p_tx mem_tx}}}.
Proof.
Admitted.

End mem_send.
