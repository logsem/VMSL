From machine_program_logic.program_logic Require Import weakestpre.
From HypVeri Require Import lifting rules.rules_base machine_extra.
From HypVeri.algebra Require Import base mem reg pagetable mailbox trans base_extra.
From HypVeri.lang Require Import lang_extra reg_extra mem_extra pagetable_extra trans_extra.

Section mem_share.

Context `{hypparams: HypervisorParameters}.
Context `{vmG: !gen_VMG Σ}.

Lemma hvc_mem_share_nz {i wi r0 r1 r2 hvcf p_tx sacc} ai j mem_tx sh (ps: gset PID) :
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
  parse_transaction_descriptor mem_tx (of_pid p_tx) len = Some (i,None,W0,j,ps) ->
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
   ExecI @ i {{{ RET (false,ExecI) ;
                 PC @@ i ->r (ai ^+ 1)%f ∗
                 ai ->a wi ∗
                 ([∗ set] p ∈ ps, p -@O> i ) ∗
                 i -@A> (sacc ∖ ps) ∗
                 R0 @@ i ->r (encode_hvc_ret_code Succ) ∗
                 R1 @@ i ->r r1 ∗
                 (∃ (wh: Word), ⌜wh ∈ sh⌝ ∗
                 R2 @@ i ->r wh ∗
                 wh ->t (i,W0,j,ps,Sharing) ∗
                 wh ->re false ∗
                 fresh_handles 1 (sh∖{[wh]})) ∗
                 TX@ i := p_tx ∗
                 memory_page p_tx mem_tx}}}.
Proof.
Admitted.

Lemma hvc_mem_send_invalid_len {i wi r0 r1 r2 hvcf tt q sacc p_tx} ai :
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
   ExecI @ i {{{ RET (false,ExecI) ;
                 PC @@ i ->r (ai ^+ 1)%f ∗
                 ai ->a wi ∗
                 i -@{q}A> sacc ∗
                 R0 @@ i ->r (encode_hvc_ret_code Error) ∗
                 R1 @@ i ->r r1 ∗
                 R2 @@ i ->r (encode_hvc_error InvParam) ∗
                 TX@ i := p_tx}}}.
Proof.
Admitted.

Lemma hvc_mem_send_invalid_msg {i wi r0 r1 r2 hvcf tt p_tx q sacc} ai mem_tx :
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
   ExecI @ i {{{ RET (false,ExecI) ;
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

Lemma hvc_mem_send_invalid_des {i wi r0 r1 r2 hvcf p_tx tt q sacc} ai mem_tx tran :
  (tpa ai) ∈ sacc ->
  (tpa ai) ≠ p_tx ->
  let len := (Z.to_nat (finz.to_z r1)) in
  decode_instruction wi = Some(Hvc) ->
  decode_hvc_func r0 = Some(hvcf) ->
  hvcf_to_tt hvcf = Some tt ->
  (len <= page_size)%Z ->
  parse_transaction_descriptor mem_tx (of_pid p_tx) len = Some tran ->
  validate_transaction_descriptor i tt tran = false ->
  {SS{{ ▷(PC @@ i ->r ai) ∗
      ▷ ai ->a wi ∗
      ▷ i -@{q}A> sacc ∗
      ▷ (R0 @@ i ->r r0) ∗
      ▷ (R1 @@ i ->r r1) ∗
      ▷ (R2 @@ i ->r r2) ∗
      ▷ (TX@ i := p_tx) ∗
      ▷ (memory_page p_tx mem_tx)
       }}}
   ExecI @ i {{{ RET (false,ExecI) ;
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

Lemma hvc_mem_send_not_owned {i wi r0 r1 r2 hvcf p_tx tt q sacc} ai mem_tx tran p O :
  (tpa ai) ∈ sacc ->
  (tpa ai) ≠ p_tx ->
  let len := (Z.to_nat (finz.to_z r1)) in
  decode_instruction wi = Some(Hvc) ->
  decode_hvc_func r0 = Some(hvcf) ->
  hvcf_to_tt hvcf = Some tt ->
  (len <= page_size)%Z ->
  parse_transaction_descriptor mem_tx (of_pid p_tx) len = Some tran ->
  validate_transaction_descriptor i tt tran = true ->
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
   ExecI @ i {{{ RET (false,ExecI) ;
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

Lemma hvc_mem_send_not_excl {i wi r0 r1 r2 hvcf p_tx tt q sacc} ai mem_tx tran p :
  (tpa ai) ∈ sacc ->
  (tpa ai) ≠ p_tx ->
  let len := (Z.to_nat (finz.to_z r1)) in
  decode_instruction wi = Some(Hvc) ->
  decode_hvc_func r0 = Some(hvcf) ->
  hvcf_to_tt hvcf = Some tt ->
  (len <= page_size)%Z ->
  parse_transaction_descriptor mem_tx (of_pid p_tx) len = Some tran ->
  validate_transaction_descriptor i tt tran = true ->
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
   ExecI @ i {{{ RET (false,ExecI) ;
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

Lemma hvc_mem_send_not_acc {i wi r0 r1 r2 hvcf p_tx tt sacc} ai mem_tx tran p :
  (tpa ai) ∈ sacc ->
  (tpa ai) ≠ p_tx ->
  let len := (Z.to_nat (finz.to_z r1)) in
  decode_instruction wi = Some(Hvc) ->
  decode_hvc_func r0 = Some(hvcf) ->
  hvcf_to_tt hvcf = Some tt ->
  (len <= page_size)%Z ->
  parse_transaction_descriptor mem_tx (of_pid p_tx) len = Some tran ->
  validate_transaction_descriptor i tt tran = true ->
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
   ExecI @ i {{{ RET (false,ExecI) ;
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

Lemma hvc_mem_send_in_trans {i wi r0 r1 r2 hvcf p_tx tt wh q tran' q' sacc} ai mem_tx tran p :
  (tpa ai) ∈ sacc ->
  (tpa ai) ≠ p_tx ->
  let len := (Z.to_nat (finz.to_z r1)) in
  decode_instruction wi = Some(Hvc) ->
  decode_hvc_func r0 = Some(hvcf) ->
  hvcf_to_tt hvcf = Some tt ->
  (len <= page_size)%Z ->
  parse_transaction_descriptor mem_tx (of_pid p_tx) len = Some tran ->
  validate_transaction_descriptor i tt tran = true ->
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
   ExecI @ i {{{ RET (false,ExecI) ;
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


End mem_share.

