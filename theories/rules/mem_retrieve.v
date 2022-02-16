From machine_program_logic.program_logic Require Import weakestpre.
From HypVeri Require Import lifting rules.rules_base stdpp_extra.
From HypVeri.algebra Require Import base mem reg pagetable mailbox trans.
From HypVeri.lang Require Import lang_extra reg_extra mem_extra pagetable_extra trans_extra.

Section retrieve.

Context `{hypparams: HypervisorParameters}.
Context `{vmG: !gen_VMG Σ}.

Lemma mem_retrieve_donate {E i wi sacc r0 sh j mem_rx p_rx} {ps: gset PID} ai wh:
  (* has access to the page which the instruction is in *)
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
       (* new descriptor in rx *)
       RX@ i := p_rx ∗
       (∃ l des, RX_state@ i := Some(l, i) ∗ ⌜((Z.to_nat (finz.to_z l)) = (length des))%nat⌝ ∗
       (* XXX: not sure if it is useful *)
       (⌜des = ([of_imm (encode_vmid j); wh; encode_transaction_type Donation ;(l ^- 5)%f] ++ map of_pid (elements ps))⌝ ∗
                 memory_page p_rx ((list_to_map (zip (finz.seq p_rx (length des)) des)) ∪ mem_rx))) ∗
       (* the transaction is completed, deallocate it and release the handle *)
       fresh_handles 1 (sh ∪ {[wh]}) }}}.
Proof.
Admitted.

Lemma mem_retrieve_donate_rx {E i wi sacc r0 sh j mem_rx } {ps: gset PID} ai wh:
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
       (* new descriptor in rx *)
       RX@ i := (tpa ai) ∗
       (∃ l des, RX_state@ i := Some(l, i) ∗ ⌜((Z.to_nat (finz.to_z l)) = (length des))%nat⌝ ∗
       (* XXX: not sure if it is useful *)
       (⌜des = ([of_imm (encode_vmid j); wh; encode_transaction_type Donation ;(l ^- 5)%f] ++ map of_pid (elements ps))⌝ ∗
                 memory_page (tpa ai) ((list_to_map (zip (finz.seq (tpa ai) (length des)) des)) ∪ mem_rx))) ∗
       (* the transaction is completed, deallocate it and release the handle *)
       fresh_handles 1 (sh ∪ {[wh]}) }}}.
Proof.
Admitted.

Lemma mem_retrieve_invalid_handle {E i wi sacc r0 r2 wh} ai:
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
       ▷ i -@A> sacc}}}
   ExecI @ i; E
   {{{ RET (false, ExecI) ;
       (* PC is incremented *)
       PC @@ i ->r (ai ^+ 1)%f ∗ ai ->a wi ∗
       R0 @@ i ->r (encode_hvc_ret_code Error) ∗
       R1 @@ i ->r wh ∗
       R2 @@ i ->r (encode_hvc_error InvParam) ∗
       i -@A> sacc
   }}}.
Proof.
Admitted.

Lemma mem_retrieve_fresh_handle {E i wi sacc r0 r2 wh sh q} ai:
  (tpa ai) ∈ sacc ->
  decode_instruction wi = Some(Hvc) ->
  decode_hvc_func r0 = Some(Retrieve) ->
  wh ∈ sh ->
  {SS{{▷ (PC @@ i ->r ai) ∗ ▷ ai ->a wi ∗
       ▷ (R0 @@ i ->r r0) ∗
       ▷ (R1 @@ i ->r wh) ∗
       ▷ (R2 @@ i ->r r2) ∗
       ▷ i -@A> sacc ∗
       ▷ fresh_handles q sh}}}
   ExecI @ i; E
   {{{ RET (false, ExecI) ;
       PC @@ i ->r (ai ^+ 1)%f ∗ ai ->a wi ∗
       R0 @@ i ->r (encode_hvc_ret_code Error) ∗
       R1 @@ i ->r wh ∗
       R2 @@ i ->r (encode_hvc_error InvParam) ∗
       i -@A> sacc ∗
       fresh_handles q sh
   }}}.
Proof.
Admitted.

Lemma mem_retrieve_invalid_trans {E i wi sacc r0 r2 wh meta q} ai:
  (tpa ai) ∈ sacc ->
  decode_instruction wi = Some(Hvc) ->
  decode_hvc_func r0 = Some(Retrieve) ->
  meta.1.1.2 ≠ i ->
  {SS{{▷ (PC @@ i ->r ai) ∗ ▷ ai ->a wi ∗
       ▷ (R0 @@ i ->r r0) ∗
       ▷ (R1 @@ i ->r wh) ∗
       ▷ (R2 @@ i ->r r2) ∗
       ▷ i -@A> sacc ∗
       ▷ wh -{q}>t (meta)
       }}}
   ExecI @ i; E
   {{{ RET (false, ExecI) ;
       PC @@ i ->r (ai ^+ 1)%f ∗ ai ->a wi ∗
       R0 @@ i ->r (encode_hvc_ret_code Error) ∗
       R1 @@ i ->r wh ∗
       R2 @@ i ->r (encode_hvc_error Denied) ∗
       i -@A> sacc ∗
       wh -{q}>t (meta)
   }}}.
Proof.
Admitted.

Lemma mem_retrieve_retrieved{E i wi sacc r0 r2 wh q} ai:
  (tpa ai) ∈ sacc ->
  decode_instruction wi = Some(Hvc) ->
  decode_hvc_func r0 = Some(Retrieve) ->
  {SS{{▷ (PC @@ i ->r ai) ∗ ▷ ai ->a wi ∗
       ▷ (R0 @@ i ->r r0) ∗
       ▷ (R1 @@ i ->r wh) ∗
       ▷ (R2 @@ i ->r r2) ∗
       ▷ i -@A> sacc ∗
       ▷ wh -{q}>re true
       }}}
   ExecI @ i; E
   {{{ RET (false, ExecI) ;
       PC @@ i ->r (ai ^+ 1)%f ∗ ai ->a wi ∗
       R0 @@ i ->r (encode_hvc_ret_code Error) ∗
       R1 @@ i ->r wh ∗
       R2 @@ i ->r (encode_hvc_error Denied) ∗
       i -@A> sacc ∗
       wh -{q}>re true
   }}}.
Proof.
Admitted.

Lemma mem_retrieve_rx_full{E i wi sacc r0 r2 q1 q2 j tt rx_state} {ps: gset PID} ai wh:
  (tpa ai) ∈ sacc ->
  decode_instruction wi = Some(Hvc) ->
  decode_hvc_func r0 = Some(Retrieve) ->
  is_Some (rx_state) ->
  {SS{{▷ (PC @@ i ->r ai) ∗ ▷ ai ->a wi ∗
       ▷ (R0 @@ i ->r r0) ∗
       ▷ (R1 @@ i ->r wh) ∗
       ▷ (R2 @@ i ->r r2) ∗
       ▷ i -@A> sacc ∗
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
       wh -{q1}>re false ∗
       wh -{q2}>t (j, i, ps, tt) ∗
       RX_state@i := rx_state
   }}}.
Proof.
Admitted.

Lemma mem_retrieve_lend{E i wi sacc r0 j mem_rx p_rx q} {ps: gset PID} ai wh:
  (* has access to the page which the instruction is in *)
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
       wh ->re true ∗ wh -{q}>t (j, i, ps, Lending) ∗
       (* new descriptor in rx *)
       RX@ i := p_rx ∗
       (∃ l des, RX_state@ i := Some(l, i) ∗ ⌜((Z.to_nat (finz.to_z l)) = (length des))%nat⌝ ∗
       (* XXX: not sure if it is useful *)
       (⌜des = ([of_imm (encode_vmid j); wh; encode_transaction_type Donation ;(l ^- 5)%f] ++ map of_pid (elements ps))⌝ ∗
                 memory_page p_rx ((list_to_map (zip (finz.seq p_rx (length des)) des)) ∪ mem_rx)))
        }}}.
Proof.
Admitted.

Lemma mem_retrieve_lend_rx{E i wi sacc r0 j mem_rx q} {ps: gset PID} ai wh:
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
       wh ->re true ∗ wh -{q}>t (j, i, ps, Lending) ∗
       (* new descriptor in rx *)
       RX@ i := (tpa ai) ∗
       (∃ l des, RX_state@ i := Some(l, i) ∗ ⌜((Z.to_nat (finz.to_z l)) = (length des))%nat⌝ ∗
       (* XXX: not sure if it is useful *)
       (⌜des = ([of_imm (encode_vmid j); wh; encode_transaction_type Donation ;(l ^- 5)%f] ++ map of_pid (elements ps))⌝ ∗
                 memory_page (tpa ai) ((list_to_map (zip (finz.seq (tpa ai) (length des)) des)) ∪ mem_rx)))
        }}}.
Proof.
Admitted.


Lemma mem_retrieve_share{E i wi sacc r0 j mem_rx p_rx q} {ps: gset PID} ai wh:
  (* has access to the page which the instruction is in *)
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
       wh ->re true ∗ wh -{q}>t (j, i, ps, Sharing) ∗
       (* new descriptor in rx *)
       RX@ i := p_rx ∗
       (∃ l des, RX_state@ i := Some(l, i) ∗ ⌜((Z.to_nat (finz.to_z l)) = (length des))%nat⌝ ∗
       (* XXX: not sure if it is useful *)
       (⌜des = ([of_imm (encode_vmid j); wh; encode_transaction_type Donation ;(l ^- 5)%f] ++ map of_pid (elements ps))⌝ ∗
                 memory_page p_rx ((list_to_map (zip (finz.seq p_rx (length des)) des)) ∪ mem_rx)))
        }}}.
Proof.
Admitted.

Lemma mem_retrieve_share_rx{E i wi sacc r0 j mem_rx q} {ps: gset PID} ai wh:
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
       wh ->re true ∗ wh -{q}>t (j, i, ps, Sharing) ∗
       (* new descriptor in rx *)
       RX@ i := (tpa ai) ∗
       (∃ l des, RX_state@ i := Some(l, i) ∗ ⌜((Z.to_nat (finz.to_z l)) = (length des))%nat⌝ ∗
       (* XXX: not sure if it is useful *)
       (⌜des = ([of_imm (encode_vmid j); wh; encode_transaction_type Donation ;(l ^- 5)%f] ++ map of_pid (elements ps))⌝ ∗
                 memory_page (tpa ai) ((list_to_map (zip (finz.seq (tpa ai) (length des)) des)) ∪ mem_rx)))
        }}}.
Proof.
Admitted.


End retrieve.
