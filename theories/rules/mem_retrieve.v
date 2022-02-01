From machine_program_logic.program_logic Require Import weakestpre.
From HypVeri Require Import lifting rules.rules_base stdpp_extra.
From HypVeri.algebra Require Import base mem reg pagetable mailbox trans.
From HypVeri.lang Require Import lang_extra reg_extra mem_extra pagetable_extra trans_extra.

Section retrieve.

Context `{hypparams: HypervisorParameters}.
Context `{vmG: !gen_VMG Σ}.

Lemma hvc_mem_retrieve_donate {E i wi sacc pi mem_tx r0 sh j wf mem_rx p_tx p_rx l } {ps: gset PID} ai wh:
  (tpa ai) ∈ sacc ->
  (* the current instruction is hvc *)
  (* the decoding of wi is correct *)
  decode_instruction wi = Some(Hvc) ->
  (* the instruction is in page pi *)
  addr_in_page ai pi ->
  (* the hvc call to invoke is retrieve *)
  decode_hvc_func r0 = Some(Retrieve) ->
  (* has access to the page which the instruction is in *)
  pi ∈ sacc ->
  (* has neither owership nor access to these pages *)
  ps ## sacc ->
  (* l is the number of involved pages, of type word *)
  (finz.to_z l) = Z.of_nat (size ps) ->
  {SS{{(* the encoding of instruction wi is stored in location ai *)
       ▷ (PC @@ i ->r ai) ∗ ▷ ai ->a wi ∗
       (* registers *)
       ▷ (R0 @@ i ->r r0) ∗
       ▷ (R1 @@ i ->r wh) ∗
       (* the pagetable *)
       ▷ ([∗ set] p ∈ ps, p -@O> j) ∗
       ▷ i -@A> sacc ∗
       (* the transaction hasn't been retrieved *)
       ▷ wh ->re false ∗ ▷ wh -{1}>t (j, wf, i, ps, Donation) ∗
       (* the tx page and the descriptor in it *)
       ▷ TX@ i := p_tx ∗ ▷ memory_page p_tx mem_tx∗
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
       (* the same tx *)
       TX@ i := p_tx ∗ memory_page p_tx mem_tx ∗
       (* new descriptor in rx *)
       RX@ i := p_rx ∗ RX_state@ i := Some((l ^+ 5)%f, i) ∗
       (* XXX: not sure if it is useful *)
       (∃ mem_rx, memory_page p_rx mem_rx ∗
          ⌜parse_transaction_descriptor mem_rx (of_pid p_rx) (size ps + 5) = Some (j,Some wh,wf,i,ps)⌝) ∗
       (* the transaction is completed, deallocate it and release the handle *)
       fresh_handles 1 (sh ∪ {[wh]}) }}}.
Proof.
Admitted.

Lemma hvc_mem_retrieve_invalid_handle {E i wi sacc pi r0 r2 mem_tx p_tx wh sh q_sh} {ps: gset PID} ai:
  (tpa ai) ∈ sacc ->
  (* the current instruction is hvc *)
  (* the decoding of wi is correct *)
  decode_instruction wi = Some(Hvc) ->
  (* the instruction is in page pi *)
  addr_in_page ai pi ->
  (* the hvc call to invoke is retrieve *)
  decode_hvc_func r0 = Some(Retrieve) ->
  wh ∈ sh ->
  {SS{{(* the encoding of instruction wi is stored in location ai *)
       ▷ (PC @@ i ->r ai) ∗ ▷ ai ->a wi ∗
       (* registers *)
       ▷ (R0 @@ i ->r r0) ∗
       ▷ (R1 @@ i ->r wh) ∗
       ▷ (R2 @@ i ->r r2) ∗
       ▷ i -@A> sacc ∗
       ▷ TX@i := p_tx ∗
       ▷ (memory_page p_tx mem_tx) ∗
       ▷ fresh_handles q_sh sh}}}
   ExecI @ i; E
   {{{ RET (false, ExecI) ;
       (* PC is incremented *)
       PC @@ i ->r (ai ^+ 1)%f ∗ ai ->a wi ∗
       R0 @@ i ->r (encode_hvc_ret_code Error) ∗
       R1 @@ i ->r wh ∗
       R2 @@ i ->r (encode_hvc_error InvParam) ∗
       i -@A> sacc ∗
       TX@i := p_tx ∗
       (memory_page p_tx mem_tx) ∗
       fresh_handles q_sh sh
   }}}.
Proof.
Admitted.

Lemma hvc_mem_retrieve_invalid_trans {E i wi sacc pi r0 r2 mem_tx p_tx wh meta} {ps: gset PID} ai:
  (tpa ai) ∈ sacc ->
  decode_instruction wi = Some(Hvc) ->
  addr_in_page ai pi ->
  decode_hvc_func r0 = Some(Retrieve) ->
  meta.1.1.2 ≠ i ->
  {SS{{▷ (PC @@ i ->r ai) ∗ ▷ ai ->a wi ∗
       ▷ (R0 @@ i ->r r0) ∗
       ▷ (R1 @@ i ->r wh) ∗
       ▷ (R2 @@ i ->r r2) ∗
       ▷ i -@A> sacc ∗
       ▷ TX@i := p_tx ∗
       ▷ (memory_page p_tx mem_tx) ∗
       ▷ wh -{1}>t (meta)
       }}}
   ExecI @ i; E
   {{{ RET (false, ExecI) ;
       PC @@ i ->r (ai ^+ 1)%f ∗ ai ->a wi ∗
       R0 @@ i ->r (encode_hvc_ret_code Error) ∗
       R1 @@ i ->r wh ∗
       R2 @@ i ->r (encode_hvc_error Denied) ∗
       i -@A> sacc ∗
       TX@i := p_tx ∗
       (memory_page p_tx mem_tx) ∗
       wh -{1}>t (meta)
   }}}.
Proof.
Admitted.

Lemma hvc_mem_retrieve_retrieved{E i wi sacc pi r0 r2 mem_tx p_tx wh} {ps: gset PID} ai:
  (tpa ai) ∈ sacc ->
  decode_instruction wi = Some(Hvc) ->
  addr_in_page ai pi ->
  decode_hvc_func r0 = Some(Retrieve) ->
  {SS{{▷ (PC @@ i ->r ai) ∗ ▷ ai ->a wi ∗
       ▷ (R0 @@ i ->r r0) ∗
       ▷ (R1 @@ i ->r wh) ∗
       ▷ (R2 @@ i ->r r2) ∗
       ▷ i -@A> sacc ∗
       ▷ TX@i := p_tx ∗
       ▷ (memory_page p_tx mem_tx) ∗
       ▷ wh -{1}>re true
       }}}
   ExecI @ i; E
   {{{ RET (false, ExecI) ;
       PC @@ i ->r (ai ^+ 1)%f ∗ ai ->a wi ∗
       R0 @@ i ->r (encode_hvc_ret_code Error) ∗
       R1 @@ i ->r wh ∗
       R2 @@ i ->r (encode_hvc_error Denied) ∗
       i -@A> sacc ∗
       TX@i := p_tx ∗
       (memory_page p_tx mem_tx) ∗
       wh -{1}>re true
   }}}.
Proof.
Admitted.

Lemma hvc_mem_retrieve_lend{E i wi sacc pi mem_tx r0 sh j wf mem_rx p_tx p_rx l } {ps: gset PID}
      ai wh:
  (tpa ai) ∈ sacc ->
  (* the current instruction is hvc *)
  (* the decoding of wi is correct *)
  decode_instruction wi = Some(Hvc) ->
  (* the instruction is in page pi *)
  addr_in_page ai pi ->
  (* the hvc call to invoke is retrieve *)
  decode_hvc_func r0 = Some(Retrieve) ->
  (* has access to the page which the instruction is in *)
  pi ∈ sacc ->
  (* has neither owership nor access to these pages *)
  ps ## sacc ->
  (* l is the number of involved pages, of type word *)
  (finz.to_z l) = Z.of_nat (size ps) ->
  {SS{{(* the encoding of instruction wi is stored in location ai *)
       ▷ (PC @@ i ->r ai) ∗ ▷ ai ->a wi ∗
       (* registers *)
       ▷ (R0 @@ i ->r r0) ∗
       ▷ (R1 @@ i ->r wh) ∗
       (* the pagetable *)
       ▷ i -@A> sacc ∗
       (* the transaction hasn't been retrieved *)
       ▷ wh ->re false ∗ ▷ wh -{1}>t (j, wf, i, ps, Lending) ∗
       (* the tx page and the descriptor in it *)
       ▷ TX@ i := p_tx ∗ ▷ memory_page p_tx mem_tx∗
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
       i -@A> (ps ∪ sacc) ∗
       wh ->re true ∗ wh -{1}>t (j, wf, i, ps, Lending) ∗
       (* the same tx *)
       TX@ i := p_tx ∗ memory_page p_tx mem_tx ∗
       (* new descriptor in rx *)
       RX@ i := p_rx ∗ RX_state@ i := Some((l ^+ 5)%f, i) ∗
       (* XXX: not sure if it is useful *)
       (∃ mem_rx, memory_page p_rx mem_rx ∗
          ⌜parse_transaction_descriptor mem_rx (of_pid p_rx) (size ps + 5) = Some (j,Some wh,wf,i,ps)⌝)
        }}}.
Proof.
Admitted.


Lemma hvc_mem_retrieve_share{E i wi sacc pi mem_tx r0 sh j wf mem_rx p_tx p_rx l } {ps: gset PID}
      ai wh:
  (tpa ai) ∈ sacc ->
  (* the current instruction is hvc *)
  (* the decoding of wi is correct *)
  decode_instruction wi = Some(Hvc) ->
  (* the instruction is in page pi *)
  addr_in_page ai pi ->
  (* the hvc call to invoke is retrieve *)
  decode_hvc_func r0 = Some(Retrieve) ->
  (* has access to the page which the instruction is in *)
  pi ∈ sacc ->
  (* has neither owership nor access to these pages *)
  ps ## sacc ->
  (* l is the number of involved pages, of type word *)
  (finz.to_z l) = Z.of_nat (size ps) ->
  {SS{{(* the encoding of instruction wi is stored in location ai *)
       ▷ (PC @@ i ->r ai) ∗ ▷ ai ->a wi ∗
       (* registers *)
       ▷ (R0 @@ i ->r r0) ∗
       ▷ (R1 @@ i ->r wh) ∗
       (* the pagetable *)
       ▷ i -@A> sacc ∗
       (* the transaction hasn't been retrieved *)
       ▷ wh ->re false ∗ ▷ wh -{1}>t (j, wf, i, ps, Sharing) ∗
       (* the tx page and the descriptor in it *)
       ▷ TX@ i := p_tx ∗ ▷ memory_page p_tx mem_tx∗
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
       i -@A> (ps ∪ sacc) ∗
       wh ->re true ∗ wh -{1}>t (j, wf, i, ps, Sharing) ∗
       (* the same tx *)
       TX@ i := p_tx ∗ memory_page p_tx mem_tx ∗
       (* new descriptor in rx *)
       RX@ i := p_rx ∗ RX_state@ i := Some((l ^+ 5)%f, i) ∗
       (* XXX: not sure if it is useful *)
       (∃ mem_rx, memory_page p_rx mem_rx ∗
          ⌜parse_transaction_descriptor mem_rx (of_pid p_rx) (size ps + 5) = Some (j,Some wh,wf,i,ps)⌝)
        }}}.
Proof.
Admitted.
