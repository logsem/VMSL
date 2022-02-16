From machine_program_logic.program_logic Require Import weakestpre.
From HypVeri Require Import lifting rules.rules_base stdpp_extra.
From HypVeri.algebra Require Import base reg mem pagetable trans mailbox.
From HypVeri.lang Require Import lang_extra mem_extra reg_extra pagetable_extra trans_extra.

Section mem_reclaim.

Context `{hypparams: HypervisorParameters}.
Context `{vmG: !gen_VMG Σ}.

Lemma mem_reclaim_lend {E i wi sacc j sh r0 p_tx} {spsd: gset PID}
      ai wh:
  tpa ai ≠ p_tx ->
  tpa ai ∈ sacc ->
  (* current instruction is hvc *)
  decode_instruction wi = Some(Hvc) ->
  (* the hvc call to invoke is relinquish *)
  decode_hvc_func r0 = Some(Reclaim) ->
  {SS{{(* the encoding of instruction wi is stored in location ai *)
       ▷(PC @@ i ->r ai) ∗ ▷ ai ->a wi ∗
       (* the handle of transaction is stored in R1 *)
       ▷ (R0 @@ i ->r r0) ∗ ▷ (R1 @@ i ->r wh) ∗
       (* the pagetable *)
       ▷ i -@A> sacc ∗
       ▷ TX@ i := p_tx ∗
       (* the transaction has not been retrieved/has been relinquished *)
       ▷ wh ->re false ∗ ▷ wh ->t (i, j, spsd, Lending) ∗
       (* handle pool *)
       ▷ fresh_handles 1 sh}}}
  ExecI @ i; E
  {{{ RET (false, ExecI) ;
      (* PC is incremented *)
      PC @@ i ->r (ai ^+ 1)%f ∗ ai ->a wi ∗
      (* return Succ to R0*)
      R0 @@ i ->r (encode_hvc_ret_code Succ) ∗ (R1 @@ i ->r wh) ∗
      (* gain access/ownership of those pages *)
      i -@A> (sacc ∪ spsd) ∗
      TX@ i := p_tx ∗
      (* the transaction is deallocated, release the handle to the handle pool *)
      fresh_handles 1 (sh ∪ {[wh]}) }}}.
Proof.
Admitted.

Lemma mem_reclaim_donate {E i wi sacc j sh r0 p_tx} {spsd: gset PID}
      ai wh:
  tpa ai ≠ p_tx ->
  tpa ai ∈ sacc ->
  (* current instruction is hvc *)
  decode_instruction wi = Some(Hvc) ->
  (* the hvc call to invoke is relinquish *)
  decode_hvc_func r0 = Some(Reclaim) ->
  {SS{{(* the encoding of instruction wi is stored in location ai *)
       ▷(PC @@ i ->r ai) ∗ ▷ ai ->a wi ∗
       (* the handle of transaction is stored in R1 *)
       ▷ (R0 @@ i ->r r0) ∗ ▷ (R1 @@ i ->r wh) ∗
       (* the pagetable *)
       ▷ i -@A> sacc ∗
       ▷ TX@ i := p_tx ∗
       (* the transaction has not been retrieved/has been relinquished *)
       ▷ wh ->re false ∗ ▷ wh ->t (i, j, spsd, Donation) ∗
       (* handle pool *)
       ▷ fresh_handles 1 sh}}}
  ExecI @ i; E
  {{{ RET (false, ExecI) ;
      (* PC is incremented *)
      PC @@ i ->r (ai ^+ 1)%f ∗ ai ->a wi ∗
      (* return Succ to R0*)
      R0 @@ i ->r (encode_hvc_ret_code Succ) ∗ (R1 @@ i ->r wh) ∗
      (* gain access/ownership of those pages *)
      i -@A> (sacc ∪ spsd) ∗
      TX@ i := p_tx ∗
      (* the transaction is deallocated, release the handle to the handle pool *)
      fresh_handles 1 (sh ∪ {[wh]}) }}}.
Proof.
Admitted.

Lemma mem_reclaim_share {E i wi sacc j sh r0 p_tx} {spsd: gset PID}
      ai wh:
  tpa ai ≠ p_tx ->
  tpa ai ∈ sacc ->
  (* current instruction is hvc *)
  decode_instruction wi = Some(Hvc) ->
  (* the hvc call to invoke is relinquish *)
  decode_hvc_func r0 = Some(Reclaim) ->
  {SS{{(* the encoding of instruction wi is stored in location ai *)
       ▷(PC @@ i ->r ai) ∗ ▷ ai ->a wi ∗
       (* the handle of transaction is stored in R1 *)
       ▷ (R0 @@ i ->r r0) ∗ ▷ (R1 @@ i ->r wh) ∗
       (* the pagetable *)
       ▷ i -@A> sacc ∗
       ▷ ([∗ set] p ∈ spsd, p -@E> false) ∗
       ▷ TX@ i := p_tx ∗
       (* the transaction has not been retrieved/has been relinquished *)
       ▷ wh ->re false ∗ ▷ wh ->t (i, j, spsd, Sharing) ∗
       (* handle pool *)
       ▷ fresh_handles 1 sh}}}
  ExecI @ i; E
  {{{ RET (false, ExecI) ;
      (* PC is incremented *)
      PC @@ i ->r (ai ^+ 1)%f ∗ ai ->a wi ∗
      (* return Succ to R0*)
      R0 @@ i ->r (encode_hvc_ret_code Succ) ∗ (R1 @@ i ->r wh) ∗
      (* gain access/ownership of those pages *)
      i -@A> (sacc ∪ spsd) ∗
      ([∗ set] p ∈ spsd, p -@E> true) ∗
      TX@ i := p_tx ∗
      (* the transaction is deallocated, release the handle to the handle pool *)
      fresh_handles 1 (sh ∪ {[wh]}) }}}.
Proof.
Admitted.

Lemma mem_reclaim_invalid_handle {E i wi sacc r0 r2 wh p_tx} ai:
  tpa ai ≠ p_tx ->
  (tpa ai) ∈ sacc ->
  (* the current instruction is hvc *)
  (* the decoding of wi is correct *)
  decode_instruction wi = Some(Hvc) ->
  (* the hvc call to invoke is retrieve *)
  decode_hvc_func r0 = Some(Reclaim) ->
  wh ∉ hs_all ->
  {SS{{(* the encoding of instruction wi is stored in location ai *)
       ▷ (PC @@ i ->r ai) ∗ ▷ ai ->a wi ∗
       (* registers *)
       ▷ (R0 @@ i ->r r0) ∗
       ▷ (R1 @@ i ->r wh) ∗
       ▷ (R2 @@ i ->r r2) ∗
       ▷ i -@A> sacc ∗
       ▷ TX@ i := p_tx}}}
   ExecI @ i; E
   {{{ RET (false, ExecI) ;
       (* PC is incremented *)
       PC @@ i ->r (ai ^+ 1)%f ∗ ai ->a wi ∗
       R0 @@ i ->r (encode_hvc_ret_code Error) ∗
       R1 @@ i ->r wh ∗
       R2 @@ i ->r (encode_hvc_error InvParam) ∗
       i -@A> sacc ∗
       TX@ i := p_tx
   }}}.
Proof.
Admitted.

Lemma mem_reclaim_fresh_handle {E i wi sacc r0 r2 wh sh q p_tx} ai:
  tpa ai ≠ p_tx ->
  (tpa ai) ∈ sacc ->
  decode_instruction wi = Some(Hvc) ->
  decode_hvc_func r0 = Some(Reclaim) ->
  wh ∈ sh ->
  {SS{{▷ (PC @@ i ->r ai) ∗ ▷ ai ->a wi ∗
       ▷ (R0 @@ i ->r r0) ∗
       ▷ (R1 @@ i ->r wh) ∗
       ▷ (R2 @@ i ->r r2) ∗
       ▷ i -@A> sacc ∗
       ▷ TX@ i := p_tx ∗
       ▷ fresh_handles q sh}}}
   ExecI @ i; E
   {{{ RET (false, ExecI) ;
       PC @@ i ->r (ai ^+ 1)%f ∗ ai ->a wi ∗
       R0 @@ i ->r (encode_hvc_ret_code Error) ∗
       R1 @@ i ->r wh ∗
       R2 @@ i ->r (encode_hvc_error InvParam) ∗
       i -@A> sacc ∗
       TX@ i := p_tx ∗
       fresh_handles q sh
   }}}.
Proof.
Admitted.

Lemma mem_reclaim_invalid_trans {E i wi sacc r0 r2 wh meta q p_tx} ai:
  tpa ai ≠ p_tx ->
  (tpa ai) ∈ sacc ->
  decode_instruction wi = Some(Hvc) ->
  decode_hvc_func r0 = Some(Reclaim) ->
  meta.1.1.1 ≠ i ->
  {SS{{▷ (PC @@ i ->r ai) ∗ ▷ ai ->a wi ∗
       ▷ (R0 @@ i ->r r0) ∗
       ▷ (R1 @@ i ->r wh) ∗
       ▷ (R2 @@ i ->r r2) ∗
       ▷ i -@A> sacc ∗
       ▷ TX@ i := p_tx ∗
       ▷ wh -{q}>t meta
       }}}
   ExecI @ i; E
   {{{ RET (false, ExecI) ;
       PC @@ i ->r (ai ^+ 1)%f ∗ ai ->a wi ∗
       R0 @@ i ->r (encode_hvc_ret_code Error) ∗
       R1 @@ i ->r wh ∗
       R2 @@ i ->r (encode_hvc_error Denied) ∗
       i -@A> sacc ∗
       TX@ i := p_tx ∗
       wh -{q}>t meta
   }}}.
Proof.
Admitted.

Lemma mem_reclaim_retrieved{E i wi sacc r0 r2 wh q p_tx} ai:
  tpa ai ≠ p_tx ->
  (tpa ai) ∈ sacc ->
  decode_instruction wi = Some(Hvc) ->
  decode_hvc_func r0 = Some(Reclaim) ->
  {SS{{▷ (PC @@ i ->r ai) ∗ ▷ ai ->a wi ∗
       ▷ (R0 @@ i ->r r0) ∗
       ▷ (R1 @@ i ->r wh) ∗
       ▷ (R2 @@ i ->r r2) ∗
       ▷ i -@A> sacc ∗
       ▷ TX@ i := p_tx ∗
       ▷ wh -{q}>re true
       }}}
   ExecI @ i; E
   {{{ RET (false, ExecI) ;
       PC @@ i ->r (ai ^+ 1)%f ∗ ai ->a wi ∗
       R0 @@ i ->r (encode_hvc_ret_code Error) ∗
       R1 @@ i ->r wh ∗
       R2 @@ i ->r (encode_hvc_error Denied) ∗
       i -@A> sacc ∗
       TX@ i := p_tx ∗
       wh -{q}>re true
   }}}.
Proof.
Admitted.

End mem_reclaim.
