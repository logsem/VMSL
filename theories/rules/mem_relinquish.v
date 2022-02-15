From machine_program_logic.program_logic Require Import weakestpre.
From HypVeri Require Import lifting rules.rules_base stdpp_extra.
From HypVeri.algebra Require Import base reg mem pagetable trans mailbox.
From HypVeri.lang Require Import lang_extra mem_extra reg_extra pagetable_extra trans_extra.

Section relinquish_nz.

Context `{hypparams: HypervisorParameters}.
Context `{vmG: !gen_VMG Σ}.

Lemma mem_relinquish {tt wi sacc i j p_tx wf} {spsd: gset PID}
      ai r0 wh:
  (* has access to the page which the instruction is in *)
  tpa ai ≠ p_tx ->
  tpa ai ∈ sacc ->
  (* current instruction is hvc *)
  decode_instruction wi = Some(Hvc) ->
  (* the hvc call to invoke is relinquish *)
  decode_hvc_func r0 = Some(Relinquish) ->
  (* must have access to these involved pages *)
  spsd ⊆ sacc ->
  {SS{{(* the encoding of instruction wi is stored in location ai *)
       ▷(PC @@ i ->r ai) ∗  ▷ ai ->a wi ∗
                                     ▷ (R0 @@ i ->r r0) ∗
       (* the pagetable, the owership ra is not required *)
       ▷ i -@A> sacc ∗
       (* the descriptor is ready in the tx page *)
       ▷ TX@ i := p_tx ∗
       (* is the receiver and the transaction has been retrieved *)
       ▷ wh ->t (j, wf, i, spsd, tt) ∗ ▷ wh ->re true }}}
  ExecI @ i
  {{{ RET (false, ExecI) ;
      (* PC is incremented *)
      PC @@ i ->r (ai ^+ 1)%f ∗ ai ->a wi ∗
      (* donesn't have access to psd anymore *)
      i -@A> (sacc ∖ spsd) ∗
      (* return Succ to R0 *)
      R0 @@ i ->r (encode_hvc_ret_code Succ) ∗
      (* the transaction is marked as unretrieved *)
      wh ->t(j, wf, i, spsd, tt) ∗ wh ->re false ∗
      (* the same tx *)
      TX@ i := p_tx }}}.
Proof.
Admitted.
