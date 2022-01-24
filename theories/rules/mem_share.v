From machine_program_logic.program_logic Require Import weakestpre.
From HypVeri Require Import lifting rules.rules_base machine_extra.
From HypVeri.algebra Require Import base mem reg pagetable mailbox trans base_extra.
From HypVeri.lang Require Import lang_extra reg_extra mem_extra pagetable_extra trans_extra.

Section mem_share.

Context `{hypparams: HypervisorParameters}.
Context `{vmG: !gen_VMG Σ}.

Lemma hvc_mem_share_nz {i wi r0 r1 r2 hvcf p_tx sacc } ai j mem_tx sh (spsd: gset PID) :
  (* len is the length of the msg *)
  let len := (Z.of_nat (finz.to_z r1)) in
  (* the decoding of wi is correct *)
  decode_instruction wi = Some(Hvc) ->
  (* the decoding of R0 is a FFA mem send *)
  decode_hvc_func r0 = Some(hvcf) ->
  hvcf_to_tt hvcf = Some Sharing ->
  (* caller is not the receiver *)
  i ≠ j ->
  (* the descriptor, in list Word *)
  (* des = serialized_transaction_descriptor i j W0 l (elements spsd) W0 -> *)
  (* the whole descriptor resides in the TX page *)
  (len < page_size)%Z ->
  (* there is at least one free handle in the hpool *)
  sh ≠ ∅ ->
  {SS{{ ▷(PC @@ i ->r ai) ∗
      ▷ ai ->a wi ∗
  (* VM i owns pages in spsd *)
      ▷ ([∗ set] p ∈ spsd, p -@O> i) ∗
  (* pages in spsed are exclusive to VM i *)
      ▷ (i -@A> sacc) ∗
      (* and the page which the instruction is in is not being shared, i.e. (tpa ai) ∉ spsd *)
      ▷ (R0 @@ i ->r r0) ∗
      ▷ (R1 @@ i ->r r1) ∗
      ▷ (R2 @@i ->r r2) ∗
      ▷ (fresh_handles 1 sh) ∗
      ▷ TX@ i := p_tx ∗
      ▷ mem_region des p_tx
       }}}
   ExecI @ i {{{ RET (false,ExecI) ;
                 PC @@ i ->r (ai ^+ 1)%f ∗
                 ai ->a wi ∗
                 ([∗ set] p ∈ spsd, p -@O> i ) ∗
                 i -@A> (sacc ∖ spsd) ∗
                 R0 @@ i ->r (encode_hvc_ret_code Succ) ∗
                 R1 @@ i ->r r1 ∗
                 (∃ (wh: Word), ⌜wh ∈ sh⌝ ∗
                 R2 @@ i ->r wh ∗
                 wh ->t (i,W0,j,spsd,Sharing) ∗
                 wh ->re false ∗
                 fresh_handles 1 (sh∖{[wh]})) ∗
                 TX@ i := p_tx ∗
                 mem_region des p_tx}}}.
