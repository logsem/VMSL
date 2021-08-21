From machine_program_logic.program_logic Require Import machine weakestpre.
From HypVeri Require Import RAs rule_misc lifting rules.rules_base transaction utils.
From iris.proofmode Require Import tactics.
Require Import iris.base_logic.lib.ghost_map.
Require Import stdpp.fin.

Section relinquish.

Context `{vmG: !gen_VMG Σ}.

Lemma hvc_relinquish_donate_nz {wi sown sacc pi sexcl i j des ptx} {spsd: gset PID}
      ai r0 wh wf (psd: list PID) :
  decode_instruction wi = Some(Hvc) ->
  addr_in_page ai pi ->
  decode_hvc_func r0 = Some(Relinquish) ->
  pi ∈ sacc ->
  spsd = (list_to_set psd) ->
  spsd ## sacc ->
  spsd ## sown ->
  spsd ## sexcl ->
  des = [wh; wf] ->
  {SS{{ ▷(PC @@ i ->r ai) ∗ ▷ (R0 @@ i ->r r0)
  ∗ ▷ ai ->a wi
  ∗ ▷ wh ->re true ∗ ▷ wh ->t{1}(j, wf, i, psd, Donation)
  ∗ ▷ O@i:={1}[sown ∪ spsd] ∗ ▷ E@i:={1}[sexcl ∪ spsd] ∗ ▷ A@i:={1}[sacc ∪ spsd]
  ∗ ▷ TX@ i := ptx ∗ ▷ mem_region des ptx }}}
   ExecI @ i {{{ RET ExecI ; PC @@ i ->r (ai ^+ 1)%f ∗ ai ->a wi
  ∗ O@i:={1}[(sown)] ∗ E@i:={1}[(sexcl)] ∗ A@i:={1}[(sacc)]
  ∗ R0 @@ i ->r (encode_hvc_ret_code Succ) ∗ wh ->t{1}(j, wf, i, psd, Donation)
  ∗ wh ->re false ∗ TX@ i := ptx ∗ mem_region des ptx }}}.
Admitted.

End relinquish.
