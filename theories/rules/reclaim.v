From machine_program_logic.program_logic Require Import machine weakestpre.
From HypVeri Require Import RAs rule_misc lifting rules.rules_base transaction utils.
From iris.proofmode Require Import tactics.
Require Import iris.base_logic.lib.ghost_map.
Require Import stdpp.fin.

Section reclaim.

Context `{vmG: !gen_VMG Σ}.

Lemma hvc_reclaim {wi sown sacc pi sexcl i j sh tt} {spsd: gset PID}
      ai r0 wh wf (psd: list PID) :
  decode_instruction wi = Some(Hvc) ->
  addr_in_page ai pi ->
  decode_hvc_func r0 = Some(Reclaim) ->
  pi ∈ sacc ->
  spsd = (list_to_set psd) ->
  spsd ## sacc ->
  spsd ## sown ->
  spsd ## sexcl ->
  {SS{{ ▷(PC @@ i ->r ai) ∗ ▷ (R0 @@ i ->r r0) ∗ ▷ (R1 @@ i ->r wh)
  ∗ ▷ ai ->a wi ∗ ▷ hp{ 1 }[ sh ] 
  ∗ ▷ wh ->re false ∗ ▷ wh ->t{1}(i, wf, j, psd, tt)
  ∗ ▷ O@i:={1}[sown] ∗ ▷ E@i:={1}[sexcl] ∗ ▷ A@i:={1}[sacc] }}}
   ExecI @ i {{{ RET ExecI ; PC @@ i ->r (ai ^+ 1)%f ∗ ai ->a wi
  ∗ O@i:={1}[(sown ∪ spsd)] ∗ E@i:={1}[(sexcl ∪ spsd)] ∗ A@i:={1}[(sacc ∪ spsd)]
  ∗ R0 @@ i ->r (encode_hvc_ret_code Succ) ∗ hp{ 1 }[ (sh ∪ {[wh]})] }}}.
Admitted.

End reclaim.
