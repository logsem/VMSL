From iris.base_logic.lib Require Import ghost_map.
From HypVeri.algebra Require Import base.

Section token_rules.
  Context `{vmG :!gen_VMG Σ}.

 Lemma token_frag_valid i1 i2 q1 q2 :
   << i1 >>{ q1 } -∗
   << i2 >>{ q2 } -∗
   ⌜ i1 = i2 ⌝ ∧ ⌜ ((q1 + q2) ≤ 1)%Qp ⌝.
  Proof.
    rewrite token_agree_eq /token_agree_def.
    iIntros "H1 H2".
    iDestruct (own_valid_2  with "H1 H2") as %Hvalid.
    rewrite /get_token in Hvalid.
    rewrite <- frac_auth_frag_op in Hvalid.
    apply frac_auth_frag_valid in Hvalid.
    destruct Hvalid.
    apply to_agree_op_inv_L in H0.
    done.
  Qed.

  Lemma token_frag_split i q1 q2 :
   (q1 + q2 = 1)%Qp ->
   << i >>{ 1%Qp } -∗
   << i >>{ q1 } ∗ << i >>{ q2}.
  Proof.
    intro.
    rewrite token_agree_eq /token_agree_def.
    iIntros "H".
    rewrite -own_op.
    rewrite -frac_auth_frag_op.
    rewrite H.
    by rewrite agree_idemp.
  Qed.

  Lemma token_frag_merge i q1 q2 :
   (q2 + q1 = 1)%Qp ->
   << i >>{ q1 } -∗ << i >>{ q2} -∗
   << i >>{ 1%Qp }.
  Proof.
    intro.
    rewrite token_agree_eq /token_agree_def.
    iIntros "H1 H2".
    iDestruct (own_op with "[H1 H2]") as "H".
    iFrame.
    rewrite -frac_auth_frag_op.
    rewrite H.
    by rewrite agree_idemp.
  Qed.

  Lemma token_auth_valid i1 i2 q :
   << i1 >>{ q } -∗
   (own (gen_token_name vmG) (get_token i2)%I) -∗
   ⌜ i1 = i2 ⌝.
  Proof.
    rewrite token_agree_eq /token_agree_def.
    iIntros "H1 H2".
    iDestruct (own_valid_2  with "H2 H1") as %Hvalid.
    rewrite /get_token in Hvalid.
    apply frac_auth_included_total in Hvalid.
    apply to_agree_included in Hvalid.
    destruct Hvalid.
    done.
  Qed.

  Lemma token_update i1 i2 i3 :
   << i1 >>{ 1%Qp } -∗
   (own (gen_token_name vmG) (get_token i2))  ==∗
   << i3 >>{ 1%Qp } ∗ (own (gen_token_name vmG) (get_token i3)).
  Proof.
    rewrite token_agree_eq /token_agree_def /get_token.
    rewrite -own_op.
    iApply own_update_2.
   apply frac_auth_update_1.
   done.
  Qed.

  Lemma gen_token_valid_neq{σ q} i j:
   i ≠ j ->
   << i >>{ q } -∗
   own (gen_token_name vmG) (get_token (get_current_vm σ)) -∗
   ⌜ ¬ scheduler σ j ⌝.
  Proof.
    iIntros (Hne) "Htok Hstate".
    iDestruct (token_auth_valid with "Htok Hstate") as %->.
    iPureIntro.
    rewrite /scheduler .
    intro.
    apply fin_to_nat_inj in H.
    done.
    Qed.


  End token_rules.
