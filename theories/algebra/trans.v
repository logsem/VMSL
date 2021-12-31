From HypVeri.algebra Require Import base.

Section trans_rules.

  Context `{HyperConst : !HypervisorConstants}.
  Context `{vmG :!gen_VMG Σ}.

(* rules for transactions *)

  Lemma trans_valid {σ} {meta} wh:
    wh ->t (meta) -∗
    (ghost_map_auth (gen_trans_name vmG) 1 (get_trans_gmap σ))-∗
    ⌜∃ (b:bool), (get_transactions σ).1 !! wh = Some (meta,b)⌝.
  Proof.
    iIntros "Htrn Hσ".
    rewrite trans_mapsto_eq /trans_mapsto_def.
    destruct σ as [[[[[? ?] ?] ?] ?] σ'].
    rewrite /get_trans_gmap /get_transactions_gmap.
    iDestruct (ghost_map_lookup with "Hσ Htrn") as "%Hlk".
    iPureIntro.
    apply elem_of_list_to_map_2 in Hlk.
    apply elem_of_list_In in Hlk.
    apply in_map_iff in Hlk.
    destruct Hlk as [? [Heqp Hin]].
    inversion Heqp; subst; clear Heqp.
    apply elem_of_list_In in Hin.
    apply elem_of_map_to_list' in Hin.
    exists x.2.2.
    rewrite Hin -?surjective_pairing //.
  Qed.

  Lemma retri_valid {σ b} wh:
    wh ->re b -∗ ghost_map_auth (gen_retri_name vmG) 1 (get_retri_gmap σ) -∗
    ⌜∃ t, (get_transactions σ).1 !! wh = Some (t,b)⌝.
  Proof.
    iIntros "Hretri Hσ".
    rewrite retri_mapsto_eq /retri_mapsto_def.
    destruct σ as [[[[[? ?] ?] ?] ?] σ'].
    rewrite /get_retri_gmap /get_transactions_gmap.
    iDestruct (ghost_map_lookup with "Hσ Hretri") as "%Hlk".
    iPureIntro.
    apply elem_of_list_to_map_2 in Hlk.
    apply elem_of_list_In in Hlk.
    apply in_map_iff in Hlk.
    destruct Hlk as [? [Heqp Hin]].
    inversion Heqp; subst; clear Heqp.
    apply elem_of_list_In in Hin.
    apply elem_of_map_to_list' in Hin.
    exists x.2.1.
    destruct x.2.
    done.
  Qed.

  Lemma hpool_valid {σ} s :
    hp [ s ] -∗
    (own (gen_hpool_name vmG) (frac_auth_auth (get_hpool_gset σ)))-∗
    ⌜s = (get_transactions σ).2⌝.
  Proof.
    rewrite hpool_mapsto_eq /hpool_mapsto_def.
    iIntros "H1 H2".
    iDestruct (own_valid_2  with "H2 H1") as %Hvalid.
    rewrite /get_hpool_gset in Hvalid.
    apply frac_auth_agree_L in Hvalid.
    iPureIntro.
    inversion Hvalid.
    done.
  Qed.

  Lemma hpool_valid_elem {σ} s :
    hp [ s ] -∗
    (own (gen_hpool_name vmG) (frac_auth_auth (get_hpool_gset σ)))-∗
    ⌜(elements s) = get_fresh_handles (get_transactions σ)⌝.
  Proof.
    iIntros "H1 H2".
    iDestruct (hpool_valid with "H1 H2") as %Hvalid.
    rewrite /get_hpool_gset in Hvalid.
    rewrite /get_fresh_handles.
    iPureIntro.
    set_solver.
  Qed.

  Lemma trans_update_insert {σ} h meta:
    (get_trans_gmap σ) !! h = None ->
    (ghost_map_auth (gen_trans_name vmG) 1 (get_trans_gmap σ))==∗
    (ghost_map_auth (gen_trans_name vmG) 1 (<[h:= meta]>(get_trans_gmap σ))) ∗
    h ->t (meta).
  Proof.
    iIntros (HNone) "Htrans".
    rewrite trans_mapsto_eq /trans_mapsto_def.
    iApply (ghost_map_insert with "Htrans");auto.
  Qed.

  Lemma trans_update_delete {σ meta} h :
    h ->t (meta) -∗
    (ghost_map_auth (gen_trans_name vmG) 1 (get_trans_gmap σ))==∗
    (ghost_map_auth (gen_trans_name vmG) 1 ((delete h (get_trans_gmap σ)))).
  Proof.
    iIntros "Hh Htrans".
    rewrite trans_mapsto_eq /trans_mapsto_def.
    iApply (ghost_map_delete with "Htrans Hh").
  Qed.

  Lemma hpool_update_minus {σ s} h:
    h ∈ s ->
    hp [ s ] -∗
    (own (gen_hpool_name vmG) (frac_auth_auth (get_hpool_gset σ))) ==∗
    (own (gen_hpool_name vmG) (frac_auth_auth ((get_hpool_gset σ) ∖ {[h]})))∗
    hp [ s ∖ {[h]} ].
  Proof.
    iIntros (HIn) "Hhp HHp".
    iDestruct (hpool_valid with "Hhp HHp")as %Hvalid.
    rewrite hpool_mapsto_eq /hpool_mapsto_def.
    rewrite -own_op.
    iApply ((own_update _ (●F (get_hpool_gset σ) ⋅ ◯F s) _ ) with "[HHp Hhp]").
    2: { rewrite own_op. iFrame. }
    assert (get_hpool_gset σ = s) as ->.
    { rewrite  /get_hpool_gset //. }
    apply frac_auth_update_1.
    done.
  Qed.

  Lemma retri_update_flip {σ b} h :
    (get_retri_gmap σ) !! h = Some b ->
    h ->re b -∗
    ghost_map_auth (gen_retri_name vmG) 1 (get_retri_gmap σ) ==∗
    ∃ nb, ⌜nb = negb b⌝ ∗ ghost_map_auth (gen_retri_name vmG) 1 (<[h:=nb]>(get_retri_gmap σ)) ∗
    h ->re nb.
  Proof.
    iIntros (HNone) "Q H".
    rewrite retri_mapsto_eq /retri_mapsto_def.
    iDestruct ((ghost_map_update (negb b)) with "H Q") as ">H"; eauto.
  Qed.

  Lemma retri_update_delete {σ b} (h: Word):
    h ->re b -∗
    ghost_map_auth (gen_retri_name vmG) 1 (get_retri_gmap σ) ==∗
    ghost_map_auth (gen_retri_name vmG) 1 (delete h (get_retri_gmap σ)).
  Proof.
    iIntros "Q H".
    rewrite retri_mapsto_eq /retri_mapsto_def.
    iApply ((ghost_map_delete ) with "H Q").
  Qed.

  Lemma hpool_update_union {σ s} (h: Word):
    h ∉ s ->
    hp [ s ] -∗
    (own (gen_hpool_name vmG) (frac_auth_auth (get_hpool_gset σ))) ==∗
    (own (gen_hpool_name vmG) (frac_auth_auth ((get_hpool_gset σ) ∪ {[h]})))∗
    hp [ s ∪ {[h]} ].
  Proof.
    iIntros (HnIn) "Hhp HHp".
    iDestruct (hpool_valid with "Hhp HHp")as %Hvalid.
    rewrite hpool_mapsto_eq /hpool_mapsto_def.
    rewrite -own_op.
    iApply ((own_update _ (●F (get_hpool_gset σ) ⋅ ◯F s) _ ) with "[HHp Hhp]").
    2: { rewrite own_op. iFrame. }
    assert (get_hpool_gset σ = s) as ->.
    { rewrite  /get_hpool_gset //. }
    apply frac_auth_update_1.
    done.
  Qed.

  Lemma retri_update_insert {σ} (h: Word):
    (get_retri_gmap σ) !! h = None ->
    ghost_map_auth (gen_retri_name vmG) 1 (get_retri_gmap σ) ==∗
    ghost_map_auth (gen_retri_name vmG) 1 (<[h:=false]>(get_retri_gmap σ))∗
    h ->re false.
  Proof.
    iIntros (HNone) "H".
    rewrite retri_mapsto_eq /retri_mapsto_def.
    iDestruct (ghost_map_insert with "H") as "H";eauto.
  Qed.

End trans_rules.
