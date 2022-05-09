From HypVeri.algebra Require Import base base_extra.

Section trans_rules.

  Context `{HyperConst : !HypervisorConstants}.
  Context `{vmG :!gen_VMG Σ}.

(* rules for transactions *)

  Lemma trans_split w q tran :
    w -{q}>t tran ⊣⊢ w -{q/2}>t tran ∗ w -{q/2}>t tran.
  Proof.
    rewrite trans_mapsto_eq /trans_mapsto_def.
    iSplit.
    iIntros "[H %]".
    iDestruct (ghost_map_elem_split with "H") as "[H1 H2]".
    by iFrame.
    iIntros "[[H1 %] [H2 _]]".
    iDestruct (ghost_map_elem_split with "[$H1 $H2]") as "H".
    by iFrame.
   Qed.

  Lemma trans_valid_handle_Some w q tran :
    w -{q}>t tran ⊢ ⌜w ∈ valid_handles⌝.
  Proof.
    rewrite trans_mapsto_eq /trans_mapsto_def.
    iIntros "[H %Hvalid]".
    by iFrame.
  Qed.

  Lemma trans_valid_handle_None w q :
    w -{q}>t - ⊢ ⌜w ∈ valid_handles⌝.
  Proof.
    rewrite trans_mapsto_eq /trans_mapsto_def.
    iIntros "[H %Hvalid]".
    by iFrame.
  Qed.

  Lemma retri_split w q bool:
    w -{q}>re bool ⊣⊢ w -{q/2}>re bool ∗ w -{q/2}>re bool.
  Proof.
    rewrite retri_mapsto_eq /retri_mapsto_def.
    iSplit.
    iIntros "[H %]".
    iDestruct (ghost_map_elem_split with "H") as "[H1 H2]".
    by iFrame.
    iIntros "[[H1 %] [H2 _]]".
    iDestruct ((ghost_map_elem_split w _ q (Some bool)) with "[$H1 $H2]") as "H".
    by iFrame.
  Qed.

  Lemma retri_valid_handle_Some w q b :
    w -{q}>re b ⊢ ⌜w ∈ valid_handles⌝.
  Proof.
    rewrite retri_mapsto_eq /retri_mapsto_def.
    iIntros "[H %Hvalid]".
    by iFrame.
  Qed.

  Lemma retri_valid_handle_None w q :
    w -{q}>re - ⊢ ⌜w ∈ valid_handles⌝.
  Proof.
    rewrite retri_mapsto_eq /retri_mapsto_def.
    iIntros "[H %Hvalid]".
    by iFrame.
  Qed.

  Lemma trans_valid_Some {σ q} {meta} wh:
    (ghost_map_auth gen_trans_name 1 (get_trans_gmap σ)) -∗
     wh -{q}>t (meta) -∗
    ⌜(∃ (b:bool), (get_transactions σ) !! wh = Some (Some (meta,b)))⌝.
  Proof.
    iIntros "Hσ [Htrn %Hvalid]".
    rewrite trans_mapsto_eq /trans_mapsto_def.
    rewrite /get_trans_gmap /get_transactions_gmap.
    iDestruct (ghost_map_lookup with "Hσ Htrn") as "%Hlk".
    iPureIntro.
    rewrite lookup_fmap_Some in Hlk.
    destruct Hlk as [otrans [Heq Hlk]].
    destruct otrans;last inversion Heq.
    inversion_clear Heq.
    exists t.2.
    rewrite -?surjective_pairing //.
  Qed.

  Lemma trans_valid_None {σ q} wh:
    (ghost_map_auth gen_trans_name 1 (get_trans_gmap σ)) -∗
    wh -{q}>t - -∗
    ⌜(get_transactions σ) !! wh = Some (None)⌝.
  Proof.
    iIntros "Hσ [Htrn %Hvalid]".
    rewrite trans_mapsto_eq /trans_mapsto_def.
    rewrite /get_trans_gmap /get_transactions_gmap.
    iDestruct (ghost_map_lookup with "Hσ Htrn") as "%Hlk".
    iPureIntro.
    rewrite lookup_fmap_Some in Hlk.
    destruct Hlk as [otrans [Heq Hlk]].
    destruct otrans;last inversion Heq.
    inversion_clear Heq.
    done.
  Qed.

  Lemma retri_valid_Some {σ q b} wh:
    ghost_map_auth gen_retri_name 1 (get_retri_gmap σ) -∗
    wh -{q}>re b -∗
    ⌜(∃ t, (get_transactions σ) !! wh = Some (Some (t,b)))⌝.
  Proof.
    iIntros "Hσ [Hretri %Hvalid]".
    rewrite retri_mapsto_eq /retri_mapsto_def.
    rewrite /get_retri_gmap /get_transactions_gmap.
    iDestruct (ghost_map_lookup with "Hσ Hretri") as "%Hlk".
    iPureIntro.
    rewrite lookup_fmap_Some in Hlk.
    destruct Hlk as [otrans [Heq Hlk]].
    destruct otrans;last inversion Heq.
    inversion_clear Heq.
    exists t.1.
    rewrite -?surjective_pairing //.
  Qed.

  Lemma retri_valid_None {σ q} wh:
    ghost_map_auth gen_retri_name 1 (get_retri_gmap σ) -∗
    wh -{q}>re - -∗
    ⌜(get_transactions σ) !! wh = Some (None)⌝.
  Proof.
    iIntros "Hσ [Hretri %Hvalid]".
    rewrite retri_mapsto_eq /retri_mapsto_def.
    rewrite /get_retri_gmap /get_transactions_gmap.
    iDestruct (ghost_map_lookup with "Hσ Hretri") as "%Hlk".
    iPureIntro.
    rewrite lookup_fmap_Some in Hlk.
    destruct Hlk as [otrans [Heq Hlk]].
    destruct otrans;last inversion Heq.
    inversion_clear Heq.
    done.
  Qed.

  Lemma trans_update_insert {σ} h meta:
   (ghost_map_auth gen_trans_name 1 (get_trans_gmap σ)) -∗
   h ->t - ==∗
   (ghost_map_auth gen_trans_name 1 (<[h:= Some meta]>(get_trans_gmap σ))) ∗ h ->t (meta).
  Proof.
    iIntros "auth tran".
    iDestruct (trans_valid_None with "auth tran") as "%Hvalid".
    rewrite trans_mapsto_eq /trans_mapsto_def.
    iDestruct "tran" as "[tran Hvalid]".
    iFrame. iApply (ghost_map_update with "auth tran");auto.
  Qed.

  Lemma trans_update_delete {σ meta} h :
    ghost_map_auth gen_trans_name 1 (get_trans_gmap σ) -∗
    h ->t meta ==∗
    ghost_map_auth gen_trans_name 1 (<[h := None]>(get_trans_gmap σ)) ∗
    h ->t -.
  Proof.
    iIntros "auth tran".
    rewrite trans_mapsto_eq /trans_mapsto_def.
    iDestruct "tran" as "[tran Hvalid]".
    iFrame. iApply (ghost_map_update None with "auth tran").
  Qed.

  Lemma retri_update_flip {σ b} h :
    ghost_map_auth gen_retri_name 1 (get_retri_gmap σ) -∗
    h ->re b ==∗
    ghost_map_auth gen_retri_name 1 (<[h:= Some (negb b)]>(get_retri_gmap σ)) ∗
    h ->re (negb b).
  Proof.
    iIntros "auth retri".
    rewrite retri_mapsto_eq /retri_mapsto_def.
    iDestruct "retri" as "[retri Hvalid]".
    iFrame. iApply ((ghost_map_update (Some (negb b))) with "auth retri").
  Qed.

  Lemma retri_update_delete {σ b} (h: Word):
    ghost_map_auth gen_retri_name 1 (get_retri_gmap σ) -∗
    h ->re b ==∗
    ghost_map_auth gen_retri_name 1 (<[h := None]>(get_retri_gmap σ)) ∗
    h ->re -.
  Proof.
    iIntros "auth retri".
    rewrite retri_mapsto_eq /retri_mapsto_def.
    iDestruct "retri" as "[retri Hvalid]".
    iFrame. iApply ((ghost_map_update None) with "auth retri").
  Qed.

  Lemma retri_update_insert {σ} (h: Word):
    ghost_map_auth gen_retri_name 1 (get_retri_gmap σ) -∗
    h ->re - ==∗
    ghost_map_auth gen_retri_name 1 (<[h:= Some false]>(get_retri_gmap σ))∗
    h ->re false.
  Proof.
    iIntros "auth retri".
    rewrite retri_mapsto_eq /retri_mapsto_def.
    iDestruct "retri" as "[retri Hvalid]".
    iFrame. iApply(ghost_map_update (Some false) with "auth retri").
  Qed.

  Lemma hpool_valid {σ q} s :
    own gen_hpool_name (frac_auth_auth (to_agree (get_hpool_gset σ))) -∗
    hp {q}[ s ] -∗
    ⌜s = get_fresh_handles (get_transactions σ)⌝.
  Proof.
    iIntros "auth hpool".
    rewrite hpool_mapsto_eq /hpool_mapsto_def.
    iDestruct (own_valid_2  with "auth hpool") as %Hvalid.
    rewrite /get_hpool_gset in Hvalid.
    apply frac_auth_included_total in Hvalid.
    rewrite to_agree_included in Hvalid.
    fold_leibniz.
    done.
  Qed.

  Lemma hpool_update_diff {σ s} h:
    (own gen_hpool_name (frac_auth_auth (to_agree (get_hpool_gset σ)))) -∗
    hp [ s ] ==∗
    (own gen_hpool_name (frac_auth_auth (to_agree ((get_hpool_gset σ) ∖ {[h]}))))∗
    hp [ s ∖ {[h]} ].
  Proof.
    iIntros "auth hp".
    iDestruct (hpool_valid with "auth hp")as %Hvalid.
    rewrite hpool_mapsto_eq /hpool_mapsto_def.
    rewrite -own_op.
    iApply ((own_update _ (●F (to_agree (get_hpool_gset σ)) ⋅ ◯F (to_agree s)) _ ) with "[auth hp]").
    2: { rewrite own_op. iFrame. }
    rewrite /get_hpool_gset -Hvalid.
    apply frac_auth_update_1.
    done.
  Qed.

  Lemma hpool_update_union {σ s} (h: Word):
    (own gen_hpool_name (frac_auth_auth (to_agree (get_hpool_gset σ)))) -∗
    hp [ s ] ==∗
    (own gen_hpool_name (frac_auth_auth (to_agree ({[h]} ∪ (get_hpool_gset σ)))))∗
    hp [ {[h]} ∪ s ].
  Proof.
    iIntros "auth hp".
    iDestruct (hpool_valid with "auth hp")as %Hvalid.
    rewrite hpool_mapsto_eq /hpool_mapsto_def.
    rewrite -own_op.
    iApply ((own_update _ (●F (to_agree (get_hpool_gset σ)) ⋅ ◯F (to_agree s)) _ ) with "[auth hp]").
    2: { rewrite own_op. iFrame. }
    rewrite /get_hpool_gset -Hvalid.
    apply frac_auth_update_1.
    done.
  Qed.

  Definition fresh_handles q hs := (hp {q}[hs] ∗ ([∗ set] h ∈ hs, h -{q}>t - ∗ h -{q}>re -))%I.

  Lemma not_elem_of_fresh_handles hs q w q' tran:
    fresh_handles q hs ∗ w -{q'}>t tran ⊢ ⌜w ∉ hs⌝.
  Proof.
    rewrite /fresh_handles.
    iIntros "[[_ hs] [tran _]]".
    destruct (decide (w ∈ hs)).
    iDestruct (big_sepS_elem_of _ hs w e with "hs") as "[[tran' _] _]".
    rewrite trans_mapsto_eq /trans_mapsto_def.
    iDestruct (ghost_map_elem_agree with "tran tran'") as %H.
    inversion H.
    done.
  Qed.

  Lemma fresh_handles_disj hs q (trans : gmap Addr transaction) q':
    fresh_handles q hs ∗
    ([∗ map] w ↦ tran ∈ trans, w -{q'}>t tran.1) ⊢ ⌜hs ## dom (gset _) trans⌝.
  Proof.
    iIntros "[fresh map]".
    rewrite elem_of_disjoint.
    iIntros (? Hin_hs Hin_dom).
    rewrite elem_of_dom in Hin_dom.
    destruct Hin_dom as [? Hlookup].
    iDestruct (big_sepM_lookup with "map") as "tran";eauto.
    iDestruct (not_elem_of_fresh_handles with "[$fresh $tran]") as %Hnin.
    done.
  Qed.

End trans_rules.
