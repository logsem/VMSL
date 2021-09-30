From HypVeri.algebra Require Import base.

Section trans_rules.

  Context `{HyperConst : !HypervisorConstants}.
  Context `{vmG :!gen_VMG Σ}.

(* rules for transactions *)

(* Lemma trans_split wh q1 q2 i (r:VMID) wf m f: *)
(*  wh ->t{(q1+q2)%Qp}(i,wf,r,m,f) -∗  wh ->t{q1}(i,wf,r,m,f) ∗ wh ->t{q2}(i,wf,r,m,f). *)
(* Proof using. *)
(*   iIntros "HT". *)
(*   rewrite trans_mapsto_eq /trans_mapsto_def. *)
(*   rewrite ?ghost_map_elem_eq /ghost_map_elem_def. *)
(*   rewrite -own_op gmap_view_frag_add. *)
(*   done. *)
(* Qed. *)

  Lemma gen_trans_valid {σ q i wf} {r:VMID} {m f} wh :
    wh ->t{q}(i,wf,r,m,f) -∗
    (ghost_map_auth (gen_trans_name vmG) 1 (get_trans_gmap σ))-∗
    ⌜∃ (b:bool), (get_transactions σ).1 !! wh = Some (i,wf,b,r,m,f)⌝.
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
    exists x.2.1.1.1.2.
    rewrite Hin -?surjective_pairing //.
  Qed.

  Lemma gen_retri_valid {σ wh b} :
    wh ->re b -∗ ghost_map_auth (gen_retri_name vmG) 1 (get_retri_gmap σ) -∗
    ⌜∃ t, (get_transactions σ).1 !! wh = Some t ∧ t.1.1.1.2 = b⌝.
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
    exists x.2.
    done.
  Qed.

  Lemma gen_hpool_valid_subset {σ q} s :
    hp{ q }[ s ] -∗
    (own (gen_hpool_name vmG) (frac_auth_auth (GSet (get_hpool_gset σ))))-∗
    ⌜s ⊆ (get_hpool_gset σ)⌝.
  Proof.
    rewrite hpool_mapsto_eq /hpool_mapsto_def.
    iIntros "H1 H2".
    iDestruct (own_valid_2 with "H2 H1") as %Hvalid.
    rewrite /get_hpool_gset in Hvalid.
    apply frac_auth_included in Hvalid.
    iPureIntro.
    apply option_included_total in Hvalid.
    destruct Hvalid as [|Hvalid];[done|].
    destruct Hvalid as [? [? [Heq1 [Heq2 Hincl]]]].
    inversion Heq1;subst x.
    inversion Heq2;subst x0.
    apply gset_disj_included in Hincl.
    assumption.
  Qed.

  Lemma gen_hpool_valid_eq {σ} s :
    hp{ 1 }[ s ] -∗
    (own (gen_hpool_name vmG) (frac_auth_auth (GSet (get_hpool_gset σ))))-∗
    ⌜s = (get_hpool_gset σ)⌝.
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

  Lemma gen_hpool_valid_elem_subset {σ q} s :
    hp{ q }[ s ] -∗
    (own (gen_hpool_name vmG) (frac_auth_auth (GSet (get_hpool_gset σ))))-∗
    ⌜(elements s) ⊆ get_fresh_handles (get_transactions σ)⌝.
  Proof.
    iIntros "H1 H2".
    iDestruct (gen_hpool_valid_subset with "H1 H2") as %Hvalid.
    rewrite /get_hpool_gset in Hvalid.
    rewrite /get_fresh_handles.
    iPureIntro.
    set_solver.
  Qed.

  Lemma gen_hpool_valid_elem {σ} s :
    hp{ 1 }[ s ] -∗
    (own (gen_hpool_name vmG) (frac_auth_auth (GSet (get_hpool_gset σ))))-∗
    ⌜(elements s) = get_fresh_handles (get_transactions σ)⌝.
  Proof.
    iIntros "H1 H2".
    iDestruct (gen_hpool_valid_eq with "H1 H2") as %Hvalid.
    rewrite /get_hpool_gset in Hvalid.
    rewrite /get_fresh_handles.
    iPureIntro.
    set_solver.
  Qed.

  Lemma gen_trans_update_insert {σ} h i wf rc m f:
    (get_trans_gmap σ) !! h = None ->
    (ghost_map_auth (gen_trans_name vmG) 1 (get_trans_gmap σ))==∗
    (ghost_map_auth (gen_trans_name vmG) 1 (<[h:= (i,wf,rc,m,f)]>(get_trans_gmap σ))) ∗
    h ->t{1}(i,wf,rc,m,f).
  Proof.
    iIntros (HNone) "Htrans".
    rewrite trans_mapsto_eq /trans_mapsto_def.
    iApply (ghost_map_insert with "Htrans");auto.
  Qed.

  Lemma gen_trans_update_delete {σ} h i wf rc m f:
    h ->t{1}(i,wf,rc,m,f) -∗
    (ghost_map_auth (gen_trans_name vmG) 1 (get_trans_gmap σ))==∗
    (ghost_map_auth (gen_trans_name vmG) 1 ((delete h (get_trans_gmap σ)))).
  Proof.
    iIntros "Hh Htrans".
    rewrite trans_mapsto_eq /trans_mapsto_def.
    iApply (ghost_map_delete with "Htrans Hh").
  Qed.

  Lemma gen_hpool_update_diff {σ s q} (h: handle):
    h ∈ s ->
    hp{ q }[ s ] -∗
    (own (gen_hpool_name vmG) (frac_auth_auth (GSet (get_hpool_gset σ)))) ==∗
    (own (gen_hpool_name vmG) (frac_auth_auth (GSet ( (get_hpool_gset σ)∖ {[h]}))))∗
    hp{ q }[ s ∖ {[h]} ].
  Proof.
    iIntros (HIn) "Hhp HHp".
    iDestruct (gen_hpool_valid_subset with "Hhp HHp")as %Hvalid.
    rewrite hpool_mapsto_eq /hpool_mapsto_def.
    rewrite -own_op.
    iApply ((own_update _ (●F (GSet (get_hpool_gset σ)) ⋅ ◯F{q } (GSet s)) _ ) with "[HHp Hhp]").
    2: { rewrite own_op. iFrame. }
    apply frac_auth_update.
    set (X := (get_hpool_gset σ ∖ {[h]})).
    set (Y := (s ∖ {[h]})).
    assert (HX: GSet (get_hpool_gset σ) = GSet {[h]} ⋅ GSet X ).
    { rewrite gset_disj_union;[|set_solver].  f_equal. rewrite singleton_union_difference_L.
      rewrite difference_diag_L difference_empty_L. set_solver. }
    assert (HY: GSet s = GSet {[h]} ⋅ GSet Y ).
    { rewrite gset_disj_union;[|set_solver].  f_equal. rewrite singleton_union_difference_L.
      rewrite difference_diag_L difference_empty_L. set_solver. }
    rewrite HX HY.
    apply gset_disj_dealloc_op_local_update.
  Qed.

  Lemma gen_retri_update {σ} b b' (h: handle):
    (get_retri_gmap σ) !! h = Some b ->
    h ->re b -∗
    ghost_map_auth (gen_retri_name vmG) 1 (get_retri_gmap σ) ==∗
    ghost_map_auth (gen_retri_name vmG) 1 (<[h:=b']>(get_retri_gmap σ)) ∗
    h ->re b'.
  Proof.
    iIntros (HNone) "Q H".
    rewrite retri_mapsto_eq /retri_mapsto_def.
    iDestruct ((ghost_map_update b') with "H Q") as "H"; eauto.
  Qed.

  Lemma gen_retri_update_delete {σ b} (h: handle):
    h ->re b -∗
    ghost_map_auth (gen_retri_name vmG) 1 (get_retri_gmap σ) ==∗
    ghost_map_auth (gen_retri_name vmG) 1 (delete h (get_retri_gmap σ)).
  Proof.
    iIntros "Q H".
    rewrite retri_mapsto_eq /retri_mapsto_def.
    iApply ((ghost_map_delete ) with "H Q").
  Qed.

  Lemma gen_hpool_update_union {σ s q} (h: handle):
    h ∉ (get_hpool_gset σ) ->
    hp{ q }[ s ] -∗
    (own (gen_hpool_name vmG) (frac_auth_auth (GSet (get_hpool_gset σ)))) ==∗
    (own (gen_hpool_name vmG) (frac_auth_auth (GSet ( (get_hpool_gset σ) ∪ {[h]}))))∗
    hp{ q }[ s ∪ {[h]} ].
  Proof.
    iIntros (HIn) "Hhp HHp".
    iDestruct (gen_hpool_valid_subset with "Hhp HHp")as %Hvalid.
    rewrite hpool_mapsto_eq /hpool_mapsto_def.
    rewrite -own_op.
    iApply ((own_update _ (●F (GSet (get_hpool_gset σ)) ⋅ ◯F{q} (GSet s)) _ ) with "[HHp Hhp]").
    2: { rewrite own_op. iFrame. }
    apply frac_auth_update.
    set (X := (get_hpool_gset σ ∖ {[h]})).
    set (Y := (s ∖ {[h]})).
    rewrite union_comm_L.
    assert (HY: GSet (s ∪ {[h]}) = GSet ({[h]} ∪ s) ).
    { rewrite union_comm_L //. }
    rewrite HY.
    apply gset_disj_alloc_local_update;by set_solver.
  Qed.

  Lemma gen_retri_update_insert {σ} (h: handle):
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
