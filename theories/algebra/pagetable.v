From iris.base_logic.lib Require Import gen_heap ghost_map.
From HypVeri.algebra Require Import base base_extra.

Section pagetable_rules.

  Context `{vmG :gen_VMG Σ}.

  (** properties of the pagetable RA **)

  (* own *)
  Lemma own_ne p1 p2 (v1 v2 : VMID):
   p1 -@O> v1 ∗ p2 -@O>v2 -∗ ⌜p1 ≠ p2⌝ .
  Proof using.
    iIntros "[HO1 HO2]".
    rewrite own_mapsto_eq /own_mapsto_def.
    destruct (decide (p1 = p2)).
    { subst p2.
      iDestruct (ghost_map_elem_valid_2 with "HO1 HO2") as "[%Hvalid _]".
      apply dfrac_valid_own_l in Hvalid.
      inversion Hvalid.
    }
    done.
  Qed.

  Lemma own_split {q} p o :
    p -@{q}O> o ⊣⊢ p -@{q/2}O> o ∗ p -@{q/2}O> o.
  Proof.
    rewrite own_mapsto_eq /own_mapsto_def.
    iApply (ghost_map_elem_split p _ q (Some o)).
  Qed.

  Lemma own_comb {q} p o o' :
     p -@{q/2}O> o ∗ p -@{q/2}O> o' ⊢ p -@{q}O> o.
  Proof.
    rewrite own_mapsto_eq /own_mapsto_def.
    iIntros "[H1 H2]".
    iDestruct (ghost_map_elem_combine with "H1 H2") as "[H %]".
    rewrite dfrac_op_own.
    rewrite Qp_div_2 //.
  Qed.

  Lemma own_invalid {q} p o o' :
     p -@O> o ∗ p -@{q}O> o' ⊢ False.
  Proof.
    rewrite own_mapsto_eq /own_mapsto_def.
    iIntros "[H1 H2]".
    iDestruct (ghost_map_elem_valid_2 with "H1 H2") as "[% %]".
    rewrite dfrac_op_own in H.
    rewrite dfrac_valid_own in H.
    exfalso.
    rewrite Qp_le_ngt in H.
    apply H.
    apply Qp_lt_add_l.
  Qed.

  Lemma own_agree {gm: gmap PID (option VMID )} { q γ} p s:
   ghost_map_auth γ 1 gm  -∗
   ghost_map_elem γ p (DfracOwn q) s -∗
   ⌜gm !! p = Some s⌝.
  Proof.
    iIntros  "Hσ Hpt".
    iApply (ghost_map_lookup with "Hσ Hpt").
  Qed.

  (* excl *)
  Lemma excl_ne p1 p2 (b1 b2 : bool):
   p1 -@E> b1 ∗ p2 -@E>b2 -∗ ⌜p1 ≠ p2⌝ .
  Proof using.
    iIntros "[HO1 HO2]".
    rewrite excl_mapsto_eq /excl_mapsto_def.
    destruct (decide (p1 = p2)).
    { subst p2.
      iDestruct (ghost_map_elem_valid_2 with "HO1 HO2") as "[%Hvalid _]".
      apply dfrac_valid_own_l in Hvalid.
      inversion Hvalid.
    }
    done.
  Qed.

  Lemma excl_split {q} p o :
    p -@{q}E> o ⊣⊢ p -@{q/2}E> o ∗ p -@{q/2}E> o.
  Proof.
    rewrite excl_mapsto_eq /excl_mapsto_def.
    iApply (ghost_map_elem_split p _ q o).
  Qed.

  Lemma excl_agree {gm: gmap PID bool} {q γ} p s:
   ghost_map_auth γ 1 gm -∗
   ghost_map_elem γ p (DfracOwn q) s -∗
   ⌜gm !! p = Some s⌝.
  Proof.
    iIntros  "Hσ Hpt".
    iApply (ghost_map_lookup with "Hσ Hpt").
  Qed.

  (* access *)

  Lemma access_split {q} v (s : gset PID) :
    v -@{ q }A> s ⊣⊢
    v -@{ q/2 }A> s ∗ v -@{ q/2 }A> s.
  Proof.
    rewrite access_mapsto_eq /access_mapsto_def.
    rewrite -own_op.
    rewrite -auth_frag_op.
    setoid_rewrite singleton_op.
    rewrite -frac_agree_op.
    iEval(rewrite (Qp_div_2 q)).
    iSplit;eauto.
  Qed.

  Lemma access_agree_eq {q1 q2} v (s1 s2 : gset PID) :
    v -@{ q1 }A> s1 ∗ v -@{ q2 }A> s2 ⊢ ⌜s1 = s2⌝.
  Proof.
    rewrite access_mapsto_eq /access_mapsto_def.
    rewrite -own_op.
    rewrite -auth_frag_op.
    setoid_rewrite singleton_op.
    iIntros "acc".
    iDestruct (own_valid with "acc") as "%valid".
    rewrite auth_frag_valid in valid.
    rewrite singleton_valid in valid.
    rewrite dfrac_agree_op_valid in valid.
    destruct valid.
    fold_leibniz.
    done.
  Qed.

  (** relations between get_access_gmap and the opsem **)
  Lemma access_pgt_lookup {σ} {s:gset PID} (v:VMID):
  (get_access_gmap σ) !! v = Some (to_frac_agree 1 s) ->
  set_Forall (λ p, ∃ i b s, (get_page_table σ) !! p = Some(i,b,s) ∧ v ∈ s) s.
  Proof.
    intro Hlookup.
    rewrite /get_access_gmap in Hlookup.
    apply (elem_of_list_to_map_2 _ v) in Hlookup.
    apply elem_of_list_In in Hlookup.
    apply in_map_iff in Hlookup.
    destruct Hlookup as [? [Heqp _]].
    inversion Heqp;subst;clear Heqp.
    intros p Hin.
    rewrite elem_of_dom in Hin.
    destruct Hin as [sa Hlookup].
    pose proof Hlookup as Hlookup'.
    apply (map_filter_lookup_Some_1_1 _ _ p sa) in Hlookup.
    apply (map_filter_lookup_Some_1_2 _ _ p sa) in Hlookup'.
    apply lookup_fmap_Some in Hlookup.
    destruct Hlookup as [[[]] [<- Hlookup]].
    exists o,b,g.
    split;eauto.
  Qed.

  Lemma access_pgt_elem_of {σ} {s:gset PID} (v:VMID) p:
    (get_access_gmap σ) !! v = Some (to_frac_agree 1 s) ->
    (∃ (o:permission), (get_page_table σ) !! p = Some o ∧ v ∈ o.2) ->
    p ∈ s.
  Proof.
    intros Hlookup [? [Hlookup_pgt Hin]].
    rewrite /get_access_gmap in Hlookup.
    apply (elem_of_list_to_map_2 _ v) in Hlookup.
    apply elem_of_list_In in Hlookup.
    apply in_map_iff in Hlookup.
    destruct Hlookup as [? [Heqp _]].
    inversion Heqp;subst;clear Heqp.
    rewrite elem_of_dom.
    exists x.2.
    rewrite map_filter_lookup_Some.
    split;auto.
    apply lookup_fmap_Some.
    exists x.
    split;done.
  Qed.

  Lemma own_pgt_lookup {σ} {i:option VMID} (p:PID):
  (get_own_gmap σ) !! p = Some i ->
  ∃ b s, (get_page_table σ) !! p = Some(i, b, s).
  Proof.
    rewrite /get_own_gmap.
    rewrite lookup_fmap_Some.
    intros [? [Helem Hlookup]].
    inversion Helem.
    subst.
    exists x.1.2, x.2.
    destruct x; destruct p0;done.
  Qed.

  Lemma excl_pgt_lookup {σ} {b:bool} (p:PID):
  (get_excl_gmap σ) !! p = Some b ->
  ∃ o b' s, (get_page_table σ) !! p = Some(o, b', s) ∧ b = b' && bool_decide (size s <= 1).
  Proof.
    rewrite /get_excl_gmap.
    rewrite lookup_fmap_Some.
    intros [? [Helem Hlookup]].
    subst.
    exists x.1.1, x.1.2,  x.2.
    destruct x; destruct p0;done.
  Qed.

  (** agreement (RA -> opsem) **)

  (* single pt *)

  Lemma access_agree {σ} (v:VMID) q s:
   own gen_access_name (● (get_access_gmap σ)) -∗
   (v -@{q}A> s) -∗
   ⌜(get_access_gmap σ) !! v = Some (to_frac_agree 1 s)⌝.
  Proof.
    iIntros "Hσ Hpt".
    rewrite access_mapsto_eq /access_mapsto_def.
    iDestruct (own_valid_2 with "Hσ Hpt") as "%Hvalid".
    setoid_rewrite auth_both_valid_discrete in Hvalid.
    destruct Hvalid as [Hvalid1 Hvalid2].
    apply singleton_included_l in Hvalid1.
    destruct Hvalid1 as [y [Hvalid1 Hvalid1']].
    apply option_included in Hvalid1'.
    destruct Hvalid1' as [? | Hvalid1']; first done.
    destruct Hvalid1' as [? [? Hvalid1']].
    destruct Hvalid1' as [? [? Hvalid1']].
    simplify_eq.
    iPureIntro.
    assert (get_access_gmap σ !! v = Some(to_frac_agree 1
                (dom (map_filter (λ kv : PID * gset VMID, v ∈ kv.2) (λ x1 : PID * gset VMID, decide_rel elem_of v x1.2)
                      ((λ p : option VMID * bool * gset VMID, p.2) <$> σ.1.1.1.2))))) as Hlookup.
    { rewrite /get_access_gmap.
      apply (elem_of_list_to_map_1 _ v).
      {
        rewrite -list_fmap_compose.
        simpl.
        rewrite NoDup_fmap.
        apply NoDup_list_of_vmids.
      }
      apply elem_of_list_In.
      apply in_map_iff.
      exists v.
      split;auto.
      apply in_list_of_vmids.
    }
    rewrite Hlookup in Hvalid1.
    inversion Hvalid1.
    subst.
    destruct Hvalid1' as [Hvalid1' | Hvalid1'].
    * rewrite -Hvalid1' in H1.
      inversion H1.
      simpl in *.
      rewrite Hlookup.
      f_equal.
      f_equal.
      apply to_agree_inj in H0.
      fold_leibniz.
      done.
    * rewrite -H1 in Hvalid1'.
      apply dfrac_agree_included_L in Hvalid1'.
      destruct Hvalid1'.
      rewrite Hlookup.
      subst s.
      done.
  Qed.

  Lemma access_agree_lookup {σ} v s:
   own gen_access_name (●(get_access_gmap σ)) -∗
   (v -@A> s) -∗
   ⌜set_Forall (λ p, ∃ o b s, (get_page_table σ) !! p = Some (o,b,s) ∧ v ∈ s) s⌝.
  Proof.
    iIntros "Hauth Hfrag".
    iDestruct (access_agree with "Hauth Hfrag") as %Hvalid.
    iPureIntro.
    apply access_pgt_lookup in Hvalid as Hvalid.
    done.
  Qed.

  Lemma access_agree_elem_of {σ} v s p:
    (∃ (o:permission), (get_page_table σ) !! p = Some o ∧ v ∈ o.2) ->
   own gen_access_name (●(get_access_gmap σ)) -∗
   (v -@A> s) -∗
   ⌜p ∈ s⌝.
  Proof.
    iIntros (H) "Hauth Hfrag".
    iDestruct (access_agree with "Hauth Hfrag") as %Hvalid.
    iPureIntro.
    eapply (access_pgt_elem_of);eauto.
  Qed.

  Lemma access_agree_check_false {σ v} p s:
   p ∉ s ->
   own gen_access_name (●(get_access_gmap σ)) -∗
   (v -@A> s) -∗
   ⌜(check_access_page σ v p)= false⌝.
  Proof.
    iIntros (Hnin) "Hauth Hfrag".
    iDestruct (access_agree with "Hauth Hfrag") as %Hlookup.
    iPureIntro.
    rewrite /get_access_gmap in Hlookup.
    apply (elem_of_list_to_map_2 _ v) in Hlookup.
    apply elem_of_list_In in Hlookup.
    apply in_map_iff in Hlookup.
    destruct Hlookup as [? [Heqp _]].
    inversion Heqp;subst;clear Heqp.
    rewrite not_elem_of_dom in Hnin.
    apply (map_filter_lookup_None_1 _ _ p) in Hnin.
    rewrite /check_access_page.
    destruct (σ.1.1.1.2 !! p) eqn:Heq;auto.
    destruct Hnin.
    rewrite lookup_fmap Heq //in H.
    specialize (H p0.2).
    case_match.
    case_match;auto.
    exfalso.
    apply H.
    rewrite lookup_fmap Heq //.
    done.
  Qed.

  Lemma access_agree_check_true_forall {q} σ v s :
    own gen_access_name (●(get_access_gmap σ)) -∗
    v -@{ q }A> s -∗
    ⌜set_Forall (λ p, check_access_page σ v p = true) s⌝.
  Proof.
    iIntros "Hσ Hacc".
    iDestruct (access_agree with "Hσ Hacc") as %Hvalid.
    apply access_pgt_lookup in Hvalid as Hvalid.
    iPureIntro.
    intros p Hin.
    eapply Hvalid in Hin.
    rewrite /check_access_page.
    destruct Hin as (? & ? & ? & [-> Hin']).
    case_match;auto.
  Qed.

  Lemma access_agree_check_true {σ q} p i s:
   p ∈ s ->
   own gen_access_name (●(get_access_gmap σ)) -∗
   (i -@{q}A> s) -∗
   ⌜(check_access_page σ i p)= true⌝.
  Proof.
    iIntros (Hin) "Hσ Hacc".
    iDestruct (access_agree_check_true_forall with "Hσ Hacc") as "%Hforall".
    iPureIntro.
    by apply Hforall.
  Qed.

  Lemma own_agree_Some_lookup {σ} p i:
   ghost_map_auth gen_own_name 1 (get_own_gmap σ) -∗
   (p -@O> i) -∗
   ⌜∃ b s, (get_page_table σ) !! p= Some (Some i,b,s)⌝.
  Proof.
    iIntros "Hσ Hown".
    rewrite own_mapsto_eq /own_mapsto_def.
    iDestruct (own_agree with "Hσ Hown") as %Hvalid.
    iPureIntro.
    apply own_pgt_lookup in Hvalid as [? Hvalid].
    exists x.
    done.
  Qed.

  Lemma own_agree_None_lookup {σ} p:
   ghost_map_auth gen_own_name 1 (get_own_gmap σ) -∗
   (p -@O> -) -∗
   ⌜∃ b s, (get_page_table σ) !! p= Some (None,b,s)⌝.
  Proof.
    iIntros "Hσ Hown".
    rewrite own_mapsto_eq /own_mapsto_def.
    iDestruct (own_agree with "Hσ Hown") as %Hvalid.
    iPureIntro.
    apply own_pgt_lookup in Hvalid as [? [? Hvalid]].
    do 2 eexists.
    done.
  Qed.

  Lemma own_agree_Some_check_true {σ} p i:
   ghost_map_auth gen_own_name 1 (get_own_gmap σ) -∗
   (p -@O> i) -∗
   ⌜(check_ownership_page σ i p)= true⌝.
  Proof.
    iIntros  "Hσ Hown".
    iDestruct (own_agree_Some_lookup with "Hσ Hown") as %[b [s Hlookup]].
    iPureIntro.
    rewrite /check_ownership_page.
    rewrite Hlookup.
    rewrite decide_True;eauto.
  Qed.

  Lemma own_agree_Some_check_false {σ} p i j:
    j ≠ i ->
    ghost_map_auth gen_own_name 1 (get_own_gmap σ) -∗
    (p -@O> j) -∗
    ⌜(check_ownership_page σ i p)= false⌝.
  Proof.
    iIntros (Hneq) "Hσ Hown".
    iDestruct (own_agree_Some_lookup with "Hσ Hown") as %[b [s Hlookup]].
    iPureIntro.
    rewrite /check_ownership_page.
    rewrite Hlookup.
    rewrite decide_False;eauto.
  Qed.

  Lemma own_agree_None_check {σ} p i:
    ghost_map_auth gen_own_name 1 (get_own_gmap σ) -∗
    (p -@O> -) -∗
    ⌜(check_ownership_page σ i p)= false⌝.
  Proof.
    iIntros "Hσ Hown".
    iDestruct (own_agree_None_lookup with "Hσ Hown") as %[b [s Hlookup]].
    iPureIntro.
    rewrite /check_ownership_page.
    rewrite Hlookup //.
  Qed.

  Lemma excl_agree_Some_lookup {σ} p b:
   ghost_map_auth gen_excl_name 1 (get_excl_gmap σ) -∗
   (p -@E> b) -∗
   ⌜∃ o b' s, (get_page_table σ) !! p= Some (o,b',s) ∧ b = b' && bool_decide (size s <= 1)⌝.
  Proof.
    iIntros  "Hσ Hexcl".
    rewrite excl_mapsto_eq /excl_mapsto_def.
    iDestruct (excl_agree with "Hσ Hexcl") as %Hvalid.
    iPureIntro.
    apply excl_pgt_lookup in Hvalid as (? & ? & Hvalid).
    exists x, x0.
    done.
  Qed.

  Lemma excl_agree_Some_check_true {σ} p:
   ghost_map_auth gen_excl_name 1 (get_excl_gmap σ) -∗
   (p -@E> true) -∗
   ⌜(check_excl_page σ p)= true⌝.
  Proof.
    iIntros  "Hσ Hexcl".
    iDestruct (excl_agree_Some_lookup with "Hσ Hexcl") as %[o [b [s [Hlookup Heq]]]].
    iPureIntro.
    rewrite /check_excl_page.
    rewrite Hlookup.
    symmetry in Heq.
    rewrite andb_true_iff in Heq.
    destruct Heq;done.
  Qed.

  (* own *)
  Lemma own_agree_Some_lookup_bigS {σ i} (s:gset PID):
   ghost_map_auth gen_own_name 1 (get_own_gmap σ) -∗
   ([∗ set] p ∈ s, p -@O> i) -∗
   ⌜set_Forall (λ p, ∃ b s,  get_page_table σ !! p = Some (Some i,b,s) ) s⌝.
  Proof.
    iIntros "Hown Hpgt".
    iIntros (p Hin_p).
    iDestruct (big_sepS_elem_of _ _ p Hin_p with "Hpgt") as "Hpgt".
    iApply (own_agree_Some_lookup with "Hown Hpgt").
  Qed.

  Lemma own_agree_Some_check_true_bigS {σ i} (s:gset PID):
   ghost_map_auth gen_own_name 1 (get_own_gmap σ) -∗
   ([∗ set] p ∈ s, p -@O> i) -∗
   ⌜set_Forall (λ p, check_ownership_page σ i p = true) s⌝.
  Proof.
    iIntros "Hown Hpgt".
    iIntros (p Hin_p).
    iDestruct (big_sepS_elem_of _ _ p Hin_p with "Hpgt") as "Hpgt".
    iApply (own_agree_Some_check_true with "Hown Hpgt").
  Qed.

  (* excl *)
  Lemma excl_agree_Some_lookup_bigS {σ b} (s:gset PID):
   ghost_map_auth gen_excl_name 1 (get_excl_gmap σ) -∗
   ([∗ set] p ∈ s, p -@E> b) -∗
   ⌜set_Forall (λ p, ∃ o b' s,  get_page_table σ !! p = Some (o,b',s) ∧ b = b' && bool_decide(size s <= 1)) s⌝.
  Proof.
    iIntros "Hexcl Hpgt".
    iIntros (p Hin_p).
    iDestruct (big_sepS_elem_of _ _ p Hin_p with "Hpgt") as "Hpgt".
    iApply  (excl_agree_Some_lookup with "Hexcl Hpgt").
  Qed.

  Lemma excl_agree_Some_check_true_bigS {σ} (s:gset PID):
   ghost_map_auth gen_excl_name 1 (get_excl_gmap σ) -∗
   ([∗ set] p ∈ s, p -@E> true) -∗
   ⌜set_Forall (λ p, check_excl_page σ p = true) s⌝.
  Proof.
    iIntros "Hexcl Hpgt".
    iIntros (p Hin_p).
    iDestruct (big_sepS_elem_of _ _ p Hin_p with "Hpgt") as "Hpgt".
    iApply (excl_agree_Some_check_true with "Hexcl Hpgt").
  Qed.

  Lemma excl_update{gm x b} b':
    gm !! x = Some b ->
    ghost_map_auth gen_excl_name 1 gm -∗ x -@E> b ==∗
    ghost_map_auth gen_excl_name 1  (<[x := b']>gm) ∗ x -@E> b'.
  Proof.
    iIntros (Hlookup) "Hauth Hfrag".
    rewrite excl_mapsto_eq /excl_mapsto_def.
    iApply ((ghost_map_update b') with "Hauth Hfrag").
  Qed.

  Lemma owned_update{gm x i} j:
    gm !! x = Some (Some i) ->
    ghost_map_auth gen_own_name 1 gm -∗ x -@O> i ==∗
    ghost_map_auth gen_own_name 1  (<[x := (Some j)]>gm) ∗ x -@O> j.
  Proof.
    iIntros (Hlookup) "Hauth Hfrag".
    rewrite own_mapsto_eq /own_mapsto_def.
    iApply ((ghost_map_update (Some j)) with "Hauth Hfrag").
  Qed.

  Lemma access_update{gm x s} s':
    gm !! x = Some (to_frac_agree 1 s) ->
    own gen_access_name (● gm) -∗ x -@A> s ==∗
    own gen_access_name (● <[x := (to_frac_agree 1 s')]>gm) ∗ x -@A> s'.
  Proof.
    iIntros (Hlookup) "Hauth Hfrag".
    rewrite access_mapsto_eq /access_mapsto_def.
    rewrite -own_op.
    iApply ((own_update _ (● gm ⋅ ◯ {[x := (to_frac_agree 1 s)]}) _ ) with "[Hauth Hfrag]").
    2: { rewrite own_op. iFrame. }
    apply auth_update.
    apply (singleton_local_update gm x (to_frac_agree 1 s)).
    done.
    apply exclusive_local_update.
    done.
  Qed.

  Lemma excl_update_flip {gm b} sps:
    ghost_map_auth gen_excl_name 1 gm -∗
    ([∗ set] p ∈ sps, p -@E> b)%I==∗
    ghost_map_auth gen_excl_name 1 (flip_excl_gmap gm sps) ∗
    ([∗ set] p ∈ sps, p -@E> (negb b))%I.
  Proof.
    iIntros "Hauth Hfrag".
    rewrite /flip_excl_gmap /update_pgt_gmap /=.
    iInduction sps as [|] "IH" using set_ind_L forall (gm).
    rewrite set_fold_empty.
    rewrite !big_sepS_empty.
    by iFrame.
    rewrite set_fold_disj_union_strong.
    rewrite set_fold_singleton.
    iDestruct (big_sepS_union with "Hfrag") as "[Hsingle Hfrag]".
    set_solver + H.
    rewrite big_sepS_singleton.
    iDestruct (excl_agree with "Hauth [Hsingle]") as %Hlookup.
    { rewrite excl_mapsto_eq /excl_mapsto_def. iFrame. }
    rewrite Hlookup.
    {
      iDestruct (excl_update (negb b) with "Hauth Hsingle") as ">[Hauth Hsingle]";auto.
      rewrite big_sepS_union;last set_solver + H.
      rewrite big_sepS_singleton.
      iFrame "Hsingle".
      iApply ("IH" with "Hauth Hfrag").
     }
    {
      intros.
      destruct (b' !! x2) as [p2|] eqn: Hlookup2, (b' !! x1) as [p1|] eqn:Hlookup1;
        try destruct p1 as [q1 []]; try destruct p2 as [q2 []]; rewrite ?lookup_insert_ne ?Hlookup1 ?Hlookup2 //;last eauto.
      apply insert_commute.
      done.
    }
    set_solver + H.
  Qed.

  Lemma own_update_upd {gm i} j ps:
    ghost_map_auth gen_own_name 1 gm -∗
    ([∗ set] p ∈ ps, p -@O> i)%I==∗
    ghost_map_auth gen_own_name 1 (upd_own_gmap j gm ps) ∗
    ([∗ set] p ∈ ps, p -@O> j)%I.
  Proof.
    iIntros "Hauth Hfrag".
    rewrite /upd_own_gmap /update_pgt_gmap /=.
    iInduction ps as [|] "IH" using set_ind_L forall (gm).
    rewrite set_fold_empty.
    rewrite !big_sepS_empty.
    by iFrame.
    rewrite set_fold_disj_union_strong.
    rewrite set_fold_singleton.
    iDestruct (big_sepS_union with "Hfrag") as "[Hsingle Hfrag]".
    set_solver + H.
    rewrite big_sepS_singleton.
    iDestruct (own_agree with "Hauth [Hsingle]") as %Hlookup.
    { rewrite own_mapsto_eq /own_mapsto_def. iFrame. }
    rewrite Hlookup.
    {
      iDestruct (owned_update j with "Hauth Hsingle") as ">[Hauth Hsingle]";auto.
      rewrite big_sepS_union;last set_solver + H.
      rewrite big_sepS_singleton.
      iFrame "Hsingle".
      iApply ("IH" with "Hauth Hfrag").
     }
    {
      intros.
      destruct (b' !! x2) as [p2|] eqn: Hlookup2, (b' !! x1) as [p1|] eqn:Hlookup1;
        try destruct p1 as [q1 []]; try destruct p2 as [q2 []]; rewrite ?lookup_insert_ne ?Hlookup1 ?Hlookup2 //;last eauto.
      apply insert_commute.
      done.
    }
    set_solver + H.
  Qed.

End pagetable_rules.
