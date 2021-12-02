From HypVeri.algebra Require Import base.
From HypVeri Require Import lang_extra.

Section mem_rules.

  Context `{vmG : gen_VMG Σ}.
  Implicit Type σ : state.
  Implicit Types w: Word.
  Implicit Types a: Addr.

  Definition mem_region (instr: list Word) (b:Addr):=
    ([∗ list] a;w ∈ (finz.seq b (length instr));instr, (a ->a w))%I.

  (* This definition implicitly requires the length of instr is equal to/less than page_size  *)
  Definition mem_page (instr: list Word) (p: PID):=
    ([∗ list] a;w ∈ (finz.seq (of_pid p) (Z.to_nat page_size));instr, (a ->a w))%I.

  (* rules for memory points-to *)

  Lemma mem_dupl_false a w1 w2:
    a ->a w1 -∗ a ->a w2 -∗ False.
  Proof using.
    rewrite mem_mapsto_eq /mem_mapsto_def.
    iIntros "Ha1 Ha2".
    iDestruct (ghost_map_elem_valid_2 with "Ha1 Ha2") as %Hvalid.
    destruct Hvalid as [Hvalid _].
    apply dfrac_valid_own_r in Hvalid.
    inversion Hvalid.
  Qed.

  Lemma mem_neq a1 a2 w1 w2:
    a1 ->a w1 -∗ a2 ->a w2 -∗ ⌜ a1 <> a2⌝.
  Proof using.
    iIntros "Ha1 Ha2".
    destruct (decide (a1 = a2)).
    - rewrite e //.
      iDestruct (mem_dupl_false with "Ha1 Ha2") as %[].
    - done.
  Qed.

  Lemma gen_mem_valid {σ} a w:
    ghost_map_auth (gen_mem_name vmG) 1 (get_mem σ) -∗
    a ->a w -∗
    ⌜(get_mem σ) !! a = Some w⌝.
  Proof.
    iIntros "Hσ Ha".
    rewrite mem_mapsto_eq /mem_mapsto_def.
    iApply (ghost_map_lookup with "Hσ Ha").
  Qed.

  Lemma gen_mem_valid_SepM {σ} mem:
    ghost_map_auth (gen_mem_name vmG) 1 (get_mem σ) -∗
    ([∗ map] a↦w ∈ mem, a ->a w)-∗
    ([∗ map] a↦w ∈ mem, ⌜(get_mem σ) !! a = Some w⌝).
  Proof.
    iIntros "Hσ Hmem".
    rewrite mem_mapsto_eq /mem_mapsto_def.
    iDestruct ((ghost_map_lookup_big mem) with "Hσ Hmem") as "%Hincl".
    iApply big_sepM_pure.
    iPureIntro.
    intros a w H.
    apply (lookup_weaken mem (get_mem σ) _ _ H Hincl) .
  Qed.

  Lemma gen_mem_valid_SepL {σ} al ml:
    NoDup al ->
    ghost_map_auth (gen_mem_name vmG) 1 (get_mem σ) -∗
    ([∗ list] a;w ∈ al;ml, a ->a w)-∗
    ([∗ list] a;w ∈ al;ml, ⌜(get_mem σ) !! a = Some w⌝).
  Proof.
    iIntros (Hnodup) "Hσ Hmem".
    iDestruct (big_sepL2_alt with "Hmem") as "[%Heqlen Hmem]".
    iApply big_sepL2_alt.
    iSplitR;eauto.
    rewrite <- (@map_to_list_to_map Addr (gmap Addr) _  _  _  _ _ _ _ _ _ Word (zip al ml)).
    2: { rewrite fst_zip;[eauto|lia].  }
    rewrite -(big_opM_map_to_list (λ a w, ⌜(get_mem σ) !! a = Some w ⌝%I)).
    rewrite -(big_opM_map_to_list (λ a w, (a ->a w)%I)).
    iApply (gen_mem_valid_SepM with "Hσ Hmem").
  Qed.

  Lemma gen_mem_valid_SepL_pure {σ} al ml:
    NoDup al ->
    ghost_map_auth (gen_mem_name vmG) 1 (get_mem σ) -∗
    ([∗ list] a;w ∈ al;ml,  a ->a w) -∗
    ⌜∀ (k : nat) (y1 y2 : Addr),
      al !! k = Some y1 → ml !! k = Some y2 → get_mem σ !! y1 = Some y2⌝.
  Proof.
    iIntros (Hnodup) "Hσ Hmem".
    iDestruct (gen_mem_valid_SepL with "Hσ Hmem") as "H";eauto.
    iApply (big_sepL2_pure_1 with "H").
  Qed.

  Lemma gen_mem_valid2 {σ} a1 w1 a2 w2:
    ghost_map_auth (gen_mem_name vmG) 1 (get_mem σ) -∗
    a1 ->a w1 -∗
    a2 ->a w2 -∗
    ⌜(get_mem σ) !! a1 = Some w1⌝ ∗ ⌜(get_mem σ) !! a2 = Some w2⌝.
  Proof.
    iIntros "Hσ Ha1 Ha2".
    iDestruct (mem_neq with "Ha1 Ha2") as "%Hne".
    iDestruct (gen_mem_valid_SepM {[a1:=w1;a2:=w2]} with "Hσ [Ha1 Ha2]") as "%Hforall";eauto.
    { rewrite !big_sepM_insert ?big_sepM_empty;eauto.
      iFrame.
      by simplify_map_eq.
    }
    iPureIntro. split.
    by apply (Hforall a1 w1 (lookup_insert _ a1 w1)).
    apply (Hforall a2 w2); by simplify_map_eq.
  Qed.

  Lemma gen_mem_update1 {σ} a w w':
    ghost_map_auth (gen_mem_name vmG) 1 (get_mem σ) -∗
    a ->a w ==∗
    ghost_map_auth (gen_mem_name vmG) 1 (<[a:=w']>(get_mem σ)) ∗
    a ->a w'.
  Proof.
    iIntros "Hσ Ha".
    rewrite mem_mapsto_eq /mem_mapsto_def.
    iDestruct (ghost_map_update w' with "Hσ Ha") as ">[Hσ Ha]".
    by iFrame.
  Qed.

  Lemma gen_mem_update_SepL2 {σ} (ads : list Addr) (wl wl': list Word):
    NoDup ads ->
    length wl = length wl' ->
    ghost_map_auth (gen_mem_name vmG) 1 (get_mem σ) -∗
    ([∗ list] a;w ∈ ads;wl, a ->a w) ==∗
    ghost_map_auth (gen_mem_name vmG) 1 ((list_to_map (zip ads wl'))  ∪ (get_mem σ)) ∗
    [∗ list] a;w' ∈ ads;wl', a ->a w'.
  Proof.
    iIntros (Hnodup Hlen) "Hσ Hmm".
    iDestruct (big_sepL2_alt with "Hmm") as "[% Hmm]".
    rewrite <- (@map_to_list_to_map Addr (gmap Addr) _  _  _  _ _ _ _ _ _ Word _).
    2: { rewrite fst_zip //;lia. }
    rewrite -(big_opM_map_to_list (λ a w,  (a ->a w)%I) _ ).
    rewrite  mem_mapsto_eq /mem_mapsto_def.
    iDestruct ((ghost_map_update_big _  (list_to_map (zip ads wl'))) with "Hσ Hmm") as ">[Hσ Hmm]".
    { rewrite  !dom_list_to_map_L. f_equal.  rewrite !fst_zip  //. lia. lia. }
    rewrite (big_opM_map_to_list (λ a w,  (a ↪[gen_mem_name vmG] w)%I) _ ).
    rewrite map_to_list_to_map.
    2 : { rewrite fst_zip //. lia. }
    rewrite big_sepL2_alt.
    iFrame "Hσ Hmm". rewrite -Hlen H //.
  Qed.

  Lemma gen_mem_update_page{σ wl} p (wl': list Word):
    length wl' = (Z.to_nat page_size) ->
    ghost_map_auth (gen_mem_name vmG) 1 (get_mem σ) -∗
    mem_page wl p ==∗
    ghost_map_auth (gen_mem_name vmG) 1
    (list_to_map (zip (finz.seq p (Z.to_nat page_size)) wl') ∪ get_mem σ) ∗
    mem_page wl' p.
  Proof.
    iIntros (Hlen) "Hσ Hp".
    rewrite /mem_page.
    iAssert (⌜ length wl = Z.to_nat 1000 ⌝%I) as "%Hlen'".
    { iDestruct (big_sepL2_alt with "Hp") as "[% Hp]". iPureIntro. rewrite finz_seq_length in H. lia. }
    iApply ((gen_mem_update_SepL2 (finz.seq p (Z.to_nat 1000)) wl wl') with "Hσ");eauto.
    apply finz_seq_NoDup'.
    apply last_addr_in_bound. lia.
  Qed.

  Lemma mem_pages_SepL2_length_pure ps wss:
    ([∗ list] p;ws ∈ ps;wss, mem_page ws p) ⊢ ⌜ (forall ws, ws ∈ wss -> length ws = (Z.to_nat page_size)) ⌝.
  Proof.
    revert ps.
    rewrite /mem_page.
    induction wss.
    - iIntros (?) "Hl".
      iPureIntro; intros; inversion H.
    -  iIntros (?) "Hl".
       destruct ps; cbn.
       { iExFalso; done. }
       { iIntros (??).
         iDestruct "Hl" as "[Hl Hls]".
         iDestruct (big_sepL2_length with  "Hl") as "%".
         rewrite finz_seq_length in H.
         apply elem_of_cons in a1 as [Heqa | Hin].
         subst a0.
         done.
         iDestruct ((IHwss ps) with "Hls") as "%Hforall".
         iPureIntro.
         by apply Hforall. }
  Qed.

  Lemma mem_page2_invalid{ws ws'} p :
    mem_page ws p ∗ mem_page ws' p -∗ False.
  Proof.
    iIntros "[Hpg Hpg']".
    rewrite /mem_page.
    iDestruct (big_sepL2_alt with "Hpg") as "[%Heqlen Hpg]".
    iDestruct (big_sepL2_alt with "Hpg'") as "[%Heqlen' Hpg']".
    destruct ws, ws';cbn.
    inversion Heqlen.
    inversion Heqlen.
    inversion Heqlen'.
    rewrite finz_seq_cons;[|lia].
    cbn.
    iDestruct "Hpg" as "[Hp Hpg]".
    iDestruct "Hpg'" as "[Hp' Hpg']".
    rewrite mem_mapsto_eq /mem_mapsto_def.
    iDestruct (ghost_map_elem_valid_2 with "Hp Hp'") as "%Hvalid".
    destruct Hvalid as [Hvalid _].
    rewrite dfrac_op_own in Hvalid.
    rewrite -> dfrac_valid_own in Hvalid.
    exfalso.
    apply (bool_decide_unpack _).
    by compute.
  Qed.

  Lemma mem_pages_SepL2_acc p ps wss:
    p ∈ ps ->
    ([∗ list] p;ws ∈ ps;wss, mem_page ws p) ⊢
    ∃ ws,  mem_page ws p ∗ ( mem_page ws p -∗  ([∗ list] p;ws ∈ ps;wss, mem_page ws p)).
  Proof.
    iIntros (Hin) "Hl".
    apply elem_of_list_lookup_1 in Hin.
    destruct Hin as [? Hlk].
    assert (HisSome: is_Some (ps!!x)). eauto.
    pose proof (lookup_lt_is_Some_1 ps x HisSome) as Hltlen.
    iDestruct (big_sepL2_length with  "Hl") as "%Heqlen".
    rewrite Heqlen in Hltlen.
    apply lookup_lt_is_Some_2 in Hltlen.
    destruct Hltlen as [? Hlk'].
    iExists x0.
    iApply (big_sepL2_lookup_acc (λ _ p0 ws, mem_page ws p0) ps wss );eauto.
  Qed.

  Lemma mem_pages_SepL2_NoDup ps wss:
    ([∗ list] p;ws ∈ ps;wss, mem_page ws p) -∗ ⌜ NoDup ps ⌝.
  Proof.
    revert wss.
    induction ps.
    - iIntros (?) "Hl".
      iPureIntro; intros; constructor.
    -  iIntros (?) "Hl".
       destruct wss; cbn.
       { iExFalso; done. }
       { rewrite NoDup_cons.
         iAssert (⌜ a ∉ ps ⌝%I) as "%Hnotin".
         iIntros (?).
         iDestruct "Hl" as "[Hl Hls]".
         iDestruct ((mem_pages_SepL2_acc a ps wss) with "Hls") as "Hl'";eauto.
         iDestruct "Hl'" as (ws') "[Hl' Hacc]".
         iApply mem_page2_invalid.
         iFrame "Hl Hl'".
         iDestruct "Hl" as "[Hl Hls]".
         iDestruct ((IHps wss) with "Hls") as "%Hnodup".
         done. }
  Qed.

  Lemma mem_pages_to_mem_region_SepL2 (ps: list PID) (wss: list (list Word)):
    ([∗ list] p;ws ∈ ps;wss, mem_page ws p) -∗
    [∗ list] a;w ∈ (list_pid_to_addr ps);(flat_list_list_word wss), a ->a w.
  Proof.
    rewrite /mem_page /list_pid_to_addr /flat_list_list_word.
    iRevert (wss).
    iInduction ps as [|p ps'] "IH";cbn.
    iIntros (?) "Hl".
    iDestruct (big_sepL2_alt with "Hl") as "[%Heqlen Hl]".
    destruct a;try inversion Heqlen.
    done.
    iIntros (wss) "Hlist".
    destruct wss;cbn;try done.
    iDestruct ("Hlist") as "[Hl Hlist]".
    iApply (big_sepL2_app with "Hl").
    by iApply "IH".
  Qed.

  Lemma mem_region_to_mem_pages_SepL2 (ps: list PID) (wss: list (list Word)):
    (forall ws', ws' ∈ wss -> length ws' = (Z.to_nat page_size)) ->
    ([∗ list] a;w ∈ (list_pid_to_addr ps);(flat_list_list_word wss), a ->a w) -∗
    ([∗ list] p;ws ∈ ps;wss, mem_page ws p).
  Proof.
    rewrite /mem_page /list_pid_to_addr /flat_list_list_word.
    iRevert (wss).
    iInduction ps as [|p ps'] "IH";cbn.
    iIntros (??) "Hl".
    iDestruct (big_sepL2_alt with "Hl") as "[%Heqlen Hl]".
    destruct a.
    done.
    assert (length l = Z.to_nat 1000) as Heqlen'.
    { apply x. apply elem_of_cons;left;done. }
    rewrite app_length Heqlen' in Heqlen.
    inversion Heqlen.
    iIntros (wss Hlen) "Hlist".
    destruct wss;cbn;try done.
    iDestruct (big_sepL2_app_inv with "Hlist") as "Hlist".
    { left. rewrite finz_seq_length. symmetry;apply Hlen.  apply elem_of_cons;left;done. }
    iDestruct ("Hlist") as "[Hl Hlist]".
    iFrame "Hl".
    iApply "IH".
    { iPureIntro. intros.
      apply Hlen.
      apply elem_of_cons;right;done. }
    done.
  Qed.

  Lemma gen_mem_update_pages{wss σ} (ps: list PID) (wss': list (list Word)):
    (forall ws', ws' ∈ wss' -> length ws' = (Z.to_nat page_size)) ->
    length ps = length wss' ->
    ghost_map_auth (gen_mem_name vmG) 1 (get_mem σ) -∗
    ([∗ list] p;ws ∈ ps;wss, mem_page ws p) ==∗
    ghost_map_auth (gen_mem_name vmG) 1 ((list_to_map
                              (zip (list_pid_to_addr ps) (flat_list_list_word wss'))) ∪ (get_mem σ)) ∗
    [∗ list] p;ws'∈ ps;wss',mem_page ws' p.
  Proof.
    iIntros (Hwslen Hwsslen) "Hσ Hpgs".
    iDestruct (mem_pages_SepL2_NoDup with "Hpgs") as "%".
    iDestruct (mem_pages_SepL2_length_pure with "Hpgs") as "%".
    iDestruct (big_sepL2_length with "Hpgs") as "%".
    iDestruct (mem_pages_to_mem_region_SepL2 with "Hpgs") as "Hpgs".
    iDestruct ((gen_mem_update_SepL2 _ (flat_list_list_word wss) (flat_list_list_word wss')) with "Hσ Hpgs") as ">[Hσ Hpgs]".
    { apply list_pid_to_addr_NoDup;eauto. }
    { apply flat_list_list_word_length_eq;eauto. lia. }
    iFrame "Hσ".
    iApply mem_region_to_mem_pages_SepL2;eauto.
  Qed.

End mem_rules.
