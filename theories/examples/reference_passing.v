From iris.algebra Require Import excl.
From iris.heap_lang Require Import proofmode notation tactics.
From iris.heap_lang.lib Require Import par.
From iris.proofmode Require Import tactics.
From iris_monotone Require Import monotone.

Definition wait : val :=
  rec: "f" "l" "v" := if: !"l" = "v" then #() else "f" "l" "v".

Definition thread1 : val :=
  λ: "l" "lw",
    let: "l'" := ref #42 in
    "l" <- "l'";;
    "lw" <- #1;;
    wait "lw" #2;;
    !"l'".

Definition thread2 : val :=
  λ: "l" "lw",
    wait "lw" #1;;
    FAA !"l" #2;;
    "lw" <- #2.

Definition program : expr :=
  let: "l" := ref #0 in
  let: "lw" := ref #0 in
  (thread1 "l" "lw") ||| (thread2 "l" "lw").

  Definition sts_state : Type := nat * option loc * nat.

  Inductive sts_rel_base : relation sts_state :=
  | sts_rel_base_none_some l : sts_rel_base (0, None, 0) (1, Some l, 42)
  | sts_rel_base_42_44 l : sts_rel_base (1, Some l, 42) (1, Some l, 44)
  | sts_rel_base_one_two l : sts_rel_base (1, Some l, 44) (2, Some l, 44).

  Definition sts_rel := rtc sts_rel_base.

  Lemma sts_rel_zeros x : sts_rel (0, None, 0) x → x.1.1 = 0 → x = (0, None, 0).
  Proof.
    intros Hrl; destruct x as [[k ol] n].
    set (P (x : sts_state) := x.1.1 = 0 → x = (0, None, 0)).
    eapply (rtc_ind_r P (0, None, 0)); unfold P; clear P; [by eauto| |done].
    intros y [[] ?] IHy Hyz Hy Hz1; simplify_eq/=.
    inversion Hyz; eauto.
  Qed.

  Lemma sts_rel_loc_fixed x y l :
    sts_rel x y → x.1.2 = Some l → y.1.2 = Some l.
  Proof.
    set (P (y : sts_state) := x.1.2 = Some l → y.1.2 = Some l).
    eapply (rtc_ind_r P x); unfold P; clear P; [done|].
    intros [[] ] [[]] IHw Hwz Hx1 Hx2; intros; simplify_eq/=.
    apply Hx1 in Hx2.
    inversion Hwz; simplify_eq/=; done.
  Qed.

  Lemma sts_rel_one_two x y l :
    sts_rel x y → x.1.1 = 1 → x.1.2 = Some l → y.1.1 = 2 → y = (2, Some l, 44).
  Proof.
    set (P (y : sts_state) :=
           x.1.1 = 1 → x.1.2 = Some l → y.1.1 = 2 → y = (2, Some l, 44)).
    eapply (rtc_ind_r P x); unfold P; clear P; [|].
    - destruct x as [[] ]; intros; simplify_eq/=.
    - intros w [[]] IHw Hwz ? ?; intros; simplify_eq/=.
      inversion Hwz; simplify_eq/=.
      eapply sts_rel_loc_fixed in IHw; last done.
      simplify_eq/=; done.
  Qed.

  Lemma sts_rel_from_two x y l :
    sts_rel x y → x = (2, Some l, 44) → y = (2, Some l, 44).
  Proof.
    set (P (y : sts_state) := x = (2, Some l, 44) → y = (2, Some l, 44)).
    eapply (rtc_ind_r P x); unfold P; clear P; [done|].
    intros w [[]] IHw Hwz Hw ?; simplify_eq/=.
    rewrite Hw in Hwz; last done.
    inversion Hwz.
  Qed.

  Lemma sts_rel_zero_one x :
    sts_rel (0, None, 0) x → x.1.1 = 1 →
    ∃ l, x = (1, Some l, 42) ∨ x = (1, Some l, 44).
  Proof.
    intros Hrl; destruct x as [[k ol] n].
    set (P (x : sts_state) :=
           x.1.1 = 1 → ∃ l, x = (1, Some l, 42) ∨ x = (1, Some l, 44)).
    eapply (rtc_ind_r P (0, None, 0)); unfold P; clear P; [by eauto| |done].
    intros y [[] ?] IHy Hyz Hy Hz1; simplify_eq/=.
    inversion Hyz; eauto.
  Qed.

  Lemma sts_rel_from_one_42 x y l :
    sts_rel x y →
    x = (1, Some l, 42) →
    y = (1, Some l, 42) ∨ y = (1, Some l, 44) ∨ y = (2, Some l, 44).
  Proof.
    set (P (y : sts_state) :=
           x = (1, Some l, 42) →
           y = (1, Some l, 42) ∨ y = (1, Some l, 44) ∨ y = (2, Some l, 44)).
    eapply (rtc_ind_r P x); unfold P; clear P; [eauto|].
    intros w [[]] IHw Hwz Hw ?; simplify_eq/=.
    destruct Hw as [|[]]; first done; simplify_eq; inversion Hwz; eauto.
  Qed.

  Lemma sts_rel_from_one_44 x y l :
    sts_rel x y →
    x = (1, Some l, 44) →
    y = (1, Some l, 44) ∨ y = (2, Some l, 44).
  Proof.
    set (P (y : sts_state) :=
           x = (1, Some l, 44) → y = (1, Some l, 44) ∨ y = (2, Some l, 44)).
    eapply (rtc_ind_r P x); unfold P; clear P; [eauto|].
    intros w [[]] IHw Hwz Hw ?; simplify_eq/=.
    destruct Hw as [|]; first done; simplify_eq; inversion Hwz; eauto.
  Qed.

Section proof.
  Context `{!heapG Σ, !spawnG Σ,
            !inG Σ (authUR (monotoneUR sts_rel)), !inG Σ (exclR unitR)}.

  Definition state_exact (γ : gname) (s : sts_state) :=
    own γ (● principal sts_rel s).
  Definition state_atleast (γ : gname) (s : sts_state) :=
    own γ (◯ principal sts_rel s).

  Lemma state_alloc s: ⊢|==> ∃ γ, state_exact γ s.
  Proof. iApply own_alloc; apply auth_auth_valid; done. Qed.

  Lemma state_exact_atleast γ s s':
    state_exact γ s -∗ state_atleast γ s' -∗ ⌜sts_rel s' s⌝.
  Proof.
    iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as %[Hincl ?]%auth_both_valid_discrete.
    revert Hincl; rewrite principal_included; done.
  Qed.

  Lemma state_update γ s s' :
    sts_rel s s' → state_exact γ s ==∗ state_exact γ s'.
  Proof.
    intros Hss.
    iApply own_update.
    eapply auth_update_auth.
    apply monotone_local_update_grow; done.
  Qed.

  Lemma state_observe γ s :
    state_exact γ s ==∗ state_exact γ s ∗ state_atleast γ s.
  Proof.
    rewrite /state_exact /state_atleast -own_op.
    iApply own_update.
    eapply auth_update_alloc.
    apply monotone_local_update_get_frag; done.
  Qed.

  Definition token γ := own γ (Excl ()).

  Lemma token_alloc : ⊢|==> ∃ γ, token γ.
  Proof. iApply own_alloc; done. Qed.

  Lemma token_excl γ : token γ -∗ token γ -∗ False.
  Proof. iIntros "H1 H2"; iDestruct (own_valid_2 with "H1 H2") as %?; done. Qed.

  Definition invname := nroot .@ "refpass".

  Definition refpass_inv (γ γ1 γ2 γ3 : gname) (l lw : loc) : iProp Σ :=
    ∃ s, state_exact γ s ∗
     match s with
     | (k, ol, n) =>
       lw ↦ #k ∗
       (⌜1 ≤ k⌝ → token γ1 ∗ (⌜42 < n⌝ → token γ2)) ∗
       (⌜2 ≤ k⌝ → token γ3) ∗
       match ol with
       | None => True
       | Some l' => l ↦ #l' ∗ l' ↦ #n
       end
     end.

  Lemma wp_wait l (n : nat) P Q :
    {{{ P ∗ □ (P ={⊤, ⊤ ∖ ↑ invname}=∗
               ∃ w, l ↦ w ∗
                 (l ↦ w ={⊤ ∖ ↑ invname, ⊤}=∗ if decide (w = #n) then Q else P))
    }}}
      wait #l #n
    {{{ RET #(); Q }}}.
  Proof.
    iIntros (Φ) "[HP #Hws] HΦ".
    iLöb as "IH".
    rewrite /wait.
    wp_pures.
    wp_bind (! _)%E.
    iMod ("Hws" with "HP") as (w) "[Hl Hcl]".
    wp_load.
    iMod ("Hcl" with "Hl") as "Hcl".
    iModIntro.
    wp_op.
    destruct decide.
    - rewrite bool_decide_eq_true_2; last done.
      wp_pures. iApply "HΦ"; done.
    - rewrite bool_decide_eq_false_2; last done.
      wp_pure _.
      iApply ("IH" with "Hcl HΦ").
  Qed.

  Lemma wp_thread1 γ γ1 γ2 γ3 l lw :
    {{{ l ↦ #0 ∗ state_atleast γ (0, None, 0) ∗
        inv invname (refpass_inv γ γ1 γ2 γ3 l lw) ∗ token γ1 }}}
      thread1 #l #lw
    {{{ RET #44; True}}}.
  Proof.
    iIntros (Φ) "(Hl & #Hstal & #Hinv & Ht1) HΦ".
    rewrite /thread1.
    wp_pures.
    wp_alloc l' as "Hl'".
    wp_store.
    wp_bind (_ <- _)%E.
    iInv invname as ([[k ol] n]) "(>Hs & >Hlw & >Hge1 & Hrest)".
    iAssert (⌜k = 0⌝)%I as %->.
    { destruct k; first done.
      iDestruct ("Hge1" with "[]") as "[Ht1' _]"; first by auto with lia.
      iDestruct (token_excl with "Ht1 Ht1'") as %?; done. }
    wp_store.
    iDestruct (state_exact_atleast with "Hs Hstal") as %->%sts_rel_zeros;
      last done.
    iMod (state_update _ _ (1, Some l', 42) with "Hs") as "Hs".
    { repeat econstructor. }
    iMod (state_observe with "Hs") as "[Hs #Hsat]".
    iModIntro.
    iSplitL "Hs Hlw Hl Hl' Ht1".
    { iNext.
      replace #1 with #1%nat; last done.
      iExists _; iFrame; iFrame.
      iSplitL; last by iIntros (?); lia.
      iIntros (? ?); lia. }
    wp_pures.
    iClear "Hge1 Hrest".
    replace #2 with #2%nat; last done.
    wp_apply (wp_wait _ _ True (state_atleast γ (2, Some l', 44)))%I.
    { iSplit; first done.
      iIntros "!# _".
      iInv invname as ([[k' ol'] n']) "(>Hs & >Hlw & >Hge1 & Hrest)" "Hcl".
      iModIntro.
      iExists _; iFrame.
      iIntros "Hlw".
      iDestruct (state_exact_atleast with "Hs Hsat") as %Hrel.
      iMod (state_observe with "Hs") as "[Hs #Hsat']".
      iMod ("Hcl" with "[Hs Hge1 Hrest Hlw]") as "_".
      { iNext; iExists _; iFrame; iFrame. }
      iModIntro.
      destruct decide; simplify_eq; last done.
      eapply sts_rel_one_two in Hrel; [|done|done|done]; simplify_eq/=; done. }
    iIntros "#Hsat'".
    wp_pures.
    iInv invname as ([[k' ol'] n']) "(>Hs & >Hlw & >Hge1 & Htk3 & Hl)" "Hcl".
    iDestruct (state_exact_atleast with "Hs Hsat'") as %Hrel.
    eapply sts_rel_from_two in Hrel; last done; simplify_eq.
    iDestruct "Hl" as "[Hl Hl']".
    wp_load.
    iMod ("Hcl" with "[- HΦ]") as "_".
    { iNext. iExists _; iFrame; iFrame. }
    iApply "HΦ"; done.
  Qed.

    Lemma wp_thread2 γ γ1 γ2 γ3 l lw :
    {{{ state_atleast γ (0, None, 0) ∗
        inv invname (refpass_inv γ γ1 γ2 γ3 l lw) ∗ token γ2 ∗ token γ3 }}}
      thread2 #l #lw
    {{{ RET #(); True}}}.
  Proof.
    iIntros (Φ) "(#Hstal & #Hinv & Ht2 & Ht3) HΦ".
    rewrite /thread2.
    wp_pures.
    replace #1 with #1%nat; last done.
    wp_apply (wp_wait
                _ _ (token γ2)
                (∃ l', token γ2 ∗ state_atleast γ (1, Some l', 42))
                with "[Ht2]")%I.
    { iSplit; first done.
      iIntros "!# Ht2".
      iInv invname as ([[k' ol'] n']) "(>Hs & >Hlw & >Hge1 & Hrest)" "Hcl".
      iModIntro.
      iExists _; iFrame.
      iIntros "Hlw".
      destruct decide.
      - simplify_eq/=.
        iDestruct (state_exact_atleast with "Hs Hstal") as %Hrel.
        apply sts_rel_zero_one in Hrel as [l' [Hrel|Hrel]];
          simplify_eq; last done.
        + iMod (state_observe with "Hs") as "[Hs #Hsat']".
          iMod ("Hcl" with "[Hs Hge1 Hrest Hlw]") as "_".
          { iNext; iExists _; iFrame; iFrame. }
          iModIntro; eauto.
        + iDestruct ("Hge1" with "[]") as "[? Hge1]"; first done.
          iDestruct ("Hge1" with "[]") as "Ht2'"; first by auto with lia.
          iDestruct (token_excl with "Ht2 Ht2'") as %?; done.
      - iMod ("Hcl" with "[Hs Hge1 Hrest Hlw]") as "_"; last done.
        iNext; iExists _; iFrame; iFrame. }
    iDestruct 1 as (l') "[Ht2 #Hsat]".
    wp_pures.
    wp_bind (! _)%E.
    iInv invname as ([[k ol] n]) "(>Hs & >Hlw & >Hge1 & Htk3 & Hl)" "Hcl".
    iDestruct (state_exact_atleast with "Hs Hsat") as %Hrel.
    eapply sts_rel_loc_fixed in Hrel; last done; simplify_eq/=.
    iDestruct "Hl" as "[Hl Hl']".
    wp_load.
    iMod ("Hcl" with "[- Ht2 Ht3 HΦ]") as "_".
    { iNext. iExists _; iFrame; iFrame. }
    iModIntro.
    wp_bind (FAA _ _)%E.
    iInv invname as ([[k' ol'] n']) "(>Hs & >Hlw & >Hge1 & Htk3 & Hl)" "Hcl".
    iDestruct (state_exact_atleast with "Hs Hsat") as %Hrel.
    iAssert (⌜(k', ol', n') = (1, Some l', 42)⌝)%I as %?.
    { eapply sts_rel_from_one_42 in Hrel as [|[]]; last done;
        simplify_eq; [done| |].
      - iDestruct ("Hge1" with "[]") as "[? Hge1]"; first done.
        iDestruct ("Hge1" with "[]") as "Ht2'"; first by auto with lia.
        iDestruct (token_excl with "Ht2 Ht2'") as %?; done.
      - iDestruct ("Hge1" with "[]") as "[? Hge1]"; first by auto with lia.
        iDestruct ("Hge1" with "[]") as "Ht2'"; first by auto with lia.
        iDestruct (token_excl with "Ht2 Ht2'") as %?; done. }
    simplify_eq.
    iDestruct "Hl" as "[Hl Hl']".
    wp_faa.
    replace #(42%nat + 2) with #44 by done.
    iMod (state_update _ _ (1, Some l', 44) with "Hs") as "Hs".
    { repeat econstructor. }
    iMod (state_observe with "Hs") as "[Hs #Hsat']".
    iMod ("Hcl" with "[- Ht3 HΦ]") as "_".
    { iDestruct ("Hge1" with "[]") as "[? Hge1]"; first done.
      iNext. iExists _; iFrame; iFrame; eauto. }
    iModIntro.
    wp_pures.
    iInv invname as ([[k' ol'] n']) "(>Hs & >Hlw & Hge1 & >Htk3 & Hl)" "Hcl".
    iDestruct (state_exact_atleast with "Hs Hsat'") as %Hrel'.
    iAssert (⌜(k', ol', n') = (1, Some l', 44)⌝)%I as %?.
    { eapply sts_rel_from_one_44 in Hrel' as []; last done;
        simplify_eq; [done|].
      iDestruct ("Htk3" with "[]") as "Htk3"; first done.
      iDestruct (token_excl with "Ht3 Htk3") as %?; done. }
    simplify_eq.
    iDestruct "Hl" as "[Hl Hl']".
    wp_store.
    replace #44%nat with #44 by done.
    iMod (state_update _ _ (2, Some l', 44) with "Hs") as "Hs".
    { repeat econstructor. }
    iMod ("Hcl" with "[- HΦ]") as "_".
    { iDestruct ("Hge1" with "[]") as "[? Hge1]"; first done.
      iDestruct ("Hge1" with "[]") as "?"; first by auto with lia.
      iNext. iExists _; iFrame; iFrame; eauto. }
    iModIntro.
    iApply "HΦ"; done.
  Qed.

  Theorem wp_program :
    {{{ True }}} program {{{ RET (#44, #()); True}}}.
  Proof.
    iIntros (?) "_ HΦ".
    rewrite /program.
    wp_alloc l as "Hl".
    wp_alloc lw as "Hlw".
    wp_pures.
    iMod (state_alloc (0, None, 0)) as (γ) "Hs".
    iMod (state_observe with "Hs") as "[Hs #Hast]".
    iMod token_alloc as (γ1) "Ht1".
    iMod token_alloc as (γ2) "Ht2".
    iMod token_alloc as (γ3) "Ht3".
    iMod (inv_alloc invname _ (refpass_inv γ γ1 γ2 γ3 l lw)
            with "[Hs Hlw]") as "#Hinv".
    { replace #0 with #0%nat; last done.
      iNext. iExists _; iFrame; iFrame.
      iSplitL; [|iSplitL]; last done; iIntros (?); lia. }
    wp_apply (wp_par (λ v, ⌜v = #44⌝) (λ v, ⌜v = #()⌝)
                with "[Ht1 Hl] [Ht2 Ht3]")%I.
    { wp_apply (wp_thread1 γ γ1 γ2 γ3 with "[Ht1 Hl]"); last done.
      iFrame; iFrame "#". }
    { wp_apply (wp_thread2 γ γ1 γ2 γ3 with "[Ht2 Ht3]"); last done.
      iFrame. iFrame "#". }
    iIntros (? ? [-> ->]).
    iApply "HΦ"; done.
  Qed.

End proof.
