From iris.program_logic Require Export weakestpre.
From iris.heap_lang Require Export notation lang.
From iris.proofmode Require Export tactics.
From iris.heap_lang Require Import proofmode.
From iris.base_logic.lib Require Export invariants.
From iris.algebra Require Import numbers excl auth csum frac.



Section code.

  Definition wait : val := rec: "wait" "l" "v" :=  if: (!"l" ≠ "v") then ("wait" "l" "v") else #().

  Definition thread1: val := λ: "l" "lw" , let: "l'" := ref #42 in
                                             (* resolve_proph: "p" to: "l'";; *)
                                             "l" <- "l'";;
                                             "lw" <- #1;;
                                             (wait "lw" #2);;
                                             !"l'".

  Definition thread2: val := λ: "l" "lw", (wait "lw" #1);;
                                          FAA (!"l") #2;;
                                          "lw" <- #2.

  Definition example: val := λ: <>, let: "lw" := ref #0 in
                                    let: "l" := ref #0 in
                                    (* let: "p" := NewProph in *)
                                    (Fork (thread2 "l" "lw"));;
                                    (thread1 "l" "lw" ).

End code.

Class prophG Σ := {
  oneshotG :> inG Σ (csumR (exclR unitO) (agreeR locO));
  exclG :> inG Σ (exclR unitO);
}.



Context `{!heapG Σ, !prophG Σ}.

Section spec.


Definition example_spec := {{{True}}} example #() {{{v, RET v; True }}}.
Definition wait_spec l (v w: nat):= {{{l ↦ #w }}} wait #l #v {{{k, RET k; l↦ #v}}}.

End spec.

Section proof.

(* Lemma wait_proof l v w: wait_spec l v w. *)
(*   Proof. *)
(*     iIntros (Φ) "Hl Post". *)
(*     iLöb as "IH". *)
(*     wp_lam. *)
(*     wp_pures. *)
(*     wp_load. *)
(*     wp_binop. *)
(*    case_bool_decide. *)
(*    - wp_unop. *)
(*      wp_pures. *)
(*      iModIntro. *)
(*      destruct H. *)
(*      iApply "Post". *)
(*      done. *)
(*    - wp_unop. *)
(*      wp_pures. *)
(*      iApply ("IH" with "Hl Post"). *)
(*   Qed. *)


Definition allocated (γ : gname) : iProp Σ := own γ (Excl ())%I.

Definition pending (γ: gname) : iProp Σ := own γ (Cinl (Excl ()))%I.

Definition shot (γ: gname) (l:loc) : iProp Σ := own γ (Cinr (to_agree l))%I.

Lemma allocated_exclusive (γ : gname) : allocated γ   -∗  allocated γ -∗ False.
  Proof.
    iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as %[].
  Qed.

Lemma pending_exclusive γ l  : pending γ -∗ shot γ l -∗ False.
  Proof.
    iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as %[].
Qed.

Lemma shot_agree (γ : gname) (l1 l2: loc): shot γ l1 -∗ shot γ l2 -∗ ⌜ l1 = l2 ⌝.
Proof.
  iIntros "H1 H2".
  iDestruct (own_valid_2 with "H1 H2") as %?%to_agree_op_inv_L.
  done.
Qed.

Lemma pending_shot γ l :
  pending γ ==∗ shot γ l.
Proof.
  iIntros "Hγ". iMod (own_update with "Hγ") as "$"; last done.
  by apply cmra_update_exclusive with (y:=(Cinr (to_agree l))).
Qed.

Lemma shot_duplicate γ l :
   shot γ l -∗ (shot γ l ∗ shot γ l).
Proof.
  iIntros "Hγ". rewrite -own_op.
 rewrite -Cinr_op.
 rewrite agree_idemp.
 done.
Qed.


Definition isEven (n:Z) : Prop :=Z.even n.

Lemma isEven_isEven n: isEven n -> isEven (n + 2).
Proof.
  unfold isEven.
  intro.
  rewrite <- (Z.even_succ_succ n) in H.
  simpl.
  rewrite (Z.add_comm n 2).
  assert (H' : (Z.succ (Z.succ n)) = (Z.add 2%Z n)).
  eauto.
  lia.
  rewrite <- H'.
  done.
Qed.

Lemma isEven_42 : isEven 42.
Proof.
  unfold isEven.
  Search Z.even.
  rewrite (Z.even_add_mul_2 0 21).
  done.
Qed.

Definition inv (γ0 γ1: gname) (l lw : loc) : iProp Σ :=
  (∃ v, l ↦ #v ∗ lw ↦ #0 ∗ pending γ1 )∨
       (∃ (l':loc) (v:Z), l ↦ #l' ∗ shot γ1 l' ∗ l' ↦ #v ∗ ⌜ isEven v  ⌝∗ (lw ↦ #1 ∨ lw↦ #0 ∨ lw ↦ #2) ∗ allocated γ0 )%I.
Let N := nroot .@ "proph".

Lemma example_proof : example_spec.
  Proof.
   iIntros (Φ) "_ Post".
   wp_lam.
   wp_alloc lw as "Hlw".
   wp_pures.
   wp_alloc l as "Hl".
   wp_pures.
   (* wp_apply wp_new_proph; first done. *)
   (* iIntros (vs p) "Hp". *)
   (* wp_pures. *)
   iMod (own_alloc (Excl ())) as (γ0) "Hexcl".
   { done. }
   iMod (own_alloc (Cinl (Excl ()))) as (γ1) "Hshot".
   { done. }
   iMod (inv_alloc N _ (inv γ0 γ1 l lw) with "[-Post Hexcl]") as "#Hinv".
   {iNext.  iLeft. iExists 0. iFrame.}
   wp_bind (Fork _).
   iApply wp_fork.
   - iNext.
     wp_lam.
     wp_pures.
     iLöb as "IH".
    wp_rec.
    wp_let.
    wp_bind (Load _).
    iInv N as  "[> Hleft| >Hright]" "Close".
    + iDestruct "Hleft" as (v) "(Hl & Hlw & Hpending)".
      wp_load.
      iMod ("Close" with "[-]") as "_".
      {iNext. iLeft. iExists v. iFrame. }
      iModIntro.
      wp_pures.
      iApply "IH".
    + iDestruct "Hright" as (l' v) "(Hl & Hshot & Hl' & Heven & [Hlw1 | Hlw2] & Hallocated)".
      * wp_load.
        iDestruct (shot_duplicate with "Hshot") as "[Hshot1 Hshot2]".
        iMod ("Close" with "[- Hshot2] ") as "_".
        {iNext. iRight. iExists l', v. iFrame. }
        iModIntro.
        wp_pures.
        wp_bind (Load _).
        iInv N as  "[> HLeft| >Hright]" "Close".
        -- iDestruct "HLeft" as (?) "(_ & _ & Hpending)".
           iDestruct (pending_exclusive with "Hpending Hshot2") as %[].
        -- iDestruct "Hright" as (l'' ?) "(Hl & Hshot1 & Hl' & Heven & ?)".
           iDestruct (shot_agree with "Hshot1 Hshot2") as %->.
           wp_load.
           iMod ("Close" with "[- Hshot2] ") as "_".
           {iNext. iRight. iExists l', v0. iFrame. }
           clear v0.
           iModIntro.
           wp_bind (FAA _ _).
           iInv N as  "[> Hleft| >Hright]" "Close".
           ++ iDestruct "Hleft" as (?) "(_ & _ & Hpending)".
           iDestruct (pending_exclusive with "Hpending Hshot2") as %[].
           ++ iDestruct "Hright" as (l'' v') "(Hl & Hshot1 & Hl' & Heven & ?)".
              iDestruct (shot_agree with "Hshot1 Hshot2") as %->.
              wp_faa.
              iMod ("Close" with "[- Hshot2] ") as "_".
              {iNext. iRight.  iExists l',  (v'+2)%Z. iFrame.
               iDestruct "Heven" as %Heven. 
               iPureIntro.
               apply isEven_isEven.
               done. }
              iModIntro.
              wp_seq.
              clear v'.
              iInv N as  "[> Hleft| >Hright]" "Close".
              ** iDestruct "Hleft" as (?) "(_ & _ & Hpending)".
                 iDestruct (pending_exclusive with "Hpending Hshot2") as %[].
              **  iDestruct "Hright" as (l'' v') "(? & ? & ? & ? & [Hlw1 | [Hlw0 |Hlw2]] & ? )";
                    wp_store;
                  iMod ("Close" with "[- Hshot2] ") as "_"; try(iNext; iRight; iExists l'', v'; iFrame);iModIntro;done.
      *  iDestruct "Hlw2" as "[Hlw0| Hlw2]";wp_load;
        iMod ("Close" with "[-] ") as "_";
        try(iNext; iRight; iExists l' ,v; iFrame);
        iModIntro;
        wp_pures;
        iApply "IH".
  - iNext.
    wp_seq.
    wp_lam.
    wp_pures.
    wp_alloc l' as "Hl'".
    wp_let.
    wp_bind (Store _ _).
    iInv N as  "[> Hleft| >Hright]" "Close".
    + iDestruct "Hleft" as (?) "(Hl & Hlw & Hpending)".
      wp_store.
      iDestruct (pending_shot _ l'  with "Hpending") as ">Hshot".
      iDestruct (shot_duplicate with "Hshot") as "[Hshot1 Hshot2]".
      iMod ("Close" with "[- Hshot2 Post] ") as "_".
      {iNext. iRight. iExists l', 42%Z. iFrame. }
      iModIntro.
      wp_seq.
      wp_bind (Store _ _).
      iInv N as  "[> Hleft| >Hright]" "Close".
      * iDestruct "Hleft" as (?) "(_ & _ & Hpending)".
        iDestruct (pending_exclusive with "Hpending Hshot2") as %[].
      * iDestruct "Hright" as (l'' v') "(? & ? & ? & ? & [Hlw1 | [Hlw0 |Hlw2]] & ? )";
                    wp_store;
                  iMod ("Close" with "[- Hshot2 Post] ") as "_"; try(iNext; iRight; iExists l'', v'; iFrame);iModIntro;wp_seq.
        iLöb as "IH".
        wp_lam.
        wp_pures.
        wp_bind (Load #lw ).
        iInv N as  "[> Hleft| >Hright]" "Close".
        -- iDestruct "Hleft" as (?) "(_ & _ & Hpending)".
          iDestruct (pending_exclusive with "Hpending Hshot2") as %[].
        -- iDestruct "Hright" as (l''' v'') "(? & ? & ? & ? & [Hlw1 | [Hlw0 |Hlw2]] & ? )";wp_load;
         iMod ("Close" with "[- Hshot2 Post] ") as "_";try (iNext; iRight; iExists l''', v''; iFrame);iModIntro;
         try(wp_pures;  iApply ("IH" with "Hshot2 Post")).
           wp_pures.
           iInv N as  "[> Hleft| >Hright]" "Close".
           ++ iDestruct "Hleft" as (?) "(_ & _ & Hpending)".
        iDestruct (pending_exclusive with "Hpending Hshot2") as %[].
          ++ iDestruct "Hright" as (l'''' v''') "(? & Hshot1 & Hl' & ? & ? & ? )".
             iDestruct (shot_agree with "Hshot1 Hshot2") as %->.
             wp_load.
             iMod ("Close" with "[- Post Hshot2] ") as "_";try (iNext; iRight; iExists l', v'''; iFrame).
             iModIntro. iApply "Post". done.
        -- iLöb as "IH".
        wp_lam.
        wp_pures.
        wp_bind (Load #lw ).
        iInv N as  "[> Hleft| >Hright]" "Close".
           ++ iDestruct "Hleft" as (?) "(_ & _ & Hpending)".
          iDestruct (pending_exclusive with "Hpending Hshot2") as %[].
           ++ iDestruct "Hright" as (l''' v'') "(? & ? & ? & ? & [Hlw1 | [Hlw0 |Hlw2]] & ? )";wp_load;
              iMod ("Close" with "[- Hshot2 Post] ") as "_";try (iNext; iRight; iExists l''', v''; iFrame);iModIntro;
              try(wp_pures;  iApply ("IH" with "Hshot2 Post")).
              wp_pures.
              iInv N as  "[> Hleft| >Hright]" "Close".
           ** iDestruct "Hleft" as (?) "(_ & _ & Hpending)".
              iDestruct (pending_exclusive with "Hpending Hshot2") as %[].
           ** iDestruct "Hright" as (l'''' v''') "(? & Hshot1 & Hl' & ? & ? & ? )".
              iDestruct (shot_agree with "Hshot1 Hshot2") as %->.
              wp_load.
              iMod ("Close" with "[- Post Hshot2] ") as "_";try (iNext; iRight; iExists l', v'''; iFrame).
              iModIntro. iApply "Post". done.
        -- iLöb as "IH".
        wp_lam.
        wp_pures.
        wp_bind (Load #lw ).
        iInv N as  "[> Hleft| >Hright]" "Close".
           ++ iDestruct "Hleft" as (?) "(_ & _ & Hpending)".
          iDestruct (pending_exclusive with "Hpending Hshot2") as %[].
           ++ iDestruct "Hright" as (l''' v'') "(? & ? & ? & ? & [Hlw1 | [Hlw0 |Hlw2]] & ? )";wp_load;
              iMod ("Close" with "[- Hshot2 Post] ") as "_";try (iNext; iRight; iExists l''', v''; iFrame);iModIntro;
              try(wp_pures;  iApply ("IH" with "Hshot2 Post")).
              wp_pures.
              iInv N as  "[> Hleft| >Hright]" "Close".
           ** iDestruct "Hleft" as (?) "(_ & _ & Hpending)".
              iDestruct (pending_exclusive with "Hpending Hshot2") as %[].
           ** iDestruct "Hright" as (l'''' v''') "(? & Hshot1 & Hl' & ? & ? & ? )".
              iDestruct (shot_agree with "Hshot1 Hshot2") as %->.
              wp_load.
              iMod ("Close" with "[- Post Hshot2] ") as "_";try (iNext; iRight; iExists l', v'''; iFrame).
              iModIntro. iApply "Post". done.
    + iDestruct "Hright" as (? ?) "(? & ? & ? & ?& ? & Hexcl2)".
      iDestruct (allocated_exclusive with "Hexcl Hexcl2") as %[].
Qed.
