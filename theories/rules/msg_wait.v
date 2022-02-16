From machine_program_logic.program_logic Require Import weakestpre.
From HypVeri Require Import lifting rules.rules_base.
From HypVeri.algebra Require Import base reg mem pagetable mailbox.
From HypVeri.lang Require Import lang_extra reg_extra current_extra.
Require Import stdpp.fin.

Section msg_wait.
Context `{hypparams: HypervisorParameters}.
Context `{vmG: !gen_VMG Σ}.

Lemma msg_wait_filled {E i w1 r0 r1 r2 q s l j p_tx} ai:
  tpa ai ∈ s ->
  tpa ai ≠ p_tx ->
  decode_instruction w1 = Some Hvc ->
  decode_hvc_func r0 = Some Wait ->
  {SS{{▷ (PC @@ i ->r ai)
          ∗ ▷ (ai ->a w1)
          ∗ ▷ (TX@i := p_tx)
          ∗ ▷ (i -@{q}A> s )
          ∗ ▷ (R0 @@ i ->r r0)
          ∗ ▷ (R1 @@ i ->r r1)
          ∗ ▷ (R2 @@ i ->r r2)
          ∗ ▷ (RX_state@ i := Some (l, j))}}}
    ExecI @ i ;E
    {{{ RET (false, ExecI); PC @@ i ->r (ai ^+ 1)%f
                     ∗ ai ->a w1
                     ∗ TX@i := p_tx
                     ∗ i -@{q}A> s
                     ∗ R0 @@ i ->r r0
                     ∗ R1 @@ i ->r l
                     ∗ R2 @@ i ->r (encode_vmid j)
                     ∗ RX_state@ i := None}}}.
Proof.
Admitted.

Lemma msg_wait_empty {E i w1 r0 q q' s r0' r1' p_tx P Q R'} ai R P':
  tpa ai ∈ s ->
  tpa ai ≠ p_tx ->
  decode_instruction w1 = Some Hvc ->
  decode_hvc_func r0 = Some Wait ->
  let T' := (PC @@ i ->r (ai ^+ 1)%f
                     ∗ R0 @@ i ->r r0
                     ∗ ai ->a w1
                     ∗ i -@{q}A> s
                     ∗ TX@i := p_tx
                     ∗ RX_state{q'}@ i := None
                     ∗ R0 @@ V0 ->r (encode_hvc_func Wait)
                     ∗ R1 @@ V0 ->r (encode_vmid i))%I in
  {SS{{▷ (VMProp V0 Q (1/2)%Qp) ∗
          ▷ (VMProp i P 1%Qp) ∗
          ▷ (PC @@ i ->r ai) ∗
          ▷ (R0 @@ i ->r r0) ∗
          ▷ (ai ->a w1) ∗
          ▷ (i -@{q}A> s) ∗
          ▷ (TX@i := p_tx) ∗
          ▷ (RX_state{q'}@ i := None) ∗
          ▷ (R0 @@ V0 ->r r0') ∗
          ▷ (R1 @@ V0 ->r r1') ∗
          ▷ (T' ∗ R ∗ VMProp i P' (1/2)%Qp -∗ (Q ∗ R')) ∗
          ▷ R}}}
    ExecI @ i ;E
    {{{ RET (true,ExecI); R' ∗ VMProp i P' 1%Qp}}}.
Proof.
Admitted.

End msg_wait.
