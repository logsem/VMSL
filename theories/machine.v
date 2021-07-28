From stdpp Require Import countable fin vector.
From Coq Require Import ssreflect Bool Eqdep_dec ZArith.
From ExtLib Require Import Structures.Monads.
From machine_utils Require Export finz.

Open Scope general_if_scope.

Definition reg_count : nat := 31.
Definition word_size : Z := 2000000. (*TODO: Now a word is 64-bit long, how should I change this? *)
Definition page_size : Z := 1000.
Definition page_count : Z := 2000.
Definition imm_size : Z := 1000000.
Lemma page_size_sanity : Z.mul page_size page_count = word_size.
Proof.
  unfold page_size.
  unfold page_count.
  unfold word_size.
  by compute.
Qed.

Notation Word := (finz word_size).

Notation Addr := Word.

Inductive PID: Type :=
| P (z : Addr) (align: (Z.rem z page_size = 0)%Z) .

Definition of_pid (p: PID): Word :=
  match p with
  | P a _ => a
  end.

Coercion of_pid: PID >-> Word.

Program Definition to_pid (w: Addr): option PID :=
  match (decide ((Z.rem w page_size) = 0)%Z) with
                | left H => Some (P w H)
                | right _ => None
  end.

(* don't know how to prove it *)
(* Lemma to_of_pid p:  (to_pid (of_pid p))= Some p. *)
(*   Proof. *)
(*     destruct p. *)
(*     rewrite /to_pid /of_pid //=. *)
(*     unfold Is_true in align. *)
(*     destruct (decide ((z `rem` page_size)%Z =? 0)%Z). *)
(*     repeat f_equal. *)
(*     unfold Is_true in i. *)
(*     destruct (decide ((z `rem` page_size)%Z = 0)%Z). *)
(*     apply Z.eqb_eq in e. *)
(*     inversion align. *)
(*     rewrite e in i,align. *)
(*     rewrite Z.eqb_eq in align. *)
(*     unfold Is_true. *)
(*     assert (Hdecide: (left align) = bool_decide ((z `rem` page_size)%Z = 0%Z)). *)
(*     destruct align. *)
(*     (* destruct (decide ((z `rem` page_size)%Z = (z `rem` page_size)%Z)). *) *)
(*     (* destruct e. *) *)
(*     unfold decide. *)
(*     unfold decide_rel. *)
(*     case (Z_eq_dec (z `rem` page_size)%Z (z `rem` page_size)%Z). *)
(*     intro. *)
(*     Check eq_refl. *)
(*     unfold Z.eq_dec. *)
(*     unfold Z_eq_dec. *)
(*     constructor. *)
(*     rewrite X. *)
(*     by exists (P z e). *)
(*     lia. *)
(* Qed. *)

Program Definition to_pid_aligned (w: Word): PID:=
  let z:=(page_size * (w / page_size) )%Z in
  let wr:= (finz.FinZ z _ _) in
  P wr _.
Next Obligation.
intros.
destruct w.
pose finz_lt.
apply -> (Z.ltb_lt z0 word_size ) in e.
apply  (Z.ltb_lt z word_size ).
subst z.
simpl.
apply -> (Z.leb_le 0 z0 ) in finz_nonneg.
assert (Hlt' : ( page_size * (z0 / page_size)  <= z0)%Z).
apply Z_mult_div_ge.
unfold page_size.
lia.
lia.
Defined.
Next Obligation.
intros.
destruct w.
subst z.
simpl.
apply -> (Z.leb_le 0 z0) in finz_nonneg.
apply Z.leb_le .
assert (Hlt' : (0 <= (z0 / page_size) * page_size )%Z).
apply Zmult_gt_0_le_0_compat.
unfold page_size.
lia.
apply Z.div_pos.
lia.
unfold page_size.
lia.
lia.
Qed.
Next Obligation.
intros.
subst wr.
simpl.
subst z.
unfold Z.divide.
apply Z.rem_divide.
unfold page_size.
lia.
exists (w / page_size)%Z.
lia.
Defined.

(* Program Definition to_pid_aligned (w: Word): PID:= *)
(*   let z:=(w - (w `mod` page_size))%Z in *)
(*   let wr:= (finz.FinZ z _ _) in *)
(*   P wr _. *)
(* Next Obligation. *)
(* intros. *)
(* destruct w. *)
(* pose finz_lt. *)
(* apply -> (Z.ltb_lt z0 word_size ) in e. *)
(* apply  (Z.ltb_lt z word_size ). *)
(* subst z. *)
(* simpl. *)
(* apply -> (Z.leb_le 0 z0 ) in finz_nonneg. *)
(* assert (Hrem': (0 ≤ z0 `mod` page_size)%Z). *)
(* apply Z_mod_pos. *)
(* unfold page_size. *)
(* lia. *)
(* lia. *)
(* Defined. *)
(* Next Obligation. *)
(* intros. *)
(* destruct w. *)
(* subst z. *)
(* simpl. *)
(* apply -> (Z.leb_le 0 z0) in finz_nonneg. *)
(* apply Z.leb_le . *)
(* assert (Hlt: (z0 `mod` page_size ≤ z0)%Z). *)
(* apply Z.mod_le;eauto. *)
(* unfold page_size. *)
(* lia. *)
(* lia. *)
(* Qed. *)
(* Next Obligation. *)
(* intros. *)
(* subst wr. *)
(* simpl. *)
(* subst z. *)
(* apply Z.eqb_eq. *)
(* rewrite <- Zminus_mod_idemp_l. *)
(* simpl. *)
(* assert (Heq0: (w mod page_size - w mod page_size)%Z = 0%Z). *)
(* apply (Zminus_diag (w mod page_size)%Z). *)
(* rewrite Heq0. *)
(* apply Zmod_0_l. *)
(* Defined. *)


Inductive Imm: Type :=
| I (w : Word) (fin: Z.ltb w imm_size = true) .

Definition of_imm (im: Imm): Word :=
  match im with
  | I w fin => w
  end.

Coercion of_imm: Imm >-> Word.

Global Instance pid_eq_dec: EqDecision PID.
intros x y.
destruct x,y .
destruct (finz_eq_dec word_size z z0).
- left. subst z0. f_equal. apply eq_proofs_unicity; decide equality; decide equality.
- right. inversion 1. contradiction.
Defined.

Global Instance imm_eq_dec: EqDecision Imm.
intros x y. destruct x,y.
destruct (finz_eq_dec word_size w w0).
- left. subst w0. f_equal. apply eq_proofs_unicity; decide equality.
- right. inversion 1. contradiction.
Defined.


Global Instance pid_countable : Countable PID.
Proof.
  refine {| encode r := encode (of_pid r) ;
            decode n := match (decode n) with
                        | Some w => to_pid w
                        | None => None
                        end ;
            decode_encode := _ |}.
  intro r. destruct r; auto.
  rewrite decode_encode.
  unfold to_pid. simpl.
  destruct (decide ((z `rem` page_size)%Z=0%Z)).
  - repeat f_equal; apply eq_proofs_unicity; decide equality; decide equality.
  - exfalso. done.
Defined.

Inductive reg_name : Type :=
| PC
| NZ
| R (n : nat) (fin : n < reg_count).

Global Instance eq_decision_reg_name : EqDecision reg_name.
Proof.
  intros x y. destruct x as [| | n fin], y as [| | n' fin']; try (by left); try (by right).
  destruct (nat_eq_dec n n').
  - subst n'; left; f_equal; apply proof_irrel.
  - right; congruence.
Qed.

Program Definition n_to_regname (n : nat) : option reg_name :=
  if (nat_lt_dec n reg_count) then Some (R n _) else None.
Next Obligation.
  auto.
Defined.

Global Instance countable_reg_name : Countable reg_name.
Proof.
  refine {| encode r := encode match r with
                               | PC => inl false
                               | NZ => inl true
                               | R n fin => inr n
                               end;
            decode n := match (decode n) with
                        | Some (inl false) => Some PC
                        | Some (inl true) => Some NZ
                        | Some (inr n) => n_to_regname n
                        | None => None
                        end;
            decode_encode := _ |}.
  intro r. destruct r; auto.
  rewrite decode_encode.
  unfold n_to_regname.
  destruct (nat_lt_dec n reg_count).
  - do 2 f_equal; apply proof_irrel.
  - exfalso; auto.
Qed.

Inductive ownership : Type :=
| Owned
| NotOwned.

Global Instance eq_decision_ownership : EqDecision ownership.
Proof.
  solve_decision.
Qed.

Inductive access : Type :=
| NoAccess
| SharedAccess
| ExclusiveAccess.

Global Instance eq_decision_access : EqDecision access.
Proof.
  solve_decision.
Qed.

Definition permission : Type :=
  (ownership * access).

Definition is_accessible (p : permission) : bool :=
  match p with
  | (_, SharedAccess) => true
  | (_, ExclusiveAccess) => true
  | _ => false
  end.

Definition is_exclusive (p : permission) : bool :=
  match p with
  | (_, ExclusiveAccess) => true
  | _ => false
  end.

Definition is_owned (p : permission) : bool :=
  match p with
  | (Owned, _) => true
  | _ => false
  end.

Global Instance eq_decision_permission : EqDecision permission.
Proof.
  solve_decision.
Qed.

Inductive transaction_type : Type :=
| Donation
| Sharing
| Lending.

Global Instance eq_decision_transaction_type : EqDecision transaction_type.
Proof.
  solve_decision.
Qed.

Inductive instruction : Type :=
| Mov (dst : reg_name) (src : Imm + reg_name)
| Ldr (dst : reg_name) (src : reg_name)
| Str (src : reg_name) (dst : reg_name)
| Cmp (arg1 : reg_name) (arg2 : Imm + reg_name)
| Bne (arg : reg_name)
| Br (arg : reg_name)
| Halt
| Fail
| Hvc.

Definition reg_valid_cond (r : reg_name) : Prop :=
  PC ≠ r /\ NZ ≠ r.

Inductive valid_instruction : instruction -> Prop :=
| valid_mov_imm imm dst : reg_valid_cond dst ->
                          valid_instruction (Mov dst (inl imm))
| valid_mov_reg  src dst : reg_valid_cond dst ->
                          reg_valid_cond src ->
                          dst ≠ src ->
                          valid_instruction (Mov dst (inr src))
| valid_ldr src dst : reg_valid_cond dst ->
                      reg_valid_cond src ->
                      dst ≠ src ->
                      valid_instruction (Ldr dst src)
| valid_str src dst : reg_valid_cond dst ->
                      reg_valid_cond src ->
                      dst ≠ src ->
                      valid_instruction (Str dst src)
| valid_cmp_imm imm dst : reg_valid_cond dst ->
                      valid_instruction (Cmp dst (inl imm))
| valid_cmp_reg src dst : reg_valid_cond dst ->
                      reg_valid_cond src ->
                      dst ≠ src ->
                      valid_instruction (Cmp dst (inr src))
| valid_bne r : reg_valid_cond r ->
                valid_instruction (Bne r)
| valid_br r : reg_valid_cond r ->
                valid_instruction (Br r).

Class InstructionSerialization := {
  decode_instruction : Word -> option instruction;
  decode_instruction_valid : forall w i, decode_instruction w = Some i -> valid_instruction i;
  encode_instruction : instruction -> Word;
  decode_encode_instruction : forall (i : instruction), decode_instruction (encode_instruction i) = Some i;
                                 }.

Context `{InstrSer : InstructionSerialization}.

Instance eq_decision_instruction : EqDecision instruction.
Proof.
  solve_decision.
Qed.

Instance countable_instruction : Countable instruction.
Proof.
  refine {| encode := fun i => encode (encode_instruction i);
            decode := fun p => match decode p with
                               | None => None
                               | Some p' => decode_instruction p'
                               end;
            decode_encode := _ |}.
  intros x.
  rewrite decode_encode.
  apply decode_encode_instruction.
Qed.

(* TODO: ZArith seems to be much more convenient *)

Class HypervisorConstants := {
  vm_count : nat;
  vm_count_pos : 0 < vm_count;
 }.

Section hyp_def.
Context `{_: HypervisorConstants}.

Inductive hvc_func : Type :=
  Run
| Yield
| Share
| Lend
| Donate
| Retrieve
| Relinquish
| Reclaim
| Send
| Wait.

Inductive hvc_ret_code : Type :=
  Error
| Succ.

Inductive hvc_error : Type :=
  InvParam
| Denied
| Busy
| Ready
| NoMem.

Definition VMID : Type := fin vm_count.

Class HypervisorParameters := {
  decode_vmid : Word -> option VMID;
  encode_vmid : VMID -> Imm;
  decode_encode_vmid : forall (vmid : VMID),
      decode_vmid (encode_vmid vmid) = Some vmid;
  decode_hvc_func : Word -> option hvc_func;
  encode_hvc_func : hvc_func -> Imm;
  (* we use Imm because it is more convenient to write programs.. *)
  decode_encode_hvc_func : forall (hvc : hvc_func),
      decode_hvc_func (encode_hvc_func hvc) = Some hvc;
  decode_hvc_error : Word -> option hvc_error;
  encode_hvc_error : hvc_error -> Imm;
  decode_encode_hvc_error : forall (hvc : hvc_error),
      decode_hvc_error (encode_hvc_error hvc) = Some hvc;
  decode_hvc_ret_code : Word -> option hvc_ret_code;
  encode_hvc_ret_code : hvc_ret_code -> Imm;
  decode_encode_hvc_ret_code : forall (hvc : hvc_ret_code),
      decode_hvc_ret_code (encode_hvc_ret_code hvc) = Some hvc;
  decode_transaction_type : Word -> option transaction_type;
  encode_transaction_type : transaction_type -> Word;
  decode_encode_transaction_type : forall (ty : transaction_type),
      decode_transaction_type (encode_transaction_type ty) = Some ty
                                                                }.
End hyp_def.
