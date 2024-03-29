(* This file defines some basic types that will be used in the operational semantics *)
From stdpp Require Import countable fin vector gmap.
From Coq Require Import ssreflect Bool Eqdep_dec ZArith.
From machine_utils Require Export finz.

Open Scope general_if_scope.

Notation reg_count := 31.
Notation word_size := 2000000%Z.
Notation page_size := 1000%Z.
Notation page_count := 2000%Z.
Notation imm_size := 1000000%Z.
(*define these numbers as notation so that we don't need to unfold them before lia. *)

(* word_size must be a multiple of page_size *)
Lemma page_size_sanity : Z.mul page_size page_count = word_size.
Proof.
  by compute.
Qed.

(* word is a positive integer with word_size as the upper bound *)
Notation Word := (finz word_size).

Notation Addr := Word.

(** page identifier *)
(* TODO: page_id or PGID would be better *)
(* we introduce PID as there will be some operations on pagetables *)
Inductive PID: Type :=
| P (z : Addr) (align: (Z.rem z page_size =? 0)%Z = true).

Definition of_pid (p: PID): Word :=
  match p with
  | P a _ => a
  end.

Coercion of_pid: PID >-> Word.

Definition to_pid (w: Addr): option PID.
  Proof.
  destruct (Z_eq_dec (Z.rem w page_size) 0%Z).
  - apply (Z.eqb_eq (Z.rem w page_size) 0%Z) in e.
    exact (Some (P w e)).
  - exact None.
Defined.

Lemma pid_spec p :
  ((Z.rem (of_pid p) page_size) = 0)%Z.
Proof.
  destruct p. cbn. rewrite -> Z.eqb_eq in align.
  lia.
Qed.

Lemma of_pid_eq p1 p2 :
  of_pid p1 = of_pid p2 →
  p1 = p2.
Proof.
  destruct p1, p2; cbn. intros ->.
  repeat f_equal; apply eq_proofs_unicity; decide equality.
Qed.

Lemma to_of_pid p:  (to_pid (of_pid p))= Some p.
  Proof.
   generalize (pid_spec p); intros ?.
  set (w := (of_pid p)) in *.
  unfold to_pid.
  destruct (Z_eq_dec (Z.rem w page_size) 0%Z) eqn:?.
  { f_equal. apply of_pid_eq. cbn. done. }
  all: lia.
Qed.

(* this conversion is always successful *)
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
lia.
apply Z.div_pos.
lia.
lia.
lia.
Qed.
Next Obligation.
intros.
subst wr.
simpl.
subst z.
unfold Z.divide.
apply Z.eqb_eq.
apply Z.rem_divide.
lia.
exists (w / page_size)%Z.
lia.
Defined.

Notation tpa := to_pid_aligned.

Global Instance pid_eq_dec: EqDecision PID.
intros x y.
destruct x,y .
destruct (finz_eq_dec z z0).
- left. subst z0. f_equal. apply eq_proofs_unicity; decide equality; decide equality.
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
  apply to_of_pid.
Defined.


(* Immediate numbers will only be used in some instructions,
   it is needed to make sure Word is countable *)
Inductive Imm: Type :=
| I (w : Word) (fin: Z.ltb w imm_size = true) .

Definition of_imm (im: Imm): Word :=
  match im with
  | I w fin => w
  end.

Coercion of_imm: Imm >-> Word.

Global Instance imm_eq_dec: EqDecision Imm.
intros x y. destruct x,y.
destruct (finz_eq_dec w w0).
- left. subst w0. f_equal. apply eq_proofs_unicity; decide equality.
- right. inversion 1. contradiction.
Defined.


(** There are 31 general purpose registers and three system registers PC NZ *)
(* TODO: three? *)
Inductive reg_name : Type :=
(* program counter *)
| PC
(* TODO: ??? *)
| NZ
| R (n : nat) (fin : n < reg_count).

Global Instance eq_decision_reg_name : EqDecision reg_name.
Proof.
  intros x y. destruct x as [| |n fin], y as [| | n' fin']; try (by left); try (by right).
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
                               | PC => inl 0
                               | NZ => inl 1
                               | R n fin => inr n
                               end;
            decode n := match (decode n) with
                        | Some (inl 0) => Some PC
                        | Some (inl 1) => Some NZ
                        | Some (inl _) => None
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

(* if a VM ownes a page *)
Inductive ownership : Type :=
| Owned
| NotOwned.

Global Instance eq_decision_ownership : EqDecision ownership.
Proof.
  solve_decision.
Qed.

(** by the FF-A specs ("Arm Firmware Framework for Armv8-A"), a VM has the following three ways to share memory *)
Inductive transaction_type : Type :=
| Donation
| Sharing
| Lending.


Global Instance eq_decision_transaction_type : EqDecision transaction_type.
Proof.
  solve_decision.
Qed.

(* only essential regular instructions are included *)
(* Halt and Fail are introduced to model termination and exception *)
(* Hvc is "hypervisor call" (aka. "hypercall"), to invoke FF-A calls *)
(* TODO: label arguments so that a reader can understand what each does! *)
Inductive instruction : Type :=
| Nop
| Mov (dst : reg_name) (src : Imm + reg_name)
| Ldr (dst : reg_name) (src : reg_name)
| Str (src : reg_name) (dst : reg_name)
| Cmp (arg1 : reg_name) (arg2 : Imm + reg_name)
| Add (op1 : reg_name) (op2 : reg_name)
| Sub (op1 : reg_name) (op2 : reg_name)
| Mult (op1 : reg_name) (op2 : Imm)
| Bne (arg : reg_name)
| Br (arg : reg_name)
| Halt
| Fail
| Hvc.

(* these conditions describe a valid instruction *)
Definition is_general_reg (r : reg_name) : Prop :=
  PC ≠ r /\ NZ ≠ r.

Notation reg_valid_cond := is_general_reg.

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
| valid_add src dst : reg_valid_cond dst ->
                      reg_valid_cond src ->
                      dst ≠ src ->
                      valid_instruction (Add src dst)
| valid_sub src dst : reg_valid_cond dst ->
                      reg_valid_cond src ->
                      dst ≠ src ->
                      valid_instruction (Sub src dst)
| valid_mult src dst : reg_valid_cond dst ->
                      valid_instruction (Mult dst src)
| valid_bne r : reg_valid_cond r ->
                valid_instruction (Bne r)
| valid_br r : reg_valid_cond r ->
                valid_instruction (Br r)
| valid_nop : valid_instruction Nop.


(* the decoding instruction is always valid,
so that we can avoid considering the invalid instruction exceptions  *)
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

Section hyp_config.
(* there are only fixed number of VMs in the machine *)

Class HypervisorConstants := {
  vm_count : nat;
  vm_count_pos : 0 < vm_count;
  valid_handles : gset Word;
}.

End hyp_config.

Section hyp_def.
Context `{_: HypervisorConstants}.

(** All the FF-A hypercalls that we support *)
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
| Wait
| Poll.

Inductive hvc_ret_code : Type :=
  Error
| Succ.

Inductive hvc_error : Type :=
  InvParam
| Denied
| Busy
| Ready
| NoMem.

Definition VMID: Type := fin vm_count.

Class HypervisorParameters := {
  decode_vmid : Word -> option VMID;
  encode_vmid : VMID -> Imm;
  decode_encode_vmid : forall (vmid : VMID),
      decode_vmid (encode_vmid vmid) = Some vmid;
  decode_hvc_func : Word -> option hvc_func;
  encode_hvc_func : hvc_func -> Imm;
  (* we use Imm here because it will be more convenient to write programs.. *)
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
      decode_transaction_type (encode_transaction_type ty) = Some ty;
}.

End hyp_def.
