From stdpp Require Import countable fin vector.
From Coq Require Import ssreflect Bool Eqdep_dec.
From ExtLib Require Import Structures.Monads.

Open Scope general_if_scope.

Definition reg_count_lower_bound := 30.
Definition word_size_lower_bound := 15. (*TODO: Now a word is 64-bit long, how should I change this? *)
Definition page_size_lower_bound := 15.

(* TODO: ZArith seems to be much more convenient *)
Class MachineParameters := {
  word_size : nat;
  word_size_at_least : word_size_lower_bound < word_size;
  
  reg_count : nat;
  reg_count_at_least : reg_count_lower_bound < reg_count;
  
  page_size : nat; (* in words *)
  page_size_at_least : page_size_lower_bound < page_size;
  
  page_count : nat;
  
  decode_pid : fin word_size -> option (fin page_count);
  encode_pid : fin page_count -> fin word_size;
  decode_encode_pid : forall (pid : fin page_count),
      decode_pid (encode_pid pid) = Some pid;
  
  page_size_sanity : page_size * page_count = word_size;
  
  mm_translation : fin word_size -> fin page_count;
  mm_translation_inv : fin page_count -> vec (fin word_size) page_size;
  mm_translation_mm_translation_inv : forall (addr : fin word_size),
      In addr (mm_translation_inv (mm_translation addr));
  mm_translation_inv_mm_translation : forall (pid : fin page_count),
      Forall (fun x => x = pid) (map mm_translation (mm_translation_inv pid));
  }.

Context `(MachineParams : MachineParameters).

Definition word : Type :=
  fin word_size.

Instance eq_decision_word : EqDecision word.
Proof.
  solve_decision.
Qed.

Instance countable_word : Countable word.
Proof.
  refine {| encode := _;
            decode := _;
            decode_encode := _ |}.
  apply fin_countable.
Qed.

Inductive reg_name : Type :=
| PC
| NZ
| R (n : nat) (fin : n < reg_count).

Instance eq_decision_reg_name : EqDecision reg_name.
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

Instance countable_reg_name : Countable reg_name.
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

Instance eq_decision_ownership : EqDecision ownership.
Proof.
  solve_decision.
Qed.

Inductive access : Type :=
| NoAccess
| SharedAccess
| ExclusiveAccess.

Instance eq_decision_access : EqDecision access.
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

Definition is_owned (p : permission) : bool :=
  match p with
  | (Owned, _) => true
  | _ => false
  end.

Instance eq_decision_permission : EqDecision permission.
Proof.
  solve_decision.
Qed.

Inductive transaction_type : Type :=
| Donation
| Sharing
| Lending.

Instance eq_decision_transaction_type : EqDecision transaction_type.
Proof.
  solve_decision.
Qed.

Inductive instruction : Type :=
| Mov (dst : reg_name) (src : word + reg_name)
| Ldr (dst : reg_name) (src : reg_name)
| Str (src : reg_name) (dst : reg_name)
| Cmp (arg1 : reg_name) (arg2 : word + reg_name)
| Jnz (arg : reg_name)
| Jmp (arg : reg_name)
| Halt
| Fail
| Hvc.

Definition reg_valid_cond (r : reg_name) : Prop :=
  PC ≠ r /\ NZ ≠ r.

(* Definition double_word : Type := *)
  (* (word * word). *)
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
| valid_jnz r : reg_valid_cond r ->
                valid_instruction (Jnz r)
| valid_jmp r : reg_valid_cond r ->
                valid_instruction (Jmp r).

Class InstructionSerialization := {
  decode_instruction : word -> option instruction;
  decode_instruction_valid : forall w i, decode_instruction w = Some i -> valid_instruction i;
  encode_instruction : instruction -> word;
  decode_encode_instruction : forall (i : instruction), decode_instruction (encode_instruction i) = Some i;
                                 }.

Context `(InstrSer : InstructionSerialization).

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

Definition addr : Type := word.

Instance eq_decision_addr : EqDecision addr.
Proof.
  solve_decision.
Qed.

Instance countable_addr : Countable addr.
Proof.
  refine {| encode := _;
            decode := _;
            decode_encode := _ |}.
  apply fin_countable.
Qed.

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

Class HypervisorParameters := {
  vm_count : nat;
  vm_count_pos : 0 < vm_count;
  decode_vmid : word -> option (fin vm_count);
  encode_vmid : (fin vm_count)  -> word;
  decode_encode_vmid : forall (vmid : fin vm_count),
      decode_vmid (encode_vmid vmid) = Some vmid;
  decode_hvc_func : word -> option hvc_func;
  encode_hvc_func : hvc_func -> word;
  decode_encode_hvc_func : forall (hvc : hvc_func),
      decode_hvc_func (encode_hvc_func hvc) = Some hvc;
  decode_hvc_error : word -> option hvc_error;
  encode_hvc_error : hvc_error -> word;
  decode_encode_hvc_error : forall (hvc : hvc_error),
      decode_hvc_error (encode_hvc_error hvc) = Some hvc;
  decode_hvc_ret_code : word -> option hvc_ret_code;
  encode_hvc_ret_code : hvc_ret_code -> word;
  decode_encode_hvc_ret_code : forall (hvc : hvc_ret_code),
      decode_hvc_ret_code (encode_hvc_ret_code hvc) = Some hvc;
  decode_transaction_type : word -> option transaction_type;
  encode_transaction_type : transaction_type -> word;
  decode_encode_transaction_type : forall (ty : transaction_type),
      decode_transaction_type (encode_transaction_type ty) = Some ty
                             }.
