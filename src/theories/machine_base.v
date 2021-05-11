From stdpp Require Import countable fin.
From Coq Require Import ssreflect Bool Eqdep_dec.
From ExtLib Require Import Structures.Monads.

Open Scope general_if_scope.

(* TODO: ZArith seems to be much more convenient *)
(*
Class MachineParameters := {
  WordUpperBound : nat;
  WordHasAtLeastTwoValues : 1 < WordUpperBound;
  RegCountUpperBound : nat;
  RegCountAtLeastOne : 0 < RegCountUpperBound;
  AddressSpaceSize : nat;
                          }.

Context `(MachineParams : MachineParameters).
 *)

Definition WordUpperBound := 65536.
Definition RegCountUpperBound := 32.
Definition AddressSpaceSize := 512.

Definition Word : Type :=
  fin WordUpperBound.

Instance eqDecisionWord : EqDecision Word.
Proof.
  solve_decision.
Qed.

Instance countableWord : Countable Word.
Proof.
  refine {| encode := _;
            decode := _;
            decode_encode := _ |}.
  apply fin_countable.
Qed.

Inductive RegName : Type :=
| PC
| NZ
| R (n : nat) (fin : n < RegCountUpperBound).

Instance eqDecisionRegName : EqDecision RegName.
Proof.
  intros x y. destruct x as [| | n fin], y as [| | n' fin']; try (by left); try (by right).
  destruct (nat_eq_dec n n').
  - subst n'; left; f_equal; apply proof_irrel.
  - right; congruence.
Qed.

Program Definition n_to_regname (n : nat) : option RegName :=
  if (nat_lt_dec n RegCountUpperBound) then Some (R n _) else None.
Next Obligation.
  auto.
Defined.

Instance countableRegName : Countable RegName.
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
  destruct (nat_lt_dec n RegCountUpperBound).
  - do 2 f_equal; apply proof_irrel.
  - exfalso; auto.
Qed.

Inductive Ownership : Type :=
| Owned
| NotOwned.

Instance eqDecisionOwnership : EqDecision Ownership.
Proof.
  solve_decision.
Qed.

Inductive Access : Type :=
| NoAccess
| SharedAccess
| ExclusiveAccess.

Instance eqDecisionAccess : EqDecision Access.
Proof.
  solve_decision.
Qed.

Definition Perm : Type :=
  (Ownership * Access).

Definition isAccessible (p : Perm) : bool :=
  match p with
  | (_, SharedAccess) => true
  | (_, ExclusiveAccess) => true
  | _ => false
  end.

Definition isOwned (p : Perm) : bool :=
  match p with
  | (Owned, _) => true
  | _ => false
  end.

Instance eqDecisionPerm : EqDecision Perm.
Proof.
  solve_decision.
Qed.

Inductive TransactionType : Type :=
| Donation
| Sharing
| Lending.

Instance eqDecisionTransactionType : EqDecision TransactionType.
Proof.
  solve_decision.
Qed.

Inductive Instruction : Type :=
| Mov (dst : RegName) (src : Word + RegName)
| Ldr (dst : RegName) (src : RegName)
| Str (src : RegName) (dst : RegName)
| Cmp (arg1 : RegName) (arg2 : Word + RegName)
| Jnz (arg : RegName)
| Jmp (arg : RegName)
| Halt
| Fail
| Hvc.

Class InstructionSerialization := {
  DecodeInstr : Word -> option Instruction;
  EncodeInstr : Instruction -> Word;
  DecodeEncodeInstr : forall (i : Instruction), DecodeInstr (EncodeInstr i) = Some i;
                                 }.

Context `(InstrSer : InstructionSerialization).

Instance eqDecisionInstruction : EqDecision Instruction.
Proof.
  solve_decision.
Qed.

Instance countableInstruction : Countable Instruction.
Proof.
  refine {| encode := fun i => encode (EncodeInstr i);
            decode := fun p => match decode p with
                               | None => None
                               | Some p' => DecodeInstr p'
                               end;
            decode_encode := _ |}.
  intros x.
  rewrite decode_encode.
  apply DecodeEncodeInstr.
Qed.

Definition Addr : Type :=
  fin AddressSpaceSize.

Instance eqDecisionAddr : EqDecision Addr.
Proof.
  solve_decision.
Qed.

Instance countableAddr : Countable Addr.
Proof.
  refine {| encode := _;
            decode := _;
            decode_encode := _ |}.
  apply fin_countable.
Qed.

Inductive HvcFunc : Type :=
  Run
| Yield
| Share
| Lend 
| Donate
| Retrieve
| Relinquish
| Reclaim
| Send 
| Receive
| Wait.

Inductive HvcError : Type :=
  InvParam
| Denied
| Busy
| Ready.

Class HypervisorParameters := {
  VMCount : nat;
  VMCountPos : 0 < VMCount;
  DecodeVMID : Word -> option (fin VMCount);
  EncodeVMID : (fin VMCount)  -> Word;
  DecodeEncodeVMID : forall (vmid : fin VMCount),
      DecodeVMID (EncodeVMID vmid) = Some vmid;
  DecodeHvcFunc : Word -> option HvcFunc;
  EncodeHvcFunc : HvcFunc -> Word;
  DecodeEncodeHvcFunc : forall (hvc : HvcFunc),
      DecodeHvcFunc (EncodeHvcFunc hvc) = Some hvc;
                             }.
