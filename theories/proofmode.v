From HypVeri.algebra Require Import base.
From machine_utils Require Export tactics.
From HypVeri Require Export solve_pure.

(* Extend [iFrameAuto] by registering instances for the
   [FramableMachineResource] class. *)


Class FramableRegisterPointsto `{HypervisorConstants} (r: reg_name) (i: VMID) (w: Addr) := {}.
#[export] Hint Mode FramableRegisterPointsto + + + - : typeclass_instances.

Class FramableMemoryPointsto (a: Addr) (w: Addr) := {}.
#[export] Hint Mode FramableMemoryPointsto + - : typeclass_instances.

Class FramableOwnershipPointsto `{HypervisorConstants} (p : PID) (v: VMID) := {}.
#[export] Hint Mode FramableOwnershipPointsto + - - : typeclass_instances.

Class FramableAccessPointsto `{HypervisorConstants} (v : VMID) (q:frac) (s: gset PID) := {}.
#[export] Hint Mode FramableAccessPointsto + - - - : typeclass_instances.

Class FramableTXPointsto `{HypervisorConstants} (i: VMID) (p: PID) := {}.
#[export] Hint Mode FramableTXPointsto + + - : typeclass_instances.

Class FramableRXPointsto `{HypervisorConstants} (i: VMID) (p: PID) := {}.
#[export] Hint Mode FramableRXPointsto + + - : typeclass_instances.

Class FramableWordPool (s: gset Word) := {}.
#[export] Hint Mode FramableWordPool - : typeclass_instances.

Class FramableTransaction `{HypervisorConstants} (wh : Word) (q: Qp) (meta: meta_info) := {}.
#[export] Hint Mode FramableTransaction + + - - : typeclass_instances.

Class FramableRetrieve (wh : Word) (q: Qp) (b : bool)  := {}.
#[export] Hint Mode FramableRetrieve + - - : typeclass_instances.

Class FramableRXStatePointsto `{HypervisorConstants} (i : VMID) (q: Qp) (o : option (Word * VMID))  := {}.
#[export] Hint Mode FramableRXStatePointsto + + - - : typeclass_instances.

Instance FramableRegisterPointsto_default `{HypervisorConstants} r i w :
  FramableRegisterPointsto r i w
| 100. Qed.

Instance FramableMemoryPointsto_default a w :
  FramableMemoryPointsto a w
| 100. Qed.

Instance FramableOwnershipPointsto_default `{HypervisorConstants} p v :
  FramableOwnershipPointsto p v
| 100. Qed.

Instance FramableAccessPointsto_default `{HypervisorConstants} p q s :
  FramableAccessPointsto p q s
| 100. Qed.

Instance FramableTXPointsto_default `{HypervisorConstants} i p :
  FramableTXPointsto i p
| 100. Qed.

Instance FramableRXPointsto_default `{HypervisorConstants} i p :
  FramableRXPointsto i p
| 100. Qed.

Instance FramableWordPool_default `{HypervisorConstants} s :
  FramableWordPool s
| 100. Qed.

Instance FramableTransaction_default `{HypervisorConstants} wh q meta :
  FramableTransaction wh q meta
| 100. Qed.

Instance FramableRetrieve_default wh q b:
  FramableRetrieve wh q b
| 100. Qed.

Instance FramableRXStatePointsto_default `{HypervisorConstants} i q o:
  FramableRXStatePointsto i q o
| 100. Qed.

Instance FramableMachineResource_reg `{gen_VMG Σ} r i w :
  FramableRegisterPointsto r i w →
  FramableMachineResource (r @@ i ->r w).
Qed.

Instance FramableMachineResource_mem `{gen_VMG Σ} a w :
  FramableMemoryPointsto a w →
  FramableMachineResource (a ->a w).
Qed.

Instance FramableMachineResource_own `{gen_VMG Σ} p v:
  FramableOwnershipPointsto p v →
  FramableMachineResource (p -@O> v).
Qed.

Instance FramableMachineResource_access `{gen_VMG Σ} p q s :
  FramableAccessPointsto p q s →
  FramableMachineResource (p -@{q}A> s).
Qed.

Instance FramableMachineResource_TX `{gen_VMG Σ} i p :
  FramableTXPointsto i p →
  FramableMachineResource (TX@i := p).
Qed.

Instance FramableMachineResource_RX `{gen_VMG Σ} i p :
  FramableRXPointsto i p →
  FramableMachineResource (RX@i := p).
Qed.

Instance FramableMachineResource_RXstate `{gen_VMG Σ} i q o :
  FramableRXStatePointsto i q o →
  FramableMachineResource (RX_state{q}@i := o).
Qed.

Instance FramableMachineResource_hp`{gen_VMG Σ} s :
  FramableWordPool s →
  FramableMachineResource (hp [s]).
Qed.

Instance FramableMachineResource_trans`{gen_VMG Σ} wh q meta :
  FramableTransaction wh q meta →
  FramableMachineResource (wh-{q}>t meta).
Qed.

Instance FramableMachineResource_retri `{gen_VMG Σ} wh q b:
  FramableRetrieve wh q b →
  FramableMachineResource (wh-{q}>re b).
Qed.
