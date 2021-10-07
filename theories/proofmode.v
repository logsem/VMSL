From HypVeri.algebra Require Import base.
From machine_utils Require Export tactics.
From HypVeri Require Export solve_pure.

(* Extend [iFrameAuto] by registering instances for the
   [FramableMachineResource] class. *)


Class FramableRegisterPointsto `{HypervisorConstants} (r: reg_name) (i: VMID) (w: Addr) := {}.
#[export] Hint Mode FramableRegisterPointsto + + + - : typeclass_instances.

Class FramableMemoryPointsto (a: Addr) (w: Addr) := {}.
#[export] Hint Mode FramableMemoryPointsto + - : typeclass_instances.

Class FramablePageTablePointsto `{HypervisorConstants} (i: VMID) (s: gset PID) := {}.
#[export] Hint Mode FramablePageTablePointsto + + - : typeclass_instances.

Class FramableTXPointsto `{HypervisorConstants} (i: VMID) (p: PID) := {}.
#[export] Hint Mode FramableTXPointsto + + - : typeclass_instances.

Class FramableRXPointsto `{HypervisorConstants} (i: VMID) (p: PID) := {}.
#[export] Hint Mode FramableRXPointsto + + - : typeclass_instances.

Class FramableHandlePool (s: gset handle) := {}.
#[export] Hint Mode FramableHandlePool - : typeclass_instances.

Instance FramableRegisterPointsto_default `{HypervisorConstants} r i w :
  FramableRegisterPointsto r i w
| 100. Qed.

Instance FramableMemoryPointsto_default a w :
  FramableMemoryPointsto a w
| 100. Qed.

Instance FramablePageTablePointsto_default `{HypervisorConstants} i s :
  FramablePageTablePointsto i s
| 100. Qed.

Instance FramableTXPointsto_default `{HypervisorConstants} i p :
  FramableTXPointsto i p
| 100. Qed.

Instance FramableRXPointsto_default `{HypervisorConstants} i p :
  FramableRXPointsto i p
| 100. Qed.

Instance FramableMachineResource_reg `{gen_VMG Σ} r i w :
  FramableRegisterPointsto r i w →
  FramableMachineResource (r @@ i ->r w).
Qed.

Instance FramableMachineResource_mem `{gen_VMG Σ} a w :
  FramableMemoryPointsto a w →
  FramableMachineResource (a ->a w).
Qed.

Instance FramableMachineResource_own `{gen_VMG Σ} i q s :
  FramablePageTablePointsto i s →
  FramableMachineResource (O@i :={q}[s]).
Qed.

Instance FramableMachineResource_access `{gen_VMG Σ} i q s :
  FramablePageTablePointsto i s →
  FramableMachineResource (A@i :={q}[s]).
Qed.

Instance FramableMachineResource_excl `{gen_VMG Σ} i q s :
  FramablePageTablePointsto i s →
  FramableMachineResource (E@i :={q}[s]).
Qed.

Instance FramableMachineResource_TX `{gen_VMG Σ} i p :
  FramableTXPointsto i p →
  FramableMachineResource (TX@i := p).
Qed.

Instance FramableMachineResource_RX `{gen_VMG Σ} i p :
  FramableRXPointsto i p →
  FramableMachineResource (RX@i := p).
Qed.

Instance FramableMachineResource_hp`{gen_VMG Σ} q s :
  FramableHandlePool s →
  FramableMachineResource (hp{q}[s]).
Qed.
