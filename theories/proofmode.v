From HypVeri.algebra Require Import base.
From machine_utils Require Export tactics.
From HypVeri Require Export solve_pure.

(* Extend [iFrameAuto] by registering instances for the
   [FramableMachineResource] class. *)

Class FramableRegisterPointsto (r: reg_name) (i: VMID) (w: Addr) := {}.
#[export] Hint Mode FramableRegisterPointsto + + - : typeclass_instances.

Class FramableMemoryPointsto (a: Addr) (w: Addr) := {}.
#[export] Hint Mode FramableMemoryPointsto + - : typeclass_instances.

Class FramableAccessPointsto (i: VMID) (s: gset PID) := {}.
#[export] Hint Mode FramableAccessPointsto + - : typeclass_instances.

Class FramableTXPointsto (i: VMID) (p: PID) := {}.
#[export] Hint Mode FramableTXPointsto + - : typeclass_instances.

Class FramableRXPointsto (i: VMID) (p: PID) := {}.
#[export] Hint Mode FramableRXPointsto + - : typeclass_instances.

Instance FramableRegisterPointsto_default r i w :
  FramableRegisterPointsto r i w
| 100. Qed.

Instance FramableMemoryPointsto_default a w :
  FramableMemoryPointsto a w
| 100. Qed.

Instance FramableAccessPointsto_default i s :
  FramableAccessPointsto i s
| 100. Qed.

Instance FramableTXPointsto_default i p :
  FramableTXPointsto i p
| 100. Qed.

Instance FramableRXPointsto_default i p :
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

Instance FramableMachineResource_access `{gen_VMG Σ} i q s :
  FramableAccessPointsto i s →
  FramableMachineResource (A@i :={q}[s]).
Qed.

Instance FramableMachineResource_TX `{gen_VMG Σ} i p :
  FramableTXPointsto i p →
  FramableMachineResource (TX@i := p).
Qed.

Instance FramableMachineResource_RX `{gen_VMG Σ} i p :
  FramableRXPointsto i p →
  FramableMachineResource (RX@i := p).
Qed.
