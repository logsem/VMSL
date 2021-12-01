From iris.proofmode Require Import tactics.
From machine_program_logic.program_logic Require Import weakestpre.
From HypVeri.lang Require Import lang.
From HypVeri.algebra Require Import base.
From iris.base_logic Require Export invariants na_invariants saved_prop.
From HypVeri.rules Require Import rules_base.
Import uPred.


(**  unary logical relation *)
Section logrel.
  Context `{hypconst:HypervisorConstants}.
  Context `{hypparams:!HypervisorParameters}.
  Context `{vmG: !gen_VMG Σ}.

  Notation V := ((leibnizO VMID) -n> page_table -n> iPropO Σ).
  Notation E := ((leibnizO VMID) -n> iPropO Σ).
  Implicit Types i : (leibnizO VMID).
  Implicit Types interp_expr : (E).

  Program Definition interp_execute: E :=
   λne (i: leibnizO VMID), (⌜ fin_to_nat i ≠ 0 ⌝ -∗ (VMProp_holds i (1/2)%Qp -∗ WP ExecI @ i {{(λ _, True )}}))%I.


  End logrel.
