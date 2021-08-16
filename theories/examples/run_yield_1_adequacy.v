From machine_program_logic.program_logic Require Import machine weakestpre adequacy.
From HypVeri Require Import reg_addr RAs lifting.
From HypVeri.examples Require Import run_yield_1.
From iris.proofmode Require Import tactics.
From iris.base_logic Require Import invariants na_invariants.
From iris.bi Require Import big_op.

Section Adequacy.
  Context (Σ: gFunctors).
  Context {inv_preG : invGS Σ}.
  Context {nainv_preG : na_invG Σ}.
  Context {vm_preG: gen_VMPreG Addr VMID Word reg_name PID transaction_type Σ}.
  Context {tokG: tokG Σ}.

  (* exec_mode of all VMs *)
  Definition run_vms (ms: list exec_mode) (z i: VMID):=
    ms !! (fin_to_nat i) = Some ExecI ∧
    ms !! (fin_to_nat z) = Some ExecI ∧
    ∀ v , (v ≠ z ∧ v ≠ i -> ms !! (fin_to_nat v) = Some HaltI).

  Definition mk_region (p:PID) (ws: list Word) : gmap Addr Word:=
    (list_to_map (zip (finz.seq (of_pid p) (length ws)) ws)).

  Definition mem_layout (σ :state) (z i: VMID) (p1 p2: PID) :=
      (∃ a, is_accessible a= true ∧ (get_vm_page_table σ z).2 !! p1 = Some a) ∧
      (∃ a, is_accessible a= true ∧ (get_vm_page_table σ i).2 !! p2 = Some a) ∧
      (mk_region p1 (program1 i)) ∪ (mk_region p2 program2) ⊆ (get_mem σ).

  Definition reg (σ: state) (z i: VMID) (p1 p2: PID):=
    (∃ r0 r1 ,{[PC := (of_pid p1); R0 := r0; R1 := r1]} ⊆ (get_reg_files σ)!!!z) ∧
    ∃ r0 ,{[PC := (of_pid p2); R0 := r0]} ⊆ (get_reg_files σ) !!! i .

  Definition is_initial_config (σ: state) (ms: list exec_mode):=
    ∃ (z i:VMID), (fin_to_nat z) = 0 ∧ i ≠ z ∧
                  (get_current_vm σ) = z ∧
    ∃ (p1 p2: PID), p1 ≠ p2 ∧
                  (run_vms ms z i) ∧
                  (mem_layout σ z i p1 p2) ∧
                  (reg σ z i p1 p2).

  (*TODO: prove these two *)
      (* seq_in_page (of_pid p1) (length (program1 i)) p1 -> *)
      (* seq_in_page (of_pid p2) (length program2) p2 *)

  Lemma run_yield_1_adequacy' (σ σ': state)  (ms ms': list exec_mode):
    (* we need assumptions to be able to allocate resources *)
    (* with these resources, we apply the specification and get the wptp *)
    (* along with some other stuff, then it should be enough to apply the adequacy theorem *)
    (is_initial_config σ ms) ->
    rtc machine.step (ms, σ) (ms', σ') →
    (* φ : vm 0 is scheduled but halted *)
    ((* scheduled σ' z ∧ *)  ms' !! 0 = Some HaltI).
  Proof.
    intros Hinit Hstep.
    pose proof (wp_invariance Σ hyp_machine ms σ ms' σ') as WPI;cbn in WPI.
    apply WPI. 2: assumption.
    clear WPI.
    intro Hinv.

    destruct Hinit as (z & i & Heqz & Hneq & Hcur & Hinit).
    iMod (@na_alloc Σ nainv_preG) as (logrel_nais) "Hna".


    (* pose proof (@run_yield_1_spec Σ vmG tokG nroot z i). *)

    iIntros.

    (*  init state_interp(auth+frag) + na_inv with iMod *)

    (* pose vmG Σ *)
    (* pose spec *)

    (* use assumptions to extract resources *)
    (* for mem: sepM -> sepL2 *)

    (* instantiate spec with resources and obtain a WP *)

    (* apply adequacy theorem *)
  Admitted.

End Adequacy.
