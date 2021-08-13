From machine_program_logic.program_logic Require Import machine weakestpre adequacy.
From HypVeri Require Import reg_addr RAs lifting.
From HypVeri.examples Require Import run_yield_1.
From iris.proofmode Require Import tactics.

Section Adequacy.

  Context `{gen_VMG Σ}.


  Lemma run_yield_1_adequacy' (σ σ': state)  (ms ms': list exec_mode):
    (* TODO: we need some assumptions here to be able to allocate resources *)
    (* with these resources, we apply the specification and get the wptp *)
    (* along with some other stuff, then it should be enough to apply the adequacy theorem *)
    rtc machine.step (ms, σ) (ms, σ') →
    (* what should be the φ ? *)
    True.
  Proof.
  Admitted.

End Adequacy.
