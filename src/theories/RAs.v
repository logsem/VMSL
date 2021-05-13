From iris.base_logic.lib Require Import gen_heap.
From iris.algebra Require Import auth agree dfrac csum excl gmap gmap_view gset.


Section RA.
  (* Context{A V W R P F:Type} `{Countable A, Countable V, Countable W, Countable R, Countable P}. *)

  Class gen_VMPreG (A V W R P F: Type) (Σ:gFunctors) `{Countable A, Countable V, Countable W, Countable R, Countable P} := {
                      gen_num_preG_inG :> inG Σ (agreeR natO);
                      gen_mem_preG_inG :> gen_heapPreG A W Σ;
                      gen_reg_preG_inG :> gen_heapPreG (R * V) W Σ;
                      gen_tx_preG_inG :> inG Σ (authR (gmapUR V (agreeR (leibnizO P))));
                      gen_rx_preG_inG :> inG Σ (prodR (authR (gmapUR V (agreeR (leibnizO P)))) (optionR (gmap_viewR V (prodO boolO (prodO natO (leibnizO V))))));
                      gen_owned_preG_inG :> inG Σ (authR (gset_disjUR P));
                      gen_access_preG_inG :> inG Σ (authR (gmapUR P (prodR dfracR (csumR (agreeR unitO) (exclR unitO)))));
                      gen_trans_preG_inG :> gen_heapPreG W (V * W* W*(gmap V (gset P))*F) Σ;
                      gen_retri_preG_inG :> inG Σ (authR (gmapUR W (gset_disjR (leibnizO V))))
                   }.


 Class gen_VMG(A V W R P F: Type) Σ `{Countable A, Countable V, Countable W, Countable R, Countable P}  := GenVMG{
                      gen_VM_inG :> gen_VMPreG A V W R P F Σ;
                      gen_num_name : gname;
                      gen_mem_name : gname;
                      gen_reg_name : gname;
                      gen_tx_name : gname;
                      gen_rx_name : gname;
                      gen_owned_name : gname;
                      gen_access_name : gname;
                      gen_trans_name : gname;
                      gen_retri_name : gname
                    }.


Global Arguments GenVMG A V W R P F Σ {_ _ _ _ _ _ _ _ _ _ _ } _ _ _ _ _ _ _ _ _.
Global Arguments gen_num_name {A V W R P F Σ _ _ _ _ _ _ _ _ _ _ } _.
Global Arguments gen_mem_name {A V W R P F Σ _ _ _ _ _ _ _ _ _ _ } _.
Global Arguments gen_reg_name {A V W R P F Σ _ _ _ _ _ _ _ _ _ _ } _.
Global Arguments gen_rx_name {A V W R P F Σ _ _ _ _ _ _ _ _ _ _ } _.
Global Arguments gen_tx_name {A V W R P F Σ _ _ _ _ _ _ _ _ _ _ } _.
Global Arguments gen_owned_name {A V W R P F Σ _ _ _ _ _ _ _ _ _ _ } _.
Global Arguments gen_access_name {A V W R P F Σ _ _ _ _ _ _ _ _ _ _ } _.
Global Arguments gen_trans_name {A V W R P F Σ _ _ _ _ _ _ _ _ _ _ } _.
Global Arguments gen_retri_name {A V W R P F Σ _ _ _ _ _ _ _ _ _ _ } _.

Definition gen_VMΣ (A V W R P F: Type) `{Countable A, Countable V, Countable W, Countable R, Countable P} : gFunctors :=
  #[
      GFunctor (agreeR natO);
      gen_heapΣ A W;
      gen_heapΣ (R * V) W;
      GFunctor (authR (gmapUR V (agreeR (leibnizO P))))
      GFunctor (prodR (authR (gmapUR V (agreeR (leibnizO P)))) (optionR (gmap_viewR V (prodO boolO (prodO natO (leibnizO V))))));
      GFunctor (authR (gset_disjUR P));
      GFunctor (authR (gmapUR P (prodR dfracR (csumR (agreeR unitO) (exclR unitO)))));
      gen_heapΣ W (V * W * W * (gmap V (gset P)) *F);
      GFunctor (authR (gmapUR W (gset_disjR (leibnizO V))))
   ].

Global Instance subG_gen_VMPreG {Σ A V W R P F} `{Countable A, Countable V, Countable W, Countable R, Countable P}:
  subG (gen_VMΣ A V W R P F) Σ -> gen_VMPreG A V W R P F Σ.
Proof. solve_inG.
