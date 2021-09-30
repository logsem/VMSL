From machine_program_logic.program_logic Require Import weakestpre.
From HypVeri.algebra Require Import base.
From HypVeri.rules Require Import rules_base mov halt run yield.
From HypVeri.lang Require Import lang_extra reg_extra mem_extra pagetable_extra trans_extra.
From HypVeri.algebra Require Import base mem reg pagetable mailbox trans.
From HypVeri.examples Require Import instr.

Section Lend1.
  Context `{vmG: !gen_VMG Σ}.
  
  Definition program1 (p : PID) (p' : Imm) (peq : of_pid p = p') (l : Imm) (v : Imm) : list Word := encode_instructions
    [
    (* store the page address to R1 *)
    (* tx -> memory descriptor *des*
       R3 -> address of a handle in *des* *)
    Mov R1 (inl p');
    (* store the initial value to R0 *)
    (* tx -> memory descriptor *des*
       R3 -> address of a handle in *des*
       R1 -> p *)
    Mov R0 (inl v);
    (* write v to p *)
    (* tx -> memory descriptor *des*
       R3 -> address of a handle in *des*
       R1 -> p
       R0 -> v *)
    Str R1 R0;
    (* tx is populated with memory descriptor
       lend initiation *)
    (* tx -> memory descriptor *des*
       R3 -> address of a handle in *des*
       R1 -> p
       R0 -> v 
       p -> v *)
    Mov R0 (inl (encode_hvc_func Lend));
    (* tx -> memory descriptor *des*
       R3 -> address of a handle in *des*
       R1 -> p
       R0 -> Lend 
       p -> v *)
    Hvc;
    (* R3 is populated with address of handle in the memory descriptor
       Lend returns a new handle in R2
       write h to memory descriptor *)
    (* tx -> memory descriptor *des*
       R3 -> address of a handle in *des*
       R1 -> p
       R0 -> Succ
       p -> v
       R2 -> h
       h ->  transaction entry *)
    Str R3 R2;
    (* send tx to VM1 *)
    (* tx -> memory descriptor *des* with h
       R3 -> address of a handle in *des*
       R1 -> p
       R0 -> Succ
       p -> v
       R2 -> h
       h ->  transaction entry *)
    Mov R0 (inl (encode_hvc_func Send));
    Mov R1 (inl I1);
    Mov R2 (inl l);
    Hvc;
    (* run VM1 *)
    (* tx -> memory descriptor *des* with h
       R3 -> address of a handle in *des*
       R1 -> 1
       R0 -> Succ
       p -> v
       R2 -> l
       h ->  transaction entry *)
    Mov R0 (inl (encode_hvc_func Run));
    Hvc;
    (* store the handle to R1 *)
    (* tx -> memory descriptor *des* with h
       R3 -> address of a handle in *des*
       R1 -> 1
       R0 -> Run
       p -> v'
       R2 -> l
       h ->  transaction entry *)
    Ldr R1 R3;
    (* reclaim *)
    Mov R0 (inl (encode_hvc_func Reclaim));
    Hvc;
    (* load the first word from the page to R1 *)
    (* tx -> memory descriptor *des* with h
       R3 -> address of a handle in *des*
       R1 -> h
       R0 -> Succ
       p -> v'
       R2 -> l *)
    Mov R1 (inl p');
    Ldr R0 R1;
    (* stop *)
    (* tx -> memory descriptor *des* with h
       R3 -> address of a handle in *des*
       R1 -> p
       R0 -> v'
       p -> v'
       R2 -> l *)
    Halt
    ].

  Definition program2 (l : Imm) (b : Imm) (progpage : PID) (beq : of_imm b = ((of_pid progpage) ^+ 3)%f) (p : PID) (p' : Imm) (peq : of_pid p = of_imm p') (v : Imm) (src dst : PID) (src' dst' : Imm) (srceq : of_imm src' = of_pid src) (dsteq : of_imm dst' = of_pid dst) : list Word := encode_instructions
    [
    (* loop init *)
    Mov R5 (inl l);
    Mov R6 (inl I0);
    Mov R7 (inl b);

    (* copy word from rx + l to tx + l *)
    Mov R0 I1;
    Mov R1 (inl src');
    Add R1 R5;
    Sub R1 R0;
    Ldr R2 R1;
    Mov R1 (inl dst');
    Add R1 R5;
    Sub R1 R5;
    Str R1 R2;

    (* loop end *)
    Mov R8 (inl I1);
    Sub R5 R8;
    Cmp R6 (inr R5);
    Bne R7;

    (* tx -> descriptor
       h -> transaction entry
       h -> not taken *)
    Mov R0 (inl (encode_hvc_func Retrieve));
    Mov R1 (inl l);
    Hvc;
    (* tx -> descriptor
       h -> transaction entry
       h -> taken *)
    (* store a new value *)
    Mov R1 (inl p');
    Mov R0 (inl v);
    Str R1 R0;
    (* tx -> descriptor
       h -> transaction entry
       h -> taken
       p -> v' *)
    (* prepare a new retrieve descriptor [h, 0] *)
    (* copy h from rx + 1 to tx + 0 *)
    Mov R1 (inl src');
    Mov R0 (inl I1);
    Add R1 R0;
    Ldr R0 R1;
    Mov R1 (inl dst');
    Str R1 R0;
    
    Mov R0 (inl (encode_hvc_func Relinquish));
    Hvc;
    Mov R0 (inl (encode_hvc_func Yield));
    Hvc
    ].

  Context (VM0 VM1 : VMID).

  Definition machine0_spec {sacc q sh}
             (ppage progpage ptx0 : PID)
             (p p' p'' : Imm)
             (peq : of_pid ppage = p)
             (l : Imm)
             (des des' : list Word)
             (des_eq : des = serialized_transaction_descriptor VM0 VM1 W0 I1 [ppage] W0)
             (l_eq : Z.to_nat (finz.to_z (of_imm l)) = length des)
             (addrp : addr_in_page p ppage)
             (seq_eq : seq_in_page (of_pid progpage) (length (program1 ppage p peq l p')) progpage)
             (progpage_in : progpage ∈ sacc)
             (ptx0_in : ptx0 ∈ sacc)
             (ppage_in : ppage ∈ sacc)
             (shp : sh ≠ ∅)
    : iProp Σ :=
    {PAR{{
    PC @@ VM0 ->r (of_pid progpage)
    ∗ hp{ 1 }[ sh ]                     
    ∗ A@VM0 :={q}[sacc]                     
    ∗ TX@ VM0 := ptx0
    ∗ mem_region des ptx0
    ∗ R3 @@ VM0 ->r ((of_pid ptx0) ^+ 2)%f
    ∗ (∃ r0, R0 @@ VM0 ->r r0)
    ∗ (∃ r1, R1 @@ VM0 ->r r1)
    ∗ (∃ r2, R2 @@ VM0 ->r r2)
    ∗ p ->a p'
    ∗ program (program1 ppage p peq l p') (of_pid progpage)
    }}}
      ExecI @ VM0
      {{{ RET HaltI ;
          PC @@ VM0 ->r (of_pid progpage ^+ (length (program1 ppage p peq l p')))%f
          ∗ hp{ 1 }[ sh ]
          ∗ A@VM0 :={q}[sacc]
          ∗ TX@ VM0 := ptx0
          ∗ ∃ h, ⌜des' = serialized_transaction_descriptor VM0 VM1 h I1 [ppage] W0⌝
          ∗ mem_region des' ptx0                                                      
          ∗ R0 @@ VM0 ->r I1
          ∗ R1 @@ VM0 ->r h
          ∗ R2 @@ VM0 ->r l
          ∗ R3 @@ VM0 ->r ((of_pid ptx0) ^+ 2)%f
          ∗ program (program1 ppage p peq l p') (of_pid progpage)
      }}}.

  Definition machine1_spec {sacc q h des}
             (ppage progpage ptx1 prx1 : PID)
             (ptx1b prx1b : Imm)
             (p p' p'' b : Imm)
             (beq : of_imm b = ((of_pid progpage) ^+ 3)%f)
             (ptx1eq : of_imm ptx1b = of_pid ptx1)
             (prx1eq : of_imm prx1b = of_pid prx1)
             (peq : of_pid ppage = p)
             (l : Imm)
             (addrp : addr_in_page p ppage)
             (seq_eq : seq_in_page (of_pid progpage) (length (program2 l b progpage beq ppage p peq p'' prx1 ptx1 prx1b ptx1b prx1eq ptx1eq)) progpage)
             (progpage_in : progpage ∈ sacc)
             (ptx1_in : ptx1 ∈ sacc)
             (prx1_in : prx1 ∈ sacc)
             (ppage_in : ppage ∈ sacc)
             (des_eq : des = serialized_transaction_descriptor VM0 VM1 h I1 [ppage] W0)
             
    : iProp Σ :=
    {PAR{{
    PC @@ VM1 ->r (of_pid progpage)
    ∗ h ->t{1}(VM0, W0, VM1, [ppage], Lending)
    ∗ h ->re false                    
    ∗ A@VM1 :={q}[sacc]                     
    ∗ TX@ VM1 := ptx1
    ∗ mem_region des ptx1
    ∗ R3 @@ VM1 ->r ((of_pid ptx1) ^+ 2)%f
    ∗ (∃ r0, R0 @@ VM1 ->r r0)
    ∗ (∃ r1, R1 @@ VM1 ->r r1)
    ∗ (∃ r2, R2 @@ VM1 ->r r2)
    ∗ p ->a p'
    ∗ program (program2 l b progpage beq ppage p peq p'' prx1 ptx1 prx1b ptx1b prx1eq ptx1eq) (of_pid progpage)
    }}}
      ExecI @ VM1
      {{{ RET ExecI ;
          PC @@ VM1 ->r (of_pid progpage ^+ (length (program2 l b progpage beq ppage p peq p'' prx1 ptx1 prx1b ptx1b prx1eq ptx1eq)))%f
          ∗ h ->t{1}(VM0, W0, VM1, [ppage], Lending)
          ∗ h ->re false                    
          ∗ A@VM1 :={q}[sacc]
          ∗ TX@ VM1 := ptx1
          ∗ mem_region des ptx1                                                      
          ∗ mem_region des prx1
          ∗ R0 @@ VM1 ->r encode_hvc_ret_code Succ
          ∗ R1 @@ VM1 ->r h
          ∗ R2 @@ VM1 ->r l
          ∗ R3 @@ VM1 ->r ((of_pid ptx1) ^+ 2)%f
          ∗ p ->a p''
          ∗ program (program2 l b progpage beq ppage p peq p'' prx1 ptx1 prx1b ptx1b prx1eq ptx1eq) (of_pid progpage)                      
      }}}.
  
End Lend1.
