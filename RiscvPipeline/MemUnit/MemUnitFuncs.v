(*
  This module defines the memory unit. This unit accepts a memory
  update packet and performs the requested memory writes.
*)
Require Import Kami.AllNotations.
Require Import ProcKami.FU.
Require Import ProcKami.GenericPipeline.Decoder.
Require Import ProcKami.RiscvPipeline.MemUnit.Pmp.
Require Import ProcKami.RiscvPipeline.MemUnit.PhysicalMem.
Require Import ProcKami.RiscvPipeline.MemUnit.PageTable.
Require Import ProcKami.Debug.DebugDevice.
Require Import List.
Import ListNotations.

Section mem_unit.
  Context `{procParams: ProcParams}.
  Variable ty: Kind -> Type.

  Variable func_units : list (FUEntry ty).

  Variable mem_devices : list MemDevice.

  Variable mem_table : list (MemTableEntry mem_devices).

  Local Definition DeviceTag := (DeviceTag mem_devices).

  Local Definition baseIndex := 3. (* the first available read port available to the page table walker. *)

  Open Scope kami_expr.
  Open Scope kami_action.

  Definition memTranslate
    (index : nat) (* 0 based index specifying which call to the page table walker this is. *)
    (satp_mode : Bit SatpModeWidth @# ty)
    (mode : PrivMode @# ty)
    (mprv : Bool @# ty)
    (access_type : VmAccessType @# ty)
    (vaddr : VAddr @# ty)
    :  ActionT ty (PktWithException PAddr)
    := Read mpp : PrivMode <- @^"mpp";
       Read mxr : Bool <- @^"mxr";
       Read sum : Bool <- @^"sum";
       Read satp_ppn : Bit 44 <- @^"satp_ppn";
       LET effective_mode : PrivMode
         <- IF access_type != $VmAccessInst && mprv
              then #mpp else mode;
       If #effective_mode != $MachineMode && satp_mode != $SatpModeBare
         then
           LETA paddr : PktWithException PAddr
             <- pt_walker
                  mem_table
                  baseIndex
                  index
                  satp_mode
                  #mxr
                  #sum
                  #effective_mode
                  (ppnToPAddr (ZeroExtendTruncLsb 44 #satp_ppn))
                  access_type
                  vaddr;
           Ret #paddr
         else
           Ret (STRUCT {
                    "fst" ::= SignExtendTruncLsb PAddrSz vaddr;
                    "snd" ::= Invalid
                  } : PktWithException PAddr @# ty)
         as result;
       Ret #result.

  Definition memFetch
    (index : nat)
    (satp_mode: Bit SatpModeWidth @# ty)
    (mode : PrivMode @# ty) 
    (vaddr : VAddr @# ty)
    :  ActionT ty (PktWithException CompInst)
    := System [
         DispString _ "[memFetch] fetching vaddr: ";
         DispHex vaddr;
         DispString _ "\n"
       ];
       Read mprv : Bool <- @^"mprv";
       LETA paddr
         :  PktWithException PAddr
         <- memTranslate index satp_mode mode #mprv $VmAccessInst vaddr;
       System [
         DispString _ "[memFetch] paddr: ";
         DispHex #paddr;
         DispString _ "\n"
       ];
       If #paddr @% "snd" @% "valid"
         then
           Ret
             (STRUCT {
                "fst" ::= $0;
                "snd" ::= #paddr @% "snd"
              } : PktWithException CompInst @# ty)
         else
           LETA pmp_result
             :  Pair (Pair DeviceTag PAddr) MemErrorPkt
             <- checkForFault mem_table $VmAccessInst satp_mode mode (#paddr @% "fst") $1 $$false;
           If mem_error (#pmp_result @% "snd")
             then
               LET exception
                 :  Maybe Exception
                 <- Valid ((IF !($$misaligned_access) && #pmp_result @% "snd" @% "misaligned"
                            then $InstAddrMisaligned
                            else $InstAccessFault):
                             Exception @# ty);
               Ret (STRUCT {
                   "fst" ::= $0;
                   "snd" ::= #exception
                 } : PktWithException CompInst @# ty)
             else
               LETA inst
                 :  Maybe Data
                 <- mem_region_read index
                      (#pmp_result @% "fst" @% "fst") 
                      (#pmp_result @% "fst" @% "snd")
                      $1;
               System [
                 DispString _ "[memFetch] fetched upper bits: ";
                 DispHex #inst;
                 DispString _ "\n"
               ];
               (* LET exception *)
               (*   :  FullException *)
               (*   <- STRUCT { *)
               (*        "exception" ::= $InstAccessFault; *)
               (*        "value"     ::= vaddr *)
               (*      } : FullException @# ty; *)
               Ret (STRUCT {
                   "fst" ::= ZeroExtendTruncLsb 16 (#inst @% "data");
                   "snd" ::= Invalid
                     (* ::= IF #inst @% "valid" *)
                     (*       then Invalid *)
                     (*       else Valid #exception *)
                 } : PktWithException CompInst @# ty)
             as result;
           Ret #result
         as result;
       System [
         DispString _ "[memFetch] fetch results: ";
         DispHex #result;
         DispString _ "\n"
       ];
       Ret #result.

  Local Definition mem_unit_exec_pkt
    (memRet : MemRet @# ty)
    (exception : Maybe Exception @# ty)
    :  ActionT ty (PktWithException MemRet)
    := Ret
         (STRUCT {
            "fst" ::= memRet;
            "snd" ::= exception
          } : PktWithException MemRet @# ty).

  Local Definition mem_unit_exec_pkt_def
    (exception : Maybe Exception @# ty)
    :  ActionT ty (PktWithException MemRet)
    := mem_unit_exec_pkt
         $$(getDefaultConst MemRet)
         exception.

  Local Definition mem_unit_exec_pkt_access_fault
    (vaddr : VAddr @# ty)
    (is_write : Bool @# ty)
    :  ActionT ty (PktWithException MemRet)
    := mem_unit_exec_pkt_def
         (Valid ((IF is_write
                   then $SAmoAccessFault
                  else $LoadAccessFault)
                 : Exception @# ty)).

  Definition mem_unit_exec
    (exts : Extensions @# ty)
    (satp_mode: Bit SatpModeWidth @# ty)
    (mode : PrivMode @# ty)
    (mprv : Bool @# ty)
    (addr : VAddr @# ty)
    (func_unit_id : FuncUnitId func_units @# ty)
    (inst_id : InstId func_units @# ty)
    (input_pkt : MemUnitInput @# ty)
    :  ActionT ty (PktWithException MemRet)
    := (* I. does the instruction perform a memory operation? *)
       System [
         DispString _ "[mem_unit_exec] input pkt:\n";
         DispHex input_pkt;
         DispString _ "\n";
         DispString _ "[mem_unit_exec] functional unit ID:\n";
         DispHex func_unit_id;
         DispString _ "\n";
         DispString _ "[mem_unit_exec] inst ID:\n";
         DispHex inst_id;
         DispString _ "\n"
       ];
       LETA mis_op
         :  Maybe Bool
         <- convertLetExprSyntax_ActionT
              (inst_db_get_pkt
                (fun _ _ tagged_inst
                  => let inst := snd tagged_inst in
                     RetE
                       (match optMemParams inst with
                         | Some _ => $$true
                         | None => $$false
                         end))
                func_unit_id
                inst_id);
       If #mis_op @% "data"
         then
           (* II. does the instruction perform a memory write? *)
           LETA mis_write
             :  Maybe Bool
             <- convertLetExprSyntax_ActionT
                  (inst_db_get_pkt
                    (fun _ _ tagged_inst
                      => RetE (if writeMem (instHints (snd tagged_inst)) then $$true else $$false))
                    func_unit_id
                    inst_id);
           LETA msize
             :  Maybe (@MemRqLgSize procParams)
             <-  convertLetExprSyntax_ActionT
                   (inst_db_get_pkt
                     (fun _ _ tagged_inst
                       => RetE
                            (match optMemParams (snd tagged_inst) with
                              | Some params => $(accessSize params)
                              | _ => $0
                              end))
                     func_unit_id
                     inst_id);
           If checkAligned addr (#msize @% "data")
             then
               (* III. get the physical address *)
               LETA mpaddr
                 :  PktWithException PAddr
                 <- memTranslate 2 satp_mode mode mprv
                      (IF #mis_write @% "data"
                        then $VmAccessSAmo
                        else $VmAccessLoad)
                      addr;
               System [
                 DispString _ "[mem_unit_exec] writing to vaddr: ";
                 DispHex addr;
                 DispString _ "\n";
                 DispString _ "[mem_unit_exec] writing to paddr: ";
                 DispHex #mpaddr;
                 DispString _ "\n"
               ];
               If #mpaddr @% "snd" @% "valid"
                 then
                   System [
                     DispString _ "[mem_unit_exec] the page table walker threw an exception\n"
                   ];
                   Ret (STRUCT {
                       "fst" ::= $$(getDefaultConst MemRet);
                       "snd" ::= #mpaddr @% "snd"
                     } : PktWithException MemRet @# ty)
                 else
                   LETA pmp_result
                     :  Pair (Pair DeviceTag PAddr) MemErrorPkt
                     <- checkForFault mem_table
                          (IF #mis_write @% "data"
                            then $VmAccessSAmo
                            else $VmAccessLoad)
                          satp_mode
                          mode
                          (#mpaddr @% "fst")
                          (#msize @% "data")
                          (input_pkt @% "aq" || input_pkt @% "rl");
                   If mem_error (#pmp_result @% "snd")
                     then (* TODO: return misaligned exception if mem error is misaligned. *)
                       System [
                         DispString _ "[mem_unit_exec] the pmp check failed\n"
                       ];
                       LET exception
                         :  Maybe Exception
                         <- Valid (
                              IF !($$misaligned_access) && #pmp_result @% "snd" @% "misaligned"
                              then
                                (IF #mis_write @% "data"
                                 then $SAmoAddrMisaligned
                                 else $LoadAddrMisaligned)
                              else
                                (IF #mis_write @% "data"
                                 then $SAmoAccessFault
                                 else $LoadAccessFault): Exception @# ty);
                       mem_unit_exec_pkt_def #exception
                     else
                       (* IV. read the current value and place reservation *)
                       LETA read_result
                         :  Maybe Data
                         <- mem_region_read 0
                              (#pmp_result @% "fst" @% "fst")
                              (#pmp_result @% "fst" @% "snd")
                              (#msize @% "data");
                       (* If #read_result @% "valid" *)
                       (*   then *)
                           (* TODO: should we place reservations on failed reads? *)
                           LETA read_reservation_result
                             :  Array Rlen_over_8 Bool
                             <- mem_region_read_resv
                                 (#pmp_result @% "fst" @% "fst")
                                 (#pmp_result @% "fst" @% "snd")
                                 (#msize @% "data");
                                 (* #mpaddr @% "fst" *)
                           (* VI. apply the memory transform to compute the write value *)
                           LETA mwrite_value
                             :  Maybe MemoryOutput
                             <- convertLetExprSyntax_ActionT
                                  (inst_db_get_pkt
                                    (fun _ _ tagged_inst
                                      => let inst := snd (tagged_inst) in
                                         match optMemParams inst return MemoryOutput ## ty with
                                           | Some params
                                             => (((memXform params)
                                                  (RetE
                                                    (STRUCT {
                                                      "aq" ::= input_pkt @% "aq" ;
                                                      "rl" ::= input_pkt @% "rl" ;
                                                      "reservation" ::= #read_reservation_result;
                                                      "mem" ::= #read_result @% "data";
                                                      "reg_data" ::= input_pkt @% "reg_data"
                                                     } : MemoryInput @# ty))) : MemoryOutput ## ty)
                                           | None (* impossible case *)
                                             => RetE $$(getDefaultConst MemoryOutput)
                                           end)
                                    func_unit_id
                                    inst_id);
                           LET write_mask
                             :  Array Rlen_over_8 Bool
                             <- #mwrite_value @% "data" @% "mask";
                           If #mwrite_value @% "data" @% "isWr"
                             then
                               (* VII. write to memory. *)
                               LETA write_result
                                 :  Bool
                                 <- mem_region_write 0
                                      (#pmp_result @% "fst" @% "fst")
                                      (#pmp_result @% "fst" @% "snd")
                                      (#mwrite_value @% "data" @% "data" : Data @# ty)
                                      (#write_mask : DataMask @# ty)
                                      (#msize @% "data");
                               Ret
                                 (IF #write_result
                                   then Invalid
                                   else
                                     Valid ($SAmoAccessFault: Exception @# ty))
                             else Ret Invalid
                             as write_result;
                           System [
                             DispString _ "[mem_unit_exec] write result:\n";
                             DispHex #write_result;
                             DispString _ "\n"
                           ];
                           If #mwrite_value @% "data" @% "isLrSc"
                             then
                               mem_region_write_resv
                                 (#pmp_result @% "fst" @% "fst")
                                 (#pmp_result @% "fst" @% "snd")
                                 (#write_mask : DataMask @# ty)
                                 (#mwrite_value @% "data" @% "reservation")
                                 (#msize @% "data");
                                 (* #mpaddr @% "fst" *)
                           LET memRet
                             :  MemRet
                             <- STRUCT {
                                  "writeReg?" ::= #mwrite_value @% "data" @% "reg_data" @% "valid";
                                  "tag"  ::= #mwrite_value @% "data" @% "tag";
                                  "data" ::= #mwrite_value @% "data" @% "reg_data" @% "data"
                                } : MemRet @# ty;
                           mem_unit_exec_pkt #memRet #write_result
                       (*   else mem_unit_exec_pkt_access_fault addr $$false *)
                       (*   as result; *)
                       (* Ret #result *)
                     as result;
                   Ret #result
                 as result;
               Ret #result
             else
               LET exception
                 :  Maybe Exception
                 <- Valid (IF #mis_write @% "data"
                              then if misaligned_access then $SAmoAccessFault else $SAmoAddrMisaligned
                              else if misaligned_access then $LoadAccessFault else $LoadAddrMisaligned: Exception @# ty);
               (mem_unit_exec_pkt_def #exception)
             as result;
           Ret #result
         else
           System [
             DispString _ "[mem_unit_exec] the instruction does not perform an memory operations.\n"
           ];
           (mem_unit_exec_pkt_def Invalid)
         as result;
         System [
           DispString _ "[mem_unit_exec] result:\n";
           DispHex #result;
           DispString _ "\n"
         ];
       Ret #result.

  Definition MemUnit
    (exts : Extensions @# ty)
    (xlen : XlenValue @# ty)
    (satp_mode: Bit SatpModeWidth @# ty)
    (mode : PrivMode @# ty)
    (decoder_pkt : DecoderPkt func_units @# ty)
    (exec_context_pkt : ExecContextPkt @# ty)
    (update_pkt : ExecUpdPkt @# ty)
    (exception : Maybe Exception @# ty)
    :  ActionT ty (PktWithException ExecUpdPkt)
    := bindException update_pkt exception
         (fun update_pkt : ExecUpdPkt @# ty
           => LET memUnitInput
                :  MemUnitInput
                <- STRUCT {
                     "aq"       ::= update_pkt @% "aq";
                     "rl"       ::= update_pkt @% "rl";
                     "reg_data" ::= exec_context_pkt @% "reg2"
                     } : MemUnitInput @# ty;
              Read mprv : Bool <- @^"mprv";
              LETA memRet
                :  PktWithException MemRet
                <- mem_unit_exec
                     exts
                     satp_mode
                     mode
                     #mprv
                     (xlen_sign_extend Xlen xlen
                       (update_pkt @% "val1" @% "data" @% "data" : Bit Rlen @# ty))
                     (decoder_pkt @% "funcUnitTag")
                     (decoder_pkt @% "instTag")
                     #memUnitInput;
              LET val1
                :  RoutedReg
                <- STRUCT {
                     "tag"  ::= #memRet @% "fst" @% "tag";
                     "data" ::= #memRet @% "fst" @% "data"
                   } : RoutedReg @# ty;
              LET mem_update_pkt
                :  ExecUpdPkt
                <- IF #memRet @% "fst" @% "writeReg?"
                     then update_pkt @%["val1" <- Valid #val1]
                     else update_pkt;
              Ret (STRUCT {
                  "fst" ::= #mem_update_pkt;
                  "snd" ::= #memRet @% "snd"
                } : PktWithException ExecUpdPkt @# ty)).

  Close Scope kami_expr.
  Close Scope kami_action.

End mem_unit.
