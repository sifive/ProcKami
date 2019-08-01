(*
  This module defines the memory unit. This unit accepts a memory
  update packet and performs the requested memory writes.
*)
Require Import Kami.All.
Require Import FU.
Require Import Decoder.
Require Import Pmp.
Require Import PhysicalMem.
Require Import VirtualMem.
Require Import List.
Import ListNotations.

Section mem_unit.

  Variable name: string.
  Variable Xlen_over_8: nat.
  Variable Rlen_over_8: nat.
  Variable mem_params : MemParamsType.
  Variable supported_exts : list (string * bool).
  Variable ty: Kind -> Type.

  Local Notation "^ x" := (name ++ "_" ++ x)%string (at level 0).
  Local Notation Rlen := (Rlen_over_8 * 8).
  Local Notation Xlen := (Xlen_over_8 * 8).
  Local Notation Data := (Bit Rlen).
  Local Notation VAddr := (Bit Xlen).
  Local Notation PAddrSz := (Xlen).
  Local Notation PAddr := (Bit PAddrSz).
  Local Notation InstEntry := (InstEntry Xlen_over_8 Rlen_over_8 ty).
  Local Notation FUEntry := (FUEntry Xlen_over_8 Rlen_over_8 supported_exts ty).
  Local Notation FetchPkt := (FetchPkt Xlen_over_8).
  Local Notation ExecContextPkt := (ExecContextPkt Xlen_over_8 Rlen_over_8).
  Local Notation ExecUpdPkt := (ExecUpdPkt Rlen_over_8).
  Local Notation RoutedReg := (RoutedReg Rlen_over_8). 
  Local Notation PktWithException := (PktWithException Xlen_over_8).
  Local Notation FullException := (FullException Xlen_over_8).
  Local Notation MemWrite := (MemWrite Rlen_over_8 PAddrSz).
  Local Notation MemoryInput := (MemoryInput Rlen_over_8).
  Local Notation MemoryOutput := (MemoryOutput Rlen_over_8).
  Local Notation MemUnitInput := (MemUnitInput Rlen_over_8).
  Local Notation MemRet := (MemRet Rlen_over_8).
  Local Notation lgMemSz := (mem_params_size mem_params).
  Local Notation pmp_check_execute := (@pmp_check_execute name Xlen_over_8 ty).
  Local Notation pmp_check_read := (@pmp_check_read name Xlen_over_8 ty).
  Local Notation pmp_check_write := (@pmp_check_write name Xlen_over_8 ty).
  Local Notation pMemRead := (@pMemRead name Xlen_over_8 Rlen_over_8 ty).
  Local Notation pMemWrite := (@pMemWrite name Xlen_over_8 Rlen_over_8 ty).

  Local Notation pMemReadReservation := (@pMemReadReservation name Xlen_over_8 Rlen_over_8 mem_params ty).
  Local Notation pMemWriteReservation := (@pMemWriteReservation name Xlen_over_8 Rlen_over_8 mem_params ty).

  Variable func_units : list FUEntry.
  Local Notation FuncUnitId := (@Decoder.FuncUnitId Xlen_over_8 Rlen_over_8 supported_exts ty func_units).
  Local Notation InstId := (@Decoder.InstId Xlen_over_8 Rlen_over_8 supported_exts ty func_units).
  Local Notation DecoderPkt := (@Decoder.DecoderPkt Xlen_over_8 Rlen_over_8 supported_exts ty func_units).

  Local Notation MemRegion := (@MemRegion Rlen_over_8 PAddrSz ty).
  Variable mem_regions : list MemRegion.

  Local Notation pt_walker := (@pt_walker name Xlen_over_8 Rlen_over_8 ty 4 mem_regions).
  Local Notation mem_region_read := (@mem_region_read Xlen_over_8 Rlen_over_8 ty mem_regions).
  Local Notation mem_region_write := (@mem_region_write Xlen_over_8 Rlen_over_8 ty mem_regions).

  Open Scope kami_expr.
  Open Scope kami_action.

  (* TODO: should this be sign extended? *)
  Definition pMemTranslate
    (vaddr : VAddr @# ty)
    :  PktWithException PAddr @# ty
    := STRUCT {
         "fst" ::= ZeroExtendTruncLsb PAddrSz vaddr;
         "snd" ::= Invalid
       } : PktWithException PAddr @# ty.

  Definition memTranslate
    (mode : PrivMode @# ty)
    (access_type : VmAccessType @# ty)
    (vaddr : VAddr @# ty)
    :  ActionT ty (PktWithException PAddr)
    := Read mpp : PrivMode <- ^"mpp";
       Read mprv : Bool <- ^"mprv";
       Read satp_mode : Bit 4 <- ^"satp_mode";
       Read mxr : Bool <- ^"mxr";
       Read sum : Bool <- ^"sum";
       Read satp_ppn : Bit 44 <- ^"satp_ppn";
       LET transMode
         :  Maybe PrivMode
         <- IF mode == $MachineMode
              then
                (* See 3.1.9 *)
                IF #mprv
                  then Valid #mpp
                  else Invalid
              else Valid mode;
       If #transMode @% "valid" && (!(#satp_mode == $SatpModeBare))
         then
(*
           If satp_select #satp_mode
                (fun vm_mode
                  => $0 == (vaddr >> Const ty (natToWord (Nat.log2_up vm_mode_max_width) (vm_mode_width vm_mode))))
             then
*)
               pt_walker
                 #satp_mode
                 #mxr
                 #sum
                 (#transMode @% "data")
                 (ppnToPAddr Xlen_over_8 (ZeroExtendTruncLsb 44 #satp_ppn))
                 access_type
                 vaddr
(*
             else
               LET exception : FullException <- accessException access_type vaddr;
               Ret (STRUCT {
                   "fst" ::= $0;
                   "snd" ::= Valid #exception
                 } : PktWithException PAddr @# ty)
             as result;
           Ret #result
*)
         else
           Ret (pMemTranslate vaddr)
         as result;
       Ret #result.

  Definition memFetch
    (index : nat)
    (mode : PrivMode @# ty) 
    (vaddr : VAddr @# ty)
    :  ActionT ty (PktWithException Data)
    := LETA paddr
         :  PktWithException PAddr
         <- memTranslate mode $VmAccessInst vaddr;
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
              } : PktWithException Data @# ty)
         else
           LET exception
             :  Maybe FullException
             <- Valid (STRUCT {
                    "exception" ::= $InstAccessFault;
                    "value" ::= vaddr
                  } : FullException @# ty);
           LETA pmp_result
             :  Bool
             <- pmp_check_execute mode (#paddr @% "fst") $4;
           If #pmp_result
             then
               LETA inst
                 :  Maybe Data
                 <- mem_region_read index mode (#paddr @% "fst");
               If #inst @% "valid"
                 then
                   Ret (STRUCT {
                       "fst" ::= #inst @% "data";
                       "snd" ::= Invalid
                     } : PktWithException Data @# ty)
                 else
                   Ret (STRUCT {
                       "fst" ::= $0;
                       "snd" ::= #exception
                     } : PktWithException Data @# ty)
                 as result;
               Ret #result
             else
               Ret (STRUCT {
                   "fst" ::= $0;
                   "snd" ::= #exception
                 } : PktWithException Data @# ty)
             as result;
           Ret #result
         as result;
       Ret #result.

  Local Definition mem_unit_exec_pkt
    (memRet : MemRet @# ty)
    (exception : Maybe FullException @# ty)
    :  ActionT ty (PktWithException MemRet)
    := Ret
         (STRUCT {
            "fst" ::= memRet;
            "snd" ::= exception
          } : PktWithException MemRet @# ty).

  Local Definition mem_unit_exec_pkt_def
    (exception : Maybe FullException @# ty)
    :  ActionT ty (PktWithException MemRet)
    := mem_unit_exec_pkt
         $$(getDefaultConst MemRet)
         exception.

  Local Definition mem_unit_exec_pkt_access_fault
    (vaddr : VAddr @# ty)
    (is_write : Bool @# ty)
    :  ActionT ty (PktWithException MemRet)
    := mem_unit_exec_pkt_def
         (Valid (STRUCT {
           "exception"
             ::= (IF is_write
                   then $SAmoAccessFault
                   else $LoadAccessFault
                   : Exception @# ty);
           "value" ::= vaddr
         } : FullException @# ty)).

  Definition mem_unit_exec
    (mode : PrivMode @# ty)
    (addr : VAddr @# ty)
    (func_unit_id : FuncUnitId @# ty)
    (inst_id : InstId @# ty)
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
                       (match optMemXform inst with
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
           (* III. get the physical address *)
           LETA mpaddr
             :  PktWithException PAddr
             <- memTranslate mode
                  (IF #mis_write @% "data"
                    then $VmAccessSAmo
                    else $VmAccessLoad)
                  addr;
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
               If #mis_write @% "data"
                 then pmp_check_write mode (#mpaddr @% "fst") $Xlen_over_8
                 else pmp_check_read mode (#mpaddr @% "fst") $Xlen_over_8
                 as pmp_result;
               If #pmp_result
                 then
                   (* IV. read the current value and place reservation *)
                   LETA mread_result
                     :  Maybe Data
                     <- mem_region_read 3 mode (#mpaddr @% "fst");
                   (* TODO: should we place reservations on failed reads? *)
                   LETA read_reservation_result
                     :  Array Rlen_over_8 Bool
                     <- pMemReadReservation (unsafeTruncLsb PAddrSz (#mpaddr @% "fst"));
                   (* V. did the read fail? *)
                   If #mread_result @% "valid"
                     then 
                       (* VI. apply the memory transform to compute the wrie value *)
                       LETA mwrite_value
                         :  Maybe MemoryOutput
                         <- convertLetExprSyntax_ActionT
                              (inst_db_get_pkt
                                (fun _ _ tagged_inst
                                  => let inst := snd (tagged_inst) in
                                     match optMemXform inst return MemoryOutput ## ty with
                                       | Some f
                                         => ((f
                                              (RetE
                                                (STRUCT {
                                                  "aq" ::= input_pkt @% "aq" ;
                                                  "rl" ::= input_pkt @% "rl" ;
                                                  "reservation" ::= #read_reservation_result;
                                                  "mem" ::= #mread_result @% "data" ;
                                                  "reg_data" ::= input_pkt @% "reg_data"
                                                 } : MemoryInput @# ty))) : MemoryOutput ## ty)
                                       | None (* impossible case *)
                                         => RetE $$(getDefaultConst MemoryOutput)
                                       end)
                                func_unit_id
                                inst_id);
                       If #mwrite_value @% "data" @% "isWr"
                         then
                           (* VII. write to memory. *)
                           LET write_mask
                             :  Array Rlen_over_8 Bool
                             <- #mwrite_value @% "data" @% "mask";
                           LETA write_result
                             :  Maybe Bool
                             <- mem_region_write mode
                                  (#mpaddr @% "fst")
                                  (#mwrite_value @% "data" @% "data" : Data @# ty)
                                  (#write_mask : Array Rlen_over_8 Bool @# ty);
                           Ret
                             (IF #write_result @% "data"
                               then
                                 Valid (STRUCT {
                                     "exception" ::= $SAmoAccessFault;
                                     "value" ::= addr
                                   } : FullException @# ty)
                               else Invalid)
                         else Ret Invalid
                         as write_result;
                       System [
                         DispString _ "[mem_unit_exec] write result:\n";
                         DispHex #write_result;
                         DispString _ "\n"
                       ];
                       If #mwrite_value @% "data" @% "isLrSc"
                         then pMemWriteReservation
                                (#mpaddr @% "fst")
                                (#mwrite_value @% "data" @% "mask")
                                (#mwrite_value @% "data" @% "reservation");
                       LET memRet
                         :  MemRet
                         <- STRUCT {
                              "writeReg?" ::= #mwrite_value @% "data" @% "reg_data" @% "valid";
                              "tag"  ::= #mwrite_value @% "data" @% "tag";
                              "data" ::= #mwrite_value @% "data" @% "reg_data" @% "data"
                            } : MemRet @# ty;
                       mem_unit_exec_pkt #memRet #write_result
                     else 
                       System [
                         DispString _ "[mem_unit_exec] the memory read operation threw an exception.\n"
                       ];
                       (mem_unit_exec_pkt_access_fault addr (#mis_write @% "data"))
                     as result;
                   Ret #result
                 else
                   System [
                     DispString _ "[mem_unit_exec] the pmp check failed\n"
                   ];
                   (mem_unit_exec_pkt_access_fault addr (#mis_write @% "data"))
                 as result;
               Ret #result
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
    (xlen : XlenValue @# ty)
    (mode : PrivMode @# ty)
    (decoder_pkt : DecoderPkt @# ty)
    (exec_context_pkt : ExecContextPkt @# ty)
    (update_pkt : ExecUpdPkt @# ty)
    (exception : Maybe FullException @# ty)
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
              LETA memRet
                :  PktWithException MemRet
                <- mem_unit_exec
                     mode
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
