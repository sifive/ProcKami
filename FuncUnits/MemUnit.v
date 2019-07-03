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
  (* Variable vm_params : VmParamsType. *)
  Variable ty: Kind -> Type.

  Local Notation "^ x" := (name ++ "_" ++ x)%string (at level 0).
  Local Notation Rlen := (Rlen_over_8 * 8).
  Local Notation Xlen := (Xlen_over_8 * 8).
  Local Notation Data := (Bit Rlen).
  Local Notation VAddr := (Bit Xlen).
  Local Notation PAddrSz := (mem_params_addr_size mem_params).
  Local Notation PAddr := (Bit PAddrSz).
  Local Notation InstEntry := (InstEntry Xlen_over_8 Rlen_over_8 ty).
  Local Notation FUEntry := (FUEntry Xlen_over_8 Rlen_over_8 ty).
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
  Local Notation defMemRet := (defMemRet Xlen_over_8 Rlen_over_8 ty).
  Local Notation pmp_check_execute := (@pmp_check_execute name Xlen_over_8 mem_params ty).
  Local Notation pmp_check_read := (@pmp_check_read name Xlen_over_8 mem_params ty).
  Local Notation pmp_check_write := (@pmp_check_write name Xlen_over_8 mem_params ty).
(*
  Local Notation pMemFetch := (@pMemFetch name Rlen_over_8 mem_params ty).
  Local Notation pMemRead := (@pMemRead name Rlen_over_8 mem_params ty).
  Local Notation pMemWrite := (@pMemWrite name Xlen_over_8 Rlen_over_8 mem_params ty).
*)
  Local Notation pMemFetch := (@pMemFetch name Xlen_over_8 Rlen_over_8 mem_params ty).
  Local Notation pMemRead := (@pMemRead name Xlen_over_8 Rlen_over_8 mem_params ty).
  Local Notation pMemWrite := (@pMemWrite name Xlen_over_8 Rlen_over_8 mem_params ty).

  Local Notation pMemReadReservation := (@pMemReadReservation name Rlen_over_8 mem_params ty).
  Local Notation pMemWriteReservation := (@pMemWriteReservation name Rlen_over_8 mem_params ty).

  Variable func_units : list FUEntry.
  Local Notation FuncUnitId := (@Decoder.FuncUnitId Xlen_over_8 Rlen_over_8 ty func_units).
  Local Notation InstId := (@Decoder.InstId Xlen_over_8 Rlen_over_8 ty func_units).
  Local Notation DecoderPkt := (@Decoder.DecoderPkt Xlen_over_8 Rlen_over_8 ty func_units).
  Local Notation pt_walker := (@pt_walker name Xlen_over_8 Rlen_over_8 mem_params ty 3).

  Open Scope kami_expr.
  Open Scope kami_action.

  (* TODO: should this be sign extended? *)
  Definition pMemTranslate
    (vaddr : VAddr @# ty)
    :  Maybe PAddr @# ty
    := Valid (SignExtendTruncLsb PAddrSz vaddr).

  Definition memTranslate
    (mode : PrivMode @# ty)
    (access_type : VmAccessType @# ty)
    (vaddr : VAddr @# ty)
    :  ActionT ty (Maybe PAddr)
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
           LETA paddr
             :  Maybe (Bit (mem_params_addr_size mem_params))
             <- pt_walker
                  #satp_mode
                  #mxr
                  #sum
                  (#transMode @% "data")
                  (unsafeTruncLsb (mem_params_addr_size mem_params) (ppnToPAddr mem_params (ZeroExtendTruncLsb 44 #satp_ppn)))
                  access_type
                  vaddr;
           Ret
             (IF #paddr @% "valid"
                then (Valid (SignExtendTruncLsb PAddrSz (#paddr @% "data")) : Maybe PAddr @# ty)
                else Invalid)
         else
           Ret (pMemTranslate vaddr)
         as result;
       Ret #result.

  Local Definition memFetchAux
    (exception : Exception @# ty)
    (vaddr : VAddr @# ty)
    :  Maybe FullException @# ty
    := Valid (STRUCT {
         "exception" ::= exception;
         "value" ::= vaddr
       }).

  Definition memFetch
    (index : nat)
    (mode : PrivMode @# ty) 
    (vaddr : VAddr @# ty)
    :  ActionT ty (PktWithException Data)
    := LETA paddr
         :  Maybe PAddr
         <- memTranslate mode $VmAccessInst vaddr;
       If #paddr @% "valid"
         then
           LETA inst
             :  Maybe Data
             <- pMemFetch index mode (#paddr @% "data");
           Ret
             (STRUCT {
                "fst" ::= #inst @% "data";
                "snd"
                  ::= IF #inst @% "valid"
                        then Invalid
                        else memFetchAux ($InstAccessFault) vaddr
              } : PktWithException Data @# ty)
         else
           Ret
             (STRUCT {
                "fst" ::= $0;
                "snd" ::= memFetchAux ($InstPageFault) vaddr
              } : PktWithException Data @# ty)
         as result;
       Ret #result.

  Definition mem_unit_exec
    (mode : PrivMode @# ty)
    (addr : VAddr @# ty)
    (func_unit_id : FuncUnitId @# ty)
    (inst_id : InstId @# ty)
    (input_pkt : MemUnitInput @# ty)
    :  ActionT ty (PktWithException MemRet)
    := (* I. does the instruction perform a memory operation? *)
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
             :  Maybe PAddr
             <- memTranslate mode
                  (IF #mis_write @% "data"
                    then $VmAccessSAmo
                    else $VmAccessLoad)
                  addr;
           If #mpaddr @% "valid"
             then
               (* IV. read the current value and place reservation *)
               LETA mread_result
                 :  Maybe Data
                 <- pMemRead 2 mode (#mpaddr @% "data");
               LETA read_reservation_result
                 :  Array Rlen_over_8 Bool
                 <- pMemReadReservation (#mpaddr @% "data");
               (* V. did the read fail? *)
               If #mread_result @% "valid"
                 then 
                   (* VI. apply the memory transform to compute the write value *)
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
                         <- IF #mwrite_value @% "data" @% "isWr"
                              then #mwrite_value @% "data" @% "mask"
                              else $$(ConstArray (fun (_ : Fin.t Rlen_over_8) => false));
                       LETA write_result
                         :  Maybe FullException
                         <- pMemWrite mode
                              (STRUCT {
                                 "addr" ::= (#mpaddr @% "data" : PAddr @# ty);
                                 "data" ::= (#mwrite_value @% "data" @% "data" : Data @# ty);
                                 "mask" ::= (#write_mask : Array Rlen_over_8 Bool @# ty)
                               } : MemWrite @# ty);
                       Ret #write_result
                     else
                       Ret Invalid
                     as write_exception;
                   If #write_exception @% "valid"
                     then
                       System [
                         DispString _ "[mem_unit_exec] the memory write operation threw an exception.\n"
                       ];
                       Retv;
                   If #mwrite_value @% "data" @% "isLrSc"
                     then pMemWriteReservation
                            (#mpaddr @% "data")
                            (#mwrite_value @% "data" @% "mask")
                            (#mwrite_value @% "data" @% "reservation");
                   LET result
                     :  MemRet
                     <- STRUCT {
                          "writeReg?" ::= #mwrite_value @% "data" @% "reg_data" @% "valid";
                          "tag"  ::= #mwrite_value @% "data" @% "tag";
                          "data" ::= #mwrite_value @% "data" @% "reg_data" @% "data"
                        } : MemRet @# ty;
                   LET ret_value
                     :  PktWithException MemRet
                     <- STRUCT {
                          "fst" ::= #result;
                          "snd" ::= #write_exception
                        } : PktWithException MemRet @# ty;
                   Ret #ret_value
                 else 
                   System [
                     DispString _ "[mem_unit_exec] the memory read operation threw an exception.\n"
                   ];
                   Ret defMemRet
                 as result;
               Ret #result
             else
               System [
                 DispString _ "[mem_unit_exec] the page table walker threw an exception\n"
               ];
               Ret
                 (STRUCT {
                   "fst" ::= $$(getDefaultConst MemRet);
                   "snd"
                     ::= (Valid (STRUCT {
                            "exception"
                              ::= (IF #mis_write @% "data"
                                    then $SAmoPageFault
                                    else $LoadPageFault
                                    : Exception @# ty);
                            "value" ::= addr
                          }) : Maybe FullException @# ty)
                  })
             as result;
           Ret #result
         else
           Ret defMemRet
         as result;
       Ret #result.

  Definition MemUnit
             (xlen : XlenValue @# ty)
             (mode : PrivMode @# ty)
             (decoder_pkt : DecoderPkt @# ty)
             (exec_context_pkt : ExecContextPkt @# ty)
             (opt_exec_update_pkt : PktWithException ExecUpdPkt @# ty)
    :  ActionT ty (PktWithException ExecUpdPkt)
    := LET exec_update_pkt: ExecUpdPkt <- opt_exec_update_pkt @% "fst";
       LETA memRet
         :  PktWithException MemRet
         <- mem_unit_exec
              mode
              (xlen_sign_extend Xlen xlen
                (#exec_update_pkt @% "val1" @% "data" @% "data" : Bit Rlen @# ty))
              (decoder_pkt @% "funcUnitTag")
              (decoder_pkt @% "instTag")
              (STRUCT {
                 "aq"       ::= #exec_update_pkt @% "aq";
                 "rl"       ::= #exec_update_pkt @% "rl";
                 "reg_data" ::= exec_context_pkt @% "reg2"
                 } : MemUnitInput @# ty);
       LET val1 <- (STRUCT {
                        "tag"  ::= #memRet @% "fst" @% "tag";
                        "data" ::= (#memRet @% "fst" @% "data" : Bit Rlen @# ty)
                      } : RoutedReg @# ty);
       Ret
         (mkPktWithException
            opt_exec_update_pkt
            (STRUCT {
                 "fst"
                 ::= (ITE
                        (#memRet @% "fst" @% "writeReg?")
                        (#exec_update_pkt
                           @%["val1" <- Valid #val1])
                        (#exec_update_pkt));
                 "snd" ::= #memRet @% "snd"
               } : PktWithException ExecUpdPkt @# ty)).

  Close Scope kami_expr.
  Close Scope kami_action.

End mem_unit.
