(*
  This module integrates the processor components defined in FU.v
  into a single pipeline processor model.
*)

Require Import Kami.All.
Require Import FU.
Require Import CompressedInsts.
Require Import FpuKami.Definitions.
Require Import FpuKami.Classify.
Require Import FpuKami.Compare.
Require Import Vector.
Import VectorNotations.
Require Import List.
Import ListNotations.
Require Import ConfigReader.
Require Import Fetch.
Require Import Decompressor.
Require Import Decoder.
Require Import InputTrans.
Require Import RegReader.
Require Import Executer.
Require Import FuncUnits.MemUnit.
Require Import RegWriter.
Require Import FuncUnits.CSR.
Require Import FuncUnits.TrapHandling.
Require Import Counter.
Require Import ProcessorUtils.

Section Params.
  Variable name: string.
  Local Notation "^ x" := (name ++ "_" ++ x)%string (at level 0).

  Variable Xlen_over_8: nat.
  Variable Flen_over_8: nat.
  Variable Clen_over_8: nat.
  Variable Rlen_over_8: nat.
  Variable mem_params : MemParamsType.
  Variable pmp_addr_ub : option (word 54).

  Local Notation Rlen := (Rlen_over_8 * 8).
  Local Notation Xlen := (Xlen_over_8 * 8).
  Local Notation Flen := (Flen_over_8 * 8).
  Local Notation CsrValueWidth := (Clen_over_8 * 8).
  Local Notation Data := (Bit Rlen).
  Local Notation VAddr := (Bit Xlen).
  Local Notation CsrValue := (Bit CsrValueWidth).
  Local Notation lgMemSz := (mem_params_size mem_params).
  Local Notation PAddrSz := (mem_params_addr_size mem_params).
  Local Notation FUEntry := (FUEntry Xlen_over_8 Rlen_over_8).
  Local Notation FetchPkt := (FetchPkt Xlen_over_8).
  Local Notation ExecUpdPkt := (ExecUpdPkt Rlen_over_8).
  Local Notation PktWithException := (PktWithException Xlen_over_8).
  Local Notation DispNF := (DispNF Flen_over_8).
  Local Notation initXlen := (initXlen Xlen_over_8).
  
  Section model.
    Local Open Scope kami_action.
    Local Open Scope kami_expr.

    Variable func_units : forall ty, list (FUEntry ty).
    Variable supportedExts : ConstT (Extensions).

    Local Open Scope list.
    Definition processorCore 
      :  BaseModule
      := MODULE {
              (* general context registers *)
              Register ^"mode"             : PrivMode <- ConstBit (natToWord 2 MachineMode) with
              (* Register ^"pc"               : VAddr <- ConstBit (wzero Xlen) with *)
              Register ^"pc"               : VAddr <- ConstBit (Xlen 'h"80000000") with

              (* floating point registers *)
              Register ^"fflags"           : FflagsValue <- ConstBit (natToWord FflagsWidth 0) with
              Register ^"frm"              : FrmValue    <- ConstBit (natToWord FrmWidth    0) with

              (* machine mode registers *)
              Register ^"mxl"              : XlenValue <- initXlen with
              Register ^"medeleg"          : Bit 16 <- ConstBit (wzero 16) with
              Register ^"mideleg"          : Bit 12 <- ConstBit (wzero 12) with
              Register ^"mprv"             : Bool <- ConstBool false with
              Register ^"mpp"              : Bit 2 <- ConstBit (wzero 2) with
              Register ^"mpie"             : Bool <- ConstBool false with
              Register ^"mie"              : Bool <- ConstBool false with
              Register ^"mtvec_mode"       : Bit 2 <- ConstBit (wzero 2) with
              Register ^"mtvec_base"       : Bit (Xlen - 2)%nat <- ConstBit (natToWord (Xlen - 2)%nat 0) with
              Register ^"mscratch"         : Bit Xlen <- ConstBit (wzero Xlen) with
              Register ^"mepc"             : Bit Xlen <- ConstBit (wzero Xlen) with
              Register ^"mcause_interrupt" : Bool <- ConstBool false with
              Register ^"mcause_code"      : Bit (Xlen - 1) <- ConstBit (natToWord (Xlen - 1) 0) with
              Register ^"mtval"            : Bit Xlen <- ConstBit (wzero Xlen) with

              Register ^"mvendorid"        : Bit 32 <- ConstBit (wzero 32) with
              Register ^"marchid"          : Bit Xlen <- ConstBit (wzero Xlen) with
              Register ^"mimpid"           : Bit Xlen <- ConstBit (wzero Xlen) with
              Register ^"mhartid"          : Bit Xlen <- ConstBit (wzero Xlen) with

              Register ^"usip"             : Bool <- ConstBool false with
              Register ^"ssip"             : Bool <- ConstBool false with
              Register ^"msip"             : Bool <- ConstBool false with
              Register ^"utip"             : Bool <- ConstBool false with
              Register ^"stip"             : Bool <- ConstBool false with
              Register ^"mtip"             : Bool <- ConstBool false with
              Register ^"ueip"             : Bool <- ConstBool false with
              Register ^"seip"             : Bool <- ConstBool false with
              Register ^"meip"             : Bool <- ConstBool false with

              (* supervisor mode registers *)
              Register ^"sxl"              : XlenValue <- initXlen with
              Register ^"sedeleg"          : Bit 16 <- ConstBit (wzero 16) with
              Register ^"tvm"              : Bool <- ConstBool false with
              Register ^"mxr"              : Bool <- ConstBool false with
              Register ^"sum"              : Bool <- ConstBool false with
              Register ^"spp"              : Bit 1 <- ConstBit (wzero 1) with
              Register ^"spie"             : Bool <- ConstBool false with
              Register ^"sie"              : Bool <- ConstBool false with
              Register ^"stvec_mode"       : Bit 2 <- ConstBit (wzero 2) with
              Register ^"stvec_base"       : Bit (Xlen - 2)%nat <- ConstBit (natToWord (Xlen - 2)%nat 0) with
              Register ^"sscratch"         : Bit Xlen <- ConstBit (wzero Xlen) with
              Register ^"sepc"             : Bit Xlen <- ConstBit (wzero Xlen) with
              Register ^"scause_interrupt" : Bool <- ConstBool false with
              Register ^"scause_code"      : Bit (Xlen - 1) <- ConstBit (natToWord (Xlen - 1) 0) with
              Register ^"stval"            : Bit Xlen <- ConstBit (wzero Xlen) with
              Register ^"satp_mode"        : Bit 4 <- ConstBit (wzero 4) with
              Register ^"satp_asid"        : Bit 16 <- ConstBit (wzero 16) with
              Register ^"satp_ppn"         : Bit 44 <- ConstBit (wzero 44) with

              (* user mode registers *)
              Register ^"uxl"              : XlenValue <- initXlen with
              Register ^"upp"              : Bit 0 <- ConstBit WO with (* Should be Bit 0, but this results in a system verilog error. 3.1.7 *)
              Register ^"upie"             : Bool <- ConstBool false with
              Register ^"uie"              : Bool <- ConstBool false with
              Register ^"utvec_mode"       : Bit 2 <- ConstBit (wzero 2) with
              Register ^"utvec_base"       : Bit (Xlen - 2)%nat <- ConstBit (natToWord (Xlen - 2)%nat 0) with
              Register ^"uscratch"         : Bit Xlen <- ConstBit (wzero Xlen) with
              Register ^"uepc"             : Bit Xlen <- ConstBit (wzero Xlen) with
              Register ^"ucause_interrupt" : Bool <- ConstBool false with
              Register ^"ucause_code"      : Bit (Xlen - 1) <- ConstBit (natToWord (Xlen - 1) 0) with
              Register ^"utval"            : Bit Xlen <- ConstBit (wzero Xlen) with

              (* preformance monitor registers *)
              Register ^"mcounteren"      : Bit 32 <- ConstBit (wzero 32) with
              Register ^"scounteren"      : Bit 32 <- ConstBit (wzero 32) with
              Register ^"mcycle"          : Bit 64 <- ConstBit (wzero 64) with
              Register ^"minstret"        : Bit 64 <- ConstBit (wzero 64) with
              Register ^"mcountinhibit"   : Bit 32 <- ConstBit (wzero 32) with

              (* memory protection registers. *)
              Register ^"pmp0cfg" : Bit 8 <- ConstBit (wzero 8) with
(*
                <- match pmp_addr_ub with
                     | Some _
                       => ConstBit ('b"10001111") (* grant read write privileges within address range [0, pmp_addr_ub]. *)
                       (* => ConstBit (wzero 8) *)
                     | _
                       => ConstBit (wzero 8)
                     end with
*)
              Register ^"pmp1cfg" : Bit 8 <- ConstBit (wzero 8) with
              Register ^"pmp2cfg" : Bit 8 <- ConstBit (wzero 8) with
              Register ^"pmp3cfg" : Bit 8 <- ConstBit (wzero 8) with
              Register ^"pmp4cfg" : Bit 8 <- ConstBit (wzero 8) with
              Register ^"pmp5cfg" : Bit 8 <- ConstBit (wzero 8) with
              Register ^"pmp6cfg" : Bit 8 <- ConstBit (wzero 8) with
              Register ^"pmp7cfg" : Bit 8 <- ConstBit (wzero 8) with
              Register ^"pmp8cfg" : Bit 8 <- ConstBit (wzero 8) with
              Register ^"pmp9cfg" : Bit 8 <- ConstBit (wzero 8) with
              Register ^"pmp10cfg" : Bit 8 <- ConstBit (wzero 8) with
              Register ^"pmp11cfg" : Bit 8 <- ConstBit (wzero 8) with
              Register ^"pmp12cfg" : Bit 8 <- ConstBit (wzero 8) with
              Register ^"pmp13cfg" : Bit 8 <- ConstBit (wzero 8) with
              Register ^"pmp14cfg" : Bit 8 <- ConstBit (wzero 8) with
              Register ^"pmp15cfg" : Bit 8 <- ConstBit (wzero 8) with
(*
                :  Bit 8
                <- match pmp_addr_ub with
                     | Some _
                       => ConstBit ('b"10011000") (* deny read write execute privileges beyond address range [0, pmp_addr_ub]. *)
                     | _
                       => ConstBit (wzero 8)
                     end with
*)
              Register ^"pmpaddr0" : Bit 54 <- ConstBit (wzero 54) with
(*
                <- match pmp_addr_ub with
                     | Some addr
                       => ConstBit addr
                     | _
                       => ConstBit (wzero 54)
                     end with
*)
              Register ^"pmpaddr1" : Bit 54 <- ConstBit (wzero 54) with
              Register ^"pmpaddr2" : Bit 54 <- ConstBit (wzero 54) with
              Register ^"pmpaddr3" : Bit 54 <- ConstBit (wzero 54) with
              Register ^"pmpaddr4" : Bit 54 <- ConstBit (wzero 54) with
              Register ^"pmpaddr5" : Bit 54 <- ConstBit (wzero 54) with
              Register ^"pmpaddr6" : Bit 54 <- ConstBit (wzero 54) with
              Register ^"pmpaddr7" : Bit 54 <- ConstBit (wzero 54) with
              Register ^"pmpaddr8" : Bit 54 <- ConstBit (wzero 54) with
              Register ^"pmpaddr9" : Bit 54 <- ConstBit (wzero 54) with
              Register ^"pmpaddr10" : Bit 54 <- ConstBit (wzero 54) with
              Register ^"pmpaddr11" : Bit 54 <- ConstBit (wzero 54) with
              Register ^"pmpaddr12" : Bit 54 <- ConstBit (wzero 54) with
              Register ^"pmpaddr13" : Bit 54 <- ConstBit (wzero 54) with
              Register ^"pmpaddr14" : Bit 54 <- ConstBit (wzero 54) with
              Register ^"pmpaddr15" : Bit 54 <- ConstBit (wzero 54) with
(*
                :  Bit 54
                <- match pmp_addr_ub with
                     | Some _
                       (* => ConstBit (wnot (wlshift' (natToWord 54 1) (Xlen - 2))) *)
                       (* TODO use mem granularity. *)
                       => ConstBit (wones 54) (* See table 3.9 *)
                     | _
                       => ConstBit (wzero 54)
                     end with
*)
              Rule ^"pipeline"
                := LETA cfg_pkt <- readConfig name _ supportedExts;
                   Read pc : VAddr <- ^"pc";
                   System
                     [
                       DispString _ ("[add] Xlen: " ++ natToHexStr Xlen ++ " Rlen: " ++ natToHexStr Rlen ++ "\n");
                       DispString _ " [add] xlen: ";
                       DispDecimal (#cfg_pkt @% "xlen");
                       DispString _ "\n";
                       DispString _ "PC: ";
                       DispHex #pc;
                       DispString _ "\n"
                     ];
                   LETA fetch_pkt
                     :  PktWithException FetchPkt
                     <- fetch name Xlen_over_8 Rlen_over_8 mem_params (#cfg_pkt @% "xlen") (#cfg_pkt @% "mode") (#pc);
                   System
                     [
                       DispString _ "Fetch:\n";
                       DispBinary #fetch_pkt;
                       DispString _ "\n"
                     ];
                   LETA decoder_pkt
                     <- convertLetExprSyntax_ActionT
                          (decoderWithException (func_units _) (CompInstDb _) (#cfg_pkt @% "xlen") (#cfg_pkt @% "extensions")
                            (RetE (#fetch_pkt)));
                   System
                     [
                       DispString _ "Decode:\n";
                       DispHex #decoder_pkt;
                       DispString _ "\n"
                     ];
                   System [DispString _ "Reg Read\n"];
                   LETA exec_context_pkt
                     <- readerWithException name Flen_over_8
                          #cfg_pkt
                          #decoder_pkt;
                   System
                     [
                       DispString _ "Reg Reader:\n";
                       DispHex #exec_context_pkt;    
                       DispString _ "\n"
                     ];
                   System [DispString _ "Trans\n"];
                   LETA trans_pkt
                     <- convertLetExprSyntax_ActionT
                          (transWithException
                            #cfg_pkt
                            (#decoder_pkt @% "fst")
                            (#exec_context_pkt));
                   System [DispString _ "Executor\n"];
                   LETA exec_update_pkt
                     <- convertLetExprSyntax_ActionT
                          (execWithException (#trans_pkt));
                   System
                     [
                       DispString _ "New Reg Vals\n";
                       DispHex #exec_update_pkt;
                       DispString _ "\n"
                     ];
                   (* NOTE: must be before CSR writes - see 3.1.16 *)
                   LETA mem_update_pkt
                     <- MemUnit name mem_params
                          (* ["mem"; "amo32"; "amo64"; "lrsc32"; "lrsc64"] *)
                          (#cfg_pkt @% "xlen")
                          (#cfg_pkt @% "mode")
                          (#decoder_pkt @% "fst")
                          (#exec_context_pkt @% "fst")
                          (#exec_update_pkt);
                   System
                     [
                       DispString _ "Memory Unit:\n";
                       DispHex #mem_update_pkt;    
                       DispString _ "\n"
                     ];
                   System [DispString _ "CSR Write\n"];
                   LETA mcounteren <- read_counteren _ ^"mcounteren";
                   LETA scounteren <- read_counteren _ ^"scounteren";
                   LETA csr_update_pkt
                     :  Pair (Bit CsrUpdateCodeWidth) (PktWithException ExecUpdPkt)
                     <- CsrUnit
                          name
                          Clen_over_8
                          #mcounteren
                          #scounteren
                          #pc
                          (#decoder_pkt @% "fst" @% "inst")
                          (#decoder_pkt @% "fst" @% "compressed?")
                          (#cfg_pkt)
                          (rd (#exec_context_pkt @% "fst" @% "inst"))
                          (rs1 (#exec_context_pkt @% "fst" @% "inst"))
                          (imm (#exec_context_pkt @% "fst" @% "inst"))
                          #mem_update_pkt;
                   System
                     [
                       DispString _ "CSR Unit:\n";
                       DispHex #csr_update_pkt;    
                       DispString _ "\n"
                     ];
                   System [DispString _ "Reg Write\n"];
                   LETA commit_pkt
                     :  Void
                     <- commit
                          name
                          Flen_over_8
                          #pc
                          (#decoder_pkt @% "fst" @% "inst")
                          #cfg_pkt
                          (#exec_context_pkt @% "fst")
                          (#csr_update_pkt @% "snd");
                   System [DispString _ "Inc PC\n"];
                   LETA _
                     <- inc_mcycle name
                          (#csr_update_pkt @% "fst");
                   LETA _
                     <- inc_instret name
                          (#exec_context_pkt @% "snd" @% "valid")
                          (#csr_update_pkt @% "fst");
                   Call ^"pc"(#pc: VAddr); (* for test verification *)
                   Retv
         }.

    Definition intRegFile
      :  RegFileBase
      := @Build_RegFileBase
           false
           1
           (^"int_data_reg")
           (Async [(^"read_reg_1"); (^"read_reg_2")])
           (^"regWrite")
           32
           (Bit Xlen)
           (RFNonFile _ None).

    Definition floatRegFile
      :  RegFileBase
      := @Build_RegFileBase 
           false
           1
           (^"float_reg_file")
           (Async [(^"read_freg_1"); (^"read_freg_2"); (^"read_freg_3")])
           (^"fregWrite")
           32
           (Bit Flen)
           (RFNonFile _ None).

    Definition memRegFile
       :  RegFileBase :=
       @Build_RegFileBase
         true
         Rlen_over_8
         (^"mem_reg_file")
         (Async [^"readMem1"; ^"readMem2"; ^"readMem3"; ^"readMem4"; ^"readMem5"])
         (^"writeMem")
         (pow2 lgMemSz)
         (Bit 8)
         (RFFile true true "testfile" 0 (pow2 lgMemSz) (fun _ => wzero _)).

    Definition memReservationRegFile
      :  RegFileBase
      := @Build_RegFileBase
           true
           Rlen_over_8
           (^"memReservation_reg_file")
           (Async [^"readMemReservation"])
           (^"writeMemReservation")
           (pow2 lgMemSz)
           Bool
           (RFFile true false "file0" 0 (pow2 lgMemSz) (fun _ => false)).

    Definition processor
      :  Mod 
      := createHideMod
           (fold_right
             ConcatMod
             processorCore
             (map
               (fun m => Base (BaseRegFile m)) 
               [   
                 intRegFile; 
                 floatRegFile; 
                 memRegFile;
                 memReservationRegFile
               ])) 
           [   
             ^"read_reg_1"; 
             ^"read_reg_2"; 
             ^"regWrite"; 
             ^"read_freg_1"; 
             ^"read_freg_2"; 
             ^"read_freg_3"; 
             ^"fregWrite";
             ^"readMem1"; (* fetch read mem *)
             ^"readMem2";
             ^"readMem3"; (* page table walker read mem call *)
             ^"readMem4"; (* page table walker read mem call *)
             ^"readMem5"; (* page table walker read mem call *)
             ^"readMemReservation";
             ^"writeMem";
             ^"writeMemReservation"
           ].  

    Local Close Scope list.

    Local Close Scope kami_expr.
    Local Close Scope kami_action.

  End model.
End Params.

