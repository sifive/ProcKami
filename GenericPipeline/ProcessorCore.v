(*
  This module integrates the processor components defined in FU.v
  into a single pipeline processor model.
*)

Require Import Kami.All.
Require Import ProcKami.FU.
Require Import ProcKami.RiscvIsaSpec.CompressedInsts.
Require Import FpuKami.Definitions.
Require Import FpuKami.Classify.
Require Import FpuKami.Compare.
Require Import Vector.
Import VectorNotations.
Require Import List.
Import ListNotations.
Require Import ProcKami.RiscvPipeline.ConfigReader.
Require Import ProcKami.GenericPipeline.Fetch.
Require Import ProcKami.GenericPipeline.Decompressor.
Require Import ProcKami.GenericPipeline.Decoder.
Require Import ProcKami.GenericPipeline.InputXform.
Require Import ProcKami.GenericPipeline.RegReader.
Require Import ProcKami.GenericPipeline.Executer.
Require Import ProcKami.RiscvPipeline.MemUnit.MemUnitFuncs.
Require Import ProcKami.GenericPipeline.RegWriter.
Require Import ProcKami.RiscvIsaSpec.Csr.Csr.
Require Import ProcKami.RiscvIsaSpec.Csr.CsrFuncs.
Require Import ProcKami.RiscvPipeline.Commit.
Require Import ProcKami.GenericPipeline.ProcessorUtils.

Section Params.
  Variable name: string.
  Local Notation "^ x" := (name ++ "_" ++ x)%string (at level 0).

  (* ^ The width of a general purpose, "x", register for
     this processor, divided by 8 *)
  Variable Xlen_over_8: nat.
  Variable Flen_over_8: nat.
  Variable Rlen_over_8: nat.

  Local Notation Rlen := (Rlen_over_8 * 8).
  Local Notation Xlen := (Xlen_over_8 * 8).
  Local Notation Flen := (Flen_over_8 * 8).
  Local Notation CsrValueWidth := (Xlen_over_8 * 8).
  Local Notation Data := (Bit Rlen).
  Local Notation VAddr := (Bit Xlen).
  Local Notation CsrValue := (Bit CsrValueWidth).
  Local Notation PAddrSz := (Xlen).
  Local Notation PAddr := (Bit PAddrSz).

  Local Notation pmp_reg_width := (pmp_reg_width Xlen_over_8).
  Variable pmp_addr_ub : option (word pmp_reg_width).

  Local Notation MemDevice := (@MemDevice Rlen_over_8 PAddrSz).
  Variable mem_devices : list MemDevice.

  Local Notation MemTableEntry := (@MemTableEntry Rlen_over_8 PAddrSz mem_devices).
  Variable mem_table : list MemTableEntry.

  (* The width of a general purpose, "x", register for this
     processor. This also determine the size of, say, the virtual
     address space. *)
  Local Notation lgMemSz := 20.
  Local Notation memSz := (pow2 lgMemSz).
  Local Notation FUEntry := (FUEntry Xlen_over_8 Rlen_over_8).
  Local Notation FetchPkt := (FetchPkt Xlen_over_8).
  Local Notation ExecContextPkt := (ExecContextPkt Xlen_over_8 Rlen_over_8).
  Local Notation ExecUpdPkt := (ExecUpdPkt Rlen_over_8).
  Local Notation PktWithException := (PktWithException Xlen_over_8).
  Local Notation DispNF := (DispNF Flen_over_8).
  Local Notation initXlen := (initXlen Xlen_over_8).
  Local Notation XlenValue := (XlenValue Xlen_over_8).
  
  Section model.
    Local Open Scope kami_action.
    Local Open Scope kami_expr.

    Variable supported_exts : list (string * bool).
    Variable func_units : forall ty, list (FUEntry supported_exts ty).

    Local Notation misa_field_states := (misa_field_states supported_exts).
    Local Notation supported_exts_foldr := (supported_exts_foldr supported_exts).
    Local Notation DecoderPkt := (@DecoderPkt Xlen_over_8 Rlen_over_8 supported_exts _ (func_units _)).
    Local Notation InputTransPkt := (@InputTransPkt Xlen_over_8 Rlen_over_8 supported_exts _ (func_units _)).
    Local Notation maskEpc := (@maskEpc Xlen_over_8 supported_exts _).
    Local Notation mem_device_files := (@mem_device_files Rlen_over_8 PAddrSz mem_devices).
    Local Notation mem_device_regs := (@mem_device_regs Rlen_over_8 PAddrSz mem_devices).
    Local Notation CSRs := (@CSRs name Xlen_over_8 supported_exts _).
    Local Notation csr_regs := (@csr_regs Xlen_over_8 supported_exts type CSRs).

    Local Open Scope kami_scope.

    Local Definition extRegs
      := supported_exts_foldr
           (fun ext enabled acc
             => (Register ^(ext_misa_field_name ext) : Bool <- ConstBool enabled) :: acc)
           [].

    Local Definition pmpRegs
      := fold_right
           (fun n regs
             => (Register (^"pmp" ++ nat_decimal_string n ++ "cfg") : Bit 8 <- ConstBit (wzero 8)) ::
                (Register (^"pmpaddr" ++ nat_decimal_string n) : Bit pmp_reg_width <- ConstBit (wzero pmp_reg_width)) ::
                regs)
           [] (seq 0 16).

    Close Scope kami_scope.

    Local Open Scope list.

    Definition processorCore 
      :  BaseModule
      := MODULE {
              (* extension registers *)
              Node extRegs with

              (* general context registers *)
              Register ^"mode"             : PrivMode <- ConstBit (natToWord 2 MachineMode) with
              Register ^"pc"               : VAddr <- ConstBit (Xlen 'h"80000000") with

              (* csr registers *)
              Node csr_regs with
(*
              (* floating point registers *)
              Register ^"fflags"           : FflagsValue <- ConstBit (natToWord FflagsWidth 0) with
              Register ^"frm"              : FrmValue    <- ConstBit (natToWord FrmWidth    0) with
*)
              (* machine mode registers *)
              Register ^"mxl"              : XlenValue <- initXlen with
(*
              Register ^"medeleg"          : Bit 16 <- ConstBit (wzero 16) with
              Register ^"mideleg"          : Bit 12 <- ConstBit (wzero 12) with
              Register ^"mprv"             : Bool <- ConstBool false with
              Register ^"mpp"              : Bit 2 <- ConstBit (wzero 2) with
              Register ^"mpie"             : Bool <- ConstBool false with
              Register ^"mie"              : Bool <- ConstBool false with
              Register ^"mtvec_mode"       : Bit 2 <- ConstBit (wzero 2) with
*)
              Register ^"mtvec_base"       : Bit (Xlen - 2)%nat <- ConstBit (natToWord (Xlen - 2)%nat 0) with
(*
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
              Register ^"usie"             : Bool <- ConstBool false with
              Register ^"ssie"             : Bool <- ConstBool false with
              Register ^"msie"             : Bool <- ConstBool false with
              Register ^"utie"             : Bool <- ConstBool false with
              Register ^"stie"             : Bool <- ConstBool false with
              Register ^"mtie"             : Bool <- ConstBool false with
              Register ^"ueie"             : Bool <- ConstBool false with
              Register ^"seie"             : Bool <- ConstBool false with
              Register ^"meie"             : Bool <- ConstBool false with
*)
              (* supervisor mode registers *)
              Register ^"sxl"              : XlenValue <- initXlen with
(*
              Register ^"tsr"              : Bool <- ConstBool false with
              Register ^"tw"               : Bool <- ConstBool false with
              Register ^"tvm"              : Bool <- ConstBool false with
              Register ^"mxr"              : Bool <- ConstBool false with
              Register ^"sum"              : Bool <- ConstBool false with
              Register ^"spp"              : Bit 1 <- ConstBit (wzero 1) with
              Register ^"spie"             : Bool <- ConstBool false with
              Register ^"sie"              : Bool <- ConstBool false with
              Register ^"stvec_mode"       : Bit 2 <- ConstBit (wzero 2) with
*)
              Register ^"stvec_base"       : Bit (Xlen - 2)%nat <- ConstBit (natToWord (Xlen - 2)%nat 0) with
(*
              Register ^"sscratch"         : Bit Xlen <- ConstBit (wzero Xlen) with
              Register ^"sepc"             : Bit Xlen <- ConstBit (wzero Xlen) with
              Register ^"scause_interrupt" : Bool <- ConstBool false with
              Register ^"scause_code"      : Bit (Xlen - 1) <- ConstBit (natToWord (Xlen - 1) 0) with
              Register ^"stval"            : Bit Xlen <- ConstBit (wzero Xlen) with
              Register ^"satp_mode"        : Bit 4 <- ConstBit (wzero 4) with
              Register ^"satp_asid"        : Bit 16 <- ConstBit (wzero 16) with
              Register ^"satp_ppn"         : Bit 44 <- ConstBit (wzero 44) with
*)
              (* user mode registers *)
              Register ^"uxl"              : XlenValue <- initXlen with
              Register ^"upp"              : Bit 0 <- ConstBit WO with
(*
              Register ^"upie"             : Bool <- ConstBool false with
              Register ^"uie"              : Bool <- ConstBool false with
              Register ^"utvec_mode"       : Bit 2 <- ConstBit (wzero 2) with
*)
              Register ^"utvec_base"       : Bit (Xlen - 2)%nat <- ConstBit (natToWord (Xlen - 2)%nat 0) with
(*
              Register ^"uscratch"         : Bit Xlen <- ConstBit (wzero Xlen) with
              Register ^"uepc"             : Bit Xlen <- ConstBit (wzero Xlen) with
              Register ^"ucause_interrupt" : Bool <- ConstBool false with
              Register ^"ucause_code"      : Bit (Xlen - 1) <- ConstBit (natToWord (Xlen - 1) 0) with
              Register ^"utval"            : Bit Xlen <- ConstBit (wzero Xlen) with
*)
              (* preformance monitor registers *)
(*
              Register ^"mtime"           : Bit 64 <- ConstBit (wzero 64) with
*)
              Register ^"mtimecmp"        : Bit 64 <- ConstBit (wzero 64) with
(*
              Register ^"mcounteren"      : Bit 32 <- ConstBit (wzero 32) with
              Register ^"scounteren"      : Bit 32 <- ConstBit (wzero 32) with
              Register ^"mcycle"          : Bit 64 <- ConstBit (wzero 64) with
              Register ^"minstret"        : Bit 64 <- ConstBit (wzero 64) with
*)
              Register ^"mcountinhibit_cy" : Bool <- ConstBool false with
              Register ^"mcountinhibit_tm" : Bool <- ConstBool false with
              Register ^"mcountinhibit_ir" : Bool <- ConstBool false with
              Node pmpRegs with
              Node mem_device_regs with
              Rule ^"trap_interrupt"
                := Read mode : PrivMode <- ^"mode";
                   Read pc : VAddr <- ^"pc";
                   LETA xlen : XlenValue <- readXlen name Xlen_over_8 #mode;
                   System [DispString _ "[trap_interrupt]\n"];
                   interruptAction name #xlen #mode #pc with
              Rule ^"set_time_interrupt"
                := Read mtime : Bit 64 <- ^"mtime";
                   Read mtimecmp : Bit 64 <- ^"mtimecmp";
                   If #mtime > #mtimecmp
                     then
                       Write ^"mtip" : Bool <- $$true;
                       Retv;
                   System [DispString _ "[set_time_interrupt]\n"];
                   Retv with
              Rule ^"inc_time"
                := Read mtime : Bit 64 <- ^"mtime";
                   Write ^"mtime" : Bit 64 <- #mtime + $1;
                   System [DispString _ "[inc_time]\n"];
                   Retv with
              Rule ^"inc_mcycle"
                := Read mcountinhibit_cy : Bool <- ^"mcountinhibit_cy";
                   If #mcountinhibit_cy
                     then
                       Read mcycle : Bit 64 <- ^"mcycle";
                       Write ^"mcycle" : Bit 64 <- #mcycle + $1;
                       Retv;
                   System [DispString _ "[inc_mcycle]\n"];
                   Retv with
              Rule ^"set_ext_interrupt"
                := Call meip : Bool <- ^"ext_interrupt_pending" ();
                   If #meip
                     then
                       System [DispString _ "[set_ext_interrupt] detected an external interrupt\n"];
                       Write ^"meip" : Bool <- $$true;
                       Retv;
                   System [DispString _ "[set_ext_interrupt]\n"];
                   Retv with
              Rule ^"pipeline"
                := 
                   System
                     [
                       DispString _ "created the following extension registers: \n";
                       DispString _ (fold_right String.append "" (fst misa_field_states));
                       DispString _ "\n";
                       DispString _ "the following extension registers were initialized to enabled: \n";
                       DispString _ (fold_right String.append "" (fst misa_field_states));
                       DispString _ "\n";
                       DispString _ "the following misa field names are considered valid by the csr interface: \n";
                       DispString _ (fold_right String.append "" (snd misa_field_states));
                       DispString _ "\n"
                     ];
                   LETA cfg_pkt <- readConfig name Xlen_over_8 supported_exts _;
                   Read pc : VAddr <- ^"pc";
                   System
                     [
                       DispString _ "config: ";
                       DispHex #cfg_pkt;
                       DispString _ "\n";
                       DispString _ "PC: ";
                       DispHex #pc;
                       DispString _ "\n"
                     ];
                   LETA fetch_pkt
                     :  PktWithException FetchPkt
                     <- @fetch name Xlen_over_8 Rlen_over_8 _ mem_devices mem_table (#cfg_pkt @% "xlen") (#cfg_pkt @% "satp_mode") (#cfg_pkt @% "mode") #pc;
                   System
                     [
                       DispString _ "Fetch:\n";
                       DispBinary #fetch_pkt;
                       DispString _ "\n"
                     ];
                   LETA decoder_pkt
                     :  PktWithException DecoderPkt
                     <- decoderWithException (func_units _) (CompInstDb _) (#cfg_pkt @% "xlen") (#cfg_pkt @% "extensions") #fetch_pkt;
                   System
                     [
                       DispString _ "Decode:\n";
                       DispHex #decoder_pkt;
                       DispString _ "\n"
                     ];
                   System [DispString _ "Reg Read\n"];
                   LETA exec_context_pkt
                     :  PktWithException ExecContextPkt
                     <- readerWithException name Flen_over_8 #cfg_pkt #decoder_pkt (#fetch_pkt @% "fst" @% "compressed?");
                   System
                     [
                       DispString _ "Reg Reader:\n";
                       DispHex #exec_context_pkt;    
                       DispString _ "\n"
                     ];
                   System [DispString _ "Trans\n"];
                   LETA trans_pkt
                     :  PktWithException InputTransPkt
                     <- transWithException #cfg_pkt (#decoder_pkt @% "fst") #exec_context_pkt;
                   System [DispString _ "Executor\n"];
                   LETA exec_update_pkt
                     :  PktWithException ExecUpdPkt
                     <- execWithException #trans_pkt;
                   System
                     [
                       DispString _ "New Reg Vals\n";
                       DispHex #exec_update_pkt;
                       DispString _ "\n"
                     ];
                   System [DispString _ "CSR Write\n"];
                   LETA mcounteren <- read_counteren _ ^"mcounteren";
                   LETA scounteren <- read_counteren _ ^"scounteren";
                   Read mepc_raw : VAddr <- ^"mepc";
                   LET  mepc : VAddr <- maskEpc #cfg_pkt #mepc_raw;
                   LETA csr_update_pkt
                     :  PktWithException ExecUpdPkt
                     <- CsrUnit
                          name
                          CSRs
                          #mcounteren
                          #scounteren
                          #pc
                          #mepc
                          (#decoder_pkt @% "fst" @% "inst")
                          (#fetch_pkt @% "fst" @% "compressed?")
                          #cfg_pkt
                          (rd (#exec_context_pkt @% "fst" @% "inst"))
                          (rs1 (#exec_context_pkt @% "fst" @% "inst"))
                          (imm (#exec_context_pkt @% "fst" @% "inst"))
                          #exec_update_pkt;
                   System
                     [
                       DispString _ "CSR Unit:\n";
                       DispHex #csr_update_pkt;    
                       DispString _ "\n"
                     ];
                   LETA mem_update_pkt
                     :  PktWithException ExecUpdPkt
                     <- MemUnit name mem_table
                          (#cfg_pkt @% "xlen")
                          (#cfg_pkt @% "satp_mode")
                          (#cfg_pkt @% "mode")
                          (#decoder_pkt @% "fst")
                          (#exec_context_pkt @% "fst")
                          (#exec_update_pkt @% "fst")
                          (#csr_update_pkt @% "snd");
                   System
                     [
                       DispString _ "Memory Unit:\n";
                       DispHex #mem_update_pkt;    
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
                          (#mem_update_pkt @% "fst")
                          (#mem_update_pkt @% "snd");
                   System [DispString _ "Inc PC\n"];
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
               ([   
                  intRegFile; 
                  floatRegFile; 
                  memReservationRegFile
                ] ++ (mem_device_files ))))
           [   
             ^"read_reg_1"; 
             ^"read_reg_2"; 
             ^"regWrite"; 
             ^"read_freg_1"; 
             ^"read_freg_2"; 
             ^"read_freg_3"; 
             ^"fregWrite";
             ^"readMem0"; (* mem unit loads *)
             ^"readMem1"; (* fetch lower *)
             ^"readMem2"; (* fetch upper *)
             ^"readMem3"; (* mem unit page table walker read mem call *)
             ^"readMem4"; (* mem unit page table walker read mem call *)
             ^"readMem5"; (* mem unit page table walker read mem call *)
             ^"readMem6"; (* fetch lower page table walker read mem call *)
             ^"readMem7"; (* fetch lower page table walker read mem call *)
             ^"readMem8"; (* fetch lower page table walker read mem call *)
             ^"readMem9"; (* fetch upper page table walker read mem call *)
             ^"readMemA"; (* fetch upper page table walker read mem call *)
             ^"readMemB"; (* fetch upper page table walker read mem call *)
             ^"readMemReservation";
             ^"writeMem0";
             ^"writeMemReservation"
           ].  

    Local Close Scope list.

    Local Close Scope kami_expr.
    Local Close Scope kami_action.

  End model.
End Params.

