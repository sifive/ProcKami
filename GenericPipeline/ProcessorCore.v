(*
  This module integrates the processor components defined in FU.v
  into a single pipeline processor model.
*)

Require Import Kami.AllNotations.
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

Section Params.
  Variable name: string.
  Local Notation "^ x" := (name ++ "_" ++ x)%string (at level 0).
  Context `{procParams: ProcParams}.

  Variable pmp_addr_ub : option (word pmp_reg_width).

  Variable mem_devices : list MemDevice.

  Variable mem_table : list (MemTableEntry mem_devices).

  Section model.
    Local Open Scope kami_action.
    Local Open Scope kami_expr.

    Variable supported_exts : list (string * bool).
    Variable func_units : forall ty, list (FUEntry ty).

    Local Open Scope kami_scope.

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
              Register ^"mode"             : PrivMode <- ConstBit (natToWord 2 MachineMode) with
              Register ^"pc"               : VAddr <- ConstBit (Xlen 'h"80000000") with
              Node (csr_regs (Csrs name)) with
              Register ^"upp"              : Bit 0 <- ConstBit WO with
              Register ^"mtimecmp"        : Bit 64 <- ConstBit (wzero 64) with
              Register ^"mcountinhibit_cy" : Bool <- ConstBool false with
              Register ^"mcountinhibit_tm" : Bool <- ConstBool false with
              Register ^"mcountinhibit_ir" : Bool <- ConstBool false with
              Node pmpRegs with
              Node (mem_device_regs mem_devices) with
              Rule ^"trap_interrupt"
                := Read mode : PrivMode <- ^"mode";
                   Read pc : VAddr <- ^"pc";
                   LETA xlen : XlenValue <- readXlen name #mode;
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
                   LETA cfg_pkt <- readConfig name _;
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
                     <- fetch name mem_table (#cfg_pkt @% "xlen") (#cfg_pkt @% "satp_mode") (#cfg_pkt @% "mode") #pc;
                   System
                     [
                       DispString _ "Fetch:\n";
                       DispBinary #fetch_pkt;
                       DispString _ "\n"
                     ];
                   LETA decoder_pkt
                     :  PktWithException (DecoderPkt (func_units _))
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
                     <- readerWithException name #cfg_pkt #decoder_pkt (#fetch_pkt @% "fst" @% "compressed?");
                   System
                     [
                       DispString _ "Reg Reader:\n";
                       DispHex #exec_context_pkt;    
                       DispString _ "\n"
                     ];
                   System [DispString _ "Trans\n"];
                   LETA trans_pkt
                     :  PktWithException (InputTransPkt (func_units _))
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
                   System [DispString _ "Csr Write\n"];
                   LETA mcounteren <- read_counteren _ ^"mcounteren";
                   LETA scounteren <- read_counteren _ ^"scounteren";
                   Read mepc_raw : VAddr <- ^"mepc";
                   LET  mepc : VAddr <- maskEpc #cfg_pkt #mepc_raw;
                   LETA csr_update_pkt
                     :  PktWithException ExecUpdPkt
                     <- CsrUnit
                          name
                          (Csrs name)
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
                       DispString _ "Csr Unit:\n";
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

    Local Notation lgMemSz := 20.
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
                ] ++ (mem_device_files mem_devices))))
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
