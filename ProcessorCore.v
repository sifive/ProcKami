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
Require Import PhysicalMem.
Require Import MMappedRegs.
Require Import Stale.

Require Import RenameMe.

Section Params.
  Variable name: string.
  Local Notation "^ x" := (name ++ "_" ++ x)%string (at level 0).

  (* ^ The width of a general purpose, "x", register for
     this processor, divided by 8 *)
  Variable Xlen_over_8: nat.
  Variable Flen_over_8: nat.
  Variable Clen_over_8: nat.
  Variable Rlen_over_8: nat.
  Variable mem_params : MemParamsType.
  Variable pmp_addr_ub : option (word 54).

  Local Notation Rlen := (Rlen_over_8 * 8).
  (* The width of a general purpose, "x", register for this
     processor. This also determine the size of, say, the virtual
     address space. *)
  Local Notation Xlen := (Xlen_over_8 * 8).
  Local Notation Flen := (Flen_over_8 * 8).
  Local Notation CsrValueWidth := (Clen_over_8 * 8).
  Local Notation Data := (Bit Rlen).
  Local Notation VAddr := (Bit Xlen).
  Local Notation CsrValue := (Bit CsrValueWidth).
  Local Notation lgMemSz := (mem_params_size mem_params).
  Local Notation memSz := (pow2 lgMemSz).
  Local Notation PAddrSz := (Xlen).
  Local Notation PAddr := (Bit PAddrSz).
  Local Notation FUEntry := (FUEntry Xlen_over_8 Rlen_over_8).
  Local Notation FetchPkt := (FetchPkt Xlen_over_8).
  Local Notation ExecContextPkt := (ExecContextPkt Xlen_over_8 Rlen_over_8).
  Local Notation ExecUpdPkt := (ExecUpdPkt Rlen_over_8).
  Local Notation PktWithException := (PktWithException Xlen_over_8).
  Local Notation DispNF := (DispNF Flen_over_8).
  Local Notation initXlen := (initXlen Xlen_over_8).
  Local Notation pMemDevice := (pMemDevice name Xlen_over_8 Rlen_over_8 mem_params).
  Local Notation mMappedRegDevice := (mMappedRegDevice name Xlen_over_8 Rlen_over_8).
  
  Local Notation ProcState := (@ProcState Xlen_over_8 mem_params).
  Local Notation RegState := (@RegState Xlen_over_8).
  Local Notation MemState := (@MemState mem_params).

  Section model.
    Local Open Scope kami_action.
    Local Open Scope kami_expr.

    Variable func_units : forall ty, list (FUEntry ty).
    Variable supportedExts : ConstT (Extensions).

    (* Processor core starting state *)
    Variable initProcState: ProcState.
    
    Local Notation initMemMap := (memState initProcState).
    Local Notation initRegState := (regState initProcState).

    Local Notation DecoderPkt := (@DecoderPkt Xlen_over_8 Rlen_over_8 _ (func_units _)).
    Local Notation InputTransPkt := (@InputTransPkt Xlen_over_8 Rlen_over_8 _ (func_units _)).

    (* It seems that the processor would best be parameterized by a
       number of mmio MemDevices for each device we want to talk to
       over MMIO. For now I'm modeling this as one big mmioPoolDevice
       that can potentially route requests to individual device
       memories by address.
     *)

    Local Definition mem_regions (ty : Kind -> Type)
      := [
           {|
             mem_region_addr := 0; (* TODO hardcode here? *)
             mem_region_width := 16; (* 2 * num memory mapped regs *)
             mem_region_device := (mMappedRegDevice ty);
           |};
           {|
             mem_region_addr := 80000000; (* start at 80000000 *) (* TODO should this really be hardcoded? *)
             mem_region_width := (pow2 lgMemSz);
             mem_region_device := (pMemDevice ty)
           |}
        ].

    Local Open Scope list.

    Local Definition memTranslate {ty} mode := (@memTranslate name Xlen_over_8 _ _ (mem_regions ty) mode $VmAccessInst).

    Local Definition markStale {ty} := (@markStale name ty memSz).
    Local Definition staleP {ty} := (@staleP name ty memSz).
    Local Definition flush {ty} := (@flush name ty memSz).

    Definition processorCore 
      :  BaseModule
      := MODULE {
              (* general context registers *)
              Register ^"mode"             : PrivMode <- (mode initRegState) with
              Register ^"pc"               : VAddr <- (pc initRegState) with

              (* floating point registers *)
              Register ^"fflags"           : FflagsValue <- (fflags initRegState) with
              Register ^"frm"              : FrmValue    <- (frm initRegState) with

              (* machine mode registers *)
              Register ^"mxl"              : XlenValue <- (mxl initRegState) with
              Register ^"medeleg"          : Bit 16 <- (medeleg initRegState) with
              Register ^"mideleg"          : Bit 12 <- (mideleg initRegState) with
              Register ^"mprv"             : Bool <- (mprv initRegState) with
              Register ^"mpp"              : Bit 2 <- (mpp initRegState) with
              Register ^"mpie"             : Bool <- (mpie initRegState) with
              Register ^"mie"              : Bool <- (mie initRegState) with
              Register ^"mtvec_mode"       : Bit 2 <- (mtvec_mode initRegState) with
              Register ^"mtvec_base"       : Bit (Xlen - 2)%nat <- (mtvec_base initRegState) with
              Register ^"mscratch"         : Bit Xlen <- (mscratch initRegState) with
              Register ^"mepc"             : Bit Xlen <- (mepc initRegState) with
              Register ^"mcause_interrupt" : Bool <- (mcause_interrupt initRegState) with
              Register ^"mcause_code"      : Bit (Xlen - 1) <- (mcause_code initRegState) with
              Register ^"mtval"            : Bit Xlen <- (mtval initRegState) with

              Register ^"mvendorid"        : Bit 32 <- (mvendorid initRegState) with
              Register ^"marchid"          : Bit Xlen <- (marchid initRegState) with
              Register ^"mimpid"           : Bit Xlen <- (mimpid initRegState) with
              Register ^"mhartid"          : Bit Xlen <- (mhartid initRegState) with

              Register ^"usip"             : Bool <- (usip initRegState) with
              Register ^"ssip"             : Bool <- (ssip initRegState) with
              Register ^"msip"             : Bool <- (msip initRegState) with
              Register ^"utip"             : Bool <- (utip initRegState) with
              Register ^"stip"             : Bool <- (stip initRegState) with
              Register ^"mtip"             : Bool <- (mtip initRegState) with
              Register ^"ueip"             : Bool <- (ueip initRegState) with
              Register ^"seip"             : Bool <- (seip initRegState) with
              Register ^"meip"             : Bool <- (meip initRegState) with
              Register ^"usie"             : Bool <- (usie initRegState) with
              Register ^"ssie"             : Bool <- (ssie initRegState) with
              Register ^"msie"             : Bool <- (msie initRegState) with
              Register ^"utie"             : Bool <- (utie initRegState) with
              Register ^"stie"             : Bool <- (stie initRegState) with
              Register ^"mtie"             : Bool <- (mtie initRegState) with
              Register ^"ueie"             : Bool <- (ueie initRegState) with
              Register ^"seie"             : Bool <- (seie initRegState) with
              Register ^"meie"             : Bool <- (meie initRegState) with

              (* supervisor mode registers *)
              Register ^"sxl"              : XlenValue <- (sxl initRegState) with
              Register ^"sedeleg"          : Bit 16 <- (sedeleg initRegState) with
              Register ^"sideleg"          : Bit 16 <- (sideleg initRegState) with
              Register ^"tsr"              : Bool <- (tsr initRegState) with
              Register ^"tw"               : Bool <- (tw initRegState) with
              Register ^"tvm"              : Bool <- (tvm initRegState) with
              Register ^"mxr"              : Bool <- (mxr initRegState) with
              Register ^"sum"              : Bool <- (sum initRegState) with
              Register ^"spp"              : Bit 1 <- (spp initRegState) with
              Register ^"spie"             : Bool <- (spie initRegState) with
              Register ^"sie"              : Bool <- (sie initRegState) with
              Register ^"stvec_mode"       : Bit 2 <- (stvec_mode initRegState) with
              Register ^"stvec_base"       : Bit (Xlen - 2)%nat <- (stvec_base initRegState) with
              Register ^"sscratch"         : Bit Xlen <- (sscratch initRegState) with
              Register ^"sepc"             : Bit Xlen <- (sepc initRegState) with
              Register ^"scause_interrupt" : Bool <- (scause_interrupt initRegState) with
              Register ^"scause_code"      : Bit (Xlen - 1) <- (scause_code initRegState) with
              Register ^"stval"            : Bit Xlen <- (stval initRegState) with
              Register ^"satp_mode"        : Bit 4 <- (satp_mode initRegState) with
              Register ^"satp_asid"        : Bit 16 <- (satp_asid initRegState) with
              Register ^"satp_ppn"         : Bit 44 <- (satp_ppn initRegState) with

              (* user mode registers *)
              Register ^"uxl"              : XlenValue <- (uxl initRegState) with
              Register ^"upp"              : Bit 0 <- (upp initRegState) with (* Should be Bit 0, but this results in a system verilog error. 3.1.7 *)
              Register ^"upie"             : Bool <- (upie initRegState) with
              Register ^"uie"              : Bool <- (uie initRegState) with
              Register ^"utvec_mode"       : Bit 2 <- (utvec_mode initRegState) with
              Register ^"utvec_base"       : Bit (Xlen - 2)%nat <- (utvec_base initRegState) with
              Register ^"uscratch"         : Bit Xlen <- (uscratch initRegState) with
              Register ^"uepc"             : Bit Xlen <- (uepc initRegState) with
              Register ^"ucause_interrupt" : Bool <- (ucause_interrupt initRegState) with
              Register ^"ucause_code"      : Bit (Xlen - 1) <- (ucause_code initRegState) with
              Register ^"utval"            : Bit Xlen <- (utval initRegState) with

              (* preformance monitor registers *)
              Register ^"mtime"           : Bit 64 <- (mtime initRegState) with
              Register ^"mtimecmp"        : Bit 64 <- (mtimecmp initRegState) with
              Register ^"mcounteren"      : Bit 32 <- (mcounteren initRegState) with
              Register ^"scounteren"      : Bit 32 <- (scounteren initRegState) with
              Register ^"mcycle"          : Bit 64 <- (mcycle initRegState) with
              Register ^"minstret"        : Bit 64 <- (minstret initRegState) with
              Register ^"mcountinhibit_cy" : Bool <- (mcountinhibit_cy initRegState) with
              Register ^"mcountinhibit_tm" : Bool <- (mcountinhibit_tm initRegState) with
              Register ^"mcountinhibit_ir" : Bool <- (mcountinhibit_ir initRegState) with

              (* memory protection registers. *)
              Register ^"pmp0cfg" : Bit 8 <- (pmp0cfg initRegState) with
              Register ^"pmp1cfg" : Bit 8 <- (pmp1cfg initRegState) with
              Register ^"pmp2cfg" : Bit 8 <- (pmp2cfg initRegState) with
              Register ^"pmp3cfg" : Bit 8 <- (pmp3cfg initRegState) with
              Register ^"pmp4cfg" : Bit 8 <- (pmp4cfg initRegState) with
              Register ^"pmp5cfg" : Bit 8 <- (pmp5cfg initRegState) with
              Register ^"pmp6cfg" : Bit 8 <- (pmp6cfg initRegState) with
              Register ^"pmp7cfg" : Bit 8 <- (pmp7cfg initRegState) with
              Register ^"pmp8cfg" : Bit 8 <- (pmp8cfg initRegState) with
              Register ^"pmp9cfg" : Bit 8 <- (pmp9cfg initRegState) with
              Register ^"pmp10cfg" : Bit 8 <- (pmp10cfg initRegState) with
              Register ^"pmp11cfg" : Bit 8 <- (pmp11cfg initRegState) with
              Register ^"pmp12cfg" : Bit 8 <- (pmp12cfg initRegState) with
              Register ^"pmp13cfg" : Bit 8 <- (pmp13cfg initRegState) with
              Register ^"pmp14cfg" : Bit 8 <- (pmp14cfg initRegState) with
              Register ^"pmp15cfg" : Bit 8 <- (pmp15cfg initRegState) with
              Register ^"pmpaddr0" : Bit 54 <- (pmpaddr0 initRegState) with
              Register ^"pmpaddr1" : Bit 54 <- (pmpaddr1 initRegState) with
              Register ^"pmpaddr2" : Bit 54 <- (pmpaddr2 initRegState) with
              Register ^"pmpaddr3" : Bit 54 <- (pmpaddr3 initRegState) with
              Register ^"pmpaddr4" : Bit 54 <- (pmpaddr4 initRegState) with
              Register ^"pmpaddr5" : Bit 54 <- (pmpaddr5 initRegState) with
              Register ^"pmpaddr6" : Bit 54 <- (pmpaddr6 initRegState) with
              Register ^"pmpaddr7" : Bit 54 <- (pmpaddr7 initRegState) with
              Register ^"pmpaddr8" : Bit 54 <- (pmpaddr8 initRegState) with
              Register ^"pmpaddr9" : Bit 54 <- (pmpaddr9 initRegState) with
              Register ^"pmpaddr10" : Bit 54 <- (pmpaddr10 initRegState) with
              Register ^"pmpaddr11" : Bit 54 <- (pmpaddr11 initRegState) with
              Register ^"pmpaddr12" : Bit 54 <- (pmpaddr12 initRegState) with
              Register ^"pmpaddr13" : Bit 54 <- (pmpaddr13 initRegState) with
              Register ^"pmpaddr14" : Bit 54 <- (pmpaddr14 initRegState) with
              Register ^"pmpaddr15" : Bit 54 <- (pmpaddr15 initRegState) with
                  
              (* Stale memory execution exception register *)
              Register ^"exception" : Bool <- ConstBool false with
              Register ^"stales": Array memSz Bool <- ConstArray (fun _ => ConstBool false) with

              Rule ^"trap_interrupt"
                := Read mode : PrivMode <- ^"mode";
                   Read pc : VAddr <- ^"pc";
                   LETA xlen : XlenValue <- readXlen name #mode;
                   System [DispString _ "[trap_interrupt]\n"];
                   interruptAction name Xlen_over_8 #xlen #mode #pc with
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
                := LETA cfg_pkt <- readConfig name _ supportedExts;
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
                     <- fetch name Xlen_over_8 (mem_regions _) (#cfg_pkt @% "xlen") (#cfg_pkt @% "mode") #pc;
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
                   LETA csr_update_pkt
                     :  PktWithException ExecUpdPkt
                     <- CsrUnit
                          name
                          Clen_over_8
                          #mcounteren
                          #scounteren
                          #pc
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
                     <- MemUnit name mem_params
                          (mem_regions _)
                          (#cfg_pkt @% "xlen")
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
                          memSz
                          #pc
                          (#decoder_pkt @% "fst" @% "inst")
                          #cfg_pkt
                          (#exec_context_pkt @% "fst")
                          (#mem_update_pkt @% "fst")
                          (#mem_update_pkt @% "snd");
                   System [DispString _ "Inc PC\n"];
                   Call ^"pc"(#pc: VAddr); (* for test verification *)
                   Retv with
              Rule ^"haltOnException"
                   :=
                     (* If we are about to execute a stale memory
                      region, flip the exception register and call the
                      exception method *)
                     Read mode : PrivMode <- ^"mode";
                     Read pc : VAddr <- ^"pc";
                     LETA pcPaddr  :  Maybe PAddr <- memTranslate #mode #pc;
                     If #pcPaddr @% "valid" then 
                     (LETA stale: Bool <- staleP (SignExtendTruncLsb (Nat.log2_up memSz) (#pcPaddr @% "data": _));
                      If #stale then (Write ^"exception" <- $$ true;
                                      Retv);
                      Retv);
                     Read exc: Bool <- ^"exception";
                     If #exc then (Call ^"exception" (); Retv);
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

    Definition memRegFile
       :  RegFileBase :=
       @Build_RegFileBase
         true
         Rlen_over_8
         (^"mem_reg_file")
         (Async [^"readMem1"; ^"readMem2"; ^"readMem3"; ^"readMem4"; ^"readMem5"; ^"readMem6"])
         (^"writeMem")
         (pow2 lgMemSz)
         (Bit 8)
         (RFFile true true "testfile" 0 (pow2 lgMemSz) initMemMap).

    Definition processor'
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
             ^"readMem1"; (* fetch *)
             ^"readMem2"; (* fetch *)
             ^"readMem3"; (* load instructions *)
             ^"readMem4"; (* page table walker read mem call *)
             ^"readMem5"; (* page table walker read mem call *)
             ^"readMem6"; (* page table walker read mem call *)
             ^"readMemReservation";
             ^"writeMem";
             ^"writeMemReservation"
           ].

    Local Close Scope list.

    Local Close Scope kami_expr.
    Local Close Scope kami_action.

  End model.
  
      Local Definition muraliRegState: RegState := 
      {|
          (* general context registers *)
          mode := ConstBit (natToWord 2 MachineMode);
          (* pc := ConstBit (wzero Xlen) with; *)
          pc := ConstBit (Xlen 'h"80000000");

          (* floating point registers *)
          fflags := ConstBit (natToWord FflagsWidth 0);
          frm := ConstBit (natToWord FrmWidth    0);

          (* machine mode registers *)
          mxl := initXlen;
          medeleg := ConstBit (wzero 16);
          mideleg := ConstBit (wzero 12);
          mprv := ConstBool false;
          mpp := ConstBit (wzero 2);
          mpie := ConstBool false;
          mie := ConstBool false;
          mtvec_mode := ConstBit (wzero 2);
          mtvec_base := ConstBit (natToWord (Xlen - 2)%nat 0);
          mscratch := ConstBit (wzero Xlen);
          mepc := ConstBit (wzero Xlen);
          mcause_interrupt := ConstBool false;
          mcause_code := ConstBit (natToWord (Xlen - 1) 0);
          mtval := ConstBit (wzero Xlen);

          mvendorid := ConstBit (wzero 32);
          marchid := ConstBit (wzero Xlen);
          mimpid := ConstBit (wzero Xlen);
          mhartid := ConstBit (wzero Xlen);

          usip := ConstBool false;
          ssip := ConstBool false;
          msip := ConstBool false;
          utip := ConstBool false;
          stip := ConstBool false;
          mtip := ConstBool false;
          ueip := ConstBool false;
          seip := ConstBool false;
          meip := ConstBool false;
          usie := ConstBool false;
          ssie := ConstBool false;
          msie := ConstBool false;
          utie := ConstBool false;
          stie := ConstBool false;
          mtie := ConstBool false;
          ueie := ConstBool false;
          seie := ConstBool false;
          meie := ConstBool false;

          (* supervisor mode registers *)
          sxl := initXlen;
          sedeleg := ConstBit (wzero 16);
          sideleg := ConstBit (wzero 16);
          tsr := ConstBool false;
          tw := ConstBool false;
          tvm := ConstBool false;
          mxr := ConstBool false;
          sum := ConstBool false;
          spp := ConstBit (wzero 1);
          spie := ConstBool false;
          sie := ConstBool false;
          stvec_mode := ConstBit (wzero 2);
          stvec_base := ConstBit (natToWord (Xlen - 2)%nat 0);
          sscratch := ConstBit (wzero Xlen);
          sepc := ConstBit (wzero Xlen);
          scause_interrupt := ConstBool false;
          scause_code := ConstBit (natToWord (Xlen - 1) 0);
          stval := ConstBit (wzero Xlen);
          satp_mode := ConstBit (wzero 4);
          satp_asid := ConstBit (wzero 16);
          satp_ppn := ConstBit (wzero 44);

          (* user mode registers *)
          uxl := initXlen;
          upp := ConstBit WO; (* Should be Bit 0, but this results in a system verilog error. 3.1.7 *)
          upie := ConstBool false;
          uie := ConstBool false;
          utvec_mode := ConstBit (wzero 2);
          utvec_base := ConstBit (natToWord (Xlen - 2)%nat 0);
          uscratch := ConstBit (wzero Xlen);
          uepc := ConstBit (wzero Xlen);
          ucause_interrupt := ConstBool false;
          ucause_code := ConstBit (natToWord (Xlen - 1) 0);
          utval := ConstBit (wzero Xlen);

          (* preformance monitor registers *)
          mtime := ConstBit (wzero 64);
          mtimecmp := ConstBit (wzero 64);
          mcounteren := ConstBit (wzero 32);
          scounteren := ConstBit (wzero 32);
          mcycle := ConstBit (wzero 64);
          minstret := ConstBit (wzero 64);

          (* memory protection registers. *)
          pmp0cfg := ConstBit (wzero 8);
          pmp1cfg := ConstBit (wzero 8);
          pmp2cfg := ConstBit (wzero 8);
          pmp3cfg := ConstBit (wzero 8);
          pmp4cfg := ConstBit (wzero 8);
          pmp5cfg := ConstBit (wzero 8);
          pmp6cfg := ConstBit (wzero 8);
          pmp7cfg := ConstBit (wzero 8);
          pmp8cfg := ConstBit (wzero 8);
          pmp9cfg := ConstBit (wzero 8);
          pmp10cfg := ConstBit (wzero 8);
          pmp11cfg := ConstBit (wzero 8);
          pmp12cfg := ConstBit (wzero 8);
          pmp13cfg := ConstBit (wzero 8);
          pmp14cfg := ConstBit (wzero 8);
          pmp15cfg := ConstBit (wzero 8);
          pmpaddr0 := ConstBit (wzero 54);
          pmpaddr1 := ConstBit (wzero 54);
          pmpaddr2 := ConstBit (wzero 54);
          pmpaddr3 := ConstBit (wzero 54);
          pmpaddr4 := ConstBit (wzero 54);
          pmpaddr5 := ConstBit (wzero 54);
          pmpaddr6 := ConstBit (wzero 54);
          pmpaddr7 := ConstBit (wzero 54);
          pmpaddr8 := ConstBit (wzero 54);
          pmpaddr9 := ConstBit (wzero 54);
          pmpaddr10 := ConstBit (wzero 54);
          pmpaddr11 := ConstBit (wzero 54);
          pmpaddr12 := ConstBit (wzero 54);
          pmpaddr13 := ConstBit (wzero 54);
          pmpaddr14 := ConstBit (wzero 54);
          pmpaddr15 := ConstBit (wzero 54);
          mcountinhibit_cy := ConstBool false;
          mcountinhibit_tm := ConstBool false;
          mcountinhibit_ir := ConstBool false;
      |}.

      Local Definition muraliMemory: MemState := fun _ => wzero _.

      Local Definition muraliProcState := {| regState := muraliRegState;
                                             memState := muraliMemory; |}.

      Definition processor (func_units : forall ty, list (FUEntry ty)) (supportedExts : ConstT (Extensions)) := processor' func_units supportedExts muraliProcState.
      
End Params.
