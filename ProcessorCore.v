(*
  This module integrates the processor components defined in FU.v
  into a single pipeline processor model.
*)

Require Import Kami.All FU CompressedInsts.
Require Import FpuKami.Definitions.
Require Import FpuKami.Classify.
Require Import FpuKami.Compare.
Require Import Vector.
Import VectorNotations.
Require Import List.
Import ListNotations.

Section Params.
  Variable name: string.
  Local Notation "^ x" := (name ++ "_" ++ x)%string (at level 0).

  Variable lgMemSz: nat.
  Variable Xlen_over_8: nat.
  Variable Flen_over_8: nat.
  Variable Rlen_over_8: nat.
  Local Notation Rlen := (Rlen_over_8 * 8).
  Local Notation Xlen := (Xlen_over_8 * 8).
  Local Notation Flen := (Flen_over_8 * 8).
  Local Notation Data := (Bit Rlen).
  Local Notation VAddr := (Bit Xlen).
  Local Notation FUEntry := (FUEntry Xlen_over_8 Rlen_over_8).
  Local Notation FetchPkt := (FetchPkt Xlen_over_8).
  Local Notation PktWithException := (PktWithException Xlen_over_8).

  Section model.
    Local Open Scope kami_action.
    Local Open Scope kami_expr.

    Variable func_units : forall ty, list (FUEntry ty).
    (* Variable mode       : forall ty, PrivMode @# ty. *)
    Variable supportedExts : ConstT (Extensions).

    Section Display.
      Variable ty : Kind -> Type.

      Local Definition expWidthMinus2
        :  nat
        := if Nat.eqb Flen_over_8 8
             then 9
             else 6.

      Local Definition sigWidthMinus2
        :  nat
        := if Nat.eqb Flen_over_8 8
             then 51
             else 22.

      Local Notation len := ((expWidthMinus2 + 1 + 1) + (sigWidthMinus2 + 1 + 1))%nat.

      Local Definition bitToFN (x : Bit len @# ty)
        :  FN expWidthMinus2 sigWidthMinus2 @# ty
        := unpack (FN expWidthMinus2 sigWidthMinus2) (ZeroExtendTruncLsb (size (FN expWidthMinus2 sigWidthMinus2)) x).

      Local Definition bitToNF (x : Bit len @# ty)
        :  NF expWidthMinus2 sigWidthMinus2 @# ty
        := getNF_from_FN (bitToFN x).

      Definition DispNF (prefix : string) (xlen : nat) (x : Bit xlen @# ty)
        := let y
             :  NF expWidthMinus2 sigWidthMinus2 @# ty
             := bitToNF (ZeroExtendTruncLsb len x) in
           [
             DispString _ prefix;
             DispBinary y;
             DispString _ "\n"
           ].

    End Display.

    Definition initXlen
      := ConstBit
           (natToWord XlenWidth
              (if Nat.eqb Xlen_over_8 4
                 then 1
                 else 2)).

    Local Open Scope list.
    Definition processorCore 
      :  BaseModule
      := MODULE {
              (* general context registers *)
              Register ^"mode"             : PrivMode <- ConstBit (natToWord 2 MachineMode) with
              Register ^"extensions"       : Extensions  <- supportedExts with
              Register ^"pc"               : VAddr       <- ConstBit (_ 'h "00000000") with

              (* floating point registers *)
              Register ^"fflags"           : FflagsValue <- ConstBit (natToWord FflagsWidth 0) with
              Register ^"frm"              : FrmValue    <- ConstBit (natToWord FrmWidth    0) with

              (* machine mode registers *)
              Register ^"mxl"              : XlenValue    <- initXlen with
              Register ^"mpp"              : Bit 2 <- ConstBit (natToWord 2 0) with
              Register ^"mpie"             : Bit 1 <- ConstBit (natToWord 1 0) with
              Register ^"mie"              : Bit 1 <- ConstBit (natToWord 1 0) with
              Register ^"mtvec_mode"       : Bit 2 <- ConstBit (natToWord 2 0) with
              Register ^"mtvec_base"       : Bit (Xlen - 2)%nat <- ConstBit (natToWord (Xlen - 2)%nat 0) with
              Register ^"mscratch"         : Bit Xlen <- ConstBit (natToWord Xlen 0) with
              Register ^"mepc"             : Bit Xlen <- ConstBit (natToWord Xlen 0) with
              Register ^"mcause_interrupt" : Bit 1 <- ConstBit (natToWord 1 0) with
              Register ^"mcause_code"      : Bit (Xlen - 1) <- ConstBit (natToWord (Xlen - 1) 0) with
              Register ^"mtval"            : Bit Xlen <- ConstBit (natToWord Xlen 0) with

              (* supervisor mode registers *)
              Register ^"sxl"              : XlenValue <- initXlen with
              Register ^"spp"              : Bit 1 <- ConstBit (natToWord 1 0) with
              Register ^"spie"             : Bit 1 <- ConstBit (natToWord 1 0) with
              Register ^"sie"              : Bit 1 <- ConstBit (natToWord 1 0) with
              Register ^"stvec_mode"       : Bit 2 <- ConstBit (natToWord 2 0) with
              Register ^"stvec_base"       : Bit (Xlen - 2)%nat <- ConstBit (natToWord (Xlen - 2)%nat 0) with
              Register ^"sscratch"         : Bit Xlen <- ConstBit (natToWord Xlen 0) with
              Register ^"sepc"             : Bit Xlen <- ConstBit (natToWord Xlen 0) with
              Register ^"scause_interrupt" : Bit 1 <- ConstBit (natToWord 1 0) with
              Register ^"scause_code"      : Bit (Xlen - 1) <- ConstBit (natToWord (Xlen - 1) 0) with
              Register ^"stval"            : Bit Xlen <- ConstBit (natToWord Xlen 0) with

              (* user mode registers *)
              Register ^"uxl"              : XlenValue <- initXlen with
              Register ^"upp"              : Bit 1 <- ConstBit (natToWord 1 0) with
              Register ^"upie"             : Bit 1 <- ConstBit (natToWord 1 0) with
              Register ^"uie"              : Bit 1 <- ConstBit (natToWord 1 0) with
              Register ^"utvec_mode"       : Bit 2 <- ConstBit (natToWord 2 0) with
              Register ^"utvec_base"       : Bit (Xlen - 2)%nat <- ConstBit (natToWord (Xlen - 2)%nat 0) with
              Register ^"uscratch"         : Bit Xlen <- ConstBit (natToWord Xlen 0) with
              Register ^"uepc"             : Bit Xlen <- ConstBit (natToWord Xlen 0) with
              Register ^"ucause_interrupt" : Bit 1 <- ConstBit (natToWord 1 0) with
              Register ^"ucause_code"      : Bit (Xlen - 1) <- ConstBit (natToWord (Xlen - 1) 0) with
              Register ^"utval"            : Bit Xlen <- ConstBit (natToWord Xlen 0) with
              Rule ^"pipeline"
                := LETA cfg_pkt <- readConfig name _;
                   Write ^"extensions"
                     :  Extensions
                     <- #cfg_pkt @% "extensions";
                   Read pc : VAddr <- ^"pc";
                   System
                     [
                       DispString _ "PC:";
                       DispHex #pc;
                       DispString _ "\n"
                     ];
                   LETA fetch_pkt
                     :  PktWithException FetchPkt
                     <- fetch name lgMemSz Xlen_over_8 Rlen_over_8 (#cfg_pkt @% "xlen") (#pc);
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
                       DispDecimal #decoder_pkt;
                       DispString _ "\n"
                     ];
                   System [DispString _ "Reg Read\n"];
                   LETA exec_context_pkt
                     <- readerWithException name Flen_over_8
                          (ITE
                            (#fetch_pkt @% "snd" @% "valid")
                            ((#fetch_pkt @% "snd" @% "data" @% "exception") == $InstAddrMisaligned)
                            $$(false))
                          (* TODO: does fetch raise this exception? *)
                          (ITE
                            (#fetch_pkt @% "snd" @% "valid")
                            ((#fetch_pkt @% "snd" @% "data" @% "exception") == $LoadAddrMisaligned)
                            $$(false))
                          (ITE
                            (#fetch_pkt @% "snd" @% "valid")
                            ((#fetch_pkt @% "snd" @% "data" @% "exception") == $InstAccessFault)
                            $$(false))
                          (#cfg_pkt @% "xlen")
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
                   LETA mem_update_pkt
                     <- MemUnit name lgMemSz
                          ["mem"; "amo32"; "amo64"; "lrsc32"; "lrsc64"]
                          (#cfg_pkt @% "xlen")
                          (#decoder_pkt @% "fst")
                          (#exec_context_pkt @% "fst")
                          (#exec_update_pkt);
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
(*
                          (STRUCT {
                             "xlen"         ::= #cfg_pkt @% "xlen";
                             "mode"        ::= #decoder_pkt @% "fst" @% "mode";
                             "compressed?" ::= #decoder_pkt @% "fst" @% "compressed?"
                           } : ContextCfgPkt @# _)
*)
                          #cfg_pkt
                          (#exec_context_pkt @% "fst")
                          #mem_update_pkt;
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
    
    Definition memRegFile
      :  RegFileBase
      := @Build_RegFileBase
           true
           Rlen_over_8
           (^"mem_reg_file")
           (Async [^"readMem1"; ^"readMem2"])
           (^"writeMem")
           (pow2 20)
           (Bit 8)
           (RFFile true true "testfile" (fun _ => wzero _)).

    Definition memReservationRegFile
      :  RegFileBase
      := @Build_RegFileBase
           true
           Rlen_over_8
           (^"memReservation_reg_file")
           (Async [^"readMemReservation"])
           (^"writeMemReservation")
           (pow2 20)
           Bool
           (RFNonFile _ (Some (ConstBool false))).

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
             ^"readMem1";
             ^"readMem2";
             ^"readMemReservation";
             ^"writeMem";
             ^"writeMemReservation"
           ].  

    Definition model
      := getRtlSafe processor.

    Local Close Scope list.

    Local Close Scope kami_expr.
    Local Close Scope kami_action.

  End model.
End Params.
