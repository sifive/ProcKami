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
    Variable mode       : forall ty, PrivMode @# ty.
    Variable extensions : forall ty, Extensions @# ty.

    Section display.
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

      Definition dispNF (prefix : string) (xlen : nat) (x : Bit xlen @# ty)
        := let y
             :  NF expWidthMinus2 sigWidthMinus2 @# ty
             := bitToNF (ZeroExtendTruncLsb len x) in
           [
             DispString _ prefix;
             DispStruct y
               (Vector.nth [
                  (1, Binary);  (* isNaN *)
                  (1, Binary);  (* isInf *)
                  (1, Binary);  (* isZero *)
                  (1, Binary);  (* sign *)
                  (32, Binary); (* sExp *)
                  (32, Binary)  (* sig *)
                ]%vector);
             DispString _ "= 1.";
             DispBit (y @% "sig") (32, Binary);
             DispString _ "b*2^";
             DispBit (y @% "sExp") (32, Decimal);
             DispString _ "\n"
           ].

    End display.

    Local Open Scope list.
    Definition processorCore 
      :  BaseModule
      := 
         MODULE {
              Register ^"pc" : VAddr <- ConstBit (_ 'h "00000000") with
              Rule ^"pipeline"
                := System
                     [
                       DispString _ "Start\n";
                       DispString _ "XLEN_over_8: ";
                       DispBit (Const _ (natToWord 32 Xlen_over_8)) (32, Decimal);
                       DispString _ "\n";
                       DispString _ "XLEN: ";
                       DispBit (Const _ (natToWord 32 Xlen)) (32, Decimal);
                       DispString _ "\n";
                       DispString _ "RLEN_over_8: ";
                       DispBit (Const _ (natToWord 32 Rlen_over_8)) (32, Decimal);
                       DispString _ "\n";
                       DispString _ "RLEN: ";
                       DispBit (Const _ (natToWord 32 Rlen)) (32, Decimal);
                       DispString _ "\n"
                     ];
                   Read pc : VAddr <- ^"pc";
                   System
                     [
                       DispString _ "Fetch\n";
                       DispString _ "  Fetched: ";
                       DispBit (#pc) (32, Hex);
                       DispString _ "\n"
                     ];
                   LETA fetch_pkt
                     :  PktWithException FetchPkt
                     <- fetch name lgMemSz Xlen_over_8 Rlen_over_8 (#pc);
                   System
                     [
                       DispString _ "Fetched\n";
                       DispString _ "  Inst: ";
                       DispBit (#fetch_pkt @% "fst" @% "inst") (32, Binary);
                       DispString _ "\n";
                       DispString _ "  InstHex: ";
                       DispBit (#fetch_pkt @% "fst" @% "inst") (32, Hex);
                       DispString _ "\n";
                       DispString _ "  Exception: ";
                       DispBool (#fetch_pkt @% "snd" @% "valid") (1, Binary);
                       DispString _ "\n"
                     ];
                   System [DispString _ "Decoder\n"];
                   LETA decoder_pkt
                     <- convertLetExprSyntax_ActionT
                          (decoderWithException (func_units _) (CompInstDb _) (extensions _) (mode _)
                            (RetE (#fetch_pkt)));
                   System
                     [
                       DispString _ "Decode Pkt\n";
                       DispString _ "  func unit id: ";
                       DispBit (#decoder_pkt @% "fst" @% "funcUnitTag") (32, Decimal);
                       DispString _ "\n";
                       DispString _ "  inst id: ";
                       DispBit (#decoder_pkt @% "fst" @% "instTag") (32, Decimal);
                       DispString _ "\n";
                       DispString _ "  inst: ";
                       DispBit (#decoder_pkt @% "fst" @% "inst") (32, Binary);
                       DispString _ "\n";
                       DispString _ "  compressed: ";
                       DispBool (#decoder_pkt @% "fst" @% "compressed?") (1, Binary);
                       DispString _ "\n";
                       DispString _ "  Exception: ";
                       DispBool (#decoder_pkt @% "snd" @% "valid") (1, Binary);
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
                          (#decoder_pkt);
                   System
                     ([
                       DispString _ "Reg Vals\n";
                       DispString _ "  reg1:\n";
                       DispString _ "    integer value: ";
                       DispBit (#exec_context_pkt @% "fst" @% "reg1") (Xlen, Hex);
                       DispString _ "\n"
                     ] ++
                     (dispNF "    floating point value: " (#exec_context_pkt @% "fst" @% "reg1")) ++
                     [
                       DispString _ "\n";
                       DispString _ "  reg2:\n";
                       DispString _ "    integer value: ";
                       DispBit (#exec_context_pkt @% "fst" @% "reg2") (Xlen, Hex);
                       DispString _ "\n"
                     ] ++
                     (dispNF "    floating point value: " (#exec_context_pkt @% "fst" @% "reg2")) ++
                     [
                       DispString _ "\n";
                       DispString _ "  reg3:\n";
                       DispString _ "    integer value: ";
                       DispBit (#exec_context_pkt @% "fst" @% "reg3") (Xlen, Hex);
                       DispString _ "\n"
                     ] ++
                     (dispNF "    floating point value: " (#exec_context_pkt @% "fst" @% "reg3")) ++
                     [
                       DispString _ "\n";
                       DispString _ "  csr: ";
                       DispBit (#exec_context_pkt @% "fst" @% "csr" @% "data") (32, Decimal); 
                       DispString _ "\n";
                       DispString _ "  csr valid?: ";
                       DispBool (#exec_context_pkt @% "fst" @% "csr" @% "valid") (1, Binary); 
                       DispString _ "\n";
                       DispString _ "  Exception: ";
                       DispBool (#exec_context_pkt @% "snd" @% "valid") (32, Binary);
                       DispString _ "\n"
                     ]);
                   System [DispString _ "Trans\n"];
                   LETA trans_pkt
                     <- convertLetExprSyntax_ActionT
                          (transWithException
                            (#decoder_pkt @% "fst")
                            (#exec_context_pkt));
                   System [DispString _ "Executor\n"];
                   LETA exec_update_pkt
                     <- convertLetExprSyntax_ActionT
                          (execWithException (#trans_pkt));
                   System
                     ([
                       DispString _ "New Reg Vals\n";
                       DispString _ "  PC tag: ";
                       DispBit (Const _ (natToWord 32 PcTag)) (32, Decimal);
                       DispString _ "\n";
                       DispString _ "  val1 valid: ";
                       DispBool (#exec_update_pkt @% "fst" @% "val1" @% "valid") (1, Decimal);
                       DispString _ "\n";
                       DispString _ "  val1 tag: ";
                       DispBit (#exec_update_pkt @% "fst" @% "val1" @% "data" @% "tag") (32, Decimal);
                       DispString _ "\n";
                       DispString _ "  val1:\n";
                       DispString _ "    integer value: ";
                       DispBit (#exec_update_pkt @% "fst" @% "val1" @% "data" @% "data") (Xlen, Hex);
                       DispString _ "\n"
                     ] ++
                     (dispNF "    floating point value: " (#exec_update_pkt @% "fst" @% "val1" @% "data" @% "data")) ++
                     [
                       DispString _ "\n";
                       DispString _ "  val2 valid: ";
                       DispBool (#exec_update_pkt @% "fst" @% "val2" @% "valid") (1, Decimal);
                       DispString _ "\n";
                       DispString _ "  val2 tag: ";
                       DispBit (#exec_update_pkt @% "fst" @% "val2" @% "data" @% "tag") (32, Decimal);
                       DispString _ "\n";
                       DispString _ "  val2:\n";
                       DispString _ "    integer value: ";
                       DispBit (#exec_update_pkt @% "fst" @% "val2" @% "data" @% "data") (Xlen, Hex);
                       DispString _ "\n"
                     ] ++
                     (dispNF "    floating point value: " (#exec_update_pkt @% "fst" @% "val2" @% "data" @% "data")) ++
                     [
                       DispString _ "\n";
                       DispString _ "  taken: ";
                       DispBool (#exec_update_pkt @% "fst" @% "taken?") (1, Decimal);
                       DispString _ "\n";
                       DispString _ "  Exception: ";
                       DispBool (#exec_update_pkt @% "snd" @% "valid") (32, Binary);
                       DispString _ "\n"
                     ]);
                   (* TODO: Add CSR Read operation here. CSR reads have side effects that register file reads do not. The spec requires that CSR reads not occur if the destination register is X0. *)
                   System [DispString _ "Mem\n"];
                   LETA mem_update_pkt
                     <- MemUnit name lgMemSz
                          ["mem"; "amo32"; "amo64"; "lrsc32"; "lrsc64"]
                          (#decoder_pkt @% "fst")
                          (#exec_context_pkt @% "fst")
                          (#exec_update_pkt);
                   System
                     ([
                       DispString _ "New Reg Vals (after memory ops)\n";
                       DispString _ "  val1:\n";
                       DispString _ "    integer value: ";
                       DispBit (#mem_update_pkt @% "fst" @% "val1" @% "data" @% "data") (Xlen, Hex);
                       DispString _ "\n";
                       DispString _ "  val1 tag: ";
                       DispBit (#mem_update_pkt @% "fst" @% "val1" @% "data" @% "tag") (32, Decimal);
                       DispString _ "\n"
                     ] ++
                     (dispNF "    floating point value: " (#mem_update_pkt @% "fst" @% "val1" @% "data" @% "data")) ++
                     [
                       DispString _ "\n";
                       DispString _ "  val2:\n";
                       DispString _ "    integer value: ";
                       DispBit (#mem_update_pkt @% "fst" @% "val2" @% "data" @% "data") (Xlen, Hex);
                       DispString _ "\n";
                       DispString _ "  val2 tag: ";
                       DispBit (#mem_update_pkt @% "fst" @% "val2" @% "data" @% "tag") (32, Decimal);
                       DispString _ "\n"
                     ] ++ 
                     (dispNF "    floating point value: " (#mem_update_pkt @% "fst" @% "val2" @% "data" @% "data")) ++
                     [
                       DispString _ "\n";
                       DispString _ "  Exception: ";
                       DispBool (#mem_update_pkt @% "snd" @% "valid") (32, Binary);
                       DispString _ "\n"
                     ]);
                   (* TODO: the call to commit currently ignores any exceptions propogated through mem_update_pkt. *)
                   System [DispString _ "Reg Write\n"];
                   LETA commit_pkt
                     :  Void
                     <- commit
                          name
                          Flen_over_8
                          (#pc)
                          (#decoder_pkt @% "fst" @% "inst")
                          (#mem_update_pkt)
                          (#exec_context_pkt @% "fst");
                   System [DispString _ "Inc PC\n"];
                   Write ^"pc"
                     :  VAddr
                     <- (let opt_val1
                          (* :  Maybe (RoutedReg Rlen_over_8) @# _ *)
                          := #exec_update_pkt @% "fst" @% "val1" in
                        let opt_val2
                          (* :  Maybe (RoutedReg Rlen_over_8) @# _ *)
                          := #exec_update_pkt @% "fst" @% "val2" in
                        ITE
                          ((opt_val1 @% "valid") && ((opt_val1 @% "data") @% "tag" == $PcTag))
                          (ZeroExtendTruncLsb Xlen ((opt_val1 @% "data") @% "data"))
                          (ITE
                            ((opt_val2 @% "valid") && ((opt_val2 @% "data") @% "tag" == $PcTag))
                            (ZeroExtendTruncLsb Xlen ((opt_val2 @% "data") @% "data"))
                            (ITE
                              (#decoder_pkt @% "fst" @% "compressed?")
                              (#pc + $2)
                              (#pc + $4))));
                   Call ^"pc"(#pc: VAddr);
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
    
    Definition csrRegFile
      :  RegFileBase
      := @Build_RegFileBase 
           false
           1
           (^"csr_reg_file")
           (Async [(^"read_csr_0"); (^"read_csr_1"); (^"read_csr_2"); (^"read_csr_3")])
           (^"write_csr")
           (pow2 CsrIdWidth)
           CsrValue
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
                 csrRegFile;
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
             ^"read_csr_0";
             ^"read_csr_1";
             ^"read_csr_2";
             ^"read_csr_3";
             ^"write_csr";
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
