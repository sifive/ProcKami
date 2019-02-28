Require Import Kami.All FU CompressedInsts.
Require Import FpuKami.Definitions.
Require Import FpuKami.Classify.
Require Import FpuKami.Compare.
Require Import Fpu.
Require Import List.
Import ListNotations.

Section Params.
  Variable name: string.
  Local Notation "^ x" := (name ++ "_" ++ x)%string (at level 0).
  
  Variable Xlen_over_8: nat.
  Variable expWidthMinus2: nat.
  Variable sigWidthMinus2: nat.

  Local Notation Xlen := (8 * Xlen_over_8).
  Local Notation Data := (Bit Xlen).
  Local Notation VAddr := (Bit Xlen).
  Local Notation FUEntry := (FUEntry Xlen_over_8).
  Local Notation FetchPkt := (FetchPkt Xlen_over_8).
  Local Notation PktWithException := (PktWithException Xlen_over_8).
  Local Notation NF := (NF expWidthMinus2 sigWidthMinus2).
  Local Notation bitToNF := (bitToNF Xlen_over_8 expWidthMinus2 sigWidthMinus2).

  Section pipeline.
    Local Open Scope kami_action.
    Local Open Scope kami_expr.

    Variable func_units: forall ty, list (FUEntry ty).
    Variable mode : forall ty, PrivMode @# ty.
    Variable extensions : forall ty, Extensions @# ty.

    Definition dispNF ty (x : NF @# ty) := 
      [
        DispString ty "    isNaN: ";
        DispBool ((x @% "isNaN") : Bool @# ty) (1, Binary);
        DispString ty "\n";
        DispString ty "    signals?: ";
        DispBool ((isSigNaNRawFloat x) : Bool @# ty) (1, Binary);
        DispString ty "\n";
        DispString ty "    isInf: ";
        DispBool (x @% "isInf") (1, Binary);
        DispString ty "\n";
        DispString ty "    isZero: ";
        DispBool (x @% "isZero") (1, Binary);
        DispString ty "\n";
        DispString ty "    sign: ";
        DispBool (x @% "sign") (1, Binary);
        DispString ty "\n";
        DispString ty "    signed exponent: ";
        DispBit (x @% "sExp") (32, Binary);
        DispString ty "\n";
        DispString ty "    significand: 1.";
        DispBit (x @% "sig") (32, Binary);
        DispString ty "\n"
      ].

    Local Open Scope list.
    Definition pipeline 
      :  BaseModule
      := 
         MODULE {
              Register ^"pc" : VAddr <- ConstBit (_ 'h "00000000") with
              Rule ^"pipeline"
                := System
                     [
                       DispString _ "Start\n"
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
                     <- fetch name Xlen_over_8 (#pc);
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
                       DispBool (#fetch_pkt @% "snd" @% "valid") (32, Binary);
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
                       DispBool (#decoder_pkt @% "fst" @% "compressed?") (32, Decimal);
                       DispString _ "\n";
                       DispString _ "  Exception: ";
                       DispBool (#decoder_pkt @% "snd" @% "valid") (32, Binary);
                       DispString _ "\n"
                     ];
                   System [DispString _ "Reg Read\n"];
                   LETA exec_context_pkt
                     <- readerWithException name
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
                       DispString _ "  reg1: ";
                       DispString _ "    integer value: ";
                       DispBit (#exec_context_pkt @% "fst" @% "reg1") (32, Decimal);
                       DispString _ "\n";
                       DispString _ "    floating point value:\n"
                     ] ++
                     (dispNF (bitToNF (#exec_context_pkt @% "fst" @% "reg1"))) ++
                     [
                       DispString _ "\n";
                       DispString _ "  reg2: ";
                       DispString _ "    integer value: ";
                       DispBit (#exec_context_pkt @% "fst" @% "reg2") (32, Decimal);
                       DispString _ "\n";
                       DispString _ "    floating point value:\n"
                     ] ++
                     (dispNF (bitToNF (#exec_context_pkt @% "fst" @% "reg2"))) ++
                     [
                       DispString _ "\n";
                       DispString _ "  reg3: ";
                       DispString _ "    integer value: ";
                       DispBit (#exec_context_pkt @% "fst" @% "reg3") (32, Decimal);
                       DispString _ "\n";
                       DispString _ "    floating point value: "
                     ] ++
                     (dispNF (bitToNF (#exec_context_pkt @% "fst" @% "reg3"))) ++
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
                       DispBool (#exec_update_pkt @% "fst" @% "val1" @% "valid") (32, Decimal);
                       DispString _ "\n";
                       DispString _ "  val1: ";
                       DispString _ "    integer value: ";
                       DispBit (#exec_update_pkt @% "fst" @% "val1" @% "data" @% "data") (32, Decimal);
                       DispString _ "\n";
                       DispString _ "    floating point value: "
                     ] ++
                     (dispNF (bitToNF (#exec_update_pkt @% "fst" @% "val1" @% "data" @% "data"))) ++
                     [
                       DispString _ "\n";
                       DispString _ "  val1 tag: ";
                       DispBit (#exec_update_pkt @% "fst" @% "val1" @% "data" @% "tag") (32, Decimal);
                       DispString _ "\n";
                       DispString _ "  val2 valid: ";
                       DispBool (#exec_update_pkt @% "fst" @% "val2" @% "valid") (32, Decimal);
                       DispString _ "\n";
                       DispString _ "  val2: ";
                       DispString _ "    integer value: ";
                       DispBit (#exec_update_pkt @% "fst" @% "val2" @% "data" @% "data") (32, Decimal);
                       DispString _ "\n";
                       DispString _ "    floating point value: "
                     ] ++
                     (dispNF (bitToNF (#exec_update_pkt @% "fst" @% "val2" @% "data" @% "data"))) ++
                     [
                       DispString _ "\n";
                       DispString _ "  val2 tag: ";
                       DispBit (#exec_update_pkt @% "fst" @% "val2" @% "data" @% "tag") (32, Decimal);
                       DispString _ "\n";
                       DispString _ "  taken: ";
                       DispBool (#exec_update_pkt @% "fst" @% "taken?") (32, Decimal);
                       DispString _ "\n";
                       DispString _ "  Exception: ";
                       DispBool (#exec_update_pkt @% "snd" @% "valid") (32, Binary);
                       DispString _ "\n"
                     ]);
                   (* TODO: Add CSR Read operation here. CSR reads have side effects that register file reads do not. The spec requires that CSR reads not occur if the destination register is X0. *)
                   System [DispString _ "Mem\n"];
                   LETA mem_update_pkt
                     <- MemUnit name
                          ["mem"; "amo32"; "amo64"; "lrsc32"; "lrsc64"]
                          (#decoder_pkt @% "fst")
                          (#exec_context_pkt @% "fst")
                          (#exec_update_pkt);
                   System
                     ([
                       DispString _ "New Reg Vals (after memory ops)\n";
                       DispString _ "  val1: ";
                       DispString _ "    integer value: ";
                       DispBit (#mem_update_pkt @% "fst" @% "val1" @% "data" @% "data") (32, Decimal);
                       DispString _ "\n";
                       DispString _ "    floating point value: "
                     ] ++
                     (dispNF (bitToNF (#mem_update_pkt @% "fst" @% "val1" @% "data" @% "data"))) ++
                     [
                       DispString _ "\n";
                       DispString _ "  val1 tag: ";
                       DispBit (#mem_update_pkt @% "fst" @% "val1" @% "data" @% "tag") (32, Decimal);
                       DispString _ "\n";
                       DispString _ "  val2: ";
                       DispString _ "    integer value: ";
                       DispBit (#mem_update_pkt @% "fst" @% "val2" @% "data" @% "data") (32, Decimal);
                       DispString _ "\n";
                       DispString _ "    floating point value: "
                     ] ++ 
                     (dispNF (bitToNF (#mem_update_pkt @% "fst" @% "val2" @% "data" @% "data"))) ++
                     [
                       DispString _ "\n";
                       DispString _ "  val2 tag: ";
                       DispBit (#mem_update_pkt @% "fst" @% "val2" @% "data" @% "tag") (32, Decimal);
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
                          (#pc)
                          (#decoder_pkt @% "fst" @% "inst")
                          (#mem_update_pkt)
                          (#exec_context_pkt @% "fst");
                   System [DispString _ "Inc PC\n"];
                   Write ^"pc"
                     :  VAddr
                     <- (let opt_val1
                          :  Maybe (RoutedReg Xlen_over_8) @# _
                          := #exec_update_pkt @% "fst" @% "val1" in
                        let opt_val2
                          :  Maybe (RoutedReg Xlen_over_8) @# _
                          := #exec_update_pkt @% "fst" @% "val2" in
                        ITE
                          ((opt_val1 @% "valid") && ((opt_val1 @% "data") @% "tag" == $PcTag))
                          ((opt_val1 @% "data") @% "data")
                          (ITE
                            ((opt_val2 @% "valid") && ((opt_val2 @% "data") @% "tag" == $PcTag))
                            ((opt_val2 @% "data") @% "data")
                            (ITE
                              (#decoder_pkt @% "fst" @% "compressed?")
                              (#pc + $2)
                              (#pc + $4))));
                   Call ^"pc"(#pc: VAddr);
                   Retv
         }.
    Local Close Scope list.

    Local Close Scope kami_expr.
    Local Close Scope kami_action.

  End pipeline.
End Params.
