Require Import Kami.Syntax Decode Control Execute.

Section Process.
    Definition MemCtrl := STRUCT {
        "memWrEn" :: Bool   ;
        "memAdr"  :: Bit 64 ;
        "memDat"  :: Bit 64
    }.
    Open Scope kami_expr.
    Definition Processor :=
        MODULE {
            Register "pc" : (Bit 64) <- (natToWord 64 0) with
            Rule "step" :=
                Read  pc      : _ <- "pc";
                Call  instr   : _ <- "getInstr"(#pc : _);
                LETA  dInst       <- Decode_action #instr ;
                LETA  ctrlSig     <- Control_action #dInst ;
                Call  rs1_val : _ <- "rfRead1"(#dInst @% "rs1" : _);
                Call  rs2_val : _ <- "rfRead2"(#dInst @% "rs2" : _);
                LET   csr_val     <- $$ (natToWord 64 0);
                LETA  eInst       <- Execute1_action #pc #dInst #ctrlSig #rs1_val #rs2_val #csr_val;
                LET   memCtrl     <- STRUCT {
                                       "memWrEn" ::= (#ctrlSig @% "memOp" == $$ Mem_store);
                                       "memAdr"  ::= #eInst @% "memAdr";
                                       "memDat"  ::= #eInst @% "memDat"
                                     };

                If (#ctrlSig @% "memOp" != $$ Mem_off) then (Call  memResp : _ <- "memAction"(#memCtrl : _);
                                                            Ret #memResp)
                                                       else Ret $$ (natToWord 64 0) as memResp;

                LETA  update      <- Execute2_action #ctrlSig #csr_val #eInst #memResp;
                LET   rfCtrl      <- STRUCT {
                                       "addr" ::= #dInst @% "rd";
                                       "data" ::= #update @% "new_rd"
                                     };
                If (#ctrlSig @% "werf") then Call "rfWrite"(#rfCtrl : _);
                                             Retv
                                        else Retv;
                Write "pc"        <- #update @% "new_pc";
                Retv
        }.
End Process.

Require Import Kami.Compile Kami.Extraction.

Open Scope string.
Definition rtlMod := getRtl (nil, (RegFile "RF"
                                           ("rfRead1" :: "rfRead2" :: nil)
                                           "rfWrite"
                                           32
                                           (Some (ConstBit (natToWord 64 0))) :: nil,
                                   Processor)).
Close Scope string.

Extraction "Target.hs" rtlMod size RtlModule WriteRegFile.
