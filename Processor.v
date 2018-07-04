Require Import Kami.Syntax Decode Control Execute bbv.HexNotationWord.


Section Process.
    Definition MemCtrl := STRUCT {
        "memOp"  :: Bit 2  ;
        "memAdr" :: Bit 64 ;
        "memDat" :: Bit 64
    }.
    Definition RFCtrl := STRUCT {
        "werf"   :: Bool   ;
        "rd"     :: Bit 5  ;
        "rd_val" :: Bit 64
    }.
    Open Scope kami_expr.
    Definition Processor :=
        MODULE {
            Register "pc" : (Bit 64) <- (64'h"10000000") with
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
                                       "memOp"  ::= #ctrlSig @% "memOp";
                                       "memAdr" ::= #eInst @% "memAdr";
                                       "memDat" ::= #eInst @% "memDat"
                                     };
                Call  memResp : _ <- "memAction"(#memCtrl : _);
                LETA  update      <- Execute2_action #ctrlSig #csr_val #eInst #memResp;
                LET   rfCtrl      <- STRUCT {
                                       "werf"   ::= #ctrlSig @% "werf";
                                       "rd"     ::= #dInst @% "rd";
                                       "rd_val" ::= #update @% "new_rd"
                                     };
                Call                 "rfWrite"(#rfCtrl : _);
                Write "pc"        <- #update @% "new_pc";
            Retv
        }.
End Process.
