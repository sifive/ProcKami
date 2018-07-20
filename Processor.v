Require Import Kami.Syntax Kami.Extraction Decode Control Execute Status.

Section Process.
    Definition MemReq := STRUCT {
        "memOp"   :: Bit 2  ;
        "memMask" :: Bit 8  ;
        "memAdr"  :: Bit 64 ;
        "memDat"  :: Bit 64
    }.
    Definition RFCtrl := WriteRq 32 (Bit 64).
    Open Scope kami_expr.
    Definition Processor :=
        MODULE {
            Register "mode"   : (Bit  2) <- WO~1~1           with
            Register "pc"     : (Bit 64) <- (natToWord 64 0) with
            Rule "step" :=
                Read  pc      : _ <- "pc";
                Read  mode    : _ <- "mode";
                Call  iFetch  : _ <- "getInstr"(#pc : _);
                LETA  dInst       <- Decode_action #mode #iFetch;

              (******)

                (* rdEn[1|2] covers both the case when (i) an instruction type
                   does not require register reads, and when (ii) an instruction
                   type ~does~ require register reads but the source register is x0
                *)
                LET   rdEn1       <- (#dInst @% "keys") @% "rs1?";
                LET   rdEn2       <- (#dInst @% "keys") @% "rs2?";

                If (#rdEn1) then (Call  rs1_val : _ <- "rfRead1"(#dInst @% "rs1" : _);
                                  Ret #rs1_val)
                            else Ret $$ (natToWord 64 0) as rs1_val;
                If (#rdEn2) then (Call  rs2_val : _ <- "rfRead2"(#dInst @% "rs2" : _);
                                  Ret #rs2_val)
                            else Ret $$ (natToWord 64 0) as rs2_val;

                Call csr_val : Bit 64 <- "readCSR"(#dInst @% "csradr" : _);

              (******)

                LETA  ctrlSig     <- Control_action #dInst ;
                LETA  eInst       <- Execute1_action #pc #dInst #ctrlSig #rs1_val #rs2_val #csr_val;

              (******)

                LET   memReq      <- STRUCT {
                                       "memOp"   ::= #ctrlSig @% "memOp";
                                       "memMask" ::= #eInst @% "memMask";
                                       "memAdr"  ::= #eInst @% "memAdr";
                                       "memDat"  ::= #eInst @% "memDat"
                                     };
                If (#ctrlSig @% "memOp" != $$ Mem_off) then (Call  memResp : _ <- "memAction"(#memReq : _);
                                                             Ret #memResp)
                                                       else Ret $$ (getDefaultConst MemResp) as memResp;

              (******)

                LETA  update      <- Execute2_action #mode #dInst #ctrlSig #csr_val #eInst #memResp;

              (******)

                LET   rfCtrl      <- STRUCT {
                                       "addr" ::= #dInst @% "rd";
                                       "data" ::= #update @% "rd_val"
                                     };

                If (#update @% "werf") then Call "rfWrite"(#rfCtrl : WriteRq 32 (Bit 64));
                                            Retv
                                       else Retv;

                LET   csrCtrl     <- STRUCT {
                                       "wecsr"      ::= #update @% "wecsr"     ;
                                       "csradr"     ::= #dInst @% "csradr"     ;
                                       "twiddleOut" ::= #eInst @% "twiddleOut" ;
                                       "pc"         ::= #pc                    ;
                                       "except"     ::= #update @% "except"    ;
                                       "cause"      ::= #update @% "cause"     ;
                                       "reqPC"      ::= #update @% "new_pc"
                                     };

                Call  next_pc : Bit 64 <- "writeCSR"(#csrCtrl : _);

                Write "mode"      <- #update @% "next_mode";
                Write "pc"        <- #next_pc;

              (******)

                Retv
        }.
End Process.

Definition rtlMod := getRtl (nil, (RegFile "RF"
                                           ("rfRead1" :: "rfRead2" :: nil)
                                           "rfWrite"
                                           32
                                           (Some (ConstBit (natToWord 64 0))) :: nil,
                                   Processor)).

Extraction "Target.hs" rtlMod size RtlModule WriteRegFile Nat.testbit.
