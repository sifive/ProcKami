Require Import Kami.Syntax Decode Control Execute.

Open Scope kami_action.
Definition IndexWrite ty A D
    (regMap : list (word A * string)) (addr : Bit A @# ty) (data : D @# ty) :=
    fold_right (fun (x : word A * string) acc => If (addr == $$ (fst x))
                                                 then Write (snd x)%string <- data; Retv; acc
                ) Retv regMap.
Definition IndexRead ty A D
    (regMap : list (word A * string)) (addr : Bit A @# ty) :=
     fold_left (fun acc (x : word A * string) =>
                     LETA tmpB <- acc;
                     Read tmp : (Bit D) <- (snd x);
                     Ret  ((IF addr == $$ (fst x) then #tmp else $$ (natToWord D 0)) | #tmpB)
                ) regMap (Ret $$ (natToWord D 0)).
Close Scope kami_action.

Section Test.
    Variable ty : Kind -> Type.
    Open Scope kami_expr.
    Compute IndexWrite ((WO~0~0, "foo") :: (WO~1~0, "bar") :: nil) ($$ WO~0~0) ($$ true).
    Compute IndexRead 8 ((WO~0~0, "foo") :: (WO~1~0, "bar") :: nil) ($$ WO~0~0).
    Close Scope kami_expr.
End Test.

Section Process.
    Definition MemCtrl := STRUCT {
        "memWrEn" :: Bool   ;
        "memMask" :: Bit 8  ;
        "memAdr"  :: Bit 64 ;
        "memDat"  :: Bit 64
    }.
    Definition CSRmap := ((natToWord 12 833), "mepc") :: nil.
    Open Scope kami_expr.
    Definition Processor :=
        MODULE {
            Register "pc"     : (Bit 64) <- (natToWord 64 0) with
            Register "mepc"   : (Bit 64) <- (natToWord 64 0) with
            Register "mcause" : (Bit 64) <- (natToWord 64 0) with
            Rule "step" :=
                Read  pc      : _ <- "pc";
                Call  instr   : _ <- "getInstr"(#pc : _);
                LETA  dInst       <- Decode_action #instr ;
                LETA  ctrlSig     <- Control_action #dInst ;
                Call  rs1_val : _ <- "rfRead1"(#dInst @% "rs1" : _);
                Call  rs2_val : _ <- "rfRead2"(#dInst @% "rs2" : _);

                LETA  csr_val     <- IndexRead _ CSRmap (#dInst @% "csradr");

                LETA  eInst       <- Execute1_action #pc #dInst #ctrlSig #rs1_val #rs2_val #csr_val;
                LET   memCtrl     <- STRUCT {
                                       "memWrEn" ::= (#ctrlSig @% "memOp" == $$ Mem_store);
                                       "memMask" ::= #eInst @% "memMask";
                                       "memAdr"  ::= #eInst @% "memAdr";
                                       "memDat"  ::= #eInst @% "memDat"
                                     };

                If (#ctrlSig @% "memOp" != $$ Mem_off) then (Call  memResp : _ <- "memAction"(#memCtrl : _);
                                                            Ret #memResp)
                                                       else Ret $$ (natToWord 64 0) as memResp;

                LETA  update      <- Execute2_action #dInst #ctrlSig #csr_val #eInst #memResp;
                LET   rfCtrl      <- STRUCT {
                                       "addr" ::= #dInst @% "rd";
                                       "data" ::= #update @% "new_rd"
                                     };
                If (#ctrlSig @% "werf") then Call "rfWrite"(#rfCtrl : _);
                                             Retv
                                        else Retv;
                Write "pc"        <- #update @% "new_pc";

                If (#ctrlSig @% "wecsr") then IndexWrite CSRmap
                                                         (#dInst @% "csradr")
                                                         (#eInst @% "twiddleOut")
                                        else Retv;

                If (#dInst @% "illegal") then Write "mepc" <- #pc;
                                              Retv
                                         else Retv;

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
