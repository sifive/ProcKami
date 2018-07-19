Require Import Kami.Syntax Kami.Extraction Decode Control Execute.

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

Section Process.
    Definition MemReq := STRUCT {
        "memOp"   :: Bit 2  ;
        "memMask" :: Bit 8  ;
        "memAdr"  :: Bit 64 ;
        "memDat"  :: Bit 64
    }.
    Definition RFCtrl := WriteRq 32 (Bit 64).
    Definition CSRmap := ((natToWord 12 834), "mcause") :: ((natToWord 12 833), "mepc") :: nil.
    Open Scope kami_expr.
    Definition Processor :=
        MODULE {
            Register "mode"   : (Bit  2) <- WO~1~1           with
            Register "pc"     : (Bit 64) <- (natToWord 64 0) with
            Register "mepc"   : (Bit 64) <- (natToWord 64 0) with
            Register "mcause" : (Bit 64) <- (natToWord 64 0) with
            Rule "step" :=
                Read  pc      : _ <- "pc";
                Read  mode    : _ <- "mode";
                Call  iFetch  : _ <- "getInstr"(#pc : _);
                LETA  dInst       <- Decode_action #mode #iFetch;

              (*----*)

                (* rdEn[1|2] covers both the case when (i) an instruction type
                   does not require register reads, and when (ii) an instruction
                   type ~does~ require register reads but the source register is x0
                *)
                LET   rdEn1       <- (#dInst @% "keys") @% "rs1?";
                LET   rdEn2       <- (#dInst @% "keys") @% "rs2?";
                LET   csrEn       <- (#dInst @% "keys") @% "csr?";
                If (#rdEn1) then (Call  rs1_val : _ <- "rfRead1"(#dInst @% "rs1" : _);
                                  Ret #rs1_val)
                            else Ret $$ (natToWord 64 0) as rs1_val;
                If (#rdEn2) then (Call  rs2_val : _ <- "rfRead2"(#dInst @% "rs2" : _);
                                  Ret #rs2_val)
                            else Ret $$ (natToWord 64 0) as rs2_val;
                LETA  csr_val     <- IndexRead _ CSRmap (#dInst @% "csradr");

              (*----*)

                LETA  ctrlSig     <- Control_action #dInst ;
                LETA  eInst       <- Execute1_action #pc #dInst #ctrlSig #rs1_val #rs2_val #csr_val;

              (*----*)

                LET   memReq      <- STRUCT {
                                       "memOp"   ::= #ctrlSig @% "memOp";
                                       "memMask" ::= #eInst @% "memMask";
                                       "memAdr"  ::= #eInst @% "memAdr";
                                       "memDat"  ::= #eInst @% "memDat"
                                     };
                If (#ctrlSig @% "memOp" != $$ Mem_off) then (Call  memResp : _ <- "memAction"(#memReq : _);
                                                             Ret #memResp)
                                                       else Ret $$ (getDefaultConst MemResp) as memResp;

              (*----*)

                LETA  update      <- Execute2_action #dInst #ctrlSig #csr_val #eInst #memResp;

              (*----*)

                LET   rfCtrl      <- STRUCT {
                                       "addr" ::= #dInst @% "rd";
                                       "data" ::= #update @% "rd_val"
                                     };
                If (#update @% "werf") then Call "rfWrite"(#rfCtrl : WriteRq 32 (Bit 64));
                                            Retv
                                       else Retv;
                If (#update @% "wecsr") then IndexWrite CSRmap
                                                        (#dInst @% "csradr")
                                                        (#eInst @% "twiddleOut")
                                        else Retv;
                If (#update @% "except") then Write "mepc" <- #pc;
                                              Write "mcause" <- ZeroExtend 60 (#update @% "cause");
                                              Retv
                                         else Retv;
                Write "pc"        <- #update @% "new_pc";

              (*----*)

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
