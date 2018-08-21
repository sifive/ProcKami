Require Import Kami.All Decode Control Execute1 Execute2 Status.

Section Process.
    Variable LABEL : string.
    Variable CORE_NUM : nat.

    Definition NAME : string := (LABEL ++ (natToHexStr CORE_NUM))%string.
    Local Notation "` x" := (NAME ++ "." ++ x)%string (at level 0).

    Definition RESET_VECTOR := 64'h"0000000080000000".

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
            (*       `"cycle"                                          (* 0xC00 *)   *)  (* Read Only, Shadows 0xB00 "mcycle" *)
            (*       `"time"                                           (* 0xC01 *)   *)  (* Read Only, Memory-mapped *)
            (*       `"instret"                                        (* 0xC02 *)   *)  (* Read Only, Shadow 0xB02 "minstret" *)
            (*       `"hpmcounter3"                                    (* 0xC03 *)   *)  (* Hardwired to 0 *)
            (*           ...                                           (*  ...  *)   *)  (*  ...           *)
            (*       `"hpmcounter31"                                   (* 0xC1F *)   *)  (* Hardwired to 0 *)

            (*       `"cycleh"                                         (* 0xC80 *)   *)  (* Unimplemented - RV32 only *)
            (*       `"timeh"                                          (* 0xC81 *)   *)  (* Unimplemented - RV32 only *)
            (*       `"instreth"                                       (* 0xC82 *)   *)  (* Unimplemented - RV32 only *)
            (*       `"hpmcounter3h"                                   (* 0xC83 *)   *)  (* Unimplemented - RV32 only *)
            (*           ...                                           (*  ...  *)   *)  (*  ...                      *)
            (*       `"hpmcounter31h"                                  (* 0xC9F *)   *)  (* Unimplemented - RV32 only *)

            (*       `"mvendorid"                                      (* 0xF11 *)   *)  (* Read only *)
            (*       `"marchid"                                        (* 0xF12 *)   *)  (* Read only *)
            (*       `"mimpid"                                         (* 0xF13 *)   *)  (* Read only *)
            (*       `"mhartid"                                        (* 0xF14 *)   *)  (* Read only *)

            Register `"mstatus"    : (Bit 64) <- (natToWord 64 0) with (* 0x300 *)
            (*       `"misa"                                           (* 0x301 *)   *)  (* MXL modification and extension disabling not currently supported *)
            (*       `"medeleg"                                        (* 0x302 *)   *)  (* In systems with only M-mode, or with M- and U-modes but w/o U-mode trap *)
            (*       `"mideleg"                                        (* 0x303 *)   *)  (*   support, the medeleg and mideleg registers should not exist           *)
            Register `"mie"        : (Bit 64) <- (natToWord 64 0) with (* 0x304 *)
            Register `"mtvec"      : (Bit 64) <- (Ox"000")        with (* 0x305 *)
            Register `"mcounteren" : (Bit 64) <- (natToWord 64 0) with (* 0x306 *)
            Register `"mtvt"       : (Bit 64) <- (natToWord 64 0) with (* 0x307 *)       (* See the SiFive CLIC Proposal *)

            Register `"mscratch"   : (Bit 64) <- (natToWord 64 0) with (* 0x340 *)
            Register `"mepc"       : (Bit 64) <- (natToWord 64 0) with (* 0x341 *)
            Register `"mcause"     : (Bit 64) <- (natToWord 64 0) with (* 0x342 *)
            Register `"mtval"      : (Bit 64) <- (natToWord 64 0) with (* 0x343 *)
            Register `"mip"        : (Bit 64) <- (natToWord 64 0) with (* 0x344 *)
            (*       `"mnxti"                                          (* 0x345 *)   *)  (* See the SiFive CLIC Proposal *)
            Register `"mintstatus" : (Bit 64) <- (natToWord 64 0) with (* 0x346 *)       (* See the SiFive CLIC Proposal *)
            (*       `"mscratchcsw"                                    (* 0x348 *)   *)  (* See the SiFive CLIC Proposal *)

            (*       `"pmpcfg0"                                        (* 0x3A0 *)   *)  (* Hardwired to 0 *)
            (*       `"pmpcfg1"                                        (* 0x3A1 *)   *)  (* Unimplemented - RV32 only *)
            (*       `"pmpcfg2"                                        (* 0x3A2 *)   *)  (* Hardwired to 0 *)
            (*       `"pmpcfg3"                                        (* 0x3A3 *)   *)  (* Unimplemented - RV32 only *)
            (*       `"pmpaddr0"                                       (* 0x3B0 *)   *)  (* Hardwired to 0 *)
            (*           ...                                           (*  ...  *)   *)  (* Hardwired to 0 *)
            (*       `"pmpaddr15"                                      (* 0x3BF *)   *)  (* Hardwired to 0 *)

            Register `"mcycle"     : (Bit 64) <- (natToWord 64 0) with (* 0xB00 *)
            Register `"minstret"   : (Bit 64) <- (natToWord 64 0) with (* 0xB02 *)
            (*       `"mhpmcounter3"                                   (* 0xB03 *)   *)  (* Hardwired to 0 *)
            (*           ...                                           (*  ...  *)   *)  (*  ...           *)
            (*       `"mhpmcounter31"                                  (* 0xB1F *)   *)  (* Hardwired to 0 *)

            (*       `"mcycleh"                                        (* 0xB80 *)   *)  (* Unimplemented - RV32 only *)
            (*       `"minstreth"                                      (* 0xB82 *)   *)  (* Unimplemented - RV32 only *)
            (*       `"mhpmcounter3h"                                  (* 0xB83 *)   *)  (* Unimplemented - RV32 only *)
            (*           ...                                           (*  ...  *)   *)  (*  ...                      *)
            (*       `"mhpmcounter31h"                                 (* 0xB9F *)   *)  (* Unimplemented - RV32 only *)

            (*       `"mhpmevent3"                                     (* 0x323 *)   *)  (* Hardwired to 0 *)
            (*           ...                                           (*  ...  *)   *)  (*  ...           *)
            (*       `"mhpmevent31"                                    (* 0x33F *)   *)  (* Hardwired to 0 *)

            Register `"mode"  : (Bit  2) <- WO~1~1 with
            Register `"pc"    : (Bit 64) <- RESET_VECTOR with
            Rule `"step" :=
                Read  pc      : _ <- `"pc";
                Read  mode    : _ <- `"mode";
                Call  iFetch  : _ <- `"getInstr"(#pc : _);
                LETA  dInst       <- Decode_action #mode #iFetch;

              (******)

                (* rdEn[1|2] covers both the case when (i) an instruction type
                   does not require register reads, and when (ii) an instruction
                   type ~does~ require register reads but the source register is x0
                *)
                LET rdEn1 <- (#dInst @% "keys") @% "rs1?";
                LET rdEn2 <- (#dInst @% "keys") @% "rs2?";

                If (#rdEn1) then (Call  rs1_val : _ <- `"rfRead1"(#dInst @% "rs1" : _);
                                  Ret #rs1_val)
                            else Ret $$ (natToWord 64 0) as rs1_val;
                If (#rdEn2) then (Call  rs2_val : _ <- `"rfRead2"(#dInst @% "rs2" : _);
                                  Ret #rs2_val)
                            else Ret $$ (natToWord 64 0) as rs2_val;

                LETA csr_val : Bit 64 <- ReadCSR_action LABEL CORE_NUM (#dInst @% "csradr");

              (******)

                LETA  ctrlSig <- Control_action #dInst;
                LETA  calcRes <- Execute1_action #pc #dInst #ctrlSig #rs1_val #rs2_val #csr_val;

              (******)

                LET   memReq <- STRUCT {
                                  "memOp"   ::= #ctrlSig @% "memOp";
                                  "memMask" ::= #calcRes @% "memMask";
                                  "memAdr"  ::= #calcRes @% "memAdr";
                                  "memDat"  ::= #calcRes @% "memDat"
                                };
                If (#ctrlSig @% "memOp" != $$ Mem_off) then (Call  memResp : _ <- `"memAction"(#memReq : _);
                                                             Ret #memResp)
                                                       else Ret $$ (getDefaultConst MemResp) as memResp;

              (******)

                LETA  eInst <- Execute2_action #mode #dInst #ctrlSig #csr_val #calcRes #memResp;

              (******)

                LETA tableLookup <- ClicVector_action LABEL CORE_NUM (#eInst @% "except?") (#eInst @% "cause");
                LET mtvtMemReq <- STRUCT {
                                       "memOp"   ::= $$ Mem_load;
                                       "memMask" ::= $$ WO~1~1~1~1~1~1~1~1; (* WO~1~1~1~1 in RV32 *)
                                       "memAdr"  ::= #tableLookup @% "addr";
                                       "memDat"  ::= $$ (natToWord 64 0)
                                    };
                IF (#tableLookup @% "needed?") then (Call mtvtMemResp : _ <- `"lateMemAction"(#mtvtMemReq : _);
                                                     Ret #mtvtMemResp)
                                               else Ret $$ (getDefaultConst MemResp) as #mtvtMemResp;

                LET   csrCtrl     <- STRUCT {
                                       "wecsr"      ::= #eInst @% "wecsr"        ;
                                       "csradr"     ::= #dInst @% "csradr"       ;
                                       "twiddleOut" ::= #calcRes @% "twiddleOut" ;
                                       "pc"         ::= #pc                      ;
                                       "except?"    ::= #eInst @% "except?"      ;
                                       "cause"      ::= #eInst @% "cause"        ;
                                       "ret?"       ::= #eInst @% "ret?"         ;
                                       "reqPC"      ::= #eInst @% "new_pc"
                                     };
                LETA final <- WriteCSRandRetire_action LABEL CORE_NUM #mode #csrCtrl #mtvtMemResp (#eInst @% "werf") (#eInst @% "rd_val");

                LET rfCtrl <- STRUCT {
                                "addr" ::= #dInst @% "rd";
                                "data" ::= #final @% "rd_val"
                              };
                If (#final @% "werf") then Call `"rfWrite"(#rfCtrl : WriteRq 32 (Bit 64));
                                            Retv
                                       else Retv;

                Write `"mode" <- #final @% "next_mode";
                Write `"pc"   <- #final @% "pc";

              (******)

                (* Note that this displays even if the instruction does not retire *)
                If ((#calcRes @% "memAdr" == $$ (64'h"0000000080001000")) && (#ctrlSig @% "memOp" == $$ Mem_store))
                    then (If #calcRes @% "memDat" == $$ (64'h"0000000000000001")
                          then Sys ((DispString _ "\033[32;1mWrite to Host ") :: (DispBit (#calcRes @% "memDat") (1, Decimal)) :: (DispString _ "\033[0m\n") :: (Finish _) :: nil) Retv
                          else Sys ((DispString _ "\033[31;1mWrite to Host ") :: (DispBit (#calcRes @% "memDat") (1, Decimal)) :: (DispString _ "\033[0m\n") :: (Finish _) :: nil) Retv
                        ; Retv
                         )
                    else Retv;

                Retv
        }.

    Definition rtlModModule := getRtl (nil, (RegFile `"RF"
                                                     (`"rfRead1" :: `"rfRead2" :: nil)
                                                     `"rfWrite"
                                                     32
                                                     (Some (ConstBit (natToWord 64 0))) :: nil,
                                             Processor)).
End Process.

Definition rtlMod := rtlModModule "Core" 0.
Extraction "Target.hs" rtlMod size RtlModule WriteRegFile Nat.testbit.
