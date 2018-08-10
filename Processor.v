Require Import Kami.All Decode Control Execute Retire.

Section Core.
    Variable CORE_NUM : nat.
    Definition NAME : string := ("Core" ++ (natToHexStr CORE_NUM))%string.

    Definition MXL := WO~1~0.
    (* See Table 3.2            Z Y X W V U T S R Q P O N M L K J I H G F E D C B A *)
    Definition Extensions := WO~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~0~0~0~0~0~0~0~0.
    Definition VendorID := (natToWord 64 0).
    Definition ArchID   := (natToWord 64 0).
    Definition ImplID   := (natToWord 64 0).
    Definition HartID   := (natToWord 64 CORE_NUM).

    Local Notation "` x" := (NAME ++ "." ++ x)%string (at level 0).

    Section ReadCSR.
        Variable ty : Kind -> Type.

        Definition misa_hardwire : word 64 := Word.combine (Word.combine Extensions (natToWord 36 0)) MXL.

        Open Scope kami_expr.
        Open Scope kami_action.
        Variable csradr : Bit 12 @# ty.
        Definition ReadCSR_action : ActionT ty (Bit 64).
        exact(
                    If (csradr == $$ (12'h"300")) then Read mstatus : Bit 64     <- `"mstatus"; Ret #mstatus
                                                  else Ret $$ (natToWord 64 0)
                                                    as mstatus;
                    If (csradr == $$ (12'h"301")) then Ret $$ misa_hardwire
                                                  else Ret $$ (natToWord 64 0)
                                                    as misa;
                    If (csradr == $$ (12'h"304")) then Read mie : Bit 64         <- `"mie"; Ret #mie
                                                  else Ret $$ (natToWord 64 0)
                                                    as mie;
                    If (csradr == $$ (12'h"305")) then Read mtvec : Bit 64       <- `"mtvec"; Ret #mtvec
                                                  else Ret $$ (natToWord 64 0)
                                                    as mtvec;
                    If (csradr == $$ (12'h"306")) then Read mcounteren : Bit 64  <- `"mcounteren"; Ret #mcounteren
                                                  else Ret $$ (natToWord 64 0)
                                                    as mcounteren;
                    If (csradr == $$ (12'h"307")) then Read mtvt : Bit 64        <- `"mtvt"; Ret #mtvt
                                                  else Ret $$ (natToWord 64 0)
                                                    as mtvt;
                    If (csradr == $$ (12'h"340")) then Read mscratch : Bit 64    <- `"mscratch"; Ret #mscratch
                                                  else Ret $$ (natToWord 64 0)
                                                    as mscratch;
                    If (csradr == $$ (12'h"341")) then Read mepc : Bit 64        <- `"mepc"; Ret #mepc
                                                  else Ret $$ (natToWord 64 0)
                                                    as mepc;
                    If (csradr == $$ (12'h"342")) then Read mcause : Bit 64      <- `"mcause"; Ret #mcause
                                                  else Ret $$ (natToWord 64 0)
                                                    as mcause;
                    If (csradr == $$ (12'h"343")) then Read mtval : Bit 64       <- `"mtval"; Ret #mtval
                                                  else Ret $$ (natToWord 64 0)
                                                    as mtval;
                    If (csradr == $$ (12'h"344")) then Read mip : Bit 64         <- `"mip"; Ret #mip
                                                  else Ret $$ (natToWord 64 0)
                                                    as mip;
                    If (csradr == $$ (12'h"345")) then Read mnxti : Bit 64       <- `"mnxti"; Ret #mnxti
                                                  else Ret $$ (natToWord 64 0)
                                                    as mnxti;
                    If (csradr == $$ (12'h"346")) then Read mintstatus : Bit 64  <- `"mintstatus"; Ret #mintstatus
                                                  else Ret $$ (natToWord 64 0)
                                                    as mintstatus;
                    If (csradr == $$ (12'h"348")) then Read mscratchcsw : Bit 64 <- `"mscratchcsw"; Ret #mscratchcsw
                                                  else Ret $$ (natToWord 64 0)
                                                    as mscratchcsw;
                    If (csradr == $$ (12'h"B00")) then Read mcycle : Bit 64      <- `"mcycle"; Ret #mcycle
                                                  else Ret $$ (natToWord 64 0)
                                                    as mcycle;
                    If (csradr == $$ (12'h"B02")) then Read minstret : Bit 64    <- `"minstret"; Ret #minstret
                                                  else Ret $$ (natToWord 64 0)
                                                    as minstret;
                    If (csradr == $$ (12'h"F11")) then Ret $$ VendorID
                                                  else Ret $$ (natToWord 64 0)
                                                    as mvendorid;
                    If (csradr == $$ (12'h"F12")) then Ret $$ ArchID
                                                  else Ret $$ (natToWord 64 0)
                                                    as marchid;
                    If (csradr == $$ (12'h"F13")) then Ret $$ ImplID
                                                  else Ret $$ (natToWord 64 0)
                                                    as mimpid;
                    If (csradr == $$ (12'h"F14")) then Ret $$ HartID
                                                  else Ret $$ (natToWord 64 0)
                                                    as mhartid;
                    Ret (#mstatus | #misa | #mie | #mtvec | #mcounteren | #mtvt |
                         #mscratch | #mepc | #mcause | #mtval | #mip | #mnxti |
                         #mintstatus | #mscratchcsw | #mcycle | #minstret |
                         #mvendorid | #marchid | #mimpid | #mhartid)
        ). Defined.
    End ReadCSR.

    Section WriteCSR.
        Definition CSRCtrl := STRUCT {
            "wecsr"      :: Bool   ;
            "csradr"     :: Bit 12 ;
            "twiddleOut" :: Bit 64 ;
            "pc"         :: Bit 64 ;
            "except?"    :: Bool   ;
            "cause"      :: Bit  4 ;
            "ret?"       :: Bool   ;
            "reqPC"      :: Bit 64
        }.
        Variable ty : Kind -> Type.
        Open Scope kami_expr.
        Open Scope kami_action.
        Variable csrCtrl : CSRCtrl @# ty.
        Definition WriteCSR_action : ActionT ty (Bit 64).
        exact(
                    LET wecsr           <- csrCtrl @% "wecsr";
                    LET csradr          <- csrCtrl @% "csradr";
                    LET data            <- csrCtrl @% "twiddleOut";
                    LET pc              <- csrCtrl @% "pc";
                    LET except          <- csrCtrl @% "except?";
                    LET cause           <- csrCtrl @% "cause";
                    LET ret             <- csrCtrl @% "ret?";
                    LET reqPC           <- csrCtrl @% "reqPC";

                    Read mcycle         <- `"mcycle";
                    Read minstret       <- `"minstret";

                    If !(#wecsr && (#csradr == $$ (12'h"B00")))
                                then    Write `"mcycle" <- #mcycle + $$ (natToWord 64 1); Retv;

                    If !(#wecsr && (#csradr == $$ (12'h"B02")))
                                then    Write `"minstret" <- #minstret + $$ (natToWord 64 1); Retv;

                    Read mtvec          <- `"mtvec";
                    Read mepc           <- `"mepc";

                    If (#wecsr) then   (If (#csradr == $$ (12'h"300")) then (Write `"mstatus" <- #data;     Retv);
                                     (* If (#csradr == $$ (12'h"301")) then (Write `"misa" <- #data;        Retv); *)
                                        If (#csradr == $$ (12'h"304")) then (Write `"mie" <- #data;         Retv);
                                        If (#csradr == $$ (12'h"305")) then (Write `"mtvec" <- #data;       Retv);
                                        If (#csradr == $$ (12'h"306")) then (Write `"mcounteren" <- #data;  Retv);
                                        If (#csradr == $$ (12'h"307")) then (Write `"mtvt" <- #data;        Retv);
                                        If (#csradr == $$ (12'h"340")) then (Write `"mscratch" <- #data;    Retv);
                                        If (#csradr == $$ (12'h"341")) then (Write `"mepc" <- #data;        Retv);
                                        If (#csradr == $$ (12'h"342")) then (Write `"mcause" <- #data;      Retv);
                                        If (#csradr == $$ (12'h"343")) then (Write `"mtval" <- #data;       Retv);
                                        If (#csradr == $$ (12'h"344")) then (Write `"mip" <- #data;         Retv);
                                        If (#csradr == $$ (12'h"345")) then (Write `"mnxti" <- #data;       Retv);
                                        If (#csradr == $$ (12'h"346")) then (Write `"mintstatus" <- #data;  Retv);
                                        If (#csradr == $$ (12'h"348")) then (Write `"mscratchcsw" <- #data; Retv);
                                        If (#csradr == $$ (12'h"B00")) then (Write `"mcycle" <- #data;      Retv);
                                        If (#csradr == $$ (12'h"B02")) then (Write `"minstret" <- #data;    Retv);
                                        Retv
                                       );
                    If (#except) then  (Write `"mepc" <- #pc;
                                        Write `"mcause" <- ZeroExtend 60 #cause;
                                        Retv
                                       );

                    LET final_pc        <- IF #except then #mtvec
                                           else (IF #ret then #mepc
                                                         else #reqPC);

                    Ret #final_pc
        ). Defined.
    End WriteCSR.

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
                (*       `"cycle"                                          (* 0xC00 *)   *)  (* Read Only *)
                (*       `"time"                                           (* 0xC01 *)   *)  (* Read Only *)
                (*       `"instret"                                        (* 0xC02 *)   *)  (* Read Only *)
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
             (* Register `"misa"       : (Bit 64) <- (natToWord 64 0) with (* 0x301 *) *)    (* MXL modification and extension disabling not currently supported *)
                (*        "medeleg"                                        (* 0x302 *)   *)  (* In systems with only M-mode, or with M- and U-modes but w/o U-mode trap *)
                (*        "mideleg"                                        (* 0x303 *)   *)  (*   support, the medeleg and mideleg registers should not exist           *)
                Register `"mie"        : (Bit 64) <- (natToWord 64 0) with (* 0x304 *)
                Register `"mtvec"      : (Bit 64) <- (Ox"000")        with (* 0x305 *)
                Register `"mcounteren" : (Bit 64) <- (natToWord 64 0) with (* 0x306 *)
                Register `"mtvt"       : (Bit 64) <- (natToWord 64 0) with (* 0x307 *)       (* See the SiFive CLIC Proposal *)

                Register `"mscratch"   : (Bit 64) <- (natToWord 64 0) with (* 0x340 *)
                Register `"mepc"       : (Bit 64) <- (natToWord 64 0) with (* 0x341 *)
                Register `"mcause"     : (Bit 64) <- (natToWord 64 0) with (* 0x342 *)
                Register `"mtval"      : (Bit 64) <- (natToWord 64 0) with (* 0x343 *)
                Register `"mip"        : (Bit 64) <- (natToWord 64 0) with (* 0x344 *)
                Register `"mnxti"      : (Bit 64) <- (natToWord 64 0) with (* 0x345 *)       (* See the SiFive CLIC Proposal *)
                Register `"mintstatus" : (Bit 64) <- (natToWord 64 0) with (* 0x346 *)       (* See the SiFive CLIC Proposal *)
                Register `"mscratchcsw": (Bit 64) <- (natToWord 64 0) with (* 0x348 *)       (* See the SiFive CLIC Proposal *)

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
                Register `"pc"    : (Bit 64) <- (64'h"0000000080000000") with
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
                    LET   rdEn1       <- (#dInst @% "keys") @% "rs1?";
                    LET   rdEn2       <- (#dInst @% "keys") @% "rs2?";

                    If (#rdEn1) then (Call  rs1_val : _ <- `"rfRead1"(#dInst @% "rs1" : _);
                                      Ret #rs1_val)
                                else Ret $$ (natToWord 64 0) as rs1_val;
                    If (#rdEn2) then (Call  rs2_val : _ <- `"rfRead2"(#dInst @% "rs2" : _);
                                      Ret #rs2_val)
                                else Ret $$ (natToWord 64 0) as rs2_val;

                    LETA csr_val : Bit 64 <- ReadCSR_action (#dInst @% "csradr");

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
                    If (#ctrlSig @% "memOp" != $$ Mem_off) then (Call  memResp : _ <- `"memAction"(#memReq : _);
                                                                 Ret #memResp)
                                                           else Ret $$ (getDefaultConst MemResp) as memResp;

                  (******)

                    LETA  update      <- Retire_action #mode #dInst #ctrlSig #csr_val #eInst #memResp;

                  (******)

                    LET   rfCtrl      <- STRUCT {
                                           "addr" ::= #dInst @% "rd";
                                           "data" ::= #update @% "rd_val"
                                         };

                    If (#update @% "werf") then Call `"rfWrite"(#rfCtrl : WriteRq 32 (Bit 64));
                                                Retv
                                           else Retv;

                    LET   csrCtrl     <- STRUCT {
                                           "wecsr"      ::= #update @% "wecsr"     ;
                                           "csradr"     ::= #dInst @% "csradr"     ;
                                           "twiddleOut" ::= #eInst @% "twiddleOut" ;
                                           "pc"         ::= #pc                    ;
                                           "except?"    ::= #update @% "except?"   ;
                                           "cause"      ::= #update @% "cause"     ;
                                           "ret?"       ::= #update @% "ret?"      ;
                                           "reqPC"      ::= #update @% "new_pc"
                                         };

                    LETA  next_pc : Bit 64 <- WriteCSR_action #csrCtrl;

                    Write `"mode"      <- #update @% "next_mode";
                    Write `"pc"        <- #next_pc;

                  (******)

                    If ((#eInst @% "memAdr" == $$ (64'h"0000000080001000")) && (#ctrlSig @% "memOp" == $$ Mem_store))
                        then (If #eInst @% "memDat" == $$ (64'h"0000000000000001")
                              then Sys ((DispString _ "\033[32;1mWrite to Host ") :: (DispBit (#eInst @% "memDat") (1, Decimal)) :: (DispString _ "\033[0m\n") :: (Finish _) :: nil) Retv
                              else Sys ((DispString _ "\033[31;1mWrite to Host ") :: (DispBit (#eInst @% "memDat") (1, Decimal)) :: (DispString _ "\033[0m\n") :: (Finish _) :: nil) Retv
                            ; Retv
                             )
                        else Retv;

                    Retv
            }.
    End Process.
End Core.

Definition rtlMod := getRtl (nil, (RegFile "Core0.RF"
                                           ("Core0.rfRead1" :: "Core0.rfRead2" :: nil)
                                           "Core0.rfWrite"
                                           32
                                           (Some (ConstBit (natToWord 64 0))) :: nil,
                                   Processor 0)).

Extraction "Target.hs" rtlMod size RtlModule WriteRegFile Nat.testbit.
