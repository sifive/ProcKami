Require Import Kami.All Decode.

Definition ClearBits ty w (lsb msb : nat) (e : Expr ty (SyntaxKind (Bit w))) : Expr ty (SyntaxKind (Bit w)).
  refine
    match Compare_dec.lt_dec msb w with
    | left isLt => match Compare_dec.lt_dec msb lsb with
                   | left isLt => e
                   | right isGe => castBits _ ({< (UniBit (TruncMsb (msb+1) (w-1-msb)) (castBits _ e)), (Const ty (natToWord (1+msb-lsb) 0)), (UniBit (TruncLsb lsb (w-lsb)) (castBits _ e)) >})%kami_expr
                   end
    | right isGe => match Compare_dec.lt_dec lsb w with
                    | left isLt => castBits _ ({< (UniBit (TruncMsb w 0) (castBits _ e)), (Const ty (natToWord (w-lsb) 0)), (UniBit (TruncLsb lsb (w-lsb)) (castBits _ e)) >})%kami_expr
                    | right isGe => e
                    end
    end; abstract Omega.omega.
Defined.
Definition ExtractBits ty w (lsb msb : nat) (e : Expr ty (SyntaxKind (Bit w))) : Expr ty (SyntaxKind (Bit (1+msb-lsb))).
  refine
    match Compare_dec.lt_dec msb w with
    | left isLt => match Compare_dec.lt_dec msb lsb with
                   | left isLt => Const ty (getDefaultConst (Bit _))
                   | right isGe => ConstExtract lsb (1+msb-lsb) (w-1-msb) (castBits _ e)
                   end
    | right isGe => Const ty (getDefaultConst (Bit _))
    end; abstract Omega.omega.
Defined.
Definition ReplaceBits ty w (lsb msb : nat) (r : Expr ty (SyntaxKind (Bit (1+msb-lsb)))) (e : Expr ty (SyntaxKind (Bit w))) : Expr ty (SyntaxKind (Bit w)).
  refine
    match Compare_dec.lt_dec msb w with
    | left isLt => match Compare_dec.lt_dec msb lsb with
                   | left isLt => e
                   | right isGe => castBits _ ({< (UniBit (TruncMsb (msb+1) (w-1-msb)) (castBits _ e)), r, (UniBit (TruncLsb lsb (w-lsb)) (castBits _ e)) >})%kami_expr
                   end
    | right isGe => e
    end; abstract Omega.omega.
Defined.

Inductive CSRField (ty : Kind -> Type) :=
| ReadOnly (label : string) (msb lsb : nat)
| HardZero (msb lsb : nat)
| Unsupported (label : string) (msb lsb : nat)
| WIRI     (msb lsb : nat)
| WPRIfc   (msb lsb : nat)
| WPRIbc   (msb lsb : nat)
| WLRL     (label : string) (msb lsb : nat)
| WARLaon  (label : string) (msb lsb : nat) (okay : (Bit (1 + msb - lsb) @# ty) -> (Bool @# ty))
| WARLawm  (label : string) (msb lsb : nat) (legalize : (Bit (1 + msb - lsb) @# ty) -> (Bit (1 + msb - lsb) @# ty))
.

Definition correctRead' (ty : Kind -> Type) (field : (CSRField ty)) (acc : Expr ty (SyntaxKind (Bit XLEN))) : Expr ty (SyntaxKind (Bit XLEN)).
  refine
    match field with
    | ReadOnly n msb lsb    => acc
    | HardZero msb lsb      => ClearBits lsb msb acc
    | Unsupported n msb lsb => ClearBits lsb msb acc
    | WIRI msb lsb   => ClearBits lsb msb acc
    | WPRIfc msb lsb => ClearBits lsb msb acc
    | WPRIbc msb lsb => acc
    | WLRL n msb lsb => acc
    | WARLaon n msb lsb okay => acc
    | WARLawm n msb lsb leg  => acc
    end.
Defined.

Definition correctWrite' (ty : Kind -> Type) (field : (CSRField ty)) (prev acc : Expr ty (SyntaxKind (Bit XLEN))) : Expr ty (SyntaxKind (Bit XLEN)).
  refine
    match field with
    | ReadOnly n msb lsb    => ReplaceBits lsb msb (ExtractBits lsb msb prev) acc
    | HardZero msb lsb      => ReplaceBits lsb msb (ExtractBits lsb msb prev) acc
    | Unsupported n msb lsb => ReplaceBits lsb msb (ExtractBits lsb msb prev) acc
    | WIRI msb lsb   => ReplaceBits lsb msb (ExtractBits lsb msb prev) acc
    | WPRIfc msb lsb => ReplaceBits lsb msb (ExtractBits lsb msb prev) acc
    | WPRIbc msb lsb => acc
    | WLRL n msb lsb => acc
    | WARLaon n msb lsb okay => (IF okay (ExtractBits lsb msb acc) then acc else ReplaceBits lsb msb (ExtractBits lsb msb prev) acc)%kami_expr
    | WARLawm n msb lsb leg  => ReplaceBits lsb msb (leg (ExtractBits lsb msb acc)) acc
    end.
Defined.

Definition correctRead (ty : Kind -> Type) (fields : list (CSRField ty)) (uncorrectedRead : Expr ty (SyntaxKind (Bit XLEN))) :=
    fold_left (fun a f =>
        correctRead' f a
    ) fields uncorrectedRead.

    (* Eval simpl in evalExpr (correctRead (HardZero _ 9 8 :: HardZero _ 5 4 :: nil) (Const _ (64'h"FFFFFFFFFFFFFFFF"))). *)

Definition correctWrite (ty : Kind -> Type) (fields : list (CSRField ty)) (previousValue uncorrectedWrite : Expr ty (SyntaxKind (Bit XLEN))) :=
    fold_left (fun a f =>
        correctWrite' f previousValue a
    ) fields uncorrectedWrite.

    (* Eval simpl in evalExpr (correctWrite (HardZero _ 9 8 :: HardZero _ 5 4 :: nil) (Const _ (64'h"0000000000000000")) (Const _ (64'h"FFFFFFFFFFFFFFFF"))). *)

(* * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *)
(*
   DEPENDENCY TABLE
   Interactions that only exist with S mode, an FPU, or additional extensions are NOT included.

   CSR              Implicitly Read for         Implicitly Set by           Write Side-Effects          Comments
   ---------------  --------------------------  --------------------------  --------------------------  --------------------------------------------------------------------------------
   cycle[h]          --                          --                          --                         Read only, shadows "mcycle", accessibility-in-User-mode set by "mstatus"
   time[h]           --                          --                          --                         Read only, memory-mapped, accessibility-in-User-mode set by "mstatus"
   instret[h]        --                          --                          --                         Read only, shadows "minstret", accessibility-in-User-mode set by "mstatus"
   hpmcounter*[h]    --                          --                          --                         Hardwired to 0, accessibility-in-User-mode set by "mstatus"

   mvendorid         --                          --                          --                         Read only
   marchid           --                          --                          --                         Read only
   mimpid            --                          --                          --                         Read only
   mhartid           --                          --                          --                         Read only

   mstatus          Intpt En, *RET Instrs,      *RET Instructions            --                          --
    ..              Ld/St Privelege,
    ..              mcause (in CLIC mode)
   misa              --                          --                          --                         Read only in this implementation
   medeleg           --                          --                          --                         Does not exist (see RISC-V Manual version 1.1 vol II pg 26 last paragraph)
   mideleg           --                          --                          --                         Does not exist (see RISC-V Manual version 1.1 vol II pg 26 last paragraph)
   mie              Intpt En                     --                          --                         Appears as 0 in CLIC mode (including reads for the purpose of CSR modification)
   mtvec            Exceptions,                  --                          --                          --
    ..              mie/mip (in CLIC mode),
    ..              mcause (in CLIC mode)
   mcounteren       CSR Accessibility            --                          --                          32-bit register (not MXLEN)
   mtvt             Exceptions, mnxti            --                          --                          --

   mscratch          --                          --                          --                          --
   mepc              --                         Exceptions                   --                          --
   mcause           Trap Vectoring              Exceptions                   --                         Some fields appear as 0 in CLIC mode
   mtval             --                         Exceptions                   --                          --
   mip              (Exceptions)                Exceptions                  Exceptions                  Appears as 0 in CLIC mode (including reads for the purpose of CSR modification)
   mnxti             --                          --                          --                         Not a physical register
   mintstatus        --                         Exceptions                   --                          --
   mscratchcsw       --                          --                          --                         Not a physical register

   pmpcfg*           --                          --                          --                         Hardwired to 0
   pmpaddr*          --                          --                          --                         Hardwired to 0

   mcycle[h]         --                         All Instructions             --                          --
   minstret[h]       --                         Retired Instructions         --                          --
   mhpmcounter*[h]   --                          --                          --                         Hardwired to 0

   mhpmevent*        --                          --                          --                         Hardwired to 0
*)

Section ControlStatusRegisters.
    Variable LABEL : string.
    Variable CORE_NUM : nat.

    Definition NAME : string := (LABEL ++ (natToHexStr CORE_NUM))%string.
    Local Notation "` x" := (NAME ++ "." ++ x)%string (at level 0).

    (* See Table 3.2            Z Y X W V U T S R Q P O N M L K J I H G F E D C B A *)
    Definition Extensions := WO~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~0~0~0~0~0~0~0~0.
    Definition VendorID   := (natToWord XLEN 0).
    Definition ArchID     := (natToWord XLEN 0).
    Definition ImplID     := (natToWord XLEN 0).
    Definition HartID     := (natToWord XLEN CORE_NUM).
    Definition MXL        := if RV32 then WO~0~1 else WO~1~0.

    Section CSRSpecialFields.
        Open Scope kami_expr.
        Variable ty : Kind -> Type.

        Definition mstatus_fields := Unsupported ty "SD" 63 63 :: WPRIfc _ 62 36            :: Unsupported _ "SXL" 35 34 ::
                                     Unsupported _ "UXL" 33 32 :: WPRIfc _ 31 23            :: Unsupported _ "TSR" 22 22 ::
                                     Unsupported _  "TW" 21 21 :: Unsupported _ "TVM" 20 20 :: Unsupported _ "MXR" 19 19 ::
                                     Unsupported _ "SUM" 18 18 :: Unsupported _  "XS" 16 15 :: Unsupported _  "FS" 14 13 ::
                                     WPRIfc _ 10 9             :: Unsupported _ "SPP"  8  8 :: WPRIfc _ 6 6              ::
                                     Unsupported _ "SPIE" 5  5 :: WPRIfc _ 2 2              :: Unsupported _ "SIE"  1  1 :: nil.

        Definition mie_fields := WPRIfc ty 63 12          :: WPRIfc _ 10 10 :: Unsupported _ "SEIE" 9 9 ::
                                 Unsupported _ "UEIE" 8 8 :: WPRIfc _  6  6 :: Unsupported _ "STIE" 5 5 ::
                                 Unsupported _ "UTIE" 4 4 :: WPRIfc _  2  2 :: Unsupported _ "SSIE" 1 1 ::
                                 Unsupported _ "USIE" 0 0 :: nil.

        Definition mtvec_legalize := fun (m : Bit 6 @# ty) => IF m$[1:1] == $$ WO~1 then {<($$WO~0~0~0~0),(m$[1:0])>} else m.
        Definition mtvec_fields := WARLawm "MODE" 5 0 mtvec_legalize :: nil.
        (*Definition mtvec_legalize := fun (m : Bit 6 @# type) => IF m$[1:1] == Const _ WO~1 then {<(Const _ WO~0~0~0~0),(m$[1:0])>} else m.*)
        (*Definition mtvec_fields := WARLawm "MODE" 5 0 mtvec_legalize :: nil.*)
        (*Eval simpl in evalExpr (correctWrite mtvec_fields (Const _ (64'h"0000000000000000")) (Const _ (64'h"FFFFFFFFFFFFFFFE"))).*)

        (* NOTE! mcounteren is a 32-bit register *)
        Definition mcounteren_fields := Unsupported ty "HPM" 31 3 :: Unsupported _ "TM" 1 1 :: nil.

        Definition mtvt_legalize := fun (m : Bit 64 @# ty) => ClearBits 0 5 m.
        Definition mtvt_fields := WARLawm "" 63 0 mtvt_legalize :: nil.

        Definition mscratch_fields := @nil (CSRField ty).
        Definition mepc_fields := HardZero ty 0 0 :: nil.
        Definition mcause_fields := @nil (CSRField ty).
        Definition mtval_fields := @nil (CSRField ty).

        Definition mip_fields := WPRIfc ty 64 12          :: ReadOnly _ "MEIP" 11 11 :: WIRI _ 10 10 :: Unsupported _ "SEIP" 9 9 ::
                                 Unsupported _ "UEIP" 8 8 :: ReadOnly _ "MTIP"  7  7 :: WIRI _  6  6 :: Unsupported _ "STIP" 5 5 ::
                                 Unsupported _ "UTIP" 4 4 :: ReadOnly _ "MSIP"  3  3 :: WIRI _ 2 2   :: Unsupported _ "SSIP" 1 1 ::
                                 Unsupported _ "USIP" 0 0 :: nil.

        Definition mintstatus_fields := @nil (CSRField ty).
        Definition mcycle_fields := @nil (CSRField ty).
        Definition minstret_fields := @nil (CSRField ty).

        Close Scope kami_expr.
    End CSRSpecialFields.

    Section ReadCSR.
        Definition misa_hardwire : word 64 := Word.combine (Word.combine Extensions (natToWord 36 0)) MXL.

        Open Scope kami_expr.
        Open Scope kami_action.
        Variable ty : Kind -> Type.
        Variable csradr : Bit 12 @# ty.
        Definition ReadCSR_action : ActionT ty (Bit 64).
        (* TODO mcounteren access - even if perf counters are hardwired to zero, user mode access attempts may or may not raise exception *)
        (*        Should this kind of exception be raised in decode, or here? *)
        (* TODO time 0xC01 memory mapped register - may be accessed in M mode *)
        (* TODO deal with the mnxti business - involves passing 0 or mtvt+offset into Retire, or ignoring the CSR writeback given by Retire *)
        (* TODO deal with the mscratchcsw business *)
        (* TODO figure out mtval behavior - in the Scala code this is still called "mbadaddr" *)
        exact(
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
                    If (csradr == $$ (12'h"300")) then Read mstatus : Bit 64     <- `"mstatus"; Ret (correctRead (mstatus_fields _) #mstatus)
                                                  else Ret $$ (natToWord 64 0)
                                                    as mstatus;
                    If (csradr == $$ (12'h"301")) then Ret $$ misa_hardwire
                                                  else Ret $$ (natToWord 64 0)
                                                    as misa;
                    If (csradr == $$ (12'h"304")) then Read mtvec : Bit 64 <- `"mtvec";
                                                       If #mtvec $[ 1 : 1 ] == $0
                                                       then Read mie : Bit 64    <- `"mie"; Ret (correctRead (mie_fields _) #mie)
                                                       else Ret $$ (natToWord 64 0)
                                                       as mie;
                                                       Ret #mie
                                                  else Ret $$ (natToWord 64 0)
                                                    as mie;
                    If (csradr == $$ (12'h"305")) then Read mtvec : Bit 64       <- `"mtvec"; Ret (correctRead (mtvec_fields _) #mtvec)
                                                  else Ret $$ (natToWord 64 0)
                                                    as mtvec;
                    If (csradr == $$ (12'h"306")) then Read mcounteren : Bit 32  <- `"mcounteren"; Ret (correctRead (mcounteren_fields _) (SignExtend (XLEN-32) #mcounteren))
                                                  else Ret $$ (natToWord 64 0)
                                                    as mcounteren;
                    If (csradr == $$ (12'h"307")) then Read mtvt : Bit 64        <- `"mtvt"; Ret (correctRead (mtvt_fields _) #mtvt)
                                                  else Ret $$ (natToWord 64 0)
                                                    as mtvt;
                    If (csradr == $$ (12'h"340")) then Read mscratch : Bit 64    <- `"mscratch"; Ret (correctRead (mscratch_fields _) #mscratch)
                                                  else Ret $$ (natToWord 64 0)
                                                    as mscratch;
                    If (csradr == $$ (12'h"341")) then Read mepc : Bit 64        <- `"mepc"; Ret (correctRead (mepc_fields _) #mepc)
                                                  else Ret $$ (natToWord 64 0)
                                                    as mepc;
                    If (csradr == $$ (12'h"342")) then Read mcause : Bit 64      <- `"mcause"; Ret (correctRead (mcause_fields _) #mcause)
                                                  else Ret $$ (natToWord 64 0)
                                                    as mcause;
                    If (csradr == $$ (12'h"343")) then Read mtval : Bit 64       <- `"mtval"; Ret (correctRead (mtval_fields _) #mtval)
                                                  else Ret $$ (natToWord 64 0)
                                                    as mtval;
                    If (csradr == $$ (12'h"344")) then Read mtvec : Bit 64 <- `"mtvec";
                                                       If #mtvec $[ 1 : 1 ] == $0
                                                       then Read mip : Bit 64    <- `"mip"; Ret (correctRead (mip_fields _) #mip)
                                                       else Ret $$ (natToWord 64 0)
                                                       as mip;
                                                       Ret #mip
                                                  else Ret $$ (natToWord 64 0)
                                                    as mip;
                    If (csradr == $$ (12'h"345")) then Read mcause : Bit 64      <- `"mcause"; Ret (correctRead (mcause_fields _) #mcause)
                                                  else Ret $$ (natToWord 64 0)
                                                    as mnxti;
                    If (csradr == $$ (12'h"346")) then Read mintstatus : Bit 64  <- `"mintstatus"; Ret (correctRead (mintstatus_fields _) #mintstatus)
                                                  else Ret $$ (natToWord 64 0)
                                                    as mintstatus;
                    If (csradr == $$ (12'h"348")) then Read mscratchcsw : Bit 64 <- `"mscratchcsw"; Ret (correctRead (mscratchcsw_fields _) #mscratchcsw)
                                                  else Ret $$ (natToWord 64 0)
                                                    as mscratchcsw;
                    If (csradr == $$ (12'h"B00")) ||
                       (csradr == $$ (12'h"C00")) then Read mcycle : Bit 64      <- `"mcycle"; Ret (correctRead (mcycle_fields _) #mcycle)
                                                  else Ret $$ (natToWord 64 0)
                                                    as mcycle;
                    If (csradr == $$ (12'h"B02")) ||
                       (csradr == $$ (12'h"C02")) then Read minstret : Bit 64    <- `"minstret"; Ret (correctRead (minstret_fields _) #minstret)
                                                  else Ret $$ (natToWord 64 0)
                                                    as minstret;

                    Ret (#mvendorid | #marchid | #mimpid | #mhartid |
                         #mstatus | #misa | #mie | #mtvec | #mcounteren | #mtvt |
                         #mscratch | #mepc | #mcause | #mtval | #mip | #mnxti |
                         #mintstatus | #mscratchcsw | #mcycle | #minstret)
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

        Open Scope kami_expr.
        Open Scope kami_action.
        Variable ty : Kind -> Type.
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

                    If !(#wecsr && (#csradr == $$ (12'h"B02"))) && !#except
                                then    Write `"minstret" <- #minstret + $$ (natToWord 64 1); Retv;

                    Read mtvec : Bit 64 <- `"mtvec";
                    Read mepc           <- `"mepc";

                    If (#wecsr) then   (If (#csradr == $$ (12'h"300")) then (Write `"mstatus" <- #data;     Retv);
                                        If (#csradr == $$ (12'h"304")) then (Write `"mie" <- #data;         Retv);
                                        If (#csradr == $$ (12'h"305")) then (Write `"mtvec" <- #data;       Retv);
                                        If (#csradr == $$ (12'h"306")) then (Write `"mcounteren" <- #data;  Retv);
                                        If (#csradr == $$ (12'h"307")) then (Write `"mtvt" <- #data;        Retv);
                                        If (#csradr == $$ (12'h"340")) then (Write `"mscratch" <- #data;    Retv);
                                        If (#csradr == $$ (12'h"341")) then (Write `"mepc" <- #data;        Retv);
                                        If (#csradr == $$ (12'h"342")) then (Write `"mcause" <- #data;      Retv);
                                        If (#csradr == $$ (12'h"343")) then (Write `"mtval" <- #data;       Retv);
                                        If (#csradr == $$ (12'h"344")) then (Write `"mip" <- #data;         Retv);
                                        If (#csradr == $$ (12'h"345")) then (Write `"mcause" <- #data;      Retv);
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

                    LET vector_base     <- {< (#mtvec $[ 63 : 2 ]) , ($$ WO~0~0) >};
                    LET vectoring_mode  <- #mtvec $[ 1 : 0 ];
                    LET exc_addr        <- IF #vectoring_mode == $0
                                           then #vector_base
                                           else (IF #vectoring_mode == $1
                                                 then #vector_base + {< (ZeroExtend 58 #cause) , ($$ WO~0~0) >}
                                                 else (IF #vectoring_mode == $2
                                                       then #vector_base (* TODO add CLIC support *)
                                                       else #vector_base (* TODO add CLIC support *)
                                                      )
                                                );
                    LET final_pc        <- IF #except then #exc_addr
                                           else (IF #ret then #mepc
                                                         else #reqPC);

                    Ret #final_pc
        ). Defined.
    End WriteCSR.
End ControlStatusRegisters.
