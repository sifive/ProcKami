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
    | HardZero msb lsb      => ClearBits lsb msb acc
    | Unsupported n msb lsb => ReplaceBits lsb msb (ExtractBits lsb msb prev) acc
    | WIRI msb lsb   => ReplaceBits lsb msb (ExtractBits lsb msb prev) acc
    | WPRIfc msb lsb => ClearBits lsb msb acc
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
   cycle[h]          --                          --                          --                         Read only, shadows "mcycle", accessibility-in-User-mode set by "mscounteren"
   time[h]           --                          --                          --                         Read only, memory-mapped, accessibility-in-User-mode set by "mcounteren"
   instret[h]        --                          --                          --                         Read only, shadows "minstret", accessibility-in-User-mode set by "mcounteren"
   hpmcounter*[h]    --                          --                          --                         Hardwired to 0, accessibility-in-User-mode set by "mcounteren"

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
   mcause           Trap Vectoring, mstatus     Exceptions, mnxti            --                         Some fields appear as 0 in CLIC mode
   mtval             --                         Exceptions                   --                          --
   mip              (Exceptions)                Exceptions                  Exceptions                  Appears as 0 in CLIC mode (including reads for the purpose of CSR modification)
   mnxti             --                          --                         mcause, minstatus           Not a physical register
   mintstatus        --                         Exceptions, mnxti            --                          --
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

        (* Note that UXL is hardwired to MXL - shadowing in general is handled in ReadCSR_action *)
        Definition mpp_okay := fun (m : Bit 2 @# ty) => if USER_MODE then (m == $$ WO~0~0 || m == $$ WO~1~1) else (m == $$ WO~1~1).
        Definition mstatus_fields := Unsupported ty "SD" 63 63    :: WPRIfc _ 62 36            :: Unsupported _ "SXL" 35 34 ::
                                     ReadOnly    _ "UXL" 33 32    :: WPRIfc _ 31 23            :: Unsupported _ "TSR" 22 22 ::
                                     Unsupported _  "TW" 21 21    :: Unsupported _ "TVM" 20 20 :: Unsupported _ "MXR" 19 19 ::
                                     Unsupported _ "SUM" 18 18    :: Unsupported _  "XS" 16 15 :: Unsupported _  "FS" 14 13 ::
                                     WARLaon "MPP" 12 11 mpp_okay :: WPRIfc _ 10 9             :: Unsupported _ "SPP"  8  8 ::
                                     WPRIfc _ 6 6                 :: Unsupported _ "SPIE" 5  5 :: Unsupported _ "UPIE" 4  4 ::
                                     WPRIfc _ 2 2                 :: Unsupported _ "SIE"  1  1 :: Unsupported _ "UIE"  0  0 :: nil.

        Definition mie_fields := WPRIfc ty 63 12          :: WPRIfc _ 10 10 :: Unsupported _ "SEIE" 9 9 ::
                                 Unsupported _ "UEIE" 8 8 :: WPRIfc _  6  6 :: Unsupported _ "STIE" 5 5 ::
                                 Unsupported _ "UTIE" 4 4 :: WPRIfc _  2  2 :: Unsupported _ "SSIE" 1 1 ::
                                 Unsupported _ "USIE" 0 0 :: nil.

        Definition mtvec_legalize := fun (m : Bit 6 @# ty) => IF m$[1:1] == $$ WO~1 then {<($$WO~0~0~0~0),(m$[1:0])>} else m.
        Definition mtvec_fields := WARLawm "MODE" 5 0 mtvec_legalize :: nil.
        (*Definition mtvec_legalize := fun (m : Bit 6 @# type) => IF m$[1:1] == Const _ WO~1 then {<(Const _ WO~0~0~0~0),(m$[1:0])>} else m.*)
        (*Definition mtvec_fields := WARLawm "MODE" 5 0 mtvec_legalize :: nil.*)
        (*Eval simpl in evalExpr (correctWrite mtvec_fields (Const _ (64'h"0000000000000000")) (Const _ (64'h"FFFFFFFFFFFFFFFE"))).*)

        (* Note that mcounteren is a 32-bit register *)
        Definition mcounteren_fields := Unsupported ty "HPM" 31 3 :: Unsupported _ "TM" 1 1 :: nil.

        Definition mtvt_legalize := fun (m : Bit 64 @# ty) => ClearBits 0 5 m.
        Definition mtvt_fields := WARLawm "" 63 0 mtvt_legalize :: nil.

        Definition mscratch_fields := @nil (CSRField ty).
        Definition mepc_fields := HardZero ty (if IALIGNW then 1 else 0) 0 :: nil.
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

    (* TODO time 0xC01 memory mapped register - may be accessed in M mode *)
    (* TODO deal with the mnxti business: modify returned data struct *)
    (* TODO deal with the mscratchcsw business: rd <- (mpp = current privilege mode ? rs1 : mscratch), mscratch <- mscratch * other source IF mpp != current privilege mode *)
    (* TODO figure out mtval behavior - in the Scala code this is still called "mbadaddr" *)
    (* TODO "When CLINT mode is written to mtvec, the new mcause state fields are zeroed. The other new mcause fields appear as zero in
              the mcause CSR but the corresponding state bits in the mstatus register are not cleared."
            "The new CLIC-specific fields appear to be hardwired to zero in CLINT mode" *)

    Section ValidateUserAccess.
        Definition UserAccess := STRUCT {
                                    "except?" :: Bool;
                                    "cause"  :: Bit 11
                                }.
        Open Scope kami_expr.
        Open Scope kami_action.
        Variable ty : Kind -> Type.
        Variable mode : Bit 2 @# ty.
        Variable except : Bool @# ty.
        Variable cause : Bit 11 @# ty.
        Variable csr : Bool @# ty.
        Variable csradr : Bit 12 @# ty.
        Definition OkayUserAccess_action : ActionT ty UserAccess.
        exact(
            (* This sort of exception is raised here, and not in Decode, since in a pipeline an older instruction may modify mcounteren
               while a user counter access is in flight.                                                                                *)
            (* See "csr_exists" in Decode.v - maybe this should be passed from there rather than copied? *)
            LET top7 <- csradr $[ 11 : 5 ];
            LET bot5 <- csradr $[  4 : 0 ];
            LET user_counter : Bool <- (#top7 == $$ WO~1~1~0~0~0~0~0) || (if RV32 then #top7 == $$ WO~1~1~0~0~1~0~0 else $$ false);
            LET user_mode : Bool <- mode == $$ WO~0~0;
            If ((!except) && csr && #user_counter && #user_mode)
                then Read mcounteren : Bit 32 <- `"mcounteren";
                     Ret ( (#mcounteren $[ 0 : 0 ] == $$ WO~1) && (#bot5 == $$ (natToWord 5 0)) ||
                           (#mcounteren $[ 1 : 1 ] == $$ WO~1) && (#bot5 == $$ (natToWord 5 1)) ||
                           (#mcounteren $[ 2 : 2 ] == $$ WO~1) && (#bot5 == $$ (natToWord 5 2)) )
                         (* and so on - TODO write a little Gallina function that does the whole thing *)
                else Ret $$ false as forbidden;
            LET new_except <- except || #forbidden;
            LET new_cause  <- IF except
                                 then cause
                                 else (IF #forbidden
                                       then $$ Exception_Illegal_Instr
                                       else $$ (natToWord 11 0)
                                 );
            LET userAccess : UserAccess <- STRUCT {
                                            "except?" ::= #new_except;
                                            "cause"  ::= #new_cause
                                           };
            Ret #userAccess
        ). Defined.
    End ValidateUserAccess.

    Section ReadCSR.
        Definition misa_hardwire : word 64 := Word.combine (Word.combine Extensions (natToWord 36 0)) MXL.

        Open Scope kami_expr.
        Open Scope kami_action.
        Variable ty : Kind -> Type.
        Variable csradr : Bit 12 @# ty.
        Definition ReadCSR_action : ActionT ty (Bit 64).
        (* TODO UXL shadowing in mstatus *)
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
            If (csradr == $$ (12'h"306")) then Read mcounteren : Bit 32  <- `"mcounteren"; Ret (correctRead (mcounteren_fields _) (ZeroExtend (XLEN-32) #mcounteren))
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
            If (csradr == $$ (12'h"348")) then Read mscratch : Bit 64    <- `"mscratch"; Ret (correctRead (mscratch_fields _) #mscratch)
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

    Section CLICVector.
        (* TODO look at CLIC interrupt to determine vectoring (nvbits and all that) *)
        Definition TableLookup := STRUCT {
            "needed?" :: Bool;
            "addr"    :: Bit 64
        }.

        Open Scope kami_expr.
        Open Scope kami_action.
        Variable ty : Kind -> Type.
        Variable except : Bool @# ty.
        Variable cause : Bit 11 @# ty.
        Definition ClicVector_action : ActionT ty TableLookup.
        exact(
            (* Should these reads be legalized? It wouldn't matter for correctness now, but may save someone's oversight down the line. *)
            Read mtvec  : Bit 64 <- `"mtvec";
            LET vectoring_mode   <- #mtvec $[ 1 : 0 ];
            LET intpt   : Bit  1 <- cause $[ 10 : 10 ];
            LET exccode : Bit 10 <- cause $[ 9 : 0 ];
            LET clic_vectoring : Bool <- except && (#vectoring_mode == $3) && (#intpt == $$ WO~1);
            If #clic_vectoring then
                Read mtvt : Bit 64 <- `"mtvt";
                LET pointer_addr : Bit 64 <- #mtvt + (if RV32 then {< (ZeroExtend 51 #exccode) , ($$ WO~0~0~0) >} else {< (ZeroExtend 52 #exccode) , ($$ WO~0~0) >});
                Ret #pointer_addr
            else
                Ret $$ (natToWord 64 0)
            as pointer_addr;
            LET table_lookup : TableLookup <- STRUCT {
                                                "needed?" ::= #clic_vectoring;
                                                "addr"    ::= #pointer_addr
                                              };
            Ret #table_lookup
        ). Defined.
    End CLICVector.

    Section WriteCSR.
        Definition CSRCtrl := STRUCT {
            "wecsr"      :: Bool   ;
            "csradr"     :: Bit 12 ;
            "twiddleOut" :: Bit 64 ;
            "pc"         :: Bit 64 ;
            "except?"    :: Bool   ;
            "cause"      :: Bit 11 ;
            "ret?"       :: Bool   ;
            "reqPC"      :: Bit 64
        }.

        Definition RInst := STRUCT {
            "mode"   :: Bit 2;
            "pc"     :: Bit XLEN;
            "werf"   :: Bool;
            "rd_val" :: Bit XLEN
        }.

        Open Scope kami_expr.
        Open Scope kami_action.
        Variable ty : Kind -> Type.
        Variable mode : Bit 2 @# ty.
        Variable csrCtrl : CSRCtrl @# ty.
        Variable mtvtMemResp : Bit XLEN @# ty.
        Variable req_werf : Bool @# ty.
        Variable req_rd_val : Bit XLEN @# ty.
        Definition WriteCSRandRetire_action : ActionT ty RInst.
        exact(
            LET wecsr            <- csrCtrl @% "wecsr";
            LET csradr           <- csrCtrl @% "csradr";
            LET data             <- csrCtrl @% "twiddleOut";
            LET pc               <- csrCtrl @% "pc";
            LET except           <- csrCtrl @% "except?";
            LET cause            <- csrCtrl @% "cause";
            LET intpt   : Bit  1 <- #cause $[ 10 : 10 ];
            LET exccode : Bit 10 <- #cause $[ 9 : 0 ];
            LET ret              <- csrCtrl @% "ret?";
            LET reqPC            <- csrCtrl @% "reqPC";

            (* TODO? faults during mtvt table access *)

            Read mcycle         <- `"mcycle";
            Read minstret       <- `"minstret";

            If !(#wecsr && (#csradr == $$ (12'h"B00")))
                        then Write `"mcycle" <- #mcycle + $$ (natToWord 64 1); Retv;

            If (!(#wecsr && (#csradr == $$ (12'h"B02")))) && !#except
                        then Write `"minstret" <- #minstret + $$ (natToWord 64 1); Retv;

            (* These could also be passed from ClicVector_action to avoid a double read, but the trouble is not worth it, and in any case
               the synthesized hardware ought to be identical, barring pipeline issues.                                                     *)
            Read mtvec_un       <- `"mtvec";
            Read mepc_un        <- `"mepc";
            LET mtvec           <- correctRead (mtvec_fields _) #mtvec_un;
            LET mepc            <- correctRead (mepc_fields _) #mepc_un;

            If (#wecsr) then   (If (#csradr == $$ (12'h"300")) then (Read mstatus    : Bit 64 <- `"mstatus"   ; Write `"mstatus"    <- (correctWrite (mstatus_fields _) #mstatus #data); Retv);
                                If (#csradr == $$ (12'h"304")) then (Read mie        : Bit 64 <- `"mie"       ; Write `"mie"        <- (correctWrite (mie_fields _) #mie #data); Retv);
                                If (#csradr == $$ (12'h"305")) then (                                           Write `"mtvec"      <- (correctWrite (mtvec_fields _) #mtvec #data); Retv);
                                If (#csradr == $$ (12'h"306")) then (Read mcounteren : Bit 32 <- `"mcounteren"; Write `"mcounteren" <- (correctWrite (mcounteren_fields _) (ZeroExtend 32 #mcounteren) #data) $[ 31 : 0 ]; Retv);
                                If (#csradr == $$ (12'h"307")) then (Read mtvt       : Bit 64 <- `"mtvt"      ; Write `"mtvt"       <- (correctWrite (mtvt_fields _) #mtvt #data); Retv);
                                If (#csradr == $$ (12'h"340")) then (Read mscratch   : Bit 64 <- `"mscratch"  ; Write `"mscratch"   <- (correctWrite (mscratch_fields _) #mscratch #data); Retv);
                                If (#csradr == $$ (12'h"341")) then (                                           Write `"mepc"       <- (correctWrite (mepc_fields _) #mepc #data); Retv);
                                If (#csradr == $$ (12'h"342")) then (Read mcause     : Bit 64 <- `"mcause"    ; Write `"mcause"     <- (correctWrite (mcause_fields _) #mcause #data); Retv);
                                If (#csradr == $$ (12'h"343")) then (Read mtval      : Bit 64 <- `"mtval"     ; Write `"mtval"      <- (correctWrite (mtval_fields _) #mtval #data); Retv);
                                If (#csradr == $$ (12'h"344")) then (Read mip        : Bit 64 <- `"mip"       ; Write `"mip"        <- (correctWrite (mip_fields _) #mip #data); Retv);
                                If (#csradr == $$ (12'h"345")) then (Read mcause     : Bit 64 <- `"mcause"    ; Write `"mcause"     <- (correctWrite (mcause_fields _) #mcause #data); Retv);
                                If (#csradr == $$ (12'h"346")) then (Read mintstatus : Bit 64 <- `"mintstatus"; Write `"mintstatus" <- (correctWrite (mintstatus_fields _) #mintstatus #data); Retv);
                                (* 12'h"348" mscratchcsw *)
                                If (#csradr == $$ (12'h"B00")) then (Read mcycle     : Bit 64 <- `"mcycle"    ; Write `"mcycle"     <- (correctWrite (mcycle_fields _) #mcycle #data); Retv);
                                If (#csradr == $$ (12'h"B02")) then (Read minstret   : Bit 64 <- `"minstret"  ; Write `"minstret"   <- (correctWrite (minstret_fields _) #minstret #data); Retv);
                                Retv
                               );
            If (#except) then   Write `"mepc" <- #pc;
                                Write `"mcause" <- {< #intpt , (ZeroExtend 53 #exccode) >};
                                (* MPIE = 7
                                   MIE = 3
                                   MPP = 12:11
                                 Trap from y into x (x will always be M mode)
                                   xPIE <- xIE
                                   xIE  <- 0
                                   xPP  <- y
                                   mode <- x
                                *)
                                Read mstatus : Bit 64 <- `"mstatus";
                                Write `"mstatus" <- ReplaceBits 11 12 (mode)
                                                   (ReplaceBits  3  3 ($$ WO~0)
                                                   (ReplaceBits  7  7 (ExtractBits 3 3 #mstatus) #mstatus));
                                Ret $$ WO~1~1
                                (* xRET instruction, xPP = y
                                     xPIE <- 1
                                     xIE  <- xPIE
                                     xPP  <- User mode supported ? U : M
                                     mode <- y
                                *)
                         else   If #ret then Read mstatus : Bit 64 <- `"mstatus";
                                             Write `"mstatus" <- ReplaceBits 11 12 (if USER_MODE then $$ WO~0~0 else $$ WO~1~1)
                                                                (ReplaceBits  7  7 ($$ WO~1)
                                                                (ReplaceBits  3  3 (ExtractBits 7 7 #mstatus) #mstatus));
                                             Ret (ExtractBits 11 12 #mstatus)
                                       else Ret mode
                                         as next_mode;
                                Ret #next_mode
                           as   next_mode;

            LET vector_base     <- {< (#mtvec $[ 63 : 2 ]) , ($$ WO~0~0) >};
            LET vectoring_mode  <- #mtvec $[ 1 : 0 ];
            LET exc_addr        <- IF #vectoring_mode == $0
                                   then #vector_base
                                   else (IF #vectoring_mode == $1
                                         then #vector_base + {< (ZeroExtend 52 #exccode) , ($$ WO~0~0) >}
                                         else (IF (#vectoring_mode == $2) || (#intpt == $$ WO~0)
                                               then #vector_base
                                               else {< (mtvtMemResp $[ 63 : 1 ]) , ($$ WO~0) >}
                                              )
                                        );
            LET final_pc        <- IF #except then #exc_addr
                                   else (IF #ret then #mepc
                                                 else #reqPC);
            (* #rdSrc == $$ Rd_csr
               csrAdr == mnxti

               mstatus <- mstatus * mask
               rd <- IF (no suitable interrupt to service) or (highest ranked interrupt is Selective Hardware Vectoring) or (system is ~not~ in a CLIC mode)
                     THEN 0
                     ELSE Address of the entry in the trap handler table for software trap vectoring

               mcause.exccode and minstatus.mil can be updated with new interrupt ID and level respectively
            *)

            LET rInst : RInst   <- STRUCT {
                                    "mode"   ::= #next_mode;
                                    "pc"     ::= #final_pc;
                                    "werf"   ::= req_werf;  (* May be modified if the mtvt lookup faults *)
                                    "rd_val" ::= req_rd_val (* May be modified because of mnxti          *)
                                    };
            Ret #rInst
        ). Defined.
    End WriteCSR.
End ControlStatusRegisters.
