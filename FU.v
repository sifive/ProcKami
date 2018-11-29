Require Import Kami.All.

Inductive InstSize := Compressed | Normal.

Definition UniqId := (InstSize * list {x: (nat * nat) & word (fst x - snd x + 1)})%type.

Section Params.
  Variable Xlen_over_8: nat.

  Local Notation Xlen := (8 * Xlen_over_8).
  Local Notation Data := (Bit Xlen).
  Local Notation VAddr := (Bit Xlen).
  Local Notation DataMask := (Bit Xlen_over_8).

  Definition PrivMode := (Bit 2).

  Definition Inst := (Bit 32).

  Definition Exception := (Bit 4).

  Definition MemOp := (Bit 4).

  Definition GenContextUpdTag := Bit 3.

  Definition ControlInst := 0.
  Definition IntInst := 1.
  Definition FloatInst := 2.
  Definition CsrInst := 3.
  Definition MemInst := 4.

  Definition GenContextPkt :=
    STRUCT { "pc"           :: VAddr ;
             "reg1"         :: Data ;
             "reg2"         :: Data ;
             "freg1"        :: Data ;
             "freg2"        :: Data ;
             "csr"          :: Data ;
             "inst"         :: Inst ;
             "mode"         :: PrivMode }.

  Definition GenContextUpdPkt :=
    STRUCT { "tag"        :: GenContextUpdTag ;
             "val1"       :: Data ;
             "val2"       :: Data ;
             "memOp"      :: MemOp ;
             "memBitMask" :: DataMask ;
             "exception"  :: Maybe Exception }.

  Section Ty.
    Variable ty: Kind -> Type.

    Definition invalidException := (STRUCT { "valid" ::= $$ false ;
                                             "data" ::= $$ (getDefaultConst Exception)})%kami_expr.
    
    Record LoadXform :=
      { loadK: Kind ;
        loadXform: loadK @# ty -> Data ## ty }.
    
    
    Record InstEntry ik ok :=
      { instName     : string ;
        uniqId       : UniqId ;
        inputXform   : GenContextPkt ## ty -> ik ## ty ;
        outputXform  : ok ## ty -> GenContextUpdPkt ## ty ;
        optLoadXform : option LoadXform }.

    Record FUEntry :=
      { fuName    : string ;
        fuInputK  : Kind ;
        fuOutputK : Kind ;
        fuFunc    : fuInputK ## ty -> fuOutputK ## ty ;
        fuInsts   : list (InstEntry fuInputK fuOutputK) }.
  End Ty.

  Definition DecoderInput :=
    STRUCT { "pc"   :: VAddr ;
             "inst" :: Inst ;
             "mode" :: PrivMode }.

  Definition DecoderOutput :=
    STRUCT { "inst"            :: Inst ; (* Normal (Uncompressed) instruction *)
             "rs1?"            :: Bool ;
             "rs2?"            :: Bool ;
             "rd?"             :: Bool ;
             "csr?"            :: Bool ;
             "isBranch?"       :: Bool ;
             "jump"            :: Maybe VAddr ;
             "system?"         :: Bool ;
             "compressed?"     :: Bool ;
             "illegal?"        :: Bool ; (* opcode[1:0] is not Compressed or Normal, or instruction is not valid *)
             "misalignedJump?" :: Bool ; (* Generated Jump is not aligned to N byte boundaries,
                                            N is 4 or 8 depending on support for compressed instructions *)
             "misaligned?"     :: Bool ; (* Current instruction is not aligned to N byte boundaries
                                            N is 4 or 8 depending on support for compressed instructions *)
             "privilegeFault"  :: Bool   (* Current Privilege mode not sufficient *)
           }.
End Params.
