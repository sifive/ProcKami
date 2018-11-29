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

  Definition MemOp :=
    STRUCT { "sub_opcode" :: Bit 2 ;
             "funct3"     :: Bit 3 ;
             "funct5"     :: Bit 5 }.

  Section Fields.
    Variable ty: Kind -> Type.
    Variable inst: Inst @# ty.
    Local Open Scope kami_expr.
    Definition opcode := inst$[6:2].
    Definition funct3 := inst$[14:12].
    Definition funct5 := inst$[31:27].
    Definition mem_sub_opcode := {< (inst$[5:5]), (inst$[3:3])>}.
    Local Close Scope kami_expr.
  End Fields.

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
    Context {ty: Kind -> Type}.

    Local Open Scope kami_expr.

    Definition LoadOp funct3 : MemOp @# ty := STRUCT { "sub_opcode" ::= $$ (2'b"00") ;
                                                       "funct3"     ::= funct3 ;
                                                       "funct5"     ::= $0
                                                     }.
    
    Definition StoreOp funct3 : MemOp @# ty := STRUCT { "sub_opcode" ::= $$ (2'b"10") ;
                                                        "funct3"     ::= funct3 ;
                                                        "funct5"     ::= $0
                                                      }.
    
    Definition AmoOp funct3 funct5 : MemOp @# ty := STRUCT { "sub_opcode" ::= $$ (2'b"11") ;
                                                             "funct3"     ::= funct3 ;
                                                             "funct5"     ::= funct5
                                                           }.
    
    Definition invalidException := STRUCT { "valid" ::= $$ false ;
                                            "data" ::= $$ (getDefaultConst Exception)}.
    
    Definition createControl pc : GenContextUpdPkt @# ty :=
      STRUCT { "tag"        ::= $ControlInst ;
               "val1"       ::= pc ;
               "val2"       ::= $0 ;
               "memOp"      ::= $$ (getDefaultConst MemOp) ;
               "memBitMask" ::= $0 ;
               "exception"  ::= invalidException }.

    Definition createInt val : GenContextUpdPkt @# ty :=
      STRUCT { "tag"        ::= $IntInst ;
               "val1"       ::= val ;
               "val2"       ::= $0 ;
               "memOp"      ::= $$ (getDefaultConst MemOp) ;
               "memBitMask" ::= $0 ;
               "exception"  ::= invalidException }.

    Definition createFloat floatVal intVal exception : GenContextUpdPkt @# ty :=
      STRUCT { "tag"        ::= $FloatInst ;
               "val1"       ::= intVal ;
               "val2"       ::= floatVal ;
               "memOp"      ::= $$ (getDefaultConst MemOp) ;
               "memBitMask" ::= $0 ;
               "exception"  ::= exception }.

    Definition createSimpleFloat floatVal exception : GenContextUpdPkt @# ty :=
      STRUCT { "tag"        ::= $FloatInst ;
               "val1"       ::= $0 ;
               "val2"       ::= floatVal ;
               "memOp"      ::= $$ (getDefaultConst MemOp) ;
               "memBitMask" ::= $0 ;
               "exception"  ::= exception }.

    Definition createCsr csrVal intVal exception : GenContextUpdPkt @# ty :=
      STRUCT { "tag"        ::= $CsrInst ;
               "val1"       ::= intVal ;
               "val2"       ::= csrVal ;
               "memOp"      ::= $$ (getDefaultConst MemOp) ;
               "memBitMask" ::= $0 ;
               "exception"  ::= exception }.

    Definition createMem memOp memAddr memBitMask memData exception : GenContextUpdPkt @# ty :=
      STRUCT { "tag"        ::= $MemInst ;
               "val1"       ::= memAddr ;
               "val2"       ::= memData ;
               "memOp"      ::= memOp ;
               "memBitMask" ::= memBitMask ;
               "exception"  ::= exception }.

    Local Close Scope kami_expr.
    
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
