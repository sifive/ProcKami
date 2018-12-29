Require Import Kami.All RecordUpdate.RecordSet FU Mem Decoder.
Require Import List.
Import RecordNotations.

Section Mem.
  Variable Xlen_over_8: nat.

  Variable name: string.
  Local Notation "^ x" := (name ++ "_" ++ x)%string (at level 0).
  
  Notation Xlen := (8 * Xlen_over_8).

  Notation Data := (Bit Xlen).
  Notation VAddr := (Bit Xlen).
  Notation DataMask := (Bit Xlen_over_8).

  Definition MemRead := STRUCT {
                            "data" :: Data ;
                            "exception?" :: Maybe Exception }.

  Definition MemWrite := STRUCT {
                             "addr" :: VAddr ;
                             "data" :: Data }.
  
  Definition MemRet := STRUCT {
                           "writeReg?" :: Bool ;
                           "data" :: Data ;
                           "exception?" :: Maybe Exception }.
  
  Definition MemUnitInput := STRUCT {
                                 "aq" :: Bool ;
                                 "rl" :: Bool ;
                                 "reservation" :: Bit 2 ;
                                 "reg" :: Data
                               }.

  Section Ty.
    Variable ty: Kind -> Type.

    
    Local Notation noUpdPkt := (@noUpdPkt Xlen_over_8 ty).
    Local Notation MemoryInput := (MemoryInput Xlen_over_8).
    Local Notation MemoryOutput := (MemoryOutput Xlen_over_8).
    Local Notation MaskedMem := (MaskedMem Xlen_over_8).

    Let func_unit_type
      :  Type
      := @FUEntry Xlen_over_8 ty.

    Let inst_type (sem_input_kind sem_output_kind : Kind)
      :  Type
      := @InstEntry Xlen_over_8 ty sem_input_kind sem_output_kind.

    Let exec_context_pkt_kind : Kind
      := ExecContextPkt Xlen_over_8.

    (* The functional units that comprise the instruction database. *)
    Variable func_units : list func_unit_type.

    Let func_unit_id_width := Decoder.func_unit_id_width func_units.

    Let inst_id_width := Decoder.inst_id_width func_units.

    Let func_unit_id_kind := Decoder.func_unit_id_kind func_units.

    Let inst_id_kind := Decoder.inst_id_kind func_units.

    
    Definition getMemEntryFromInsts ik ok (insts: list (inst_type ik ok)) pos :
      option (LetExprSyntax ty (FU.MemoryInput Xlen_over_8) ->
              LetExprSyntax ty (FU.MemoryOutput Xlen_over_8)) :=
      match find (fun x => getBool (Nat.eq_dec pos (fst x))) (tag insts) with
      | None => None
      | Some inst => match optMemXform (snd inst)
                     with
                     | None => None
                     | Some val => Some val
                     end
      end.

    Fixpoint getMemEntryFromFus (fus: list func_unit_type) pos:
      option (LetExprSyntax ty (FU.MemoryInput Xlen_over_8) ->
              LetExprSyntax ty (FU.MemoryOutput Xlen_over_8)) :=
      match fus with
      | nil => None
      | x :: xs => match getMemEntryFromInsts (fuInsts x) pos with
                     | Some val => Some val
                     | None => getMemEntryFromFus xs pos
                   end
      end.

    Definition getMemEntry := getMemEntryFromFus func_units.

    Local Open Scope kami_expr.
    Definition makeMemoryInput (i: MemUnitInput @# ty) (mem: Data @# ty) : MemoryInput @# ty :=
      STRUCT {
          "aq" ::= i @% "aq" ;
          "rl" ::= i @% "rl" ;
          "reservation" ::= i @% "reservation" ;
          "mem" ::= mem ;
          "reg" ::= i @% "reg"
        }.

    Definition applyMask (read: Data @# ty) (write: MaskedMem @# ty): Data ## ty.
      refine (
          LETC mask <- write @% "mask" ;
          LETC data <- write @% "data" ;
          LETC dataByte <- unpack (Array Xlen_over_8 (Bit 8)) (castBits _ #data) ;
          LETC readByte <- unpack (Array Xlen_over_8 (Bit 8)) (castBits _ read) ;
          LETC writeByte <- BuildArray (fun i => (IF ReadArrayConst #mask i
                                                  then ReadArrayConst #dataByte i
                                                  else ReadArrayConst #readByte i)) ;
          RetE (castBits _ (pack #writeByte))); unfold size; try abstract lia.
    Defined.

    Section MemAddr.
      Variable addr: VAddr @# ty.
      Variable instTag: inst_id_kind @# ty.
      Variable memUnitInput: MemUnitInput @# ty.

      Definition defMemRet: MemRet @# ty := STRUCT {
                                                "writeReg?" ::= $$ false ;
                                                "data" ::= $ 0 ;
                                                "exception?" ::= Invalid }.
      Local Open Scope kami_action.
      Definition memAction (tag: nat) : ActionT ty MemRet :=
        match getMemEntry tag with
        | Some fn =>
          Call memRead: MemRead <- "memRead"(addr: _);
            (If #memRead @% "exception?" @% "valid"
             then Ret defMemRet
             else
               (LETA memoryOutput : MemoryOutput
                                      <-
                                      convertLetExprSyntax_ActionT
                                      (fn (RetE (makeMemoryInput memUnitInput
                                                                 (#memRead @% "data"))));
                  LETA writeVal : Data <- convertLetExprSyntax_ActionT
                                       (applyMask (#memRead @% "data") (#memoryOutput @% "mem" @% "data"));
                  LET memWrite: MemWrite <- STRUCT {
                                           "addr" ::= addr ;
                                           "data" ::= #writeVal };
                  If (#memoryOutput @% "mem" @% "valid")
                  then (Call writeEx: Maybe Exception <- "memWrite"(#memWrite: _);
                          Ret #writeEx)
                  else Ret (@Invalid _ Exception)
                  as writeEx;
                  LET memRet: MemRet <- STRUCT {
                                       "writeReg?" ::= #memoryOutput @% "reg" @% "valid" ;
                                       "data" ::= #memoryOutput @% "reg" @% "data" ;
                                       "exception?" ::= #writeEx } ;
                  Ret #memRet
               ) 
              as ret;
               Ret #ret)
        | None => Ret defMemRet
        end.

      Definition fullMemAction: ActionT ty MemRet :=
        GatherActions (map memAction (0 upto (inst_max_num func_units))) as retVals;
          Ret (unpack MemRet (CABit Bor (map (@pack ty MemRet) retVals))).
      Local Close Scope kami_action.
    End MemAddr.
  End Ty.
End Mem.