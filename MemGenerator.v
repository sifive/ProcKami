Require Import Kami.All RecordUpdate.RecordSet Fetch FU Mem Decoder.
Require Import List.
Import RecordNotations.

Section Mem.
  Variable memFuNames: list string.
  Variable Xlen_over_8: nat.

  Variable name: string.
  Local Notation "^ x" := (name ++ "_" ++ x)%string (at level 0).
  
  Notation Xlen := (8 * Xlen_over_8).

  Notation Data := (Bit Xlen).
  Notation VAddr := (Bit Xlen).
  Notation DataMask := (Bit Xlen_over_8).

  Definition MemRead := STRUCT {
                            "data" :: Data ;
                            "reservation" :: Bit 2 ;
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
                                 "reg_data" :: Data
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

    Let exec_update_pkt_kind
      := ExecContextUpdPkt Xlen_over_8.

    Let PktWithException := Fetch.PktWithException Xlen_over_8.

    (* The functional units that comprise the instruction database. *)
    Variable func_units : list func_unit_type.

    Let func_unit_id_width := Decoder.func_unit_id_width func_units.

    Let inst_id_width := Decoder.inst_id_width func_units.

    Let func_unit_id_kind := Decoder.func_unit_id_kind func_units.

    Let inst_id_kind := Decoder.inst_id_kind func_units.

    Let decoder_pkt_kind := Decoder.decoder_pkt_kind func_units.
    
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

    Definition memFus := filter (fun x => getBool (in_dec string_dec (fuName (snd x)) memFuNames))
                                (tag func_units).

    Definition lengthMemFus := map (fun x => length (fuInsts (snd x))) memFus.

    Definition tagMemFus: list nat := map fst memFus.

    Definition getMemEntry fu pos:
      option (LetExprSyntax ty (FU.MemoryInput Xlen_over_8) ->
              LetExprSyntax ty (FU.MemoryOutput Xlen_over_8)) :=
      getMemEntryFromInsts (fuInsts fu) pos.

    Local Open Scope kami_expr.
    Definition makeMemoryInput (i: MemUnitInput @# ty) (mem: Data @# ty) (reservation : Bit 2 @# ty) : MemoryInput @# ty :=
      STRUCT {
          "aq" ::= i @% "aq" ;
          "rl" ::= i @% "rl" ;
          "reservation" ::= reservation ;
          "mem" ::= mem ;
          "reg_data" ::= i @% "reg_data"
        }.

    Definition applyMask (read: Data @# ty) (write: Maybe MaskedMem @# ty): Data ## ty.
      refine (
          LETC mask <- write @% "data" @% "mask" ;
          LETC data <- write @% "data" @% "data" ;
          LETC dataByte <- unpack (Array Xlen_over_8 (Bit 8)) (castBits _ #data) ;
          LETC readByte <- unpack (Array Xlen_over_8 (Bit 8)) (castBits _ read) ;
          LETC writeByte <- BuildArray (fun i => (IF ReadArrayConst #mask i
                                                  then ReadArrayConst #dataByte i
                                                  else ReadArrayConst #readByte i)) ;
          RetE (IF write @% "valid" then castBits _ (pack #writeByte) else read)); unfold size; try abstract lia.
    Defined.

    Section MemAddr.
      Variable addr: VAddr @# ty.
      Variable fuTag: func_unit_id_kind @# ty.
      Variable instTag: inst_id_kind @# ty.
      Variable memUnitInput: MemUnitInput @# ty.

      Definition defMemRet: MemRet @# ty := STRUCT {
                                                "writeReg?" ::= $$ false ;
                                                "data" ::= $ 0 ;
                                                "exception?" ::= Invalid }.

      Local Open Scope kami_action.
      Definition memAction fu (tag: nat)
        :  ActionT ty MemRet
        := If instTag == $tag
           then 
             match getMemEntry fu tag with
             | Some fn =>
               Call memRead: MemRead <- "memRead"(addr: _);
               (If #memRead @% "exception?" @% "valid"
                then Ret defMemRet
                else
                  (LETA memoryOutput
                     :  MemoryOutput
                     <- convertLetExprSyntax_ActionT
                          (fn (RetE (makeMemoryInput memUnitInput
                                      (#memRead @% "data")
                                      (#memRead @% "reservation"))));
                   LETA writeVal
                     :  Data
                     <- convertLetExprSyntax_ActionT
                          (applyMask (#memRead @% "data") (#memoryOutput @% "mem" ));
                   LET memWrite
                     :  MemWrite
                     <- STRUCT {
                          "addr" ::= addr;
                          "data" ::= #writeVal
                        };
                   If (#memoryOutput @% "mem" @% "valid")
                     then
                       (Call writeEx: Maybe Exception <- "memWrite"(#memWrite: _);
                        Ret #writeEx)
                     else
                       Ret (@Invalid _ Exception)
                    as writeEx;
                   LET memRet
                     :  MemRet
                     <- STRUCT {
                          "writeReg?" ::= #memoryOutput @% "reg_data" @% "valid";
                          "data" ::= #memoryOutput @% "reg_data" @% "data";
                          "exception?" ::= #writeEx
                        };
                   Ret #memRet
                  ) as ret;
               Ret #ret)
             | None => Ret defMemRet
             end
           else Ret defMemRet
           as ret;
           Ret #ret.

      Definition fullMemAction
        :  ActionT ty MemRet
        := GatherActions
             (map (fun memFu =>
                     (If (fuTag == $ (fst memFu))
                      then 
                        (GatherActions (map (memAction (snd memFu)) (0 upto (length (fuInsts (snd memFu))))) as retVals;
                           Ret (unpack MemRet (CABit Bor (map (@pack ty MemRet) retVals))))
                      else
                        Ret
                          (STRUCT {
                               "writeReg?"  ::= $$ false ;
                               "data"       ::= $0 ;
                               "exception?" ::= Invalid
                          })
                       as ret;
                           Ret #ret)) memFus) as retVals2;
             Ret (unpack MemRet (CABit Bor (map (@pack ty MemRet) retVals2))).

      Local Close Scope kami_action.
    End MemAddr.

    Local Open Scope kami_action.

    (*
      TODO: connect exceptions from the memory unit.
      TODO: replace with record updates.
      TODO: edit parameters so that this function on accepts a exec_update_pkt and a decoder_pkt.
      TODO: accept an exception packet and return an exception packet.
    *)
    Definition MemUnit
      (decoder_pkt : decoder_pkt_kind @# ty)
      (exec_context_pkt : exec_context_pkt_kind @# ty)
      (opt_exec_update_pkt : PktWithException exec_update_pkt_kind @# ty)
      :  ActionT ty (PktWithException exec_update_pkt_kind)
      := let exec_update_pkt
           :  exec_update_pkt_kind @# ty
           := opt_exec_update_pkt @% "fst" in
         LETA memRet
           :  MemRet
           <- fullMemAction
                (exec_update_pkt @% "val1" @% "data" @% "data")
                (decoder_pkt @% "FuncUnitTag")
                (decoder_pkt @% "InstTag")
                (STRUCT {
                   "aq"       ::= exec_update_pkt @% "aq";
                   "rl"       ::= exec_update_pkt @% "rl";
                   "reg_data" ::= exec_context_pkt @% "reg2"
                 } : MemUnitInput @# ty);
         Ret
           (mkPktWithException
             opt_exec_update_pkt
             (STRUCT {
                "fst"
                  ::= (ITE
                        (#memRet @% "writeReg?")
                        (exec_update_pkt
                           @%["val1"
                                <- Valid (STRUCT {
                                     "tag"  ::= $IntRegTag;
                                     "data" ::= #memRet @% "data"
                                   } : RoutedReg Xlen_over_8 @# ty)]
                           @%["exception" <- #memRet @% "exception?"])
                        (exec_update_pkt));
                "snd" ::= (Invalid : Maybe (FullException Xlen_over_8) @# ty)
                (* "snd" ::= (#memRet @% "exception?" : Maybe (FullException Xlen_over_8) @# ty) *)
              } : PktWithException exec_update_pkt_kind @# ty)).

      Local Close Scope kami_action.

  End Ty.
End Mem.
