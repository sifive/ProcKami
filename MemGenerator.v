Require Import Kami.All RecordUpdate.RecordSet FU Mem Decoder FuInputTrans utila.
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

    (* The functional units that comprise the instruction database. *)
    Variable func_units : list func_unit_type.

    Let func_unit_id_width := Decoder.func_unit_id_width func_units.

    Let inst_id_width := Decoder.inst_id_width func_units.

    Let func_unit_id_kind := Decoder.func_unit_id_kind func_units.

    Let inst_id_kind := Decoder.inst_id_kind func_units.

    Let tagged_func_unit_type := Decoder.tagged_func_unit_type Xlen_over_8 ty.

    Let tagged_inst_type := Decoder.tagged_inst_type Xlen_over_8 ty.

    Local Open Scope kami_expr.
    Definition makeMemoryInput (i: MemUnitInput @# ty) (mem: Data @# ty) (reservation : Bit 2 @# ty) : MemoryInput @# ty :=
      STRUCT {
          "aq" ::= i @% "aq" ;
          "rl" ::= i @% "rl" ;
          "reservation" ::= reservation ;
          "mem" ::= mem ;
          "reg_data" ::= i @% "reg_data"
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

    Definition defMemRet : MemRet @# ty
      := STRUCT {
           "writeReg?"  ::= $$false;
           "data"       ::= $0;
           "exception?" ::= Invalid
         }.

    Local Open Scope kami_action.
    Definition memAction
      (func_unit_id : func_unit_id_kind @# ty)
      (sem_in_kind sem_out_kind : Kind)
      (tagged_inst : tagged_inst_type sem_in_kind sem_out_kind)
      (sel_func_unit_id : func_unit_id_kind @# ty)
      (sel_inst_id : inst_id_kind @# ty)
      (addr : VAddr @# ty)
      (memUnitInput : MemUnitInput @# ty)
      :  ActionT ty (Maybe MemRet)
      := LET selected
           :  Bool
           <- (func_unit_id == sel_func_unit_id &&
               tagged_inst_match tagged_inst sel_inst_id);
         If #selected
         then
           (match optMemXform (detag_inst tagged_inst) with
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
                          (applyMask (#memRead @% "data") (#memoryOutput @% "mem" @% "data"));
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
             end)
         else
           (Ret defMemRet) as ret;
         Ret (utila_opt_pkt (#ret) (#selected)).

    Definition fullMemAction
      (sel_func_unit_id : func_unit_id_kind @# ty)
      (sel_inst_id : inst_id_kind @# ty)
      (addr : VAddr @# ty)
      (memUnitInput : MemUnitInput @# ty)
      :  ActionT ty MemRet
      := LETA opt_mem_action_res
           : Maybe MemRet
           <- utila_acts_find_pkt
                (map
                  (fun tagged_func_unit : tagged_func_unit_type
                    => let (func_unit_id, func_unit)
                         := tagged_func_unit in
                       utila_acts_find_pkt
                         (map
                           (fun tagged_inst
                             => memAction
                                  (func_unit_id_encode func_units func_unit_id)
                                  tagged_inst
                                  sel_func_unit_id
                                  sel_inst_id
                                  addr
                                  memUnitInput)
                           (tag (fuInsts func_unit))))
                  (tag func_units));
         Ret (#opt_mem_action_res @% "data").

    Local Close Scope kami_action.
  End Ty.
End Mem.
