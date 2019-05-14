(*
  This section defines the interface between the processor core and
  the RAM.
*)
Require Import Kami.All.
Require Import FU.
Require Import Decoder.

Section Memory.
  Variable name: string.
  Variable Xlen_over_8: nat.
  Variable Rlen_over_8: nat.
  Variable ty: Kind -> Type.
  Variable lgMemSz : nat.

  Local Notation "^ x" := (name ++ "_" ++ x)%string (at level 0).
  Local Notation Rlen := (Rlen_over_8 * 8).
  Local Notation Xlen := (Xlen_over_8 * 8).
  Local Notation Data := (Bit Rlen).
  Local Notation VAddr := (Bit Xlen).
  Local Notation InstEntry := (InstEntry Xlen_over_8 Rlen_over_8 ty).
  Local Notation FUEntry := (FUEntry Xlen_over_8 Rlen_over_8 ty).
  Local Notation FetchPkt := (FetchPkt Xlen_over_8).
  Local Notation ExecContextPkt := (ExecContextPkt Xlen_over_8 Rlen_over_8).
  Local Notation ExecContextUpdPkt := (ExecContextUpdPkt Rlen_over_8).
  Local Notation RoutedReg := (RoutedReg Rlen_over_8). 
  Local Notation PktWithException := (PktWithException Xlen_over_8).
  Local Notation FullException := (FullException Xlen_over_8).
  Local Notation MemWrite := (MemWrite Xlen_over_8 Rlen_over_8).
  Local Notation MemoryInput := (MemoryInput Rlen_over_8).
  Local Notation MemoryOutput := (MemoryOutput Rlen_over_8).
  Local Notation MemUnitInput := (MemUnitInput Rlen_over_8).
  Local Notation MemRet := (MemRet Rlen_over_8).
  Local Notation defMemRet := (defMemRet Xlen_over_8 Rlen_over_8 ty).

  Variable func_units : list FUEntry.
  Local Notation FuncUnitId := (@Decoder.FuncUnitId Xlen_over_8 Rlen_over_8 ty func_units).
  Local Notation InstId := (@Decoder.InstId Xlen_over_8 Rlen_over_8 ty func_units).
  Local Notation DecoderPkt := (@Decoder.DecoderPkt Xlen_over_8 Rlen_over_8 ty func_units).

  Open Scope kami_action.

  Definition memRead (index: nat) (addr: VAddr @# ty)
    : ActionT ty (PktWithException Data)
    := Call result: Array Rlen_over_8 (Bit 8)
                          <- (^"readMem" ++ (natToHexStr index)) (SignExtendTruncLsb _ addr: Bit lgMemSz);
         
         System (DispString _ "READ MEM: " :: DispHex addr :: DispString _ " " :: DispHex #result ::
                            DispString _ "\n" :: nil);
         Ret (STRUCT {
                  "fst" ::= pack #result ;
                  "snd" ::= Invalid } : PktWithException Data @# ty).

  Definition memReadReservation (addr: VAddr @# ty)
    : ActionT ty (Array Rlen_over_8 Bool)
    := Call result: Array Rlen_over_8 Bool
                          <- ^"readMemReservation" (SignExtendTruncLsb _ addr: Bit lgMemSz);
         Ret #result.

  Definition memWrite (pkt : MemWrite @# ty)
    : ActionT ty (Maybe FullException)
    := LET writeRq: WriteRqMask lgMemSz Rlen_over_8 (Bit 8) <- STRUCT {
                                  "addr" ::= SignExtendTruncLsb lgMemSz (pkt @% "addr") ;
                                  "data" ::= unpack (Array Rlen_over_8 (Bit 8)) (pkt @% "data") ;
                                  "mask" ::= pkt @% "mask" };
         Call ^"writeMem"(#writeRq: _);
         Ret Invalid.

  Definition memWriteReservation (addr: VAddr @# ty)
             (mask rsv: Array Rlen_over_8 Bool @# ty)
    : ActionT ty Void
    := LET writeRq: WriteRqMask lgMemSz Rlen_over_8 Bool <- STRUCT { "addr" ::= SignExtendTruncLsb lgMemSz addr ;
                                                                     "data" ::= rsv ;
                                                                     "mask" ::= mask } ;
         Call ^"writeMemReservation" (#writeRq: _);
         Retv.

  Close Scope kami_action.

  Definition getMemEntryFromInsts ik ok (insts: list (InstEntry ik ok)) pos :
    option (LetExprSyntax ty MemoryInput ->
            LetExprSyntax ty MemoryOutput) :=
    match find (fun x => getBool (Nat.eq_dec pos (fst x))) (tag insts) with
    | None => None
    | Some inst => match optMemXform (snd inst)
                   with
                   | None => None
                   | Some val => Some val
                   end
    end.

  Variable memFuNames: list string.
  Definition memFus := filter
                         (fun x => getBool (in_dec string_dec (fuName (snd x)) memFuNames))
                         (tag func_units).

  Definition lengthMemFus := map (fun x => length (fuInsts (snd x))) memFus.

  Definition tagMemFus: list nat := map fst memFus.

  Definition getMemEntry fu pos:
    option (LetExprSyntax ty MemoryInput ->
            LetExprSyntax ty MemoryOutput) :=
    getMemEntryFromInsts (fuInsts fu) pos.

  Local Open Scope kami_expr.
  Definition makeMemoryInput (i: MemUnitInput @# ty) (mem: Data @# ty)
             (reservation : Array Rlen_over_8 Bool @# ty) : MemoryInput @# ty :=
    STRUCT {
        "aq" ::= i @% "aq" ;
        "rl" ::= i @% "rl" ;
        "reservation" ::= reservation ;
        "mem" ::= mem ;
        "reg_data" ::= i @% "reg_data"
      }.

  Section MemAddr.
    Variable addr: VAddr @# ty.
    Variable fuTag: FuncUnitId @# ty.
    Variable instTag: InstId @# ty.
    Variable memUnitInput: MemUnitInput @# ty.

    Local Open Scope kami_action.

    Definition memAction (fu: FUEntry) (tag: nat)
      :  ActionT ty (PktWithException MemRet)
      := If instTag == $tag
         then 
           match getMemEntry fu tag with
             | Some fn
               => (
                  LETA memReadVal
                    :  PktWithException Data
                    <- memRead 2 addr;
                  LETA memReadReservationVal
                    : Array Rlen_over_8 Bool
                    <- memReadReservation addr;
                  System
                    (DispString _ "Mem Read: " ::
                     DispHex #memReadVal ::
                     DispString _ "\n" ::
                     nil);
                  If (#memReadVal @% "snd" @% "valid")
                  then
                    Ret defMemRet
                  else
                    (LETA memoryOutput
                     :  MemoryOutput
                     <- convertLetExprSyntax_ActionT (fn (RetE (makeMemoryInput memUnitInput
                                                                                (#memReadVal @% "fst")
                                                                                #memReadReservationVal)));
                     System
                       (DispString _ "Mem Output Write to Register: " ::
                                   DispBinary #memoryOutput ::
                                   DispString _ "\n" ::
                                   nil);
                     If (#memoryOutput @% "isWr")
                     then
                       (LET memWriteVal
                        :  MemWrite
                        <- STRUCT {
                          "addr" ::= addr;
                          "data" ::= #memoryOutput @% "data" ;
                          "mask" ::=
                            (IF #memoryOutput @% "isWr"
                             then #memoryOutput @% "mask"
                             else $$ (ConstArray (fun (_: Fin.t Rlen_over_8) => false)))
                        };
                        LETA writeEx
                        :  Maybe FullException
                        <- memWrite #memWriteVal;
                        System
                          (DispString _ "Mem Write: " ::
                           DispHex #memWriteVal ::
                           DispString _ "\n" ::
                           nil);
                        Ret #writeEx)
                     else
                        Ret (@Invalid _ FullException)
                     as writeEx;
                     If (#memoryOutput @% "isLrSc")
                     then memWriteReservation addr (#memoryOutput @% "mask") (#memoryOutput @% "reservation");
                     LET memRet
                     : PktWithException MemRet
                     <- STRUCT {
                       "fst" ::= STRUCT {
                                     "writeReg?" ::= #memoryOutput @% "reg_data" @% "valid";
                                     "tag" ::= #memoryOutput @% "tag";
                                     "data" ::= #memoryOutput @% "reg_data" @% "data" } ;
                       "snd" ::= #writeEx };
                     Ret #memRet)
                  as ret;
                Ret #ret
                )        
             | None => Ret defMemRet
             end
         else Ret defMemRet
         as ret;
           Ret #ret.

    Definition fullMemAction
      :  ActionT ty (PktWithException MemRet)
      := GatherActions
           (map (fun memFu =>
                   (If (fuTag == $ (fst memFu))
                    then 
                      (GatherActions (map (memAction (snd memFu)) (0 upto (length (fuInsts (snd memFu))))) as retVals;
                         Ret (unpack (PktWithException MemRet)
                                     (CABit Bor (map (@pack ty (PktWithException MemRet)) retVals))))
                    else
                      Ret defMemRet
                     as ret;
                      Ret #ret)) memFus) as retVals2;
           Ret (unpack (PktWithException MemRet) (CABit Bor (map (@pack ty (PktWithException MemRet)) retVals2))).

    Local Close Scope kami_action.
  End MemAddr.

  Local Open Scope kami_action.

  Definition MemUnit
             (xlen : XlenValue @# ty)
             (decoder_pkt : DecoderPkt @# ty)
             (exec_context_pkt : ExecContextPkt @# ty)
             (opt_exec_update_pkt : PktWithException ExecContextUpdPkt @# ty)
    :  ActionT ty (PktWithException ExecContextUpdPkt)
    := LET exec_update_pkt: ExecContextUpdPkt <- opt_exec_update_pkt @% "fst";
       LETA memRet
         :  PktWithException MemRet
         <- fullMemAction
              (xlen_sign_extend Xlen xlen
                (#exec_update_pkt @% "val1" @% "data" @% "data" : Bit Rlen @# ty))
              (decoder_pkt @% "funcUnitTag")
              (decoder_pkt @% "instTag")
              (STRUCT {
                 "aq"       ::= #exec_update_pkt @% "aq";
                 "rl"       ::= #exec_update_pkt @% "rl";
                 "reg_data" ::= exec_context_pkt @% "reg2"
               } : MemUnitInput @# ty);
       Ret
         (mkPktWithException
            opt_exec_update_pkt
            (STRUCT {
                 "fst"
                 ::= (ITE
                        (#memRet @% "fst" @% "writeReg?")
                        (#exec_update_pkt
                           @%["val1"
                                <- Valid (STRUCT {
                                              "tag"  ::= #memRet @% "fst" @% "tag";
                                              "data" ::= (#memRet @% "fst" @% "data" : Bit Rlen @# ty)
                                            } : RoutedReg @# ty)])
                        (#exec_update_pkt));
                 "snd" ::= #memRet @% "snd"
               } : PktWithException ExecContextUpdPkt @# ty)).

  Local Close Scope kami_action.
End Memory.
