(*
  This module defines the memory unit. This unit accepts a memory
  update packet and performs the requested memory writes.
*)
Require Import Kami.All.
Require Import FU.
Require Import Decoder.
Require Import Pmp.
Require Import PhysicalMem.
Require Import VirtualMem.
Require Import List.
Import ListNotations.

Section mem_unit.

  Variable name: string.
  Variable Xlen_over_8: nat.
  Variable Rlen_over_8: nat.
  Variable mem_params : mem_params_type.
  Variable vm_params : vm_params_type.
  Variable ty: Kind -> Type.

  Local Notation "^ x" := (name ++ "_" ++ x)%string (at level 0).
  Local Notation Rlen := (Rlen_over_8 * 8).
  Local Notation Xlen := (Xlen_over_8 * 8).
  Local Notation Data := (Bit Rlen).
  Local Notation VAddr := (Bit Xlen).
  Local Notation PAddrSz := (mem_params_addr_size mem_params).
  Local Notation PAddr := (Bit PAddrSz).
  Local Notation InstEntry := (InstEntry Xlen_over_8 Rlen_over_8 ty).
  Local Notation FUEntry := (FUEntry Xlen_over_8 Rlen_over_8 ty).
  Local Notation FetchPkt := (FetchPkt Xlen_over_8).
  Local Notation ExecContextPkt := (ExecContextPkt Xlen_over_8 Rlen_over_8).
  Local Notation ExecUpdPkt := (ExecUpdPkt Rlen_over_8).
  Local Notation RoutedReg := (RoutedReg Rlen_over_8). 
  Local Notation PktWithException := (PktWithException Xlen_over_8).
  Local Notation FullException := (FullException Xlen_over_8).
  Local Notation MemWrite := (MemWrite Rlen_over_8 PAddrSz).
  Local Notation MemoryInput := (MemoryInput Rlen_over_8).
  Local Notation MemoryOutput := (MemoryOutput Rlen_over_8).
  Local Notation MemUnitInput := (MemUnitInput Rlen_over_8).
  Local Notation MemRet := (MemRet Rlen_over_8).
  Local Notation defMemRet := (defMemRet Xlen_over_8 Rlen_over_8 ty).
  Local Notation pmp_check_execute := (@pmp_check_execute name Xlen_over_8 mem_params ty).
  Local Notation pmp_check_read := (@pmp_check_read name Xlen_over_8 mem_params ty).
  Local Notation pmp_check_write := (@pmp_check_write name Xlen_over_8 mem_params ty).
  Local Notation pMemFetch := (@pMemFetch name Xlen_over_8 Rlen_over_8 mem_params ty).
  Local Notation pMemRead := (@pMemRead name Xlen_over_8 Rlen_over_8 mem_params ty).
  Local Notation pMemWrite := (@pMemWrite name Xlen_over_8 Rlen_over_8 mem_params ty).
  Local Notation pMemReadReservation := (@pMemReadReservation name Rlen_over_8 mem_params ty).
  Local Notation pMemWriteReservation := (@pMemWriteReservation name Rlen_over_8 mem_params ty).

  Variable func_units : list FUEntry.
  Local Notation FuncUnitId := (@Decoder.FuncUnitId Xlen_over_8 Rlen_over_8 ty func_units).
  Local Notation InstId := (@Decoder.InstId Xlen_over_8 Rlen_over_8 ty func_units).
  Local Notation DecoderPkt := (@Decoder.DecoderPkt Xlen_over_8 Rlen_over_8 ty func_units).
  Local Notation pt_walker := (@pt_walker name Xlen_over_8 Rlen_over_8 mem_params ty).

  Open Scope kami_expr.
  Open Scope kami_action.

  (* TODO: should this be sign extended? *)
  Definition pMemTranslate
    (vaddr : VAddr @# ty)
    :  PktWithException PAddr @# ty
    := STRUCT {
         "fst" ::= SignExtendTruncLsb PAddrSz vaddr;
         "snd" ::= Invalid
       } : PktWithException PAddr @# ty.

  Definition memTranslate
    (mode : PrivMode @# ty)
    (access_type : Bit vm_access_width @# ty)
    (vaddr : VAddr @# ty)
    :  ActionT ty (PktWithException PAddr)
    := If mode == $MachineMode
         then Ret (pMemTranslate vaddr)
         else
           Read satp_mode : Bit 4 <- ^"satp_mode";
           If #satp_mode == $satp_mode_bare
             then Ret (pMemTranslate vaddr)
             else 
               pt_walker
                 3 (* initial walker mem read index. *)
                 mode
                 access_type
                 vaddr
             as result;
           Ret #result
         as result;
       Ret #result.

  Definition memFetch
    (index : nat)
    (mode : PrivMode @# ty) 
    (vaddr : VAddr @# ty)
    :  ActionT ty (PktWithException Data)
    := LETA paddr
         :  PktWithException PAddr
         <- memTranslate mode $vm_access_inst vaddr; (* TODO check access code. *)
       (* TODO handle exception from memTranslate *)
       LETA result
         :  PktWithException Data
         <- pMemFetch index mode (#paddr @% "fst");
       Ret #result.

  Definition memRead
    (index : nat)
    (mode : PrivMode @# ty) 
    (vaddr : VAddr @# ty)
    :  ActionT ty (PktWithException Data)
    := LETA paddr
         :  PktWithException PAddr
         <- memTranslate mode $vm_access_load vaddr; (* TODO check access code. *)
       (* TODO handle exception from memTranslate *)
       LETA result
         :  PktWithException Data
         <- pMemRead index mode (#paddr @% "fst");
       Ret #result.

  Definition memReadReservation
    (mode : PrivMode @# ty) 
    (vaddr : VAddr @# ty)
    :  ActionT ty (Array Rlen_over_8 Bool)
    := LETA paddr
         :  PktWithException PAddr
         <- memTranslate mode $vm_access_samo vaddr; (* TODO check access code. *)
       (* TODO handle exception from memTranslate *)
       LETA result
         :  Array Rlen_over_8 Bool
         <- pMemReadReservation (#paddr @% "fst");
       Ret #result.

  Definition memWriteReservation
    (index : nat)
    (mode : PrivMode @# ty) 
    (vaddr : VAddr @# ty)
    (mask rsv : Array Rlen_over_8 Bool @# ty)
    :  ActionT ty Void
    := LETA paddr
         :  PktWithException PAddr
         <- memTranslate mode $vm_access_samo vaddr; (* TODO check access code. *)
       (* TODO handle exception from memTranslate *)
       LETA result
         :  Void
         <- pMemWriteReservation (#paddr @% "fst" : PAddr @# ty) mask rsv;
       Retv.

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
    Variable mode: PrivMode @# ty.
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
                  LETA translateResult
                    :  PktWithException PAddr
                    <- memTranslate mode $vm_access_inst addr; (* TODO check access code. *)
                  (* TODO: Handle exception from memTranslate *)
                  LET paddr
                    :  PAddr
                    <- #translateResult @% "fst";
                  LETA memReadVal
                    :  PktWithException Data
                    <- pMemRead 2 mode #paddr;
                  LETA memReadReservationVal
                    : Array Rlen_over_8 Bool
                    <- pMemReadReservation #paddr;
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
                          "addr" ::= #paddr;
                          "data" ::= #memoryOutput @% "data";
                          "mask" ::=
                            (IF #memoryOutput @% "isWr"
                             then #memoryOutput @% "mask"
                             else $$ (ConstArray (fun (_: Fin.t Rlen_over_8) => false)))
                        } : MemWrite @# ty;
                        LETA writeEx
                        :  Maybe FullException
                        <- pMemWrite mode #memWriteVal;
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
                     then pMemWriteReservation #paddr (#memoryOutput @% "mask") (#memoryOutput @% "reservation");
                     LET fstVal: MemRet <- STRUCT {
                                     "writeReg?" ::= #memoryOutput @% "reg_data" @% "valid";
                                     "tag" ::= #memoryOutput @% "tag";
                                     "data" ::= #memoryOutput @% "reg_data" @% "data" } ;
                     LET memRet
                     : PktWithException MemRet
                     <- STRUCT {
                       "fst" ::= #fstVal;
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
             (mode : PrivMode @# ty)
             (decoder_pkt : DecoderPkt @# ty)
             (exec_context_pkt : ExecContextPkt @# ty)
             (opt_exec_update_pkt : PktWithException ExecUpdPkt @# ty)
    :  ActionT ty (PktWithException ExecUpdPkt)
    := LET exec_update_pkt: ExecUpdPkt <- opt_exec_update_pkt @% "fst";
       LETA memRet
         :  PktWithException MemRet
         <- fullMemAction
              mode
              (xlen_sign_extend Xlen xlen
                (#exec_update_pkt @% "val1" @% "data" @% "data" : Bit Rlen @# ty))
              (decoder_pkt @% "funcUnitTag")
              (decoder_pkt @% "instTag")
              (STRUCT {
                 "aq"       ::= #exec_update_pkt @% "aq";
                 "rl"       ::= #exec_update_pkt @% "rl";
                 "reg_data" ::= exec_context_pkt @% "reg2"
                 } : MemUnitInput @# ty);
       LET val1 <- (STRUCT {
                        "tag"  ::= #memRet @% "fst" @% "tag";
                        "data" ::= (#memRet @% "fst" @% "data" : Bit Rlen @# ty)
                      } : RoutedReg @# ty);
       Ret
         (mkPktWithException
            opt_exec_update_pkt
            (STRUCT {
                 "fst"
                 ::= (ITE
                        (#memRet @% "fst" @% "writeReg?")
                        (#exec_update_pkt
                           @%["val1" <- Valid #val1])
                        (#exec_update_pkt));
                 "snd" ::= #memRet @% "snd"
               } : PktWithException ExecUpdPkt @# ty)).

  Close Scope kami_expr.

  Close Scope kami_action.

End mem_unit.
