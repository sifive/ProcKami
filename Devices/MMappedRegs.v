Require Import Kami.AllNotations.

Require Import StdLibKami.RegMapper.

Require Import StdLibKami.Router.Ifc.

Require Import ProcKami.Device.

Require Import ProcKami.FU.
Require Import ProcKami.MemOpsFuncs.

Import ListNotations.

Section mmregs.
  Local Definition lgGranuleLgSz := Nat.log2_up 3.
  Local Definition lgMaskSz := Nat.log2_up 8.

  Section procParams.
    Context (procParams: ProcParams).

    Local Open Scope kami_expr.
    Local Open Scope kami_action.

    (*
      granule = 1 byte.
      entry = 8 bytes = 8 granules.
      mask size = 1 bit per granule.
      real address size = number of registers
    *)
    Section mmregs.
      Variable realAddrSz: nat.

      Local Notation GroupReg := (GroupReg lgMaskSz realAddrSz).
      Local Notation RegMapT := (RegMapT lgGranuleLgSz lgMaskSz realAddrSz).
      Local Notation FullRegMapT := (FullRegMapT lgGranuleLgSz lgMaskSz realAddrSz).
      Local Notation maskSz := (Nat.pow 2 lgMaskSz).
      Local Notation granuleSz := (Nat.pow 2 lgGranuleLgSz).
      Local Notation dataSz := (maskSz * granuleSz)%nat.
      Local Notation GroupReg_Gen ty := (GroupReg_Gen ty lgMaskSz realAddrSz).

      Variable mmRegs : list GroupReg.

      Variable name : string.
      Variable genReg: bool.

      Local Notation "^ x" := (name ++ "." ++ x)%string (at level 0).

      Local Definition mmReq ty
            (addr: Bit realAddrSz @# ty)
            (data: Bit dataSz @# ty)
            (isRd: Bool @# ty)
        :  ActionT ty (Bit 64)
        := LET rq_info
             :  RegMapT
             <- STRUCT {
                  "addr" ::= addr;
                  "mask" ::= $$(wones maskSz);
                  "data" ::= data
                } : RegMapT @# ty;
           LET rq
             :  FullRegMapT
             <- STRUCT {
                  "isRd" ::= isRd;
                  "info" ::= #rq_info
                } : FullRegMapT @# ty;
           LETA result
             <- readWriteGranules_GroupReg (Valid #rq) mmRegs;
           Ret (ZeroExtendTruncLsb 64 #result).


      Definition mmDev := createDevice
        {| baseName := name;
           baseIo := true;
           basePmas := map
                         (fun width
                          => {|
                              pma_width      := width;
                              pma_readable   := true;
                              pma_writeable  := true;
                              pma_executable := true;
                              pma_misaligned := true;
                            |})
                         [0;1;2;3];
           baseAmos := [];
           baseRegFiles := nil;
           baseRegs := (if genReg
                        then map (fun mmReg =>
                                    (gr_name mmReg, existT RegInitValT (SyntaxKind (gr_kind mmReg))
                                                           (Some (SyntaxConst (getDefaultConst (gr_kind mmReg)))))) mmRegs
                        else nil) ++ makeModule_regs(Register ^"response" : Maybe Data <- Default)%kami
;
           write := (fun ty req =>
                       LET addr : Bit realAddrSz <- unsafeTruncLsb realAddrSz (req @% "addr");
                       LETA _ <- mmReq #addr (ZeroExtendTruncLsb dataSz (pack (req @% "data"))) ($$false);
                       Ret $$true);
           readReq := (fun ty addr =>
                         LETA result : Bit 64 <- mmReq (unsafeTruncLsb realAddrSz addr) $0 ($$true);
                         Write ^"response": Maybe Data <- Valid (ZeroExtendTruncLsb Rlen #result);
                         Retv);
           readRes := (fun ty =>
                         Read memData : Maybe Data <- ^"response";
                         Ret #memData); |}.
    End mmregs.

    Definition msip := @mmDev 0 [{| gr_addr := $0%word;
                                    gr_kind := Bit 64;
                                    gr_name := @^"msip" |}] "msip" false.

    Definition mtime := @mmDev 0 [{| gr_addr := $0%word;
                                     gr_kind := Bit 64;
                                     gr_name := @^"mtime" |}] "mtime" false.
    
    Definition mtimecmp := @mmDev 0 [{| gr_addr := $0%word;
                                        gr_kind := Bit 64;
                                        gr_name := @^"mtimecmp" |}] "mtimecmp" false.

    Local Close Scope kami_action.
    Local Close Scope kami_expr.

  End procParams.
End mmregs.
