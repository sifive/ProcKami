(* Defines the standard Csrs. *)
Require Import Vector.
Import VectorNotations.
Require Import Kami.All.
Require Import ProcKami.FU.
Require Import ProcKami.GenericPipeline.RegWriter.
Require Import StdLibKami.RegStruct.
Require Import StdLibKami.RegMapper.
Require Import ProcKami.RiscvIsaSpec.Csr.CsrFuncs.
Require Import List.
Import ListNotations.

Section csrs.
  Variable name: string.
  Local Notation "^ x" := (name ++ "_" ++ x)%string (at level 0).
  Context `{procParams: ProcParams}.
  Variable ty: Kind -> Type.

  Open Scope kami_expr.

  Definition Csrs
    :  list (Csr _)
    := [
         {|
           csrName := ^"ustatus";
           csrAddr := natToWord CsrIdWidth 0;
           csrViews
             := let fields
                  := [
                       @csrFieldNoReg _ _ "reserved0" (Bit 27) (getDefaultConst _);
                       @csrFieldAny _ _ ^"upie" Bool Bool;
                       @csrFieldNoReg _ _ "reserved1" (Bit 3) (getDefaultConst _);
                       @csrFieldAny _ _ ^"uie" Bool Bool
                     ] in
                repeatCsrView 2
                  (@csrViewDefaultReadXform _ _ fields)
                  (@csrViewDefaultWriteXform _ _ fields);
           csrAccess := (@accessAny _)
         |};
         nilCsr ^"uie" (CsrIdWidth 'h"4") (@accessAny _);
         {|
           csrName := ^"utvec";
           csrAddr := natToWord CsrIdWidth 5;
           csrViews
             := let fields := [ @csrFieldAny _ _ ^"utvec_mode" (Bit 2) (Bit 2) ] in
                repeatCsrView 2
                  (@csrViewDefaultReadXform _ _ fields)
                  (@csrViewDefaultWriteXform _ _ fields);
           csrAccess := (@accessAny _)
         |};
         {|
           csrName := ^"uscratch";
           csrAddr := CsrIdWidth 'h"40";
           csrViews
             := [
                  let fields := [ @csrFieldAny _ _ ^"uscratch" (Bit 32) (Bit Xlen) ] in
                  {|
                    csrViewContext    := $1;
                    csrViewFields     := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform _ _ fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform _ _ fields)
                  |};
                  let fields := [ @csrFieldAny _ _ ^"uscratch" (Bit 64) (Bit Xlen) ] in
                  {|
                    csrViewContext    := $2;
                    csrViewFields     := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform _ _ fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform _ _ fields)
                  |}
                ];
           csrAccess := (@accessAny _)
         |};
         {|
           csrName := ^"uepc";
           csrAddr := CsrIdWidth 'h"41";
           csrViews
             := [
                  let fields := [ @csrFieldAny _ _ ^"uepc" (Bit 32) (Bit Xlen) ] in
                  {|
                    csrViewContext    := $1;
                    csrViewFields     := fields;
                    csrViewReadXform  := (@epcReadXform _ _ fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform _ _ fields)
                  |};
                  let fields := [ @csrFieldAny _ _ ^"uepc" (Bit 64) (Bit Xlen) ] in
                  {|
                    csrViewContext    := $2;
                    csrViewFields     := fields;
                    csrViewReadXform  := (@epcReadXform _ _ fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform _ _ fields)
                  |}
                ];
           csrAccess := (@accessAny _)
         |};
         {|
           csrName := ^"ucause";
           csrAddr := CsrIdWidth 'h"42";
           csrViews
             := [
                  let fields
                    := [
                         @csrFieldAny _ _ ^"ucause_interrupt" Bool Bool;
                         @csrFieldAny _ _ ^"ucause_code" (Bit 31) (Bit (Xlen - 1))
                       ] in
                  {|
                    csrViewContext    := $1;
                    csrViewFields     := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform _ _ fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform _ _ fields)
                  |};
                  let fields
                    := [
                         @csrFieldAny _ _ ^"ucause_interrupt" Bool Bool;
                         @csrFieldAny _ _ ^"ucause_code" (Bit 63) (Bit (Xlen - 1))
                       ] in
                  {|
                    csrViewContext    := $2;
                    csrViewFields     := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform _ _ fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform _ _ fields)
                  |}
                ];
           csrAccess := (@accessAny _)
         |};
         {|
           csrName := ^"utval";
           csrAddr := CsrIdWidth 'h"43";
           csrViews
             := [
                  let fields := [ @csrFieldAny _ _ ^"utval" (Bit 32) (Bit Xlen) ] in
                  {|
                    csrViewContext    := $1;
                    csrViewFields     := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform _ _ fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform _ _ fields)
                  |};
                  let fields := [ @csrFieldAny _ _ ^"utval" (Bit 64) (Bit Xlen) ] in
                  {|
                    csrViewContext    := $2;
                    csrViewFields     := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform _ _ fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform _ _ fields)
                  |}
                ];
           csrAccess := (@accessAny _)
         |};
         {|
           csrName := ^"uip";
           csrAddr := CsrIdWidth 'h"44";
           csrViews
             := let fields
                  := [
                       @csrFieldAny _ _ ^"ueip" Bool Bool;
                       @csrFieldNoReg _ _ ^"reserved0" (Bit 3) (getDefaultConst _);
                       @csrFieldAny _ _ ^"utip" Bool Bool;
                       @csrFieldNoReg _ _ ^"reserved1" (Bit 3) (getDefaultConst _);
                       @csrFieldAny _ _ ^"usip" Bool Bool
                     ] in
                repeatCsrView 2
                  (@csrViewDefaultReadXform _ _ fields)
                  (@csrViewDefaultWriteXform _ _ fields);
           csrAccess := (@accessMModeOnly _)
         |};
         {|
           csrName := ^"fflagsG";
           csrAddr := natToWord CsrIdWidth 1;
           csrViews
             := let fields
                  := [
                       @csrFieldNoReg _ _ "reserved" (Bit 27) (getDefaultConst _);
                       @csrFieldAny _ _ ^"fflags" (Bit 5) FflagsValue
                     ] in
                repeatCsrView 2
                  (@csrViewDefaultReadXform _ _ fields)
                  (@csrViewDefaultWriteXform _ _ fields);
           csrAccess := (@accessAny _)
         |};
         {|
           csrName := ^"frmG";
           csrAddr := natToWord CsrIdWidth 2;
           csrViews
             := let fields
                  := [
                       @csrFieldNoReg _ _ "reserved" (Bit 29) (getDefaultConst _);
                       @csrFieldAny _ _ ^"frm" (Bit 3) FrmValue
                     ] in
                repeatCsrView 2
                  (@csrViewDefaultReadXform _ _ fields)
                  (@csrViewDefaultWriteXform _ _ fields);
           csrAccess := (@accessAny _)
         |};
         {|
           csrName := ^"fcsrG";
           csrAddr := natToWord CsrIdWidth 3;
           csrViews
             := let fields
                  := [
                       @csrFieldNoReg _ _ "reserved" (Bit 24) (getDefaultConst _);
                       @csrFieldAny _ _ ^"frm" (Bit 3) FrmValue;
                       @csrFieldAny _ _ ^"fflags" (Bit 5) FflagsValue
                     ] in
                repeatCsrView 2
                  (@csrViewDefaultReadXform _ _ fields)
                  (@csrViewDefaultWriteXform _ _ fields);
           csrAccess := (@accessAny _)
         |};
         simpleCsr ^"mcycle" (CsrIdWidth 'h"c00") 64 (accessCounter "CY");
         readonlyCsr ^"mtime" (CsrIdWidth 'h"c01") 64 (@accessAny _);
         simpleCsr ^"minstret" (CsrIdWidth 'h"c02") 64 (accessCounter "IR");
         {|
           csrName := ^"cycleh";
           csrAddr := CsrIdWidth 'h"c80";
           csrViews
             := let fields := [ @csrFieldReadOnly _ _ ^"mcycle" (Bit 64) (Bit 64) ] in
                repeatCsrView 2
                  (@csrViewUpperReadXform _ _ fields)
                  (@csrViewUpperWriteXform _ _ fields);
           csrAccess := (@accessAny _)
         |};
         {|
           csrName := ^"instreth";
           csrAddr := CsrIdWidth 'h"c82";
           csrViews
             := let fields := [ @csrFieldReadOnly _ _ ^"minstret" (Bit 64) (Bit 64) ] in
                repeatCsrView 2
                  (@csrViewUpperReadXform _ _ fields)
                  (@csrViewUpperWriteXform _ _ fields);
           csrAccess := (@accessAny _)
         |};
         {|
           csrName := ^"misa";
           csrAddr := CsrIdWidth 'h"301";
           csrViews
             := [
                  let fields
                    := [
                         xlField _ ^"m";
                         @csrFieldNoReg _ _ "misa_reserved32" (Bit 4) (getDefaultConst _);
                         @csrFieldNoReg _ _
                           "extensions" (Bit 26)
                           (ConstBit WO~1~0~1~1~0~1~0~0~1~0~0~0~1~0~0~0~0~0~0~0~0~0~0~0~0~1) (* TODO *)
                       ] (* ++ ext_fields *) in
                  {|
                    csrViewContext := $1;
                    csrViewFields  := fields;
                    csrViewReadXform  := @csrViewDefaultReadXform _ _ fields;
                    csrViewWriteXform := @csrViewDefaultWriteXform _ _ fields
                  |};
                  let fields
                    := [
                         xlField _ ^"m";
                         @csrFieldNoReg _ _ "misa_reserved64" (Bit 36) (getDefaultConst _);
                         @csrFieldNoReg _ _
                           "extensions" (Bit 26)
                           (ConstBit WO~1~0~1~1~0~1~0~0~1~0~0~0~1~0~0~0~0~0~0~0~0~0~0~0~0~1) (* TODO *)
                       ] (* ++ ext_fields *) in
                  {|
                    csrViewContext := $2;
                    csrViewFields  := fields;
                    csrViewReadXform  := @csrViewDefaultReadXform _ _ fields;
                    csrViewWriteXform := @csrViewDefaultWriteXform _ _ fields
                  |}
                ];
           csrAccess := (@accessMModeOnly _)
         |};
         {|
           csrName := ^"medeleg";
           csrAddr := CsrIdWidth 'h"302";
           csrViews
             := [
                  let fields
                    := [
                         @csrFieldNoReg _ _ "reserved" (Bit 16) (getDefaultConst _);
                         @csrFieldAny _ _ ^"medeleg" (Bit 16) (Bit 16)
                       ] in
                  {|
                    csrViewContext := $1;
                    csrViewFields  := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform _ _ fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform _ _ fields)
                  |};
                  let fields
                    := [
                         @csrFieldNoReg _ _ "reserved" (Bit 48) (getDefaultConst _);
                         @csrFieldAny _ _ ^"medeleg" (Bit 16) (Bit 16)
                       ] in
                  {|
                    csrViewContext := $2;
                    csrViewFields  := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform _ _ fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform _ _ fields)
                  |}
                ];
           csrAccess := (@accessMModeOnly _)
         |};
         {|
           csrName := ^"mideleg";
           csrAddr := CsrIdWidth 'h"303";
           csrViews
             := [
                  let fields
                    := [
                         @csrFieldNoReg _ _ "reserved" (Bit 20) (getDefaultConst _);
                         @csrFieldAny _ _ ^"mideleg" (Bit 12) (Bit 12)
                       ] in
                  {|
                    csrViewContext := $1;
                    csrViewFields  := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform _ _ fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform _ _ fields)
                  |};
                  let fields
                    := [
                         @csrFieldNoReg _ _ "reserved" (Bit 52) (getDefaultConst _);
                         @csrFieldAny _ _ ^"mideleg" (Bit 12) (Bit 12)
                       ] in
                  {|
                    csrViewContext := $2;
                    csrViewFields  := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform _ _ fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform _ _ fields)
                  |}
                ];
           csrAccess := (@accessMModeOnly _)
         |};
         {|
           csrName := ^"mie";
           csrAddr := CsrIdWidth 'h"304";
           csrViews
             := let fields
                  := [
                       @csrFieldReadOnly _ _ ^"meie" Bool Bool;
                       @csrFieldNoReg _ _ ^"reserved0" Bool (getDefaultConst _);
                       @csrFieldAny _ _ ^"seie" Bool Bool;
                       @csrFieldAny _ _ ^"ueie" Bool Bool;
                       @csrFieldReadOnly _ _ ^"mtie" Bool Bool;
                       @csrFieldNoReg _ _ ^"reserved1" Bool (getDefaultConst _);
                       @csrFieldAny _ _ ^"stie" Bool Bool;
                       @csrFieldAny _ _ ^"utie" Bool Bool;
                       @csrFieldReadOnly _ _ ^"msie" Bool Bool;
                       @csrFieldNoReg _ _ ^"reserved2" Bool (getDefaultConst _);
                       @csrFieldAny _ _ ^"ssie" Bool Bool;
                       @csrFieldAny _ _ ^"usie" Bool Bool
                     ] in
                repeatCsrView 2
                  (@csrViewDefaultReadXform _ _ fields)
                  (@csrViewDefaultWriteXform _ _ fields);
           csrAccess := (@accessMModeOnly _)
         |};
         {|
           csrName := ^"mstatus";
           csrAddr := CsrIdWidth 'h"300";
           csrViews
             := [
                  let fields
                    := [
                         @csrFieldNoReg _ _ "reserved0" (Bit 9) (getDefaultConst _);
                         @csrFieldAny _ _ ^"tsr" Bool Bool;
                         @csrFieldAny _ _ ^"tw" Bool Bool;
                         @csrFieldAny _ _ ^"tvm" Bool Bool;
                         @csrFieldAny _ _ ^"mxr" Bool Bool;
                         @csrFieldAny _ _ ^"sum" Bool Bool;
                         @csrFieldAny _ _ ^"mprv" Bool Bool;
                         @csrFieldNoReg _ _ "reserved1" (Bit 4) (getDefaultConst _);
                         @csrFieldAny _ _ ^"mpp" (Bit 2) (Bit 2);
                         @csrFieldNoReg _ _ ^"hpp" (Bit 2) (getDefaultConst _);
                         @csrFieldAny _ _ ^"spp" (Bit 1) (Bit 1);
                         @csrFieldAny _ _ ^"mpie" Bool Bool;
                         @csrFieldNoReg _ _ ^"hpie" Bool (getDefaultConst _);
                         @csrFieldAny _ _ ^"spie" Bool Bool;
                         @csrFieldAny _ _ ^"upie" Bool Bool;
                         @csrFieldAny _ _ ^"mie" Bool Bool;
                         @csrFieldNoReg _ _ ^"hie" Bool (getDefaultConst _);
                         @csrFieldAny _ _ ^"sie" Bool Bool;
                         @csrFieldAny _ _ ^"uie" Bool Bool
                       ] in
                  {|
                    csrViewContext := $1;
                    csrViewFields  := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform _ _ fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform _ _ fields)
                  |};
                  let fields
                    := [
                         @csrFieldNoReg _ _ "reserved0" (Bit 28) (getDefaultConst _);
                         xlField _ ^"s";
                         xlField _ ^"u";
                         @csrFieldNoReg _ _ "reserved1" (Bit 9) (getDefaultConst _);
                         @csrFieldAny _ _ ^"tsr" Bool Bool;
                         @csrFieldAny _ _ ^"tw" Bool Bool;
                         @csrFieldAny _ _ ^"tvm" Bool Bool;
                         @csrFieldAny _ _ ^"mxr" Bool Bool;
                         @csrFieldAny _ _ ^"sum" Bool Bool;
                         @csrFieldAny _ _ ^"mprv" Bool Bool;
                         @csrFieldNoReg _ _ "reserved2" (Bit 4) (getDefaultConst _);
                         @csrFieldAny _ _ ^"mpp" (Bit 2) (Bit 2);
                         @csrFieldNoReg _ _ ^"hpp" (Bit 2) (getDefaultConst _);
                         @csrFieldAny _ _ ^"spp" (Bit 1) (Bit 1);
                         @csrFieldAny _ _ ^"mpie" Bool Bool;
                         @csrFieldNoReg _ _ ^"hpie" Bool (getDefaultConst _);
                         @csrFieldAny _ _ ^"spie" Bool Bool;
                         @csrFieldAny _ _ ^"upie" Bool Bool;
                         @csrFieldAny _ _ ^"mie" Bool Bool;
                         @csrFieldNoReg _ _ ^"hie" Bool (getDefaultConst _);
                         @csrFieldAny _ _ ^"sie" Bool Bool;
                         @csrFieldAny _ _ ^"uie" Bool Bool
                       ] in
                  {|
                    csrViewContext := $2;
                    csrViewFields  := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform _ _ fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform _ _ fields)
                  |}
                ];
           csrAccess := (@accessMModeOnly _)
         |};
         {|
           csrName := ^"mtvec";
           csrAddr := CsrIdWidth 'h"305";
           csrViews
             := [
                  let fields
                    := [
                         @tvecField _ _ ^"m" 30;
                         @csrFieldAny _ _ ^"mtvec_mode" (Bit 2) (Bit 2)
                       ] in
                  {|
                    csrViewContext := $1;
                    csrViewFields  := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform _ _ fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform _ _ fields)
                  |};
                  let fields
                    := [
                         @tvecField _ _ ^"m" 62;
                         @csrFieldAny _ _ ^"mtvec_mode" (Bit 2) (Bit 2)
                       ] in
                  {|
                    csrViewContext := $2;
                    csrViewFields  := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform _ _ fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform _ _ fields)
                  |}
                ];
           csrAccess := (@accessMModeOnly _)
         |};
         simpleCsr ^"mcounteren" (CsrIdWidth 'h"306") 32 (@accessMModeOnly _);
         {|
           csrName := ^"mscratch";
           csrAddr := CsrIdWidth 'h"340";
           csrViews
             := [
                  let fields := [ @csrFieldAny _ _ ^"mscratch" (Bit 32) (Bit Xlen) ] in
                  {|
                    csrViewContext    := $1;
                    csrViewFields     := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform _ _ fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform _ _ fields)
                  |};
                  let fields := [ @csrFieldAny _ _ ^"mscratch" (Bit 64) (Bit Xlen) ] in
                  {|
                    csrViewContext    := $2;
                    csrViewFields     := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform _ _ fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform _ _ fields)
                  |}
                ];
           csrAccess := (@accessMModeOnly _)
         |};
         {|
           csrName := ^"mepc";
           csrAddr := CsrIdWidth 'h"341";
           csrViews
             := [
                  let fields := [ @csrFieldAny _ _ ^"mepc" (Bit 32) (Bit Xlen) ] in
                  {|
                    csrViewContext := $1;
                    csrViewFields  := fields;
                    csrViewReadXform  := (@epcReadXform _ _ fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform _ _ fields)
                  |};
                  let fields := [ @csrFieldAny _ _ ^"mepc" (Bit 64) (Bit Xlen) ] in
                  {|
                    csrViewContext := $2;
                    csrViewFields  := fields;
                    csrViewReadXform  := (@epcReadXform _ _ fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform _ _ fields)
                  |}
                ];
           csrAccess := (@accessMModeOnly _)
         |};
         {|
           csrName := ^"mcause";
           csrAddr := CsrIdWidth 'h"342";
           csrViews
             := [
                  let fields
                    := [
                         @csrFieldAny _ _ ^"mcause_interrupt" Bool Bool;
                         @csrFieldAny _ _ ^"mcause_code" (Bit 31) (Bit (Xlen - 1))
                       ] in
                  {|
                    csrViewContext := $1;
                    csrViewFields  := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform _ _ fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform _ _ fields)
                  |};
                  let fields
                    := [
                         @csrFieldAny _ _ ^"mcause_interrupt" Bool Bool;
                         @csrFieldAny _ _ ^"mcause_code" (Bit 63) (Bit (Xlen - 1))
                       ] in
                  {|
                    csrViewContext := $2;
                    csrViewFields  := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform _ _ fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform _ _ fields)
                  |}
                ];
           csrAccess := (@accessMModeOnly _)
         |};
         {|
           csrName := ^"mtval";
           csrAddr := CsrIdWidth 'h"343";
           csrViews
             := [
                  let fields := [ @csrFieldAny _ _ ^"mtval" (Bit 32) (Bit Xlen) ] in
                  {|
                    csrViewContext := $1;
                    csrViewFields  := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform _ _ fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform _ _ fields)
                  |};
                  let fields := [ @csrFieldAny _ _ ^"mtval" (Bit 64) (Bit Xlen) ] in
                  {|
                    csrViewContext := $2;
                    csrViewFields  := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform _ _ fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform _ _ fields)
                  |}
                ];
           csrAccess := (@accessMModeOnly _)
         |};
         {|
           csrName := ^"mip";
           csrAddr := CsrIdWidth 'h"344";
           csrViews
             := let fields
                  := [
                       @csrFieldReadOnly _ _ ^"meip" Bool Bool;
                       @csrFieldNoReg _ _ ^"reserved0" Bool (getDefaultConst _);
                       @csrFieldAny _ _ ^"seip" Bool Bool;
                       @csrFieldAny _ _ ^"ueip" Bool Bool;
                       @csrFieldReadOnly _ _ ^"mtip" Bool Bool;
                       @csrFieldNoReg _ _ ^"reserved1" Bool (getDefaultConst _);
                       @csrFieldAny _ _ ^"stip" Bool Bool;
                       @csrFieldAny _ _ ^"utip" Bool Bool;
                       @csrFieldReadOnly _ _ ^"msip" Bool Bool;
                       @csrFieldNoReg _ _ ^"reserved2" Bool (getDefaultConst _);
                       @csrFieldAny _ _ ^"ssip" Bool Bool;
                       @csrFieldAny _ _ ^"usip" Bool Bool
                     ] in
                repeatCsrView 2
                  (@csrViewDefaultReadXform _ _ fields)
                  (@csrViewDefaultWriteXform _ _ fields);
           csrAccess := (@accessMModeOnly _)
         |};
         {|
           csrName := ^"pmpcfg0";
           csrAddr := CsrIdWidth 'h"3a0";
           csrViews
             := [
                  let fields
                    := [
                         @csrFieldAny _ _ ^"pmp3cfg" (Bit 8) (Bit 8);
                         @csrFieldAny _ _ ^"pmp2cfg" (Bit 8) (Bit 8);
                         @csrFieldAny _ _ ^"pmp1cfg" (Bit 8) (Bit 8);
                         @csrFieldAny _ _ ^"pmp0cfg" (Bit 8) (Bit 8)
                       ] in
                  {|
                    csrViewContext    := $1;
                    csrViewFields     := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform _ _ fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform _ _ fields)
                  |};
                  let fields
                    := [
                         @csrFieldAny _ _ ^"pmp7cfg" (Bit 8) (Bit 8);
                         @csrFieldAny _ _ ^"pmp6cfg" (Bit 8) (Bit 8);
                         @csrFieldAny _ _ ^"pmp5cfg" (Bit 8) (Bit 8);
                         @csrFieldAny _ _ ^"pmp4cfg" (Bit 8) (Bit 8);
                         @csrFieldAny _ _ ^"pmp3cfg" (Bit 8) (Bit 8);
                         @csrFieldAny _ _ ^"pmp2cfg" (Bit 8) (Bit 8);
                         @csrFieldAny _ _ ^"pmp1cfg" (Bit 8) (Bit 8);
                         @csrFieldAny _ _ ^"pmp0cfg" (Bit 8) (Bit 8)
                       ] in
                  {|
                    csrViewContext    := $2;
                    csrViewFields     := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform _ _ fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform _ _ fields)
                  |}
                ];
           csrAccess := (@accessMModeOnly _)
         |};
         {|
           csrName := ^"pmpcfg1";
           csrAddr := CsrIdWidth 'h"3a1";
           csrViews
             := [
                  let fields
                    := [
                         @csrFieldAny _ _ ^"pmp3cfg" (Bit 8) (Bit 8);
                         @csrFieldAny _ _ ^"pmp2cfg" (Bit 8) (Bit 8);
                         @csrFieldAny _ _ ^"pmp1cfg" (Bit 8) (Bit 8);
                         @csrFieldAny _ _ ^"pmp0cfg" (Bit 8) (Bit 8)
                       ] in
                  {|
                    csrViewContext    := $1;
                    csrViewFields     := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform _ _ fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform _ _ fields)
                  |};
                  {|
                    csrViewContext    := $2;
                    csrViewFields     := [];
                    csrViewReadXform  := (@csrViewDefaultReadXform _ _ []);
                    csrViewWriteXform := (@csrViewDefaultWriteXform _ _ [])
                  |}
                ];
           csrAccess
             := fun context : CsrAccessPkt @# ty
                  => context @% "xlen" == $1 &&
                     context @% "mode" == $MachineMode
         |};
         {|
           csrName := ^"pmpcfg2";
           csrAddr := CsrIdWidth 'h"3a2";
           csrViews
             := [
                  let fields
                    := [
                         @csrFieldAny _ _ ^"pmp11cfg" (Bit 8) (Bit 8);
                         @csrFieldAny _ _ ^"pmp10cfg" (Bit 8) (Bit 8);
                         @csrFieldAny _ _ ^"pmp9cfg" (Bit 8) (Bit 8);
                         @csrFieldAny _ _ ^"pmp8cfg" (Bit 8) (Bit 8)
                       ] in
                  {|
                    csrViewContext    := $1;
                    csrViewFields     := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform _ _ fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform _ _ fields)
                  |};
                  let fields
                    := [
                         @csrFieldAny _ _ ^"pmp15cfg" (Bit 8) (Bit 8);
                         @csrFieldAny _ _ ^"pmp14cfg" (Bit 8) (Bit 8);
                         @csrFieldAny _ _ ^"pmp13cfg" (Bit 8) (Bit 8);
                         @csrFieldAny _ _ ^"pmp12cfg" (Bit 8) (Bit 8);
                         @csrFieldAny _ _ ^"pmp11cfg" (Bit 8) (Bit 8);
                         @csrFieldAny _ _ ^"pmp10cfg" (Bit 8) (Bit 8);
                         @csrFieldAny _ _ ^"pmp9cfg" (Bit 8) (Bit 8);
                         @csrFieldAny _ _ ^"pmp8cfg" (Bit 8) (Bit 8)
                       ] in
                  {|
                    csrViewContext    := $2;
                    csrViewFields     := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform _ _ fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform _ _ fields)
                  |}
                ];
           csrAccess := (@accessMModeOnly _)
         |};
         {|
           csrName := ^"pmpcfg1";
           csrAddr := CsrIdWidth 'h"3a3";
           csrViews
             := [
                  let fields
                    := [
                         @csrFieldAny _ _ ^"pmp15cfg" (Bit 8) (Bit 8);
                         @csrFieldAny _ _ ^"pmp14cfg" (Bit 8) (Bit 8);
                         @csrFieldAny _ _ ^"pmp13cfg" (Bit 8) (Bit 8);
                         @csrFieldAny _ _ ^"pmp12cfg" (Bit 8) (Bit 8)
                       ] in
                  {|
                    csrViewContext    := $1;
                    csrViewFields     := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform _ _ fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform _ _ fields)
                  |};
                  {|
                    csrViewContext    := $2;
                    csrViewFields     := [];
                    csrViewReadXform  := (@csrViewDefaultReadXform _ _ []);
                    csrViewWriteXform := (@csrViewDefaultWriteXform _ _ [])
                  |}
                ];
           csrAccess
             := fun context : CsrAccessPkt @# ty
                  => context @% "xlen" == $1 &&
                     context @% "mode" == $MachineMode
         |};
         simpleCsr ^"pmpaddr0" (CsrIdWidth 'h"3b0") pmp_reg_width (@accessMModeOnly _);
         simpleCsr ^"pmpaddr1" (CsrIdWidth 'h"3b1") pmp_reg_width (@accessMModeOnly _);
         simpleCsr ^"pmpaddr2" (CsrIdWidth 'h"3b2") pmp_reg_width (@accessMModeOnly _);
         simpleCsr ^"pmpaddr3" (CsrIdWidth 'h"3b3") pmp_reg_width (@accessMModeOnly _);
         simpleCsr ^"pmpaddr4" (CsrIdWidth 'h"3b4") pmp_reg_width (@accessMModeOnly _);
         simpleCsr ^"pmpaddr5" (CsrIdWidth 'h"3b5") pmp_reg_width (@accessMModeOnly _);
         simpleCsr ^"pmpaddr6" (CsrIdWidth 'h"3b6") pmp_reg_width (@accessMModeOnly _);
         simpleCsr ^"pmpaddr7" (CsrIdWidth 'h"3b7") pmp_reg_width (@accessMModeOnly _);
         simpleCsr ^"pmpaddr8" (CsrIdWidth 'h"3b8") pmp_reg_width (@accessMModeOnly _);
         simpleCsr ^"pmpaddr9" (CsrIdWidth 'h"3b9") pmp_reg_width (@accessMModeOnly _);
         simpleCsr ^"pmpaddr10" (CsrIdWidth 'h"3ba") pmp_reg_width (@accessMModeOnly _);
         simpleCsr ^"pmpaddr11" (CsrIdWidth 'h"3bb") pmp_reg_width (@accessMModeOnly _);
         simpleCsr ^"pmpaddr12" (CsrIdWidth 'h"3bc") pmp_reg_width (@accessMModeOnly _);
         simpleCsr ^"pmpaddr13" (CsrIdWidth 'h"3bd") pmp_reg_width (@accessMModeOnly _);
         simpleCsr ^"pmpaddr14" (CsrIdWidth 'h"3be") pmp_reg_width (@accessMModeOnly _);
         simpleCsr ^"pmpaddr15" (CsrIdWidth 'h"3bf") pmp_reg_width (@accessMModeOnly _);
         {|
           csrName := ^"sstatus";
           csrAddr := CsrIdWidth 'h"100";
           csrViews
             := [
                  let fields
                    := [
                         @csrFieldNoReg _ _ "reserved0" (Bit 12) (getDefaultConst _);
                         @csrFieldAny _ _ ^"mxr" Bool Bool;
                         @csrFieldAny _ _ ^"sum" Bool Bool;
                         @csrFieldNoReg _ _ "reserved1" (Bit 9) (getDefaultConst _);
                         @csrFieldAny _ _ ^"spp" (Bit 1) (Bit 1);
                         @csrFieldNoReg _ _ "reserved2" (Bit 2) (getDefaultConst _);
                         @csrFieldAny _ _ ^"spie" Bool Bool;
                         @csrFieldAny _ _ ^"upie" Bool Bool;
                         @csrFieldNoReg _ _ "reserved3" (Bit 2) (getDefaultConst _);
                         @csrFieldAny _ _ ^"sie" Bool Bool;
                         @csrFieldAny _ _ ^"uie" Bool Bool
                       ] in
                  {|
                    csrViewContext := $1;
                    csrViewFields  := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform _ _ fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform _ _ fields)
                  |};
                  let fields
                    := [
                         @csrFieldNoReg _ _ "reserved0" (Bit 30) (getDefaultConst _);
                         xlField _ ^"u";
                         @csrFieldNoReg _ _ "reserved1" (Bit 12) (getDefaultConst _);
                         @csrFieldAny _ _ ^"mxr" Bool Bool;
                         @csrFieldAny _ _ ^"sum" Bool Bool;
                         @csrFieldNoReg _ _ "reserved2" (Bit 9) (getDefaultConst _);
                         @csrFieldAny _ _ ^"spp" (Bit 1) (Bit 1);
                         @csrFieldNoReg _ _ "reserved3" (Bit 2) (getDefaultConst _);
                         @csrFieldAny _ _ ^"spie" Bool Bool;
                         @csrFieldAny _ _ ^"upie" Bool Bool;
                         @csrFieldNoReg _ _ "reserved4" (Bit 2) (getDefaultConst _);
                         @csrFieldAny _ _ ^"sie" Bool Bool;
                         @csrFieldAny _ _ ^"uie" Bool Bool
                       ] in
                  {|
                    csrViewContext := $2;
                    csrViewFields  := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform _ _ fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform _ _ fields)
                  |}
                ];
           csrAccess := (@accessSMode _)
         |};
         {|
           csrName := ^"sedeleg";
           csrAddr := CsrIdWidth 'h"102";
           csrViews
             := [
                  let fields
                    := [
                         @csrFieldNoReg _ _ "reserved" (Bit 16) (getDefaultConst _);
                         @csrFieldAny _ _ ^"medeleg" (Bit 16) (Bit 16)
                       ] in
                  {|
                    csrViewContext := $1;
                    csrViewFields  := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform _ _ fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform _ _ fields)
                  |};
                  let fields
                    := [
                         @csrFieldNoReg _ _ "reserved" (Bit 48) (getDefaultConst _);
                         @csrFieldAny _ _ ^"medeleg" (Bit 16) (Bit 16)
                       ] in
                  {|
                    csrViewContext := $2;
                    csrViewFields  := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform _ _ fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform _ _ fields)
                  |}
                ];
           csrAccess := (@accessSMode _)
         |};
         {|
           csrName := ^"stvec";
           csrAddr := CsrIdWidth 'h"105";
           csrViews
             := [
                  let fields
                    := [
                         @tvecField _ _ ^"s" 30;
                         @csrFieldAny _ _ ^"stvec_mode" (Bit 2) (Bit 2)
                       ] in
                  {|
                    csrViewContext := $1;
                    csrViewFields  := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform _ _ fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform _ _ fields)
                  |};
                  let fields
                    := [
                         @tvecField _ _ ^"s" 62;
                         @csrFieldAny _ _ ^"stvec_mode" (Bit 2) (Bit 2)
                       ] in
                  {|
                    csrViewContext := $2;
                    csrViewFields  := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform _ _ fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform _ _ fields)
                  |}
                ];
           csrAccess := (@accessSMode _)
         |};
         simpleCsr ^"scounteren" (CsrIdWidth 'h"106") 32 (@accessSMode _);
         {|
           csrName := ^"sscratch";
           csrAddr := CsrIdWidth 'h"140";
           csrViews
             := [
                  let fields := [ @csrFieldAny _ _ ^"sscratch" (Bit 32) (Bit Xlen) ] in
                  {|
                    csrViewContext := $1;
                    csrViewFields  := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform _ _ fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform _ _ fields)
                  |};
                  let fields := [ @csrFieldAny _ _ ^"sscratch" (Bit 64) (Bit Xlen) ] in
                  {|
                    csrViewContext := $2;
                    csrViewFields  := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform _ _ fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform _ _ fields)
                  |}
                ];
           csrAccess := (@accessSMode _)
         |};
         {|
           csrName := ^"sepc";
           csrAddr := CsrIdWidth 'h"141";
           csrViews
             := [
                  let fields := [ @csrFieldAny _ _ ^"sepc" (Bit 32) (Bit Xlen) ] in
                  {|
                    csrViewContext := $1;
                    csrViewFields  := fields;
                    csrViewReadXform  := (@epcReadXform _ _ fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform _ _ fields)
                  |};
                  let fields := [ @csrFieldAny _ _ ^"sepc" (Bit 64) (Bit Xlen) ] in
                  {|
                    csrViewContext := $2;
                    csrViewFields  := fields;
                    csrViewReadXform  := (@epcReadXform _ _ fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform _ _ fields)
                  |}
                ];
           csrAccess := (@accessSMode _)
         |};
         {|
           csrName := ^"scause";
           csrAddr := CsrIdWidth 'h"142";
           csrViews
             := [
                  let fields
                    := [
                         @csrFieldAny _ _ ^"scause_interrupt" Bool Bool;
                         @csrFieldAny _ _ ^"scause_code" (Bit 31) (Bit (Xlen - 1))
                       ] in
                  {|
                    csrViewContext := $1;
                    csrViewFields  := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform _ _ fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform _ _ fields)
                  |};
                  let fields
                    := [
                         @csrFieldAny _ _ ^"scause_interrupt" Bool Bool;
                         @csrFieldAny _ _ ^"scause_code" (Bit 63) (Bit (Xlen - 1))
                       ] in
                  {|
                    csrViewContext := $2;
                    csrViewFields  := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform _ _ fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform _ _ fields)
                  |}
                ];
           csrAccess := (@accessSMode _)
         |};
         {|
           csrName := ^"stval";
           csrAddr := CsrIdWidth 'h"143";
           csrViews
             := [
                  let fields := [ @csrFieldAny _ _ ^"stval" (Bit 32) (Bit Xlen) ] in
                  {|
                    csrViewContext := $1;
                    csrViewFields  := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform _ _ fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform _ _ fields)
                  |};
                  let fields := [ @csrFieldAny _ _ ^"stval" (Bit 64) (Bit Xlen) ] in
                  {|
                    csrViewContext := $2;
                    csrViewFields  := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform _ _ fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform _ _ fields)
                  |}
                ];
           csrAccess := (@accessSMode _)
         |};
         {|
           csrName := satpCsrName name;
           csrAddr := CsrIdWidth 'h"180"; (* TODO *)
           csrViews
             := [
                  let fields
                    := [
                         @csrFieldAny _ _ ^"satp_mode" (Bit 1) (Bit 4);
                         @csrFieldAny _ _ ^"satp_asid" (Bit 9) (Bit 16);
                         @csrFieldAny _ _ ^"satp_ppn" (Bit 22) (Bit 44)
                       ] in
                  {|
                    csrViewContext := $1;
                    csrViewFields  := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform _ _ fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform _ _ fields)
                  |};
                  let fields
                    := [
                         @csrFieldAny _ _ ^"satp_mode" (Bit 4) (Bit 4);
                         @csrFieldAny _ _ ^"satp_asid" (Bit 16) (Bit 16);
                         @csrFieldAny _ _ ^"satp_ppn" (Bit 44) (Bit 44)
                       ] in
                  {|
                    csrViewContext := $2;
                    csrViewFields  := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform _ _ fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform _ _ fields)
                  |}
                ];
           csrAccess
             := fun context : CsrAccessPkt @# ty
                  => context @% "mode" == $MachineMode ||
                     (context @% "mode" == $SupervisorMode && !(context @% "tvm"))
         |};
         {|
           csrName  := ^"mvendorid";
           csrAddr  := CsrIdWidth 'h"f11";
           csrViews
             := let fields
                  := [ @csrFieldAny _ _ ^"mvendorid" (Bit 32) (Bit 32) ] in
                repeatCsrView 2
                  (@csrViewDefaultReadXform _ _ fields)
                  (@csrViewDefaultWriteXform _ _ fields);
           csrAccess := (@accessMModeOnly _)
         |};
         {|
           csrName := ^"marchid";
           csrAddr := CsrIdWidth 'h"f12";
           csrViews
             := [
                  let fields := [ @csrFieldAny _ _ ^"marchid" (Bit 32) (Bit Xlen) ] in
                  {|
                    csrViewContext := $1;
                    csrViewFields  := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform _ _ fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform _ _ fields)
                  |};
                  let fields := [ @csrFieldAny _ _ ^"marchid" (Bit 64) (Bit Xlen) ] in
                  {|
                    csrViewContext := $2;
                    csrViewFields  := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform _ _ fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform _ _ fields)
                  |}
                ];
           csrAccess := (@accessMModeOnly _)
         |};
         {|
           csrName := ^"mimpid";
           csrAddr := CsrIdWidth 'h"f13";
           csrViews
             := [
                  let fields := [ @csrFieldAny _ _ ^"mimpid" (Bit 32) (Bit Xlen) ] in
                  {|
                    csrViewContext := $1;
                    csrViewFields  := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform _ _ fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform _ _ fields)
                  |};
                  let fields := [ @csrFieldAny _ _ ^"mimpid" (Bit 64) (Bit Xlen) ] in
                  {|
                    csrViewContext := $2;
                    csrViewFields  := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform _ _ fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform _ _ fields)
                  |}
                ];
           csrAccess := (@accessMModeOnly _)
         |};
         {|
           csrName := ^"mhartid";
           csrAddr := CsrIdWidth 'h"f14";
           csrViews
             := [
                  let fields := [ @csrFieldAny _ _ ^"mhartid" (Bit 32) (Bit Xlen) ] in
                  {|
                    csrViewContext := $1;
                    csrViewFields  := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform _ _ fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform _ _ fields)
                  |};
                  let fields := [ @csrFieldAny _ _ ^"mhartid" (Bit 64) (Bit Xlen) ] in
                  {|
                    csrViewContext := $2;
                    csrViewFields  := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform _ _ fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform _ _ fields)
                  |}
                ];
           csrAccess := (@accessMModeOnly _)
         |};
         {|
           csrName  := ^"mcycle";
           csrAddr  := CsrIdWidth 'h"b00";
           csrViews
             := let fields := [ @csrFieldAny _ _ ^"mcycle" (Bit 64) (Bit 64) ] in
                repeatCsrView 2
                  (@csrViewDefaultReadXform _ _ fields)
                  (@csrViewDefaultWriteXform _ _ fields);
           csrAccess := (@accessMModeOnly _)
         |};
         {|
           csrName  := ^"minstret";
           csrAddr  := CsrIdWidth 'h"b02";
           csrViews
             := let fields := [ @csrFieldAny _ _ ^"minstret" (Bit 64) (Bit 64) ] in
                repeatCsrView 2
                  (@csrViewDefaultReadXform _ _ fields)
                  (@csrViewDefaultWriteXform _ _ fields);
           csrAccess := (@accessMModeOnly _)
         |};
         nilCsr ^"mhpmcounter3" (CsrIdWidth 'h"b03") (@accessMModeOnly _);
         nilCsr ^"mhpmcounter4" (CsrIdWidth 'h"b04") (@accessMModeOnly _);
         nilCsr ^"mhpmcounter5" (CsrIdWidth 'h"b05") (@accessMModeOnly _);
         nilCsr ^"mhpmcounter6" (CsrIdWidth 'h"b06") (@accessMModeOnly _);
         nilCsr ^"mhpmcounter7" (CsrIdWidth 'h"b07") (@accessMModeOnly _);
         nilCsr ^"mhpmcounter8" (CsrIdWidth 'h"b08") (@accessMModeOnly _);
         nilCsr ^"mhpmcounter9" (CsrIdWidth 'h"b09") (@accessMModeOnly _);
         nilCsr ^"mhpmcounter10" (CsrIdWidth 'h"b0a") (@accessMModeOnly _);
         nilCsr ^"mhpmcounter11" (CsrIdWidth 'h"b0b") (@accessMModeOnly _);
         nilCsr ^"mhpmcounter12" (CsrIdWidth 'h"b0c") (@accessMModeOnly _);
         nilCsr ^"mhpmcounter13" (CsrIdWidth 'h"b0d") (@accessMModeOnly _);
         nilCsr ^"mhpmcounter14" (CsrIdWidth 'h"b03") (@accessMModeOnly _);
         nilCsr ^"mhpmcounter15" (CsrIdWidth 'h"b0f") (@accessMModeOnly _);
         nilCsr ^"mhpmcounter16" (CsrIdWidth 'h"b10") (@accessMModeOnly _);
         nilCsr ^"mhpmcounter17" (CsrIdWidth 'h"b11") (@accessMModeOnly _);
         nilCsr ^"mhpmcounter18" (CsrIdWidth 'h"b12") (@accessMModeOnly _);
         nilCsr ^"mhpmcounter19" (CsrIdWidth 'h"b13") (@accessMModeOnly _);
         nilCsr ^"mhpmcounter20" (CsrIdWidth 'h"b14") (@accessMModeOnly _);
         nilCsr ^"mhpmcounter21" (CsrIdWidth 'h"b15") (@accessMModeOnly _);
         nilCsr ^"mhpmcounter22" (CsrIdWidth 'h"b16") (@accessMModeOnly _);
         nilCsr ^"mhpmcounter23" (CsrIdWidth 'h"b17") (@accessMModeOnly _);
         nilCsr ^"mhpmcounter24" (CsrIdWidth 'h"b18") (@accessMModeOnly _);
         nilCsr ^"mhpmcounter25" (CsrIdWidth 'h"b19") (@accessMModeOnly _);
         nilCsr ^"mhpmcounter26" (CsrIdWidth 'h"b1a") (@accessMModeOnly _);
         nilCsr ^"mhpmcounter27" (CsrIdWidth 'h"b1b") (@accessMModeOnly _);
         nilCsr ^"mhpmcounter28" (CsrIdWidth 'h"b1c") (@accessMModeOnly _);
         nilCsr ^"mhpmcounter29" (CsrIdWidth 'h"b1d") (@accessMModeOnly _);
         nilCsr ^"mhpmcounter30" (CsrIdWidth 'h"b1e") (@accessMModeOnly _);
         nilCsr ^"mhpmcounter31" (CsrIdWidth 'h"b1f") (@accessMModeOnly _);
         {|
           csrName  := ^"mcycleh";
           csrAddr  := CsrIdWidth 'h"b80";
           csrViews
             := let fields := [ @csrFieldAny _ _ ^"mcycle" (Bit 64) (Bit 64) ] in
                repeatCsrView 2
                  (@csrViewUpperReadXform _ _ fields)
                  (@csrViewUpperWriteXform _ _ fields);
           csrAccess := (@accessMModeOnly _)
         |};
         {|
           csrName  := ^"minstreth";
           csrAddr  := CsrIdWidth 'h"b82";
           csrViews
             := let fields := [ @csrFieldAny _ _ ^"minstret" (Bit 64) (Bit 64) ] in
                repeatCsrView 2
                  (@csrViewUpperReadXform _ _ fields)
                  (@csrViewUpperWriteXform _ _ fields);
           csrAccess := (@accessMModeOnly _)
         |};
         nilCsr ^"mhpmevent3" (CsrIdWidth 'h"323") (@accessMModeOnly _);
         nilCsr ^"mhpmevent4" (CsrIdWidth 'h"324") (@accessMModeOnly _);
         nilCsr ^"mhpmevent5" (CsrIdWidth 'h"325") (@accessMModeOnly _);
         nilCsr ^"mhpmevent6" (CsrIdWidth 'h"326") (@accessMModeOnly _);
         nilCsr ^"mhpmevent7" (CsrIdWidth 'h"327") (@accessMModeOnly _);
         nilCsr ^"mhpmevent8" (CsrIdWidth 'h"328") (@accessMModeOnly _);
         nilCsr ^"mhpmevent9" (CsrIdWidth 'h"329") (@accessMModeOnly _);
         nilCsr ^"mhpmevent10" (CsrIdWidth 'h"32a") (@accessMModeOnly _);
         nilCsr ^"mhpmevent11" (CsrIdWidth 'h"32b") (@accessMModeOnly _);
         nilCsr ^"mhpmevent12" (CsrIdWidth 'h"32c") (@accessMModeOnly _);
         nilCsr ^"mhpmevent13" (CsrIdWidth 'h"32d") (@accessMModeOnly _);
         nilCsr ^"mhpmevent14" (CsrIdWidth 'h"323") (@accessMModeOnly _);
         nilCsr ^"mhpmevent15" (CsrIdWidth 'h"32f") (@accessMModeOnly _);
         nilCsr ^"mhpmevent16" (CsrIdWidth 'h"330") (@accessMModeOnly _);
         nilCsr ^"mhpmevent17" (CsrIdWidth 'h"331") (@accessMModeOnly _);
         nilCsr ^"mhpmevent18" (CsrIdWidth 'h"332") (@accessMModeOnly _);
         nilCsr ^"mhpmevent19" (CsrIdWidth 'h"333") (@accessMModeOnly _);
         nilCsr ^"mhpmevent20" (CsrIdWidth 'h"334") (@accessMModeOnly _);
         nilCsr ^"mhpmevent21" (CsrIdWidth 'h"335") (@accessMModeOnly _);
         nilCsr ^"mhpmevent22" (CsrIdWidth 'h"336") (@accessMModeOnly _);
         nilCsr ^"mhpmevent23" (CsrIdWidth 'h"337") (@accessMModeOnly _);
         nilCsr ^"mhpmevent24" (CsrIdWidth 'h"338") (@accessMModeOnly _);
         nilCsr ^"mhpmevent25" (CsrIdWidth 'h"339") (@accessMModeOnly _);
         nilCsr ^"mhpmevent26" (CsrIdWidth 'h"33a") (@accessMModeOnly _);
         nilCsr ^"mhpmevent27" (CsrIdWidth 'h"33b") (@accessMModeOnly _);
         nilCsr ^"mhpmevent28" (CsrIdWidth 'h"33c") (@accessMModeOnly _);
         nilCsr ^"mhpmevent29" (CsrIdWidth 'h"33d") (@accessMModeOnly _);
         nilCsr ^"mhpmevent30" (CsrIdWidth 'h"33e") (@accessMModeOnly _);
         nilCsr ^"mhpmevent31" (CsrIdWidth 'h"33f") (@accessMModeOnly _)
       ].

  Close Scope kami_expr.

End csrs.
