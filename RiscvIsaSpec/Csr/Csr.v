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
    :  list Csr
    := [
         {|
           csrName := ^"ustatus";
           csrAddr := natToWord CsrIdWidth 0;
           csrViews
             := let fields
                  := [
                       @csrFieldNoReg "reserved0" (Bit 27) (getDefaultConst _);
                       @csrFieldAny ^"upie" Bool Bool;
                       @csrFieldNoReg "reserved1" (Bit 3) (getDefaultConst _);
                       @csrFieldAny ^"uie" Bool Bool
                     ] in
                repeatCsrView 2
                  (@csrViewDefaultReadXform fields)
                  (@csrViewDefaultWriteXform fields);
           csrAccess := accessAny
         |};
         nilCsr ^"uie" (CsrIdWidth 'h"4") accessAny;
         {|
           csrName := ^"utvec";
           csrAddr := natToWord CsrIdWidth 5;
           csrViews
             := let fields := [ @csrFieldAny ^"utvec_mode" (Bit 2) (Bit 2) ] in
                repeatCsrView 2
                  (@csrViewDefaultReadXform fields)
                  (@csrViewDefaultWriteXform fields);
           csrAccess := accessAny
         |};
         {|
           csrName := ^"uscratch";
           csrAddr := CsrIdWidth 'h"40";
           csrViews
             := [
                  let fields := [ @csrFieldAny ^"uscratch" (Bit 32) (Bit Xlen) ] in
                  {|
                    csrViewContext    := $1;
                    csrViewFields     := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform fields)
                  |};
                  let fields := [ @csrFieldAny ^"uscratch" (Bit 64) (Bit Xlen) ] in
                  {|
                    csrViewContext    := $2;
                    csrViewFields     := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform fields)
                  |}
                ];
           csrAccess := accessAny
         |};
         {|
           csrName := ^"uepc";
           csrAddr := CsrIdWidth 'h"41";
           csrViews
             := [
                  let fields := [ @csrFieldAny ^"uepc" (Bit 32) (Bit Xlen) ] in
                  {|
                    csrViewContext    := $1;
                    csrViewFields     := fields;
                    csrViewReadXform  := (@epcReadXform fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform fields)
                  |};
                  let fields := [ @csrFieldAny ^"uepc" (Bit 64) (Bit Xlen) ] in
                  {|
                    csrViewContext    := $2;
                    csrViewFields     := fields;
                    csrViewReadXform  := (@epcReadXform fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform fields)
                  |}
                ];
           csrAccess := accessAny
         |};
         {|
           csrName := ^"ucause";
           csrAddr := CsrIdWidth 'h"42";
           csrViews
             := [
                  let fields
                    := [
                         @csrFieldAny ^"ucause_interrupt" Bool Bool;
                         @csrFieldAny ^"ucause_code" (Bit 31) (Bit (Xlen - 1))
                       ] in
                  {|
                    csrViewContext    := $1;
                    csrViewFields     := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform fields)
                  |};
                  let fields
                    := [
                         @csrFieldAny ^"ucause_interrupt" Bool Bool;
                         @csrFieldAny ^"ucause_code" (Bit 63) (Bit (Xlen - 1))
                       ] in
                  {|
                    csrViewContext    := $2;
                    csrViewFields     := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform fields)
                  |}
                ];
           csrAccess := accessAny
         |};
         {|
           csrName := ^"utval";
           csrAddr := CsrIdWidth 'h"43";
           csrViews
             := [
                  let fields := [ @csrFieldAny ^"utval" (Bit 32) (Bit Xlen) ] in
                  {|
                    csrViewContext    := $1;
                    csrViewFields     := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform fields)
                  |};
                  let fields := [ @csrFieldAny ^"utval" (Bit 64) (Bit Xlen) ] in
                  {|
                    csrViewContext    := $2;
                    csrViewFields     := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform fields)
                  |}
                ];
           csrAccess := accessAny
         |};
         {|
           csrName := ^"uip";
           csrAddr := CsrIdWidth 'h"44";
           csrViews
             := let fields
                  := [
                       @csrFieldAny ^"ueip" Bool Bool;
                       @csrFieldNoReg ^"reserved0" (Bit 3) (getDefaultConst _);
                       @csrFieldAny ^"utip" Bool Bool;
                       @csrFieldNoReg ^"reserved1" (Bit 3) (getDefaultConst _);
                       @csrFieldAny ^"usip" Bool Bool
                     ] in
                repeatCsrView 2
                  (@csrViewDefaultReadXform fields)
                  (@csrViewDefaultWriteXform fields);
           csrAccess := accessMModeOnly
         |};
         {|
           csrName := ^"fflagsG";
           csrAddr := natToWord CsrIdWidth 1;
           csrViews
             := let fields
                  := [
                       @csrFieldNoReg "reserved" (Bit 27) (getDefaultConst _);
                       @csrFieldAny ^"fflags" (Bit 5) FflagsValue
                     ] in
                repeatCsrView 2
                  (@csrViewDefaultReadXform fields)
                  (@csrViewDefaultWriteXform fields);
           csrAccess := accessAny
         |};
         {|
           csrName := ^"frmG";
           csrAddr := natToWord CsrIdWidth 2;
           csrViews
             := let fields
                  := [
                       @csrFieldNoReg "reserved" (Bit 29) (getDefaultConst _);
                       @csrFieldAny ^"frm" (Bit 3) FrmValue
                     ] in
                repeatCsrView 2
                  (@csrViewDefaultReadXform fields)
                  (@csrViewDefaultWriteXform fields);
           csrAccess := accessAny
         |};
         {|
           csrName := ^"fcsrG";
           csrAddr := natToWord CsrIdWidth 3;
           csrViews
             := let fields
                  := [
                       @csrFieldNoReg "reserved" (Bit 24) (getDefaultConst _);
                       @csrFieldAny ^"frm" (Bit 3) FrmValue;
                       @csrFieldAny ^"fflags" (Bit 5) FflagsValue
                     ] in
                repeatCsrView 2
                  (@csrViewDefaultReadXform fields)
                  (@csrViewDefaultWriteXform fields);
           csrAccess := accessAny
         |};
         simpleCsr ^"mcycle" (CsrIdWidth 'h"c00") 64 (accessCounter "CY");
         readonlyCsr ^"mtime" (CsrIdWidth 'h"c01") 64 accessAny;
         simpleCsr ^"minstret" (CsrIdWidth 'h"c02") 64 (accessCounter "IR");
         {|
           csrName := ^"cycleh";
           csrAddr := CsrIdWidth 'h"c80";
           csrViews
             := let fields := [ @csrFieldReadOnly ^"mcycle" (Bit 64) (Bit 64) ] in
                repeatCsrView 2
                  (@csrViewUpperReadXform fields)
                  (@csrViewUpperWriteXform fields);
           csrAccess := accessAny
         |};
         {|
           csrName := ^"instreth";
           csrAddr := CsrIdWidth 'h"c82";
           csrViews
             := let fields := [ @csrFieldReadOnly ^"minstret" (Bit 64) (Bit 64) ] in
                repeatCsrView 2
                  (@csrViewUpperReadXform fields)
                  (@csrViewUpperWriteXform fields);
           csrAccess := accessAny
         |};
         {|
           csrName := ^"misa";
           csrAddr := CsrIdWidth 'h"301";
           csrViews
             := let ext_fields
                  := [
                       extField "Z";
                       extField "Y";
                       extField "X";
                       extField "W";
                       extField "V";
                       extField "U";
                       extField "T";
                       extField "S";
                       extField "R";
                       extField "Q";
                       extField "P";
                       extField "O";
                       extField "N";
                       extField "M";
                       extField "L";
                       extField "K";
                       extField "J";
                       extField "I";
                       extField "H";
                       extField "G";
                       extField "F";
                       extField "E";
                       extField "D";
                       compressedExtField;
                       extField "B";
                       extField "A"
                     ] in
                [
                  let fields
                    := [
                         xlField ^"m";
                         @csrFieldNoReg "misa_reserved32" (Bit 4) (getDefaultConst _);
                         @csrFieldNoReg
                           "extensions" (Bit 26)
                           (ConstBit WO~1~0~1~1~0~1~0~0~1~0~0~0~1~0~0~0~0~0~0~0~0~0~0~0~0~1) (* TODO *)
                       ] (* ++ ext_fields *) in
                  {|
                    csrViewContext := $1;
                    csrViewFields  := fields;
                    csrViewReadXform  := @csrViewDefaultReadXform fields;
                    csrViewWriteXform := @csrViewDefaultWriteXform fields
                  |};
                  let fields
                    := [
                         xlField ^"m";
                         @csrFieldNoReg "misa_reserved64" (Bit 36) (getDefaultConst _);
                         @csrFieldNoReg
                           "extensions" (Bit 26)
                           (ConstBit WO~1~0~1~1~0~1~0~0~1~0~0~0~1~0~0~0~0~0~0~0~0~0~0~0~0~1) (* TODO *)
                       ] (* ++ ext_fields *) in
                  {|
                    csrViewContext := $2;
                    csrViewFields  := fields;
                    csrViewReadXform  := @csrViewDefaultReadXform fields;
                    csrViewWriteXform := @csrViewDefaultWriteXform fields
                  |}
                ];
           csrAccess := accessMModeOnly
         |};
         {|
           csrName := ^"medeleg";
           csrAddr := CsrIdWidth 'h"302";
           csrViews
             := [
                  let fields
                    := [
                         @csrFieldNoReg "reserved" (Bit 16) (getDefaultConst _);
                         @csrFieldAny ^"medeleg" (Bit 16) (Bit 16)
                       ] in
                  {|
                    csrViewContext := $1;
                    csrViewFields  := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform fields)
                  |};
                  let fields
                    := [
                         @csrFieldNoReg "reserved" (Bit 48) (getDefaultConst _);
                         @csrFieldAny ^"medeleg" (Bit 16) (Bit 16)
                       ] in
                  {|
                    csrViewContext := $2;
                    csrViewFields  := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform fields)
                  |}
                ];
           csrAccess := accessMModeOnly
         |};
         {|
           csrName := ^"mideleg";
           csrAddr := CsrIdWidth 'h"303";
           csrViews
             := [
                  let fields
                    := [
                         @csrFieldNoReg "reserved" (Bit 20) (getDefaultConst _);
                         @csrFieldAny ^"mideleg" (Bit 12) (Bit 12)
                       ] in
                  {|
                    csrViewContext := $1;
                    csrViewFields  := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform fields)
                  |};
                  let fields
                    := [
                         @csrFieldNoReg "reserved" (Bit 52) (getDefaultConst _);
                         @csrFieldAny ^"mideleg" (Bit 12) (Bit 12)
                       ] in
                  {|
                    csrViewContext := $2;
                    csrViewFields  := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform fields)
                  |}
                ];
           csrAccess := accessMModeOnly
         |};
         {|
           csrName := ^"mie";
           csrAddr := CsrIdWidth 'h"304";
           csrViews
             := let fields
                  := [
                       @csrFieldReadOnly ^"meie" Bool Bool;
                       @csrFieldNoReg ^"reserved0" Bool (getDefaultConst _);
                       @csrFieldAny ^"seie" Bool Bool;
                       @csrFieldAny ^"ueie" Bool Bool;
                       @csrFieldReadOnly ^"mtie" Bool Bool;
                       @csrFieldNoReg ^"reserved1" Bool (getDefaultConst _);
                       @csrFieldAny ^"stie" Bool Bool;
                       @csrFieldAny ^"utie" Bool Bool;
                       @csrFieldReadOnly ^"msie" Bool Bool;
                       @csrFieldNoReg ^"reserved2" Bool (getDefaultConst _);
                       @csrFieldAny ^"ssie" Bool Bool;
                       @csrFieldAny ^"usie" Bool Bool
                     ] in
                repeatCsrView 2
                  (@csrViewDefaultReadXform fields)
                  (@csrViewDefaultWriteXform fields);
           csrAccess := accessMModeOnly
         |};
         {|
           csrName := ^"mstatus";
           csrAddr := CsrIdWidth 'h"300";
           csrViews
             := [
                  let fields
                    := [
                         @csrFieldNoReg "reserved0" (Bit 9) (getDefaultConst _);
                         @csrFieldAny ^"tsr" Bool Bool;
                         @csrFieldAny ^"tw" Bool Bool;
                         @csrFieldAny ^"tvm" Bool Bool;
                         @csrFieldAny ^"mxr" Bool Bool;
                         @csrFieldAny ^"sum" Bool Bool;
                         @csrFieldAny ^"mprv" Bool Bool;
                         @csrFieldNoReg "reserved1" (Bit 4) (getDefaultConst _);
                         @csrFieldAny ^"mpp" (Bit 2) (Bit 2);
                         @csrFieldNoReg ^"hpp" (Bit 2) (getDefaultConst _);
                         @csrFieldAny ^"spp" (Bit 1) (Bit 1);
                         @csrFieldAny ^"mpie" Bool Bool;
                         @csrFieldNoReg ^"hpie" Bool (getDefaultConst _);
                         @csrFieldAny ^"spie" Bool Bool;
                         @csrFieldAny ^"upie" Bool Bool;
                         @csrFieldAny ^"mie" Bool Bool;
                         @csrFieldNoReg ^"hie" Bool (getDefaultConst _);
                         @csrFieldAny ^"sie" Bool Bool;
                         @csrFieldAny ^"uie" Bool Bool
                       ] in
                  {|
                    csrViewContext := $1;
                    csrViewFields  := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform fields)
                  |};
                  let fields
                    := [
                         @csrFieldNoReg "reserved0" (Bit 28) (getDefaultConst _);
                         xlField ^"s";
                         xlField ^"u";
                         @csrFieldNoReg "reserved1" (Bit 9) (getDefaultConst _);
                         @csrFieldAny ^"tsr" Bool Bool;
                         @csrFieldAny ^"tw" Bool Bool;
                         @csrFieldAny ^"tvm" Bool Bool;
                         @csrFieldAny ^"mxr" Bool Bool;
                         @csrFieldAny ^"sum" Bool Bool;
                         @csrFieldAny ^"mprv" Bool Bool;
                         @csrFieldNoReg "reserved2" (Bit 4) (getDefaultConst _);
                         @csrFieldAny ^"mpp" (Bit 2) (Bit 2);
                         @csrFieldNoReg ^"hpp" (Bit 2) (getDefaultConst _);
                         @csrFieldAny ^"spp" (Bit 1) (Bit 1);
                         @csrFieldAny ^"mpie" Bool Bool;
                         @csrFieldNoReg ^"hpie" Bool (getDefaultConst _);
                         @csrFieldAny ^"spie" Bool Bool;
                         @csrFieldAny ^"upie" Bool Bool;
                         @csrFieldAny ^"mie" Bool Bool;
                         @csrFieldNoReg ^"hie" Bool (getDefaultConst _);
                         @csrFieldAny ^"sie" Bool Bool;
                         @csrFieldAny ^"uie" Bool Bool
                       ] in
                  {|
                    csrViewContext := $2;
                    csrViewFields  := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform fields)
                  |}
                ];
           csrAccess := accessMModeOnly
         |};
         {|
           csrName := ^"mtvec";
           csrAddr := CsrIdWidth 'h"305";
           csrViews
             := [
                  let fields
                    := [
                         @tvecField ^"m" 30;
                         @csrFieldAny ^"mtvec_mode" (Bit 2) (Bit 2)
                       ] in
                  {|
                    csrViewContext := $1;
                    csrViewFields  := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform fields)
                  |};
                  let fields
                    := [
                         @tvecField ^"m" 62;
                         @csrFieldAny ^"mtvec_mode" (Bit 2) (Bit 2)
                       ] in
                  {|
                    csrViewContext := $2;
                    csrViewFields  := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform fields)
                  |}
                ];
           csrAccess := accessMModeOnly
         |};
         simpleCsr ^"mcounteren" (CsrIdWidth 'h"306") 32 accessMModeOnly;
         {|
           csrName := ^"mscratch";
           csrAddr := CsrIdWidth 'h"340";
           csrViews
             := [
                  let fields := [ @csrFieldAny ^"mscratch" (Bit 32) (Bit Xlen) ] in
                  {|
                    csrViewContext    := $1;
                    csrViewFields     := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform fields)
                  |};
                  let fields := [ @csrFieldAny ^"mscratch" (Bit 64) (Bit Xlen) ] in
                  {|
                    csrViewContext    := $2;
                    csrViewFields     := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform fields)
                  |}
                ];
           csrAccess := accessMModeOnly
         |};
         {|
           csrName := ^"mepc";
           csrAddr := CsrIdWidth 'h"341";
           csrViews
             := [
                  let fields := [ @csrFieldAny ^"mepc" (Bit 32) (Bit Xlen) ] in
                  {|
                    csrViewContext := $1;
                    csrViewFields  := fields;
                    csrViewReadXform  := (@epcReadXform fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform fields)
                  |};
                  let fields := [ @csrFieldAny ^"mepc" (Bit 64) (Bit Xlen) ] in
                  {|
                    csrViewContext := $2;
                    csrViewFields  := fields;
                    csrViewReadXform  := (@epcReadXform fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform fields)
                  |}
                ];
           csrAccess := accessMModeOnly
         |};
         {|
           csrName := ^"mcause";
           csrAddr := CsrIdWidth 'h"342";
           csrViews
             := [
                  let fields
                    := [
                         @csrFieldAny ^"mcause_interrupt" Bool Bool;
                         @csrFieldAny ^"mcause_code" (Bit 31) (Bit (Xlen - 1))
                       ] in
                  {|
                    csrViewContext := $1;
                    csrViewFields  := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform fields)
                  |};
                  let fields
                    := [
                         @csrFieldAny ^"mcause_interrupt" Bool Bool;
                         @csrFieldAny ^"mcause_code" (Bit 63) (Bit (Xlen - 1))
                       ] in
                  {|
                    csrViewContext := $2;
                    csrViewFields  := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform fields)
                  |}
                ];
           csrAccess := accessMModeOnly
         |};
         {|
           csrName := ^"mtval";
           csrAddr := CsrIdWidth 'h"343";
           csrViews
             := [
                  let fields := [ @csrFieldAny ^"mtval" (Bit 32) (Bit Xlen) ] in
                  {|
                    csrViewContext := $1;
                    csrViewFields  := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform fields)
                  |};
                  let fields := [ @csrFieldAny ^"mtval" (Bit 64) (Bit Xlen) ] in
                  {|
                    csrViewContext := $2;
                    csrViewFields  := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform fields)
                  |}
                ];
           csrAccess := accessMModeOnly
         |};
         {|
           csrName := ^"mip";
           csrAddr := CsrIdWidth 'h"344";
           csrViews
             := let fields
                  := [
                       @csrFieldReadOnly ^"meip" Bool Bool;
                       @csrFieldNoReg ^"reserved0" Bool (getDefaultConst _);
                       @csrFieldAny ^"seip" Bool Bool;
                       @csrFieldAny ^"ueip" Bool Bool;
                       @csrFieldReadOnly ^"mtip" Bool Bool;
                       @csrFieldNoReg ^"reserved1" Bool (getDefaultConst _);
                       @csrFieldAny ^"stip" Bool Bool;
                       @csrFieldAny ^"utip" Bool Bool;
                       @csrFieldReadOnly ^"msip" Bool Bool;
                       @csrFieldNoReg ^"reserved2" Bool (getDefaultConst _);
                       @csrFieldAny ^"ssip" Bool Bool;
                       @csrFieldAny ^"usip" Bool Bool
                     ] in
                repeatCsrView 2
                  (@csrViewDefaultReadXform fields)
                  (@csrViewDefaultWriteXform fields);
           csrAccess := accessMModeOnly
         |};
         {|
           csrName := ^"pmpcfg0";
           csrAddr := CsrIdWidth 'h"3a0";
           csrViews
             := [
                  let fields
                    := [
                         @csrFieldAny ^"pmp3cfg" (Bit 8) (Bit 8);
                         @csrFieldAny ^"pmp2cfg" (Bit 8) (Bit 8);
                         @csrFieldAny ^"pmp1cfg" (Bit 8) (Bit 8);
                         @csrFieldAny ^"pmp0cfg" (Bit 8) (Bit 8)
                       ] in
                  {|
                    csrViewContext    := $1;
                    csrViewFields     := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform fields)
                  |};
                  let fields
                    := [
                         @csrFieldAny ^"pmp7cfg" (Bit 8) (Bit 8);
                         @csrFieldAny ^"pmp6cfg" (Bit 8) (Bit 8);
                         @csrFieldAny ^"pmp5cfg" (Bit 8) (Bit 8);
                         @csrFieldAny ^"pmp4cfg" (Bit 8) (Bit 8);
                         @csrFieldAny ^"pmp3cfg" (Bit 8) (Bit 8);
                         @csrFieldAny ^"pmp2cfg" (Bit 8) (Bit 8);
                         @csrFieldAny ^"pmp1cfg" (Bit 8) (Bit 8);
                         @csrFieldAny ^"pmp0cfg" (Bit 8) (Bit 8)
                       ] in
                  {|
                    csrViewContext    := $2;
                    csrViewFields     := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform fields)
                  |}
                ];
           csrAccess := accessMModeOnly
         |};
         {|
           csrName := ^"pmpcfg1";
           csrAddr := CsrIdWidth 'h"3a1";
           csrViews
             := [
                  let fields
                    := [
                         @csrFieldAny ^"pmp3cfg" (Bit 8) (Bit 8);
                         @csrFieldAny ^"pmp2cfg" (Bit 8) (Bit 8);
                         @csrFieldAny ^"pmp1cfg" (Bit 8) (Bit 8);
                         @csrFieldAny ^"pmp0cfg" (Bit 8) (Bit 8)
                       ] in
                  {|
                    csrViewContext    := $1;
                    csrViewFields     := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform fields)
                  |};
                  {|
                    csrViewContext    := $2;
                    csrViewFields     := [];
                    csrViewReadXform  := (@csrViewDefaultReadXform []);
                    csrViewWriteXform := (@csrViewDefaultWriteXform [])
                  |}
                ];
           csrAccess
             := fun context
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
                         @csrFieldAny ^"pmp11cfg" (Bit 8) (Bit 8);
                         @csrFieldAny ^"pmp10cfg" (Bit 8) (Bit 8);
                         @csrFieldAny ^"pmp9cfg" (Bit 8) (Bit 8);
                         @csrFieldAny ^"pmp8cfg" (Bit 8) (Bit 8)
                       ] in
                  {|
                    csrViewContext    := $1;
                    csrViewFields     := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform fields)
                  |};
                  let fields
                    := [
                         @csrFieldAny ^"pmp15cfg" (Bit 8) (Bit 8);
                         @csrFieldAny ^"pmp14cfg" (Bit 8) (Bit 8);
                         @csrFieldAny ^"pmp13cfg" (Bit 8) (Bit 8);
                         @csrFieldAny ^"pmp12cfg" (Bit 8) (Bit 8);
                         @csrFieldAny ^"pmp11cfg" (Bit 8) (Bit 8);
                         @csrFieldAny ^"pmp10cfg" (Bit 8) (Bit 8);
                         @csrFieldAny ^"pmp9cfg" (Bit 8) (Bit 8);
                         @csrFieldAny ^"pmp8cfg" (Bit 8) (Bit 8)
                       ] in
                  {|
                    csrViewContext    := $2;
                    csrViewFields     := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform fields)
                  |}
                ];
           csrAccess := accessMModeOnly
         |};
         {|
           csrName := ^"pmpcfg1";
           csrAddr := CsrIdWidth 'h"3a3";
           csrViews
             := [
                  let fields
                    := [
                         @csrFieldAny ^"pmp15cfg" (Bit 8) (Bit 8);
                         @csrFieldAny ^"pmp14cfg" (Bit 8) (Bit 8);
                         @csrFieldAny ^"pmp13cfg" (Bit 8) (Bit 8);
                         @csrFieldAny ^"pmp12cfg" (Bit 8) (Bit 8)
                       ] in
                  {|
                    csrViewContext    := $1;
                    csrViewFields     := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform fields)
                  |};
                  {|
                    csrViewContext    := $2;
                    csrViewFields     := [];
                    csrViewReadXform  := (@csrViewDefaultReadXform []);
                    csrViewWriteXform := (@csrViewDefaultWriteXform [])
                  |}
                ];
           csrAccess
             := fun context
                  => context @% "xlen" == $1 &&
                     context @% "mode" == $MachineMode
         |};
         simpleCsr ^"pmpaddr0" (CsrIdWidth 'h"3b0") pmp_reg_width accessMModeOnly;
         simpleCsr ^"pmpaddr1" (CsrIdWidth 'h"3b1") pmp_reg_width accessMModeOnly;
         simpleCsr ^"pmpaddr2" (CsrIdWidth 'h"3b2") pmp_reg_width accessMModeOnly;
         simpleCsr ^"pmpaddr3" (CsrIdWidth 'h"3b3") pmp_reg_width accessMModeOnly;
         simpleCsr ^"pmpaddr4" (CsrIdWidth 'h"3b4") pmp_reg_width accessMModeOnly;
         simpleCsr ^"pmpaddr5" (CsrIdWidth 'h"3b5") pmp_reg_width accessMModeOnly;
         simpleCsr ^"pmpaddr6" (CsrIdWidth 'h"3b6") pmp_reg_width accessMModeOnly;
         simpleCsr ^"pmpaddr7" (CsrIdWidth 'h"3b7") pmp_reg_width accessMModeOnly;
         simpleCsr ^"pmpaddr8" (CsrIdWidth 'h"3b8") pmp_reg_width accessMModeOnly;
         simpleCsr ^"pmpaddr9" (CsrIdWidth 'h"3b9") pmp_reg_width accessMModeOnly;
         simpleCsr ^"pmpaddr10" (CsrIdWidth 'h"3ba") pmp_reg_width accessMModeOnly;
         simpleCsr ^"pmpaddr11" (CsrIdWidth 'h"3bb") pmp_reg_width accessMModeOnly;
         simpleCsr ^"pmpaddr12" (CsrIdWidth 'h"3bc") pmp_reg_width accessMModeOnly;
         simpleCsr ^"pmpaddr13" (CsrIdWidth 'h"3bd") pmp_reg_width accessMModeOnly;
         simpleCsr ^"pmpaddr14" (CsrIdWidth 'h"3be") pmp_reg_width accessMModeOnly;
         simpleCsr ^"pmpaddr15" (CsrIdWidth 'h"3bf") pmp_reg_width accessMModeOnly;
         {|
           csrName := ^"sstatus";
           csrAddr := CsrIdWidth 'h"100";
           csrViews
             := [
                  let fields
                    := [
                         @csrFieldNoReg "reserved0" (Bit 12) (getDefaultConst _);
                         @csrFieldAny ^"mxr" Bool Bool;
                         @csrFieldAny ^"sum" Bool Bool;
                         @csrFieldNoReg "reserved1" (Bit 9) (getDefaultConst _);
                         @csrFieldAny ^"spp" (Bit 1) (Bit 1);
                         @csrFieldNoReg "reserved2" (Bit 2) (getDefaultConst _);
                         @csrFieldAny ^"spie" Bool Bool;
                         @csrFieldAny ^"upie" Bool Bool;
                         @csrFieldNoReg "reserved3" (Bit 2) (getDefaultConst _);
                         @csrFieldAny ^"sie" Bool Bool;
                         @csrFieldAny ^"uie" Bool Bool
                       ] in
                  {|
                    csrViewContext := $1;
                    csrViewFields  := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform fields)
                  |};
                  let fields
                    := [
                         @csrFieldNoReg "reserved0" (Bit 30) (getDefaultConst _);
                         xlField ^"u";
                         @csrFieldNoReg "reserved1" (Bit 12) (getDefaultConst _);
                         @csrFieldAny ^"mxr" Bool Bool;
                         @csrFieldAny ^"sum" Bool Bool;
                         @csrFieldNoReg "reserved2" (Bit 9) (getDefaultConst _);
                         @csrFieldAny ^"spp" (Bit 1) (Bit 1);
                         @csrFieldNoReg "reserved3" (Bit 2) (getDefaultConst _);
                         @csrFieldAny ^"spie" Bool Bool;
                         @csrFieldAny ^"upie" Bool Bool;
                         @csrFieldNoReg "reserved4" (Bit 2) (getDefaultConst _);
                         @csrFieldAny ^"sie" Bool Bool;
                         @csrFieldAny ^"uie" Bool Bool
                       ] in
                  {|
                    csrViewContext := $2;
                    csrViewFields  := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform fields)
                  |}
                ];
           csrAccess := accessSMode
         |};
         {|
           csrName := ^"sedeleg";
           csrAddr := CsrIdWidth 'h"102";
           csrViews
             := [
                  let fields
                    := [
                         @csrFieldNoReg "reserved" (Bit 16) (getDefaultConst _);
                         @csrFieldAny ^"medeleg" (Bit 16) (Bit 16)
                       ] in
                  {|
                    csrViewContext := $1;
                    csrViewFields  := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform fields)
                  |};
                  let fields
                    := [
                         @csrFieldNoReg "reserved" (Bit 48) (getDefaultConst _);
                         @csrFieldAny ^"medeleg" (Bit 16) (Bit 16)
                       ] in
                  {|
                    csrViewContext := $2;
                    csrViewFields  := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform fields)
                  |}
                ];
           csrAccess := accessSMode
         |};
         {|
           csrName := ^"stvec";
           csrAddr := CsrIdWidth 'h"105";
           csrViews
             := [
                  let fields
                    := [
                         @tvecField ^"s" 30;
                         @csrFieldAny ^"stvec_mode" (Bit 2) (Bit 2)
                       ] in
                  {|
                    csrViewContext := $1;
                    csrViewFields  := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform fields)
                  |};
                  let fields
                    := [
                         @tvecField ^"s" 62;
                         @csrFieldAny ^"stvec_mode" (Bit 2) (Bit 2)
                       ] in
                  {|
                    csrViewContext := $2;
                    csrViewFields  := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform fields)
                  |}
                ];
           csrAccess := accessSMode
         |};
         simpleCsr ^"scounteren" (CsrIdWidth 'h"106") 32 accessSMode;
         {|
           csrName := ^"sscratch";
           csrAddr := CsrIdWidth 'h"140";
           csrViews
             := [
                  let fields := [ @csrFieldAny ^"sscratch" (Bit 32) (Bit Xlen) ] in
                  {|
                    csrViewContext := $1;
                    csrViewFields  := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform fields)
                  |};
                  let fields := [ @csrFieldAny ^"sscratch" (Bit 64) (Bit Xlen) ] in
                  {|
                    csrViewContext := $2;
                    csrViewFields  := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform fields)
                  |}
                ];
           csrAccess := accessSMode
         |};
         {|
           csrName := ^"sepc";
           csrAddr := CsrIdWidth 'h"141";
           csrViews
             := [
                  let fields := [ @csrFieldAny ^"sepc" (Bit 32) (Bit Xlen) ] in
                  {|
                    csrViewContext := $1;
                    csrViewFields  := fields;
                    csrViewReadXform  := (@epcReadXform fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform fields)
                  |};
                  let fields := [ @csrFieldAny ^"sepc" (Bit 64) (Bit Xlen) ] in
                  {|
                    csrViewContext := $2;
                    csrViewFields  := fields;
                    csrViewReadXform  := (@epcReadXform fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform fields)
                  |}
                ];
           csrAccess := accessSMode
         |};
         {|
           csrName := ^"scause";
           csrAddr := CsrIdWidth 'h"142";
           csrViews
             := [
                  let fields
                    := [
                         @csrFieldAny ^"scause_interrupt" Bool Bool;
                         @csrFieldAny ^"scause_code" (Bit 31) (Bit (Xlen - 1))
                       ] in
                  {|
                    csrViewContext := $1;
                    csrViewFields  := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform fields)
                  |};
                  let fields
                    := [
                         @csrFieldAny ^"scause_interrupt" Bool Bool;
                         @csrFieldAny ^"scause_code" (Bit 63) (Bit (Xlen - 1))
                       ] in
                  {|
                    csrViewContext := $2;
                    csrViewFields  := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform fields)
                  |}
                ];
           csrAccess := accessSMode
         |};
         {|
           csrName := ^"stval";
           csrAddr := CsrIdWidth 'h"143";
           csrViews
             := [
                  let fields := [ @csrFieldAny ^"stval" (Bit 32) (Bit Xlen) ] in
                  {|
                    csrViewContext := $1;
                    csrViewFields  := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform fields)
                  |};
                  let fields := [ @csrFieldAny ^"stval" (Bit 64) (Bit Xlen) ] in
                  {|
                    csrViewContext := $2;
                    csrViewFields  := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform fields)
                  |}
                ];
           csrAccess := accessSMode
         |};
         {|
           csrName := satpCsrName;
           csrAddr := CsrIdWidth 'h"180"; (* TODO *)
           csrViews
             := [
                  let fields
                    := [
                         @csrFieldAny ^"satp_mode" (Bit 1) (Bit 4);
                         @csrFieldAny ^"satp_asid" (Bit 9) (Bit 16);
                         @csrFieldAny ^"satp_ppn" (Bit 22) (Bit 44)
                       ] in
                  {|
                    csrViewContext := $1;
                    csrViewFields  := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform fields)
                  |};
                  let fields
                    := [
                         @csrFieldAny ^"satp_mode" (Bit 4) (Bit 4);
                         @csrFieldAny ^"satp_asid" (Bit 16) (Bit 16);
                         @csrFieldAny ^"satp_ppn" (Bit 44) (Bit 44)
                       ] in
                  {|
                    csrViewContext := $2;
                    csrViewFields  := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform fields)
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
                  := [ @csrFieldAny ^"mvendorid" (Bit 32) (Bit 32) ] in
                repeatCsrView 2
                  (@csrViewDefaultReadXform fields)
                  (@csrViewDefaultWriteXform fields);
           csrAccess := accessMModeOnly
         |};
         {|
           csrName := ^"marchid";
           csrAddr := CsrIdWidth 'h"f12";
           csrViews
             := [
                  let fields := [ @csrFieldAny ^"marchid" (Bit 32) (Bit Xlen) ] in
                  {|
                    csrViewContext := $1;
                    csrViewFields  := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform fields)
                  |};
                  let fields := [ @csrFieldAny ^"marchid" (Bit 64) (Bit Xlen) ] in
                  {|
                    csrViewContext := $2;
                    csrViewFields  := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform fields)
                  |}
                ];
           csrAccess := accessMModeOnly
         |};
         {|
           csrName := ^"mimpid";
           csrAddr := CsrIdWidth 'h"f13";
           csrViews
             := [
                  let fields := [ @csrFieldAny ^"mimpid" (Bit 32) (Bit Xlen) ] in
                  {|
                    csrViewContext := $1;
                    csrViewFields  := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform fields)
                  |};
                  let fields := [ @csrFieldAny ^"mimpid" (Bit 64) (Bit Xlen) ] in
                  {|
                    csrViewContext := $2;
                    csrViewFields  := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform fields)
                  |}
                ];
           csrAccess := accessMModeOnly
         |};
         {|
           csrName := ^"mhartid";
           csrAddr := CsrIdWidth 'h"f14";
           csrViews
             := [
                  let fields := [ @csrFieldAny ^"mhartid" (Bit 32) (Bit Xlen) ] in
                  {|
                    csrViewContext := $1;
                    csrViewFields  := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform fields)
                  |};
                  let fields := [ @csrFieldAny ^"mhartid" (Bit 64) (Bit Xlen) ] in
                  {|
                    csrViewContext := $2;
                    csrViewFields  := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform fields)
                  |}
                ];
           csrAccess := accessMModeOnly
         |};
         {|
           csrName  := ^"mcycle";
           csrAddr  := CsrIdWidth 'h"b00";
           csrViews
             := let fields := [ @csrFieldAny ^"mcycle" (Bit 64) (Bit 64) ] in
                repeatCsrView 2
                  (@csrViewDefaultReadXform fields)
                  (@csrViewDefaultWriteXform fields);
           csrAccess := accessMModeOnly
         |};
         {|
           csrName  := ^"minstret";
           csrAddr  := CsrIdWidth 'h"b02";
           csrViews
             := let fields := [ @csrFieldAny ^"minstret" (Bit 64) (Bit 64) ] in
                repeatCsrView 2
                  (@csrViewDefaultReadXform fields)
                  (@csrViewDefaultWriteXform fields);
           csrAccess := accessMModeOnly
         |};
         nilCsr ^"mhpmcounter3" (CsrIdWidth 'h"b03") accessMModeOnly;
         nilCsr ^"mhpmcounter4" (CsrIdWidth 'h"b04") accessMModeOnly;
         nilCsr ^"mhpmcounter5" (CsrIdWidth 'h"b05") accessMModeOnly;
         nilCsr ^"mhpmcounter6" (CsrIdWidth 'h"b06") accessMModeOnly;
         nilCsr ^"mhpmcounter7" (CsrIdWidth 'h"b07") accessMModeOnly;
         nilCsr ^"mhpmcounter8" (CsrIdWidth 'h"b08") accessMModeOnly;
         nilCsr ^"mhpmcounter9" (CsrIdWidth 'h"b09") accessMModeOnly;
         nilCsr ^"mhpmcounter10" (CsrIdWidth 'h"b0a") accessMModeOnly;
         nilCsr ^"mhpmcounter11" (CsrIdWidth 'h"b0b") accessMModeOnly;
         nilCsr ^"mhpmcounter12" (CsrIdWidth 'h"b0c") accessMModeOnly;
         nilCsr ^"mhpmcounter13" (CsrIdWidth 'h"b0d") accessMModeOnly;
         nilCsr ^"mhpmcounter14" (CsrIdWidth 'h"b03") accessMModeOnly;
         nilCsr ^"mhpmcounter15" (CsrIdWidth 'h"b0f") accessMModeOnly;
         nilCsr ^"mhpmcounter16" (CsrIdWidth 'h"b10") accessMModeOnly;
         nilCsr ^"mhpmcounter17" (CsrIdWidth 'h"b11") accessMModeOnly;
         nilCsr ^"mhpmcounter18" (CsrIdWidth 'h"b12") accessMModeOnly;
         nilCsr ^"mhpmcounter19" (CsrIdWidth 'h"b13") accessMModeOnly;
         nilCsr ^"mhpmcounter20" (CsrIdWidth 'h"b14") accessMModeOnly;
         nilCsr ^"mhpmcounter21" (CsrIdWidth 'h"b15") accessMModeOnly;
         nilCsr ^"mhpmcounter22" (CsrIdWidth 'h"b16") accessMModeOnly;
         nilCsr ^"mhpmcounter23" (CsrIdWidth 'h"b17") accessMModeOnly;
         nilCsr ^"mhpmcounter24" (CsrIdWidth 'h"b18") accessMModeOnly;
         nilCsr ^"mhpmcounter25" (CsrIdWidth 'h"b19") accessMModeOnly;
         nilCsr ^"mhpmcounter26" (CsrIdWidth 'h"b1a") accessMModeOnly;
         nilCsr ^"mhpmcounter27" (CsrIdWidth 'h"b1b") accessMModeOnly;
         nilCsr ^"mhpmcounter28" (CsrIdWidth 'h"b1c") accessMModeOnly;
         nilCsr ^"mhpmcounter29" (CsrIdWidth 'h"b1d") accessMModeOnly;
         nilCsr ^"mhpmcounter30" (CsrIdWidth 'h"b1e") accessMModeOnly;
         nilCsr ^"mhpmcounter31" (CsrIdWidth 'h"b1f") accessMModeOnly;
         {|
           csrName  := ^"mcycleh";
           csrAddr  := CsrIdWidth 'h"b80";
           csrViews
             := let fields := [ @csrFieldAny ^"mcycle" (Bit 64) (Bit 64) ] in
                repeatCsrView 2
                  (@csrViewUpperReadXform fields)
                  (@csrViewUpperWriteXform fields);
           csrAccess := accessMModeOnly
         |};
         {|
           csrName  := ^"minstreth";
           csrAddr  := CsrIdWidth 'h"b82";
           csrViews
             := let fields := [ @csrFieldAny ^"minstret" (Bit 64) (Bit 64) ] in
                repeatCsrView 2
                  (@csrViewUpperReadXform fields)
                  (@csrViewUpperWriteXform fields);
           csrAccess := accessMModeOnly
         |};
         nilCsr ^"mhpmevent3" (CsrIdWidth 'h"323") accessMModeOnly;
         nilCsr ^"mhpmevent4" (CsrIdWidth 'h"324") accessMModeOnly;
         nilCsr ^"mhpmevent5" (CsrIdWidth 'h"325") accessMModeOnly;
         nilCsr ^"mhpmevent6" (CsrIdWidth 'h"326") accessMModeOnly;
         nilCsr ^"mhpmevent7" (CsrIdWidth 'h"327") accessMModeOnly;
         nilCsr ^"mhpmevent8" (CsrIdWidth 'h"328") accessMModeOnly;
         nilCsr ^"mhpmevent9" (CsrIdWidth 'h"329") accessMModeOnly;
         nilCsr ^"mhpmevent10" (CsrIdWidth 'h"32a") accessMModeOnly;
         nilCsr ^"mhpmevent11" (CsrIdWidth 'h"32b") accessMModeOnly;
         nilCsr ^"mhpmevent12" (CsrIdWidth 'h"32c") accessMModeOnly;
         nilCsr ^"mhpmevent13" (CsrIdWidth 'h"32d") accessMModeOnly;
         nilCsr ^"mhpmevent14" (CsrIdWidth 'h"323") accessMModeOnly;
         nilCsr ^"mhpmevent15" (CsrIdWidth 'h"32f") accessMModeOnly;
         nilCsr ^"mhpmevent16" (CsrIdWidth 'h"330") accessMModeOnly;
         nilCsr ^"mhpmevent17" (CsrIdWidth 'h"331") accessMModeOnly;
         nilCsr ^"mhpmevent18" (CsrIdWidth 'h"332") accessMModeOnly;
         nilCsr ^"mhpmevent19" (CsrIdWidth 'h"333") accessMModeOnly;
         nilCsr ^"mhpmevent20" (CsrIdWidth 'h"334") accessMModeOnly;
         nilCsr ^"mhpmevent21" (CsrIdWidth 'h"335") accessMModeOnly;
         nilCsr ^"mhpmevent22" (CsrIdWidth 'h"336") accessMModeOnly;
         nilCsr ^"mhpmevent23" (CsrIdWidth 'h"337") accessMModeOnly;
         nilCsr ^"mhpmevent24" (CsrIdWidth 'h"338") accessMModeOnly;
         nilCsr ^"mhpmevent25" (CsrIdWidth 'h"339") accessMModeOnly;
         nilCsr ^"mhpmevent26" (CsrIdWidth 'h"33a") accessMModeOnly;
         nilCsr ^"mhpmevent27" (CsrIdWidth 'h"33b") accessMModeOnly;
         nilCsr ^"mhpmevent28" (CsrIdWidth 'h"33c") accessMModeOnly;
         nilCsr ^"mhpmevent29" (CsrIdWidth 'h"33d") accessMModeOnly;
         nilCsr ^"mhpmevent30" (CsrIdWidth 'h"33e") accessMModeOnly;
         nilCsr ^"mhpmevent31" (CsrIdWidth 'h"33f") accessMModeOnly
       ].

  Close Scope kami_expr.

End csrs.
