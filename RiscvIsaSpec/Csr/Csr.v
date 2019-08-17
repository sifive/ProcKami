(* Defines the standard CSRs. *)
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
  Variable Xlen_over_8: nat.
  Variable supported_exts : list (string * bool).
  Variable ty: Kind -> Type.

  Local Notation "^ x" := (name ++ "_" ++ x)%string (at level 0).
  Local Notation CSR := (@CSR Xlen_over_8 supported_exts ty).
  Local Notation csrFieldNoReg := (@csrFieldNoReg Xlen_over_8 supported_exts ty).
  Local Notation csrFieldAny := (@csrFieldAny Xlen_over_8 supported_exts ty).
  Local Notation csrFieldReadOnly := (@csrFieldReadOnly Xlen_over_8 supported_exts ty).
  Local Notation csrViewDefaultReadXform := (@csrViewDefaultReadXform Xlen_over_8 supported_exts ty).
  Local Notation csrViewDefaultWriteXform := (@csrViewDefaultWriteXform Xlen_over_8 supported_exts ty).
  Local Notation csrViewUpperReadXform := (@csrViewUpperReadXform Xlen_over_8 supported_exts ty).
  Local Notation csrViewUpperWriteXform := (@csrViewUpperWriteXform Xlen_over_8 supported_exts ty).
  Local Notation repeatCSRView := (@repeatCSRView Xlen_over_8 supported_exts ty).
  Local Notation epcReadXform := (@epcReadXform Xlen_over_8 supported_exts ty).
  Local Notation extField := (@extField name Xlen_over_8 supported_exts ty).
  Local Notation compressedExtField := (@compressedExtField name Xlen_over_8 supported_exts ty).
  Local Notation xlField := (@xlField Xlen_over_8 supported_exts ty).
  Local Notation tvecField := (@tvecField Xlen_over_8 supported_exts ty).
  Local Notation accessAny := (@accessAny Xlen_over_8 ty).
  Local Notation accessMModeOnly := (@accessMModeOnly Xlen_over_8 ty).
  Local Notation accessSMode := (@accessSMode Xlen_over_8 ty).
  Local Notation accessCounter := (@accessCounter Xlen_over_8 ty).
  Local Notation nilCSR := (@nilCSR Xlen_over_8 supported_exts ty).
  Local Notation simpleCSR := (@simpleCSR Xlen_over_8 supported_exts ty).
  Local Notation readonlyCSR := (@readonlyCSR Xlen_over_8 supported_exts ty).
  Local Notation pmp_reg_width := (@pmp_reg_width Xlen_over_8).
  Local Notation satpCsrName := (@satpCsrName name).
  Local Notation CsrAccessPkt := (@CsrAccessPkt Xlen_over_8).

  Open Scope kami_expr.

  Definition CSRs
    :  list CSR
    := [
         {|
           csrName := ^"ustatus";
           csrAddr := natToWord CsrIdWidth 0;
           csrViews
             := let fields
                  := [
                       @csrFieldNoReg "reserved0" (Bit 27) (getDefaultConst _);
                       @csrFieldAny ^"upie" Bool;
                       @csrFieldNoReg "reserved1" (Bit 3) (getDefaultConst _);
                       @csrFieldAny ^"uie" Bool
                     ] in
                repeatCSRView 2
                  (@csrViewDefaultReadXform fields)
                  (@csrViewDefaultWriteXform fields);
           csrAccess := accessAny
         |};
         nilCSR ^"uie" (CsrIdWidth 'h"4") accessAny;
         {|
           csrName := ^"utvec";
           csrAddr := natToWord CsrIdWidth 5;
           csrViews
             := let fields := [ @csrFieldAny ^"utvec_mode" (Bit 2) ] in
                repeatCSRView 2
                  (@csrViewDefaultReadXform fields)
                  (@csrViewDefaultWriteXform fields);
           csrAccess := accessAny
         |};
         {|
           csrName := ^"uscratch";
           csrAddr := CsrIdWidth 'h"40";
           csrViews
             := [
                  let fields := [ @csrFieldAny ^"uscratch" (Bit 32) ] in
                  {|
                    csrViewContext    := $1;
                    csrViewFields     := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform fields)
                  |};
                  let fields := [ @csrFieldAny ^"uscratch" (Bit 64) ] in
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
                  let fields := [ @csrFieldAny ^"uepc" (Bit 32) ] in
                  {|
                    csrViewContext    := $1;
                    csrViewFields     := fields;
                    csrViewReadXform  := (@epcReadXform fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform fields)
                  |};
                  let fields := [ @csrFieldAny ^"uepc" (Bit 64) ] in
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
                         @csrFieldAny ^"ucause_interrupt" Bool;
                         @csrFieldAny ^"ucause_code" (Bit 31)
                       ] in
                  {|
                    csrViewContext    := $1;
                    csrViewFields     := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform fields)
                  |};
                  let fields
                    := [
                         @csrFieldAny ^"ucause_interrupt" Bool;
                         @csrFieldAny ^"ucause_code" (Bit 63)
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
                  let fields := [ @csrFieldAny ^"utval" (Bit 32) ] in
                  {|
                    csrViewContext    := $1;
                    csrViewFields     := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform fields)
                  |};
                  let fields := [ @csrFieldAny ^"utval" (Bit 64) ] in
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
                       @csrFieldAny ^"ueip" Bool;
                       @csrFieldNoReg ^"reserved0" (Bit 3) (getDefaultConst _);
                       @csrFieldAny ^"utip" Bool;
                       @csrFieldNoReg ^"reserved1" (Bit 3) (getDefaultConst _);
                       @csrFieldAny ^"usip" Bool
                     ] in
                repeatCSRView 2
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
                       @csrFieldAny ^"fflags" (Bit 5)
                     ] in
                repeatCSRView 2
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
                       @csrFieldAny ^"frm" (Bit 3)
                     ] in
                repeatCSRView 2
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
                       @csrFieldAny ^"frm" (Bit 3);
                       @csrFieldAny ^"fflags" (Bit 5)
                     ] in
                repeatCSRView 2
                  (@csrViewDefaultReadXform fields)
                  (@csrViewDefaultWriteXform fields);
           csrAccess := accessAny
         |};
         simpleCSR ^"mcycle" (CsrIdWidth 'h"c00") 64 (accessCounter "CY");
         readonlyCSR ^"mtime" (CsrIdWidth 'h"c01") 64 accessAny;
         simpleCSR ^"minstret" (CsrIdWidth 'h"c02") 64 (accessCounter "IR");
         {|
           csrName := ^"cycleh";
           csrAddr := CsrIdWidth 'h"c80";
           csrViews
             := let fields := [ @csrFieldReadOnly ^"mcycle" (Bit 64) ] in
                repeatCSRView 2
                  (@csrViewUpperReadXform fields)
                  (@csrViewUpperWriteXform fields);
           csrAccess := accessAny
         |};
         {|
           csrName := ^"instreth";
           csrAddr := CsrIdWidth 'h"c82";
           csrViews
             := let fields := [ @csrFieldReadOnly ^"minstret" (Bit 64) ] in
                repeatCSRView 2
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
                         @csrFieldAny ^"medeleg" (Bit 16)
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
                         @csrFieldAny ^"medeleg" (Bit 16)
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
                         @csrFieldAny ^"mideleg" (Bit 12)
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
                         @csrFieldAny ^"mideleg" (Bit 12)
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
                       @csrFieldReadOnly ^"meie" Bool;
                       @csrFieldNoReg ^"reserved0" Bool (getDefaultConst _);
                       @csrFieldAny ^"seie" Bool;
                       @csrFieldAny ^"ueie" Bool;
                       @csrFieldReadOnly ^"mtie" Bool;
                       @csrFieldNoReg ^"reserved1" Bool (getDefaultConst _);
                       @csrFieldAny ^"stie" Bool;
                       @csrFieldAny ^"utie" Bool;
                       @csrFieldReadOnly ^"msie" Bool;
                       @csrFieldNoReg ^"reserved2" Bool (getDefaultConst _);
                       @csrFieldAny ^"ssie" Bool;
                       @csrFieldAny ^"usie" Bool
                     ] in
                repeatCSRView 2
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
                         @csrFieldAny ^"tsr" Bool;
                         @csrFieldAny ^"tw" Bool;
                         @csrFieldAny ^"tvm" Bool;
                         @csrFieldAny ^"mxr" Bool;
                         @csrFieldAny ^"sum" Bool;
                         @csrFieldAny ^"mprv" Bool;
                         @csrFieldNoReg "reserved1" (Bit 4) (getDefaultConst _);
                         @csrFieldAny ^"mpp" (Bit 2);
                         @csrFieldNoReg ^"hpp" (Bit 2) (getDefaultConst _);
                         @csrFieldAny ^"spp" (Bit 1);
                         @csrFieldAny ^"mpie" Bool;
                         @csrFieldNoReg ^"hpie" Bool (getDefaultConst _);
                         @csrFieldAny ^"spie" Bool;
                         @csrFieldAny ^"upie" Bool;
                         @csrFieldAny ^"mie" Bool;
                         @csrFieldNoReg ^"hie" Bool (getDefaultConst _);
                         @csrFieldAny ^"sie" Bool;
                         @csrFieldAny ^"uie" Bool
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
                         @csrFieldAny ^"tsr" Bool;
                         @csrFieldAny ^"tw" Bool;
                         @csrFieldAny ^"tvm" Bool;
                         @csrFieldAny ^"mxr" Bool;
                         @csrFieldAny ^"sum" Bool;
                         @csrFieldAny ^"mprv" Bool;
                         @csrFieldNoReg "reserved2" (Bit 4) (getDefaultConst _);
                         @csrFieldAny ^"mpp" (Bit 2);
                         @csrFieldNoReg ^"hpp" (Bit 2) (getDefaultConst _);
                         @csrFieldAny ^"spp" (Bit 1);
                         @csrFieldAny ^"mpie" Bool;
                         @csrFieldNoReg ^"hpie" Bool (getDefaultConst _);
                         @csrFieldAny ^"spie" Bool;
                         @csrFieldAny ^"upie" Bool;
                         @csrFieldAny ^"mie" Bool;
                         @csrFieldNoReg ^"hie" Bool (getDefaultConst _);
                         @csrFieldAny ^"sie" Bool;
                         @csrFieldAny ^"uie" Bool
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
                         @csrFieldAny ^"mtvec_mode" (Bit 2)
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
                         @csrFieldAny ^"mtvec_mode" (Bit 2)
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
         simpleCSR ^"mcounteren" (CsrIdWidth 'h"306") 32 accessMModeOnly;
         {|
           csrName := ^"mscratch";
           csrAddr := CsrIdWidth 'h"340";
           csrViews
             := [
                  let fields := [ @csrFieldAny ^"mscratch" (Bit 32) ] in
                  {|
                    csrViewContext    := $1;
                    csrViewFields     := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform fields)
                  |};
                  let fields := [ @csrFieldAny ^"mscratch" (Bit 64) ] in
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
                  let fields := [ @csrFieldAny ^"mepc" (Bit 32) ] in
                  {|
                    csrViewContext := $1;
                    csrViewFields  := fields;
                    csrViewReadXform  := (@epcReadXform fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform fields)
                  |};
                  let fields := [ @csrFieldAny ^"mepc" (Bit 64) ] in
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
                         @csrFieldAny ^"mcause_interrupt" Bool;
                         @csrFieldAny ^"mcause_code" (Bit 31)
                       ] in
                  {|
                    csrViewContext := $1;
                    csrViewFields  := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform fields)
                  |};
                  let fields
                    := [
                         @csrFieldAny ^"mcause_interrupt" Bool;
                         @csrFieldAny ^"mcause_code" (Bit 63)
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
                  let fields := [ @csrFieldAny ^"mtval" (Bit 32) ] in
                  {|
                    csrViewContext := $1;
                    csrViewFields  := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform fields)
                  |};
                  let fields := [ @csrFieldAny ^"mtval" (Bit 64) ] in
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
                       @csrFieldReadOnly ^"meip" Bool;
                       @csrFieldNoReg ^"reserved0" Bool (getDefaultConst _);
                       @csrFieldAny ^"seip" Bool;
                       @csrFieldAny ^"ueip" Bool;
                       @csrFieldReadOnly ^"mtip" Bool;
                       @csrFieldNoReg ^"reserved1" Bool (getDefaultConst _);
                       @csrFieldAny ^"stip" Bool;
                       @csrFieldAny ^"utip" Bool;
                       @csrFieldReadOnly ^"msip" Bool;
                       @csrFieldNoReg ^"reserved2" Bool (getDefaultConst _);
                       @csrFieldAny ^"ssip" Bool;
                       @csrFieldAny ^"usip" Bool
                     ] in
                repeatCSRView 2
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
                         @csrFieldAny ^"pmp3cfg" (Bit 8);
                         @csrFieldAny ^"pmp2cfg" (Bit 8);
                         @csrFieldAny ^"pmp1cfg" (Bit 8);
                         @csrFieldAny ^"pmp0cfg" (Bit 8)
                       ] in
                  {|
                    csrViewContext    := $1;
                    csrViewFields     := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform fields)
                  |};
                  let fields
                    := [
                         @csrFieldAny ^"pmp7cfg" (Bit 8);
                         @csrFieldAny ^"pmp6cfg" (Bit 8);
                         @csrFieldAny ^"pmp5cfg" (Bit 8);
                         @csrFieldAny ^"pmp4cfg" (Bit 8);
                         @csrFieldAny ^"pmp3cfg" (Bit 8);
                         @csrFieldAny ^"pmp2cfg" (Bit 8);
                         @csrFieldAny ^"pmp1cfg" (Bit 8);
                         @csrFieldAny ^"pmp0cfg" (Bit 8)
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
                         @csrFieldAny ^"pmp3cfg" (Bit 8);
                         @csrFieldAny ^"pmp2cfg" (Bit 8);
                         @csrFieldAny ^"pmp1cfg" (Bit 8);
                         @csrFieldAny ^"pmp0cfg" (Bit 8)
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
                         @csrFieldAny ^"pmp11cfg" (Bit 8);
                         @csrFieldAny ^"pmp10cfg" (Bit 8);
                         @csrFieldAny ^"pmp9cfg" (Bit 8);
                         @csrFieldAny ^"pmp8cfg" (Bit 8)
                       ] in
                  {|
                    csrViewContext    := $1;
                    csrViewFields     := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform fields)
                  |};
                  let fields
                    := [
                         @csrFieldAny ^"pmp15cfg" (Bit 8);
                         @csrFieldAny ^"pmp14cfg" (Bit 8);
                         @csrFieldAny ^"pmp13cfg" (Bit 8);
                         @csrFieldAny ^"pmp12cfg" (Bit 8);
                         @csrFieldAny ^"pmp11cfg" (Bit 8);
                         @csrFieldAny ^"pmp10cfg" (Bit 8);
                         @csrFieldAny ^"pmp9cfg" (Bit 8);
                         @csrFieldAny ^"pmp8cfg" (Bit 8)
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
                         @csrFieldAny ^"pmp15cfg" (Bit 8);
                         @csrFieldAny ^"pmp14cfg" (Bit 8);
                         @csrFieldAny ^"pmp13cfg" (Bit 8);
                         @csrFieldAny ^"pmp12cfg" (Bit 8)
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
         simpleCSR ^"pmpaddr0" (CsrIdWidth 'h"3b0") pmp_reg_width accessMModeOnly;
         simpleCSR ^"pmpaddr1" (CsrIdWidth 'h"3b1") pmp_reg_width accessMModeOnly;
         simpleCSR ^"pmpaddr2" (CsrIdWidth 'h"3b2") pmp_reg_width accessMModeOnly;
         simpleCSR ^"pmpaddr3" (CsrIdWidth 'h"3b3") pmp_reg_width accessMModeOnly;
         simpleCSR ^"pmpaddr4" (CsrIdWidth 'h"3b4") pmp_reg_width accessMModeOnly;
         simpleCSR ^"pmpaddr5" (CsrIdWidth 'h"3b5") pmp_reg_width accessMModeOnly;
         simpleCSR ^"pmpaddr6" (CsrIdWidth 'h"3b6") pmp_reg_width accessMModeOnly;
         simpleCSR ^"pmpaddr7" (CsrIdWidth 'h"3b7") pmp_reg_width accessMModeOnly;
         simpleCSR ^"pmpaddr8" (CsrIdWidth 'h"3b8") pmp_reg_width accessMModeOnly;
         simpleCSR ^"pmpaddr9" (CsrIdWidth 'h"3b9") pmp_reg_width accessMModeOnly;
         simpleCSR ^"pmpaddr10" (CsrIdWidth 'h"3ba") pmp_reg_width accessMModeOnly;
         simpleCSR ^"pmpaddr11" (CsrIdWidth 'h"3bb") pmp_reg_width accessMModeOnly;
         simpleCSR ^"pmpaddr12" (CsrIdWidth 'h"3bc") pmp_reg_width accessMModeOnly;
         simpleCSR ^"pmpaddr13" (CsrIdWidth 'h"3bd") pmp_reg_width accessMModeOnly;
         simpleCSR ^"pmpaddr14" (CsrIdWidth 'h"3be") pmp_reg_width accessMModeOnly;
         simpleCSR ^"pmpaddr15" (CsrIdWidth 'h"3bf") pmp_reg_width accessMModeOnly;
         {|
           csrName := ^"sstatus";
           csrAddr := CsrIdWidth 'h"100";
           csrViews
             := [
                  let fields
                    := [
                         @csrFieldNoReg "reserved0" (Bit 12) (getDefaultConst _);
                         @csrFieldAny ^"mxr" Bool;
                         @csrFieldAny ^"sum" Bool;
                         @csrFieldNoReg "reserved1" (Bit 9) (getDefaultConst _);
                         @csrFieldAny ^"spp" (Bit 1);
                         @csrFieldNoReg "reserved2" (Bit 2) (getDefaultConst _);
                         @csrFieldAny ^"spie" Bool;
                         @csrFieldAny ^"upie" Bool;
                         @csrFieldNoReg "reserved3" (Bit 2) (getDefaultConst _);
                         @csrFieldAny ^"sie" Bool;
                         @csrFieldAny ^"uie" Bool
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
                         @csrFieldAny ^"mxr" Bool;
                         @csrFieldAny ^"sum" Bool;
                         @csrFieldNoReg "reserved2" (Bit 9) (getDefaultConst _);
                         @csrFieldAny ^"spp" (Bit 1);
                         @csrFieldNoReg "reserved3" (Bit 2) (getDefaultConst _);
                         @csrFieldAny ^"spie" Bool;
                         @csrFieldAny ^"upie" Bool;
                         @csrFieldNoReg "reserved4" (Bit 2) (getDefaultConst _);
                         @csrFieldAny ^"sie" Bool;
                         @csrFieldAny ^"uie" Bool
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
                         @csrFieldAny ^"medeleg" (Bit 16)
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
                         @csrFieldAny ^"medeleg" (Bit 16)
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
                         @csrFieldAny ^"stvec_mode" (Bit 2)
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
                         @csrFieldAny ^"stvec_mode" (Bit 2)
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
         simpleCSR ^"scounteren" (CsrIdWidth 'h"106") 32 accessSMode;
         {|
           csrName := ^"sscratch";
           csrAddr := CsrIdWidth 'h"140";
           csrViews
             := [
                  let fields := [ @csrFieldAny ^"sscratch" (Bit 32) ] in
                  {|
                    csrViewContext := $1;
                    csrViewFields  := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform fields)
                  |};
                  let fields := [ @csrFieldAny ^"sscratch" (Bit 64) ] in
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
                  let fields := [ @csrFieldAny ^"sepc" (Bit 32) ] in
                  {|
                    csrViewContext := $1;
                    csrViewFields  := fields;
                    csrViewReadXform  := (@epcReadXform fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform fields)
                  |};
                  let fields := [ @csrFieldAny ^"sepc" (Bit 64) ] in
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
                         @csrFieldAny ^"scause_interrupt" Bool;
                         @csrFieldAny ^"scause_code" (Bit 31)
                       ] in
                  {|
                    csrViewContext := $1;
                    csrViewFields  := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform fields)
                  |};
                  let fields
                    := [
                         @csrFieldAny ^"scause_interrupt" Bool;
                         @csrFieldAny ^"scause_code" (Bit 63)
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
                  let fields := [ @csrFieldAny ^"stval" (Bit 32) ] in
                  {|
                    csrViewContext := $1;
                    csrViewFields  := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform fields)
                  |};
                  let fields := [ @csrFieldAny ^"stval" (Bit 64) ] in
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
                         @csrFieldAny ^"satp_mode" (Bit 1);
                         @csrFieldAny ^"satp_asid" (Bit 9);
                         @csrFieldAny ^"satp_ppn" (Bit 22)
                       ] in
                  {|
                    csrViewContext := $1;
                    csrViewFields  := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform fields)
                  |};
                  let fields
                    := [
                         @csrFieldAny ^"satp_mode" (Bit 4);
                         @csrFieldAny ^"satp_asid" (Bit 16);
                         @csrFieldAny ^"satp_ppn" (Bit 44)
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
                  := [ @csrFieldAny ^"mvendorid" (Bit 32) ] in
                repeatCSRView 2
                  (@csrViewDefaultReadXform fields)
                  (@csrViewDefaultWriteXform fields);
           csrAccess := accessMModeOnly
         |};
         {|
           csrName := ^"marchid";
           csrAddr := CsrIdWidth 'h"f12";
           csrViews
             := [
                  let fields := [ @csrFieldAny ^"marchid" (Bit 32) ] in
                  {|
                    csrViewContext := $1;
                    csrViewFields  := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform fields)
                  |};
                  let fields := [ @csrFieldAny ^"marchid" (Bit 64) ] in
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
                  let fields := [ @csrFieldAny ^"marchid" (Bit 32) ] in
                  {|
                    csrViewContext := $1;
                    csrViewFields  := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform fields)
                  |};
                  let fields := [ @csrFieldAny ^"marchid" (Bit 64) ] in
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
                  let fields := [ @csrFieldAny ^"mhartid" (Bit 32) ] in
                  {|
                    csrViewContext := $1;
                    csrViewFields  := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform fields)
                  |};
                  let fields := [ @csrFieldAny ^"mhartid" (Bit 64) ] in
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
             := let fields := [ @csrFieldAny ^"mcycle" (Bit 64) ] in
                repeatCSRView 2
                  (@csrViewDefaultReadXform fields)
                  (@csrViewDefaultWriteXform fields);
           csrAccess := accessMModeOnly
         |};
         {|
           csrName  := ^"minstret";
           csrAddr  := CsrIdWidth 'h"b02";
           csrViews
             := let fields := [ @csrFieldAny ^"minstret" (Bit 64) ] in
                repeatCSRView 2
                  (@csrViewDefaultReadXform fields)
                  (@csrViewDefaultWriteXform fields);
           csrAccess := accessMModeOnly
         |};
         nilCSR ^"mhpmcounter3" (CsrIdWidth 'h"b03") accessMModeOnly;
         nilCSR ^"mhpmcounter4" (CsrIdWidth 'h"b04") accessMModeOnly;
         nilCSR ^"mhpmcounter5" (CsrIdWidth 'h"b05") accessMModeOnly;
         nilCSR ^"mhpmcounter6" (CsrIdWidth 'h"b06") accessMModeOnly;
         nilCSR ^"mhpmcounter7" (CsrIdWidth 'h"b07") accessMModeOnly;
         nilCSR ^"mhpmcounter8" (CsrIdWidth 'h"b08") accessMModeOnly;
         nilCSR ^"mhpmcounter9" (CsrIdWidth 'h"b09") accessMModeOnly;
         nilCSR ^"mhpmcounter10" (CsrIdWidth 'h"b0a") accessMModeOnly;
         nilCSR ^"mhpmcounter11" (CsrIdWidth 'h"b0b") accessMModeOnly;
         nilCSR ^"mhpmcounter12" (CsrIdWidth 'h"b0c") accessMModeOnly;
         nilCSR ^"mhpmcounter13" (CsrIdWidth 'h"b0d") accessMModeOnly;
         nilCSR ^"mhpmcounter14" (CsrIdWidth 'h"b03") accessMModeOnly;
         nilCSR ^"mhpmcounter15" (CsrIdWidth 'h"b0f") accessMModeOnly;
         nilCSR ^"mhpmcounter16" (CsrIdWidth 'h"b10") accessMModeOnly;
         nilCSR ^"mhpmcounter17" (CsrIdWidth 'h"b11") accessMModeOnly;
         nilCSR ^"mhpmcounter18" (CsrIdWidth 'h"b12") accessMModeOnly;
         nilCSR ^"mhpmcounter19" (CsrIdWidth 'h"b13") accessMModeOnly;
         nilCSR ^"mhpmcounter20" (CsrIdWidth 'h"b14") accessMModeOnly;
         nilCSR ^"mhpmcounter21" (CsrIdWidth 'h"b15") accessMModeOnly;
         nilCSR ^"mhpmcounter22" (CsrIdWidth 'h"b16") accessMModeOnly;
         nilCSR ^"mhpmcounter23" (CsrIdWidth 'h"b17") accessMModeOnly;
         nilCSR ^"mhpmcounter24" (CsrIdWidth 'h"b18") accessMModeOnly;
         nilCSR ^"mhpmcounter25" (CsrIdWidth 'h"b19") accessMModeOnly;
         nilCSR ^"mhpmcounter26" (CsrIdWidth 'h"b1a") accessMModeOnly;
         nilCSR ^"mhpmcounter27" (CsrIdWidth 'h"b1b") accessMModeOnly;
         nilCSR ^"mhpmcounter28" (CsrIdWidth 'h"b1c") accessMModeOnly;
         nilCSR ^"mhpmcounter29" (CsrIdWidth 'h"b1d") accessMModeOnly;
         nilCSR ^"mhpmcounter30" (CsrIdWidth 'h"b1e") accessMModeOnly;
         nilCSR ^"mhpmcounter31" (CsrIdWidth 'h"b1f") accessMModeOnly;
         {|
           csrName  := ^"mcycleh";
           csrAddr  := CsrIdWidth 'h"b80";
           csrViews
             := let fields := [ @csrFieldAny ^"mcycle" (Bit 64) ] in
                repeatCSRView 2
                  (@csrViewUpperReadXform fields)
                  (@csrViewUpperWriteXform fields);
           csrAccess := accessMModeOnly
         |};
         {|
           csrName  := ^"minstreth";
           csrAddr  := CsrIdWidth 'h"b82";
           csrViews
             := let fields := [ @csrFieldAny ^"minstret" (Bit 64) ] in
                repeatCSRView 2
                  (@csrViewUpperReadXform fields)
                  (@csrViewUpperWriteXform fields);
           csrAccess := accessMModeOnly
         |};
         nilCSR ^"mhpmevent3" (CsrIdWidth 'h"323") accessMModeOnly;
         nilCSR ^"mhpmevent4" (CsrIdWidth 'h"324") accessMModeOnly;
         nilCSR ^"mhpmevent5" (CsrIdWidth 'h"325") accessMModeOnly;
         nilCSR ^"mhpmevent6" (CsrIdWidth 'h"326") accessMModeOnly;
         nilCSR ^"mhpmevent7" (CsrIdWidth 'h"327") accessMModeOnly;
         nilCSR ^"mhpmevent8" (CsrIdWidth 'h"328") accessMModeOnly;
         nilCSR ^"mhpmevent9" (CsrIdWidth 'h"329") accessMModeOnly;
         nilCSR ^"mhpmevent10" (CsrIdWidth 'h"32a") accessMModeOnly;
         nilCSR ^"mhpmevent11" (CsrIdWidth 'h"32b") accessMModeOnly;
         nilCSR ^"mhpmevent12" (CsrIdWidth 'h"32c") accessMModeOnly;
         nilCSR ^"mhpmevent13" (CsrIdWidth 'h"32d") accessMModeOnly;
         nilCSR ^"mhpmevent14" (CsrIdWidth 'h"323") accessMModeOnly;
         nilCSR ^"mhpmevent15" (CsrIdWidth 'h"32f") accessMModeOnly;
         nilCSR ^"mhpmevent16" (CsrIdWidth 'h"330") accessMModeOnly;
         nilCSR ^"mhpmevent17" (CsrIdWidth 'h"331") accessMModeOnly;
         nilCSR ^"mhpmevent18" (CsrIdWidth 'h"332") accessMModeOnly;
         nilCSR ^"mhpmevent19" (CsrIdWidth 'h"333") accessMModeOnly;
         nilCSR ^"mhpmevent20" (CsrIdWidth 'h"334") accessMModeOnly;
         nilCSR ^"mhpmevent21" (CsrIdWidth 'h"335") accessMModeOnly;
         nilCSR ^"mhpmevent22" (CsrIdWidth 'h"336") accessMModeOnly;
         nilCSR ^"mhpmevent23" (CsrIdWidth 'h"337") accessMModeOnly;
         nilCSR ^"mhpmevent24" (CsrIdWidth 'h"338") accessMModeOnly;
         nilCSR ^"mhpmevent25" (CsrIdWidth 'h"339") accessMModeOnly;
         nilCSR ^"mhpmevent26" (CsrIdWidth 'h"33a") accessMModeOnly;
         nilCSR ^"mhpmevent27" (CsrIdWidth 'h"33b") accessMModeOnly;
         nilCSR ^"mhpmevent28" (CsrIdWidth 'h"33c") accessMModeOnly;
         nilCSR ^"mhpmevent29" (CsrIdWidth 'h"33d") accessMModeOnly;
         nilCSR ^"mhpmevent30" (CsrIdWidth 'h"33e") accessMModeOnly;
         nilCSR ^"mhpmevent31" (CsrIdWidth 'h"33f") accessMModeOnly
       ].

  Close Scope kami_expr.

End csrs.
