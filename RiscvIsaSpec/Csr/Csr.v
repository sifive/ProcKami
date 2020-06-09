Require Import Kami.AllNotations.
Require Import ProcKami.FU.
Require Import ProcKami.RiscvIsaSpec.Csr.CsrFuncs.
Import ListNotations.

Section csrs.
  Context {procParams: ProcParams}.
  Variable ty: Kind -> Type.

  Local Open Scope kami_expr.

  Definition Csrs
    :  list Csr
    := [
         {|
           csrName := "ustatus";
           csrAddr := natToWord CsrIdWidth 0;
           csrViews
             := let fields
                  := [
                       @csrFieldNoReg _ "reserved0" (Bit 27) (getDefaultConst _);
                       @csrFieldAny _ "upie" Bool Bool (Some (ConstBool false));
                       @csrFieldNoReg _ "reserved1" (Bit 3) (getDefaultConst _);
                       @csrFieldAny _ "uie" Bool Bool (Some (ConstBool false))
                     ] in
                repeatCsrView 2
                  (@csrViewDefaultReadXform _ fields)
                  (@csrViewDefaultWriteXform _ fields);
           csrAccess := accessAny
         |};
         nilCsr "uie" (CsrIdWidth 'h"4") accessAny;
         {|
           csrName := "utvec";
           csrAddr := natToWord CsrIdWidth 5;
           csrViews
             := [
                  let fields
                    := [
                         @tvecField _ "u" 30 (Xlen-2);
                         @csrFieldAny _ "utvec_mode" (Bit 2) (Bit 2) None
                       ] in
                  {|
                    csrViewContext := fun ty => $1;
                    csrViewFields  := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform _ fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform _ fields)
                  |};
                  let fields
                    := [
                         @tvecField _ "u" 62 (Xlen-2);
                         @csrFieldAny _ "utvec_mode" (Bit 2) (Bit 2) None
                       ] in
                  {|
                    csrViewContext := fun ty => $2;
                    csrViewFields  := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform _ fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform _ fields)
                  |}
                ];
           csrAccess := accessAny
         |};
         {|
           csrName := "uscratch";
           csrAddr := CsrIdWidth 'h"40";
           csrViews
             := [
                  let fields := [ @csrFieldAny _ "uscratch" (Bit 32) (Bit Xlen) None ] in
                  {|
                    csrViewContext    := fun ty => $1;
                    csrViewFields     := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform _ fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform _ fields)
                  |};
                  let fields := [ @csrFieldAny _ "uscratch" (Bit 64) (Bit Xlen) None ] in
                  {|
                    csrViewContext    := fun ty => $2;
                    csrViewFields     := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform _ fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform _ fields)
                  |}
                ];
           csrAccess := accessAny
         |};
         {|
           csrName := "uepc";
           csrAddr := CsrIdWidth 'h"41";
           csrViews
             := [
                  let fields := [ @csrFieldAny _ "uepc" (Bit 32) (Bit Xlen) None ] in
                  {|
                    csrViewContext    := fun ty => $1;
                    csrViewFields     := fields;
                    csrViewReadXform  := (@epcReadXform _ fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform _ fields)
                  |};
                  let fields := [ @csrFieldAny _ "uepc" (Bit 64) (Bit Xlen) None ] in
                  {|
                    csrViewContext    := fun ty => $2;
                    csrViewFields     := fields;
                    csrViewReadXform  := (@epcReadXform _ fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform _ fields)
                  |}
                ];
           csrAccess := accessAny
         |};
         {|
           csrName := "ucause";
           csrAddr := CsrIdWidth 'h"42";
           csrViews
             := [
                  let fields
                    := [
                         @csrFieldAny _ "ucause_interrupt" Bool Bool (Some (ConstBool false));
                         @csrFieldAny _ "ucause_code" (Bit 31) (Bit (Xlen - 1)) None
                       ] in
                  {|
                    csrViewContext    := fun ty => $1;
                    csrViewFields     := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform _ fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform _ fields)
                  |};
                  let fields
                    := [
                         @csrFieldAny _ "ucause_interrupt" Bool Bool (Some (ConstBool false));
                         @csrFieldAny _ "ucause_code" (Bit 63) (Bit (Xlen - 1)) None
                       ] in
                  {|
                    csrViewContext    := fun ty => $2;
                    csrViewFields     := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform _ fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform _ fields)
                  |}
                ];
           csrAccess := accessAny
         |};
         {|
           csrName := "utval";
           csrAddr := CsrIdWidth 'h"43";
           csrViews
             := [
                  let fields := [ @csrFieldAny _ "utval" (Bit 32) (Bit Xlen) None ] in
                  {|
                    csrViewContext    := fun ty => $1;
                    csrViewFields     := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform _ fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform _ fields)
                  |};
                  let fields := [ @csrFieldAny _ "utval" (Bit 64) (Bit Xlen) None ] in
                  {|
                    csrViewContext    := fun ty => $2;
                    csrViewFields     := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform _ fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform _ fields)
                  |}
                ];
           csrAccess := accessAny
         |};
         {|
           csrName := "uip";
           csrAddr := CsrIdWidth 'h"44";
           csrViews
             := let fields
                  := [
                       @csrFieldAny _ "ueip" Bool Bool (Some (ConstBool false));
                       @csrFieldNoReg _ "reserved0" (Bit 3) (getDefaultConst _);
                       @csrFieldAny _ "utip" Bool Bool (Some (ConstBool false));
                       @csrFieldNoReg _ "reserved1" (Bit 3) (getDefaultConst _);
                       @csrFieldAny _ "usip" Bool Bool (Some (ConstBool false))
                     ] in
                repeatCsrView 2
                  (@csrViewDefaultReadXform _ fields)
                  (@csrViewDefaultWriteXform _ fields);
           csrAccess := accessMModeOnly
         |};
         {|
           csrName := "fflagsG";
           csrAddr := natToWord CsrIdWidth 1;
           csrViews
             := let fields
                  := [
                       @csrFieldNoReg _ "reserved" (Bit 27) (getDefaultConst _);
                       @csrFieldAny _ "fflags" (Bit 5) FflagsValue (Some (ConstBit (wzero 5)))
                     ] in
                repeatCsrView 2
                  (@csrViewDefaultReadXform _ fields)
                  (@csrViewDefaultWriteXform _ fields);
           csrAccess := accessAny
         |};
         {|
           csrName := "frmG";
           csrAddr := natToWord CsrIdWidth 2;
           csrViews
             := let fields
                  := [
                       @csrFieldNoReg _ "reserved" (Bit 29) (getDefaultConst _);
                       @csrFieldAny _ "frm" (Bit 3) FrmValue (Some (ConstBit (wzero 3)))
                     ] in
                repeatCsrView 2
                  (@csrViewDefaultReadXform _ fields)
                  (@csrViewDefaultWriteXform _ fields);
           csrAccess := accessAny
         |};
         {|
           csrName := "fcsrG";
           csrAddr := natToWord CsrIdWidth 3;
           csrViews
             := let fields
                  := [
                       @csrFieldNoReg _ "reserved" (Bit 24) (getDefaultConst _);
                       @csrFieldAny _ "frm" (Bit 3) FrmValue (Some (ConstBit (wzero 3)));
                       @csrFieldAny _ "fflags" (Bit 5) FflagsValue (Some (ConstBit (wzero 5)))
                     ] in
                repeatCsrView 2
                  (@csrViewDefaultReadXform _ fields)
                  (@csrViewDefaultWriteXform _ fields);
           csrAccess := accessAny
         |};
         simpleCsr "mcycle" (CsrIdWidth 'h"c00") (Some (ConstBit (wzero 64))) (fun ty => accessCounter "CY");
         readonlyCsr "mtime" (CsrIdWidth 'h"c01") accessAny (Some (ConstBit (wzero 64)));
         simpleCsr "minstret" (CsrIdWidth 'h"c02") (Some (ConstBit (wzero 64))) (fun ty => accessCounter "IR");
         {|
           csrName := "cycleh";
           csrAddr := CsrIdWidth 'h"c80";
           csrViews
             := let fields := [ @csrFieldReadOnly _ "mcycle" (Bit 64) (Bit 64) (Some (ConstBit (wzero 64))) ] in
                repeatCsrView 2
                  (@csrViewUpperReadXform _ fields)
                  (@csrViewUpperWriteXform _ fields);
           csrAccess := accessAny
         |};
         {|
           csrName := "instreth";
           csrAddr := CsrIdWidth 'h"c82";
           csrViews
             := let fields := [ @csrFieldReadOnly _ "minstret" (Bit 64) (Bit 64) (Some (ConstBit (wzero 64))) ] in
                repeatCsrView 2
                  (@csrViewUpperReadXform _ fields)
                  (@csrViewUpperWriteXform _ fields);
           csrAccess := accessAny
         |};
         {|
           csrName := "misa";
           csrAddr := CsrIdWidth 'h"301";
           csrViews
             := [
                  let fields
                    := [
                         xlField "m";
                         @csrFieldNoReg _ "misa_reserved32" (Bit 4) (getDefaultConst _);
                         misa
                       ] in
                  {|
                    csrViewContext := fun ty => $1;
                    csrViewFields  := fields;
                    csrViewReadXform  := @csrViewDefaultReadXform _ fields;
                    csrViewWriteXform := @csrViewDefaultWriteXform _ fields
                  |};
                  let fields
                    := [
                         xlField "m";
                         @csrFieldNoReg _ "misa_reserved64" (Bit 36) (getDefaultConst _);
                         misa
                       ] in
                  {|
                    csrViewContext := fun ty => $2;
                    csrViewFields  := fields;
                    csrViewReadXform  := @csrViewDefaultReadXform _ fields;
                    csrViewWriteXform := @csrViewDefaultWriteXform _ fields
                  |}
                ];
           csrAccess := accessMModeOnly
         |};
         {|
           csrName := "medeleg";
           csrAddr := CsrIdWidth 'h"302";
           csrViews
             := [
                  let fields
                    := [
                         @csrFieldNoReg _ "reserved" (Bit 16) (getDefaultConst _);
                         @csrFieldAny _ "medeleg" (Bit 16) (Bit 16) (Some (ConstBit (wzero 16)))
                       ] in
                  {|
                    csrViewContext := fun ty => $1;
                    csrViewFields  := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform _ fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform _ fields)
                  |};
                  let fields
                    := [
                         @csrFieldNoReg _ "reserved" (Bit 48) (getDefaultConst _);
                         @csrFieldAny _ "medeleg" (Bit 16) (Bit 16) (Some (ConstBit (wzero 16)))
                       ] in
                  {|
                    csrViewContext := fun ty => $2;
                    csrViewFields  := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform _ fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform _ fields)
                  |}
                ];
           csrAccess := accessMModeOnly
         |};
         {|
           csrName := "mideleg";
           csrAddr := CsrIdWidth 'h"303";
           csrViews
             := [
                  let fields
                    := [
                         @csrFieldNoReg _ "reserved" (Bit 20) (getDefaultConst _);
                         @csrFieldAny _ "mideleg" (Bit 12) (Bit 12) (Some (ConstBit (wzero 12)))
                       ] in
                  {|
                    csrViewContext := fun ty => $1;
                    csrViewFields  := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform _ fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform _ fields)
                  |};
                  let fields
                    := [
                         @csrFieldNoReg _ "reserved" (Bit 52) (getDefaultConst _);
                         @csrFieldAny _ "mideleg" (Bit 12) (Bit 12) (Some (ConstBit (wzero 12)))
                       ] in
                  {|
                    csrViewContext := fun ty => $2;
                    csrViewFields  := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform _ fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform _ fields)
                  |}
                ];
           csrAccess := accessMModeOnly
         |};
         {|
           csrName := "mie";
           csrAddr := CsrIdWidth 'h"304";
           csrViews
             := let fields
                  := [
                       @csrFieldReadOnly _ "meie" Bool Bool (Some (ConstBool false));
                       @csrFieldNoReg _ "reserved0" Bool (getDefaultConst _);
                       @csrFieldAny _ "seie" Bool Bool (Some (ConstBool false));
                       @csrFieldAny _ "ueie" Bool Bool (Some (ConstBool false));
                       @csrFieldReadOnly _ "mtie" Bool Bool (Some (ConstBool false));
                       @csrFieldNoReg _ "htie" Bool (getDefaultConst _);
                       @csrFieldAny _ "stie" Bool Bool (Some (ConstBool false));
                       @csrFieldAny _ "utie" Bool Bool (Some (ConstBool false));
                       @csrFieldReadOnly _ "msie" Bool Bool (Some (ConstBool false));
                       @csrFieldNoReg _ "hsie" Bool (getDefaultConst _);
                       @csrFieldAny _ "ssie" Bool Bool (Some (ConstBool false));
                       @csrFieldAny _ "usie" Bool Bool (Some (ConstBool false))
                     ] in
                repeatCsrView 2
                  (@csrViewDefaultReadXform _ fields)
                  (@csrViewDefaultWriteXform _ fields);
           csrAccess := accessMModeOnly
         |};
         {|
           csrName := "mstatus";
           csrAddr := CsrIdWidth 'h"300";
           csrViews
           := let hasFloat := existsb (fun '(Build_SupportedExt x _ _) =>
                                         (x =? "F") ||
                                         (x =? "D"))%bool
                                        InitExtsAll in
                let hasFloatInit := existsb (fun '(Build_SupportedExt x y _) =>
                                               (((x =? "F") ||
                                                 (x =? "D")) && y))%bool
                                            InitExtsAll in
                let hasFloatEdit := existsb (fun '(Build_SupportedExt x _ z) =>
                                               (((x =? "F") ||
                                                 (x =? "D")) && z))%bool
                                        InitExtsAll in
                let fsInit := ConstBit (natToWord 2 (if hasFloatInit then 1 else 0)) in
                let fs := if hasFloatEdit
                          then @csrFieldAny _ "fs" (Bit 2) (Bit 2) (Some fsInit)
                          else @csrFieldNoReg _ "fs" (Bit 2) fsInit in
                [
                  let fields
                    := [
                         @csrFieldNoReg _ "reserved0" (Bit 9) (getDefaultConst _);
                         @csrFieldAny _ "tsr" Bool Bool (Some (ConstBool false));
                         @csrFieldAny _ "tw" Bool Bool (Some (ConstBool false));
                         @csrFieldAny _ "tvm" Bool Bool (Some (ConstBool false));
                         @csrFieldAny _ "mxr" Bool Bool (Some (ConstBool false));
                         @csrFieldAny _ "sum" Bool Bool (Some (ConstBool false));
                         @csrFieldAny _ "mprv" Bool Bool (Some (ConstBool false));
                         @csrFieldNoReg _ "xs" (Bit 2) (ConstBit (wzero _));
                         fs;
                         @csrFieldAny _ "mpp" (Bit 2) (Bit 2) (Some (ConstBit (wzero 2)));
                         @csrFieldNoReg _ "hpp" (Bit 2) (getDefaultConst _);
                         @csrFieldAny _ "spp" (Bit 1) (Bit 1) (Some (ConstBit (wzero 1)));
                         @csrFieldAny _ "upp" (Bit 0) (Bit 0) (Some (ConstBit (wzero 0)));
                         @csrFieldAny _ "mpie" Bool Bool (Some (ConstBool false));
                         @csrFieldNoReg _ "hpie" Bool (getDefaultConst _);
                         @csrFieldAny _ "spie" Bool Bool (Some (ConstBool false));
                         @csrFieldAny _ "upie" Bool Bool (Some (ConstBool false));
                         @csrFieldAny _ "mie" Bool Bool (Some (ConstBool false));
                         @csrFieldNoReg _ "hie" Bool (getDefaultConst _);
                         @csrFieldAny _ "sie" Bool Bool (Some (ConstBool false));
                         @csrFieldAny _ "uie" Bool Bool (Some (ConstBool false))
                       ] in
                  {|
                    csrViewContext := fun ty => $1;
                    csrViewFields  := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform _ fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform _ fields)
                  |};
                  let fields
                    := [
                         @csrFieldNoReg _ "reserved0" (Bit 28) (getDefaultConst _);
                         xlField "s";
                         xlField "u";
                         @csrFieldNoReg _ "reserved1" (Bit 9) (getDefaultConst _);
                         @csrFieldAny _ "tsr" Bool Bool (Some (ConstBool false));
                         @csrFieldAny _ "tw" Bool Bool (Some (ConstBool false));
                         @csrFieldAny _ "tvm" Bool Bool (Some (ConstBool false));
                         @csrFieldAny _ "mxr" Bool Bool (Some (ConstBool false));
                         @csrFieldAny _ "sum" Bool Bool (Some (ConstBool false));
                         @csrFieldAny _ "mprv" Bool Bool (Some (ConstBool false));
                         @csrFieldNoReg _ "xs" (Bit 2) (ConstBit (wzero _));
                         fs;
                         @csrFieldAny _ "mpp" (Bit 2) (Bit 2) (Some (ConstBit (wzero 2)));
                         @csrFieldNoReg _ "hpp" (Bit 2) (getDefaultConst _);
                         @csrFieldAny _ "spp" (Bit 1) (Bit 1) (Some (ConstBit (wzero 1)));
                         @csrFieldAny _ "upp" (Bit 0) (Bit 0) (Some (ConstBit (wzero 0)));
                         @csrFieldAny _ "mpie" Bool Bool (Some (ConstBool false));
                         @csrFieldNoReg _ "hpie" Bool (getDefaultConst _);
                         @csrFieldAny _ "spie" Bool Bool (Some (ConstBool false));
                         @csrFieldAny _ "upie" Bool Bool (Some (ConstBool false));
                         @csrFieldAny _ "mie" Bool Bool (Some (ConstBool false));
                         @csrFieldNoReg _ "hie" Bool (getDefaultConst _);
                         @csrFieldAny _ "sie" Bool Bool (Some (ConstBool false));
                         @csrFieldAny _ "uie" Bool Bool (Some (ConstBool false))
                       ] in
                  {|
                    csrViewContext := fun ty => $2;
                    csrViewFields  := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform _ fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform _ fields)
                  |}
                ];
           csrAccess := accessMModeOnly
         |};
         {|
           csrName := "mtvec";
           csrAddr := CsrIdWidth 'h"305";
           csrViews
             := [
                  let fields
                    := [
                         @tvecField _ "m" 30 (Xlen-2);
                         @csrFieldAny _ "mtvec_mode" (Bit 2) (Bit 2) None
                       ] in
                  {|
                    csrViewContext := fun ty => $1;
                    csrViewFields  := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform _ fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform _ fields)
                  |};
                  let fields
                    := [
                         @tvecField _ "m" 62 (Xlen-2);
                         @csrFieldAny _ "mtvec_mode" (Bit 2) (Bit 2) None
                       ] in
                  {|
                    csrViewContext := fun ty => $2;
                    csrViewFields  := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform _ fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform _ fields)
                  |}
                ];
           csrAccess := accessMModeOnly
         |};
         simpleCsr "mcounteren" (CsrIdWidth 'h"306") (Some (ConstBit (wzero 32))) accessMModeOnly;
         {|
           csrName := "mcountinhibit";
           csrAddr := CsrIdWidth 'h"320";
           csrViews
             := let fields
                  := [
                       @csrFieldNoReg _ "reserved0" (Bit 28) (getDefaultConst _);
                       @csrFieldAny _ "mcountinhibit_ir" Bool Bool (Some (ConstBool false));
                       @csrFieldNoReg _ "reserved1" (Bit 1)  (getDefaultConst _);
                       @csrFieldAny _ "mcountinhibit_cy" Bool Bool (Some (ConstBool false))
                     ] in
                repeatCsrView 2
                  (@csrViewDefaultReadXform _ fields)
                  (@csrViewDefaultWriteXform _ fields);
           csrAccess := accessMModeOnly
         |};
         {|
           csrName := "mscratch";
           csrAddr := CsrIdWidth 'h"340";
           csrViews
             := [
                  let fields := [ @csrFieldAny _ "mscratch" (Bit 32) (Bit Xlen) None ] in
                  {|
                    csrViewContext    := fun ty => $1;
                    csrViewFields     := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform _ fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform _ fields)
                  |};
                  let fields := [ @csrFieldAny _ "mscratch" (Bit 64) (Bit Xlen) None ] in
                  {|
                    csrViewContext    := fun ty => $2;
                    csrViewFields     := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform _ fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform _ fields)
                  |}
                ];
           csrAccess := accessMModeOnly
         |};
         {|
           csrName := "mepc";
           csrAddr := CsrIdWidth 'h"341";
           csrViews
             := [
                  let fields := [ @csrFieldAny _ "mepc" (Bit 32) (Bit Xlen) None ] in
                  {|
                    csrViewContext := fun ty => $1;
                    csrViewFields  := fields;
                    csrViewReadXform  := (@epcReadXform _ fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform _ fields)
                  |};
                  let fields := [ @csrFieldAny _ "mepc" (Bit 64) (Bit Xlen) None ] in
                  {|
                    csrViewContext := fun ty => $2;
                    csrViewFields  := fields;
                    csrViewReadXform  := (@epcReadXform _ fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform _ fields)
                  |}
                ];
           csrAccess := accessMModeOnly
         |};
         {|
           csrName := "mcause";
           csrAddr := CsrIdWidth 'h"342";
           csrViews
             := [
                  let fields
                    := [
                         @csrFieldAny _ "mcause_interrupt" Bool Bool (Some (ConstBool false));
                         @csrFieldAny _ "mcause_code" (Bit 31) (Bit (Xlen - 1)) None
                       ] in
                  {|
                    csrViewContext := fun ty => $1;
                    csrViewFields  := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform _ fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform _ fields)
                  |};
                  let fields
                    := [
                         @csrFieldAny _ "mcause_interrupt" Bool Bool (Some (ConstBool false));
                         @csrFieldAny _ "mcause_code" (Bit 63) (Bit (Xlen - 1)) None
                       ] in
                  {|
                    csrViewContext := fun ty => $2;
                    csrViewFields  := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform _ fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform _ fields)
                  |}
                ];
           csrAccess := accessMModeOnly
         |};
         {|
           csrName := "mtval";
           csrAddr := CsrIdWidth 'h"343";
           csrViews
             := [
                  let fields := [ @csrFieldAny _ "mtval" (Bit 32) (Bit Xlen) None ] in
                  {|
                    csrViewContext := fun ty => $1;
                    csrViewFields  := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform _ fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform _ fields)
                  |};
                  let fields := [ @csrFieldAny _ "mtval" (Bit 64) (Bit Xlen) None ] in
                  {|
                    csrViewContext := fun ty => $2;
                    csrViewFields  := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform _ fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform _ fields)
                  |}
                ];
           csrAccess := accessMModeOnly
         |};
         {|
           csrName := "mip";
           csrAddr := CsrIdWidth 'h"344";
           csrViews
             := let fields
                  := [
                       @csrFieldReadOnly _ "meip" Bool Bool (Some (ConstBool false));
                       @csrFieldNoReg _ "reserved0" Bool (getDefaultConst _);
                       @csrFieldAny _ "seip" Bool Bool (Some (ConstBool false));
                       @csrFieldAny _ "ueip" Bool Bool (Some (ConstBool false));
                       @csrFieldReadOnly _ "mtip" Bool Bool (Some (ConstBool false));
                       @csrFieldNoReg _ "htip" Bool (getDefaultConst _);
                       @csrFieldAny _ "stip" Bool Bool (Some (ConstBool false));
                       @csrFieldAny _ "utip" Bool Bool (Some (ConstBool false));
                       @csrFieldReadOnly _ "msip" Bool Bool (Some (ConstBool false));
                       @csrFieldNoReg _ "hsip" Bool (getDefaultConst _);
                       @csrFieldAny _ "ssip" Bool Bool (Some (ConstBool false));
                       @csrFieldAny _ "usip" Bool Bool (Some (ConstBool false))
                     ] in
                repeatCsrView 2
                  (@csrViewDefaultReadXform _ fields)
                  (@csrViewDefaultWriteXform _ fields);
           csrAccess := accessMModeOnly
         |};
         {|
           csrName := "pmpcfg0";
           csrAddr := CsrIdWidth 'h"3a0";
           csrViews
             := [
                  let fields
                    := [
                         @pmpField _ 3;
                         @pmpField _ 2;
                         @pmpField _ 1;
                         @pmpField _ 0
                       ] in
                  {|
                    csrViewContext    := fun ty => $1;
                    csrViewFields     := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform _ fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform _ fields)
                  |};
                  let fields
                    := [
                         @pmpField _ 7;
                         @pmpField _ 6;
                         @pmpField _ 5;
                         @pmpField _ 4;
                         @pmpField _ 3;
                         @pmpField _ 2;
                         @pmpField _ 1;
                         @pmpField _ 0
                       ] in
                  {|
                    csrViewContext    := fun ty => $2;
                    csrViewFields     := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform _ fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform _ fields)
                  |}
                ];
           csrAccess := accessMModeOnly
         |};
         {|
           csrName := "pmpcfg1";
           csrAddr := CsrIdWidth 'h"3a1";
           csrViews
             := [
                  let fields
                    := [
                         @pmpField _ 3;
                         @pmpField _ 2;
                         @pmpField _ 1;
                         @pmpField _ 0
                       ] in
                  {|
                    csrViewContext    := fun ty => $1;
                    csrViewFields     := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform _ fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform _ fields)
                  |};
                  {|
                    csrViewContext    := fun ty => $2;
                    csrViewFields     := [];
                    csrViewReadXform  := (@csrViewDefaultReadXform _ []);
                    csrViewWriteXform := (@csrViewDefaultWriteXform _ [])
                  |}
                ];
           csrAccess
             := fun ty context
                  => context @% "xlen" == $1 &&
                     context @% "mode" == $MachineMode
         |};
         {|
           csrName := "pmpcfg2";
           csrAddr := CsrIdWidth 'h"3a2";
           csrViews
             := [
                  let fields
                    := [
                         @pmpField _ 11;
                         @pmpField _ 10;
                         @pmpField _ 9;
                         @pmpField _ 8
                       ] in
                  {|
                    csrViewContext    := fun ty => $1;
                    csrViewFields     := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform _ fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform _ fields)
                  |};
                  let fields
                    := [
                         @pmpField _ 15;
                         @pmpField _ 14;
                         @pmpField _ 13;
                         @pmpField _ 12;
                         @pmpField _ 11;
                         @pmpField _ 10;
                         @pmpField _ 9;
                         @pmpField _ 8
                       ] in
                  {|
                    csrViewContext    := fun ty => $2;
                    csrViewFields     := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform _ fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform _ fields)
                  |}
                ];
           csrAccess := accessMModeOnly
         |};
         {|
           csrName := "pmpcfg3";
           csrAddr := CsrIdWidth 'h"3a3";
           csrViews
             := [
                  let fields
                    := [
                         @pmpField _ 15;
                         @pmpField _ 14;
                         @pmpField _ 13;
                         @pmpField _ 12
                       ] in
                  {|
                    csrViewContext    := fun ty => $1;
                    csrViewFields     := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform _ fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform _ fields)
                  |};
                  {|
                    csrViewContext    := fun ty => $2;
                    csrViewFields     := [];
                    csrViewReadXform  := (@csrViewDefaultReadXform _ []);
                    csrViewWriteXform := (@csrViewDefaultWriteXform _ [])
                  |}
                ];
           csrAccess
             := fun ty context
                  => context @% "xlen" == $1 &&
                     context @% "mode" == $MachineMode
         |};
         simpleCsr "pmpaddr0" (CsrIdWidth 'h"3b0") (width := pmp_reg_width) None accessMModeOnly;
         simpleCsr "pmpaddr1" (CsrIdWidth 'h"3b1") (width := pmp_reg_width) None accessMModeOnly;
         simpleCsr "pmpaddr2" (CsrIdWidth 'h"3b2") (width := pmp_reg_width) None accessMModeOnly;
         simpleCsr "pmpaddr3" (CsrIdWidth 'h"3b3") (width := pmp_reg_width) None accessMModeOnly;
         simpleCsr "pmpaddr4" (CsrIdWidth 'h"3b4") (width := pmp_reg_width) None accessMModeOnly;
         simpleCsr "pmpaddr5" (CsrIdWidth 'h"3b5") (width := pmp_reg_width) None accessMModeOnly;
         simpleCsr "pmpaddr6" (CsrIdWidth 'h"3b6") (width := pmp_reg_width) None accessMModeOnly;
         simpleCsr "pmpaddr7" (CsrIdWidth 'h"3b7") (width := pmp_reg_width) None accessMModeOnly;
         simpleCsr "pmpaddr8" (CsrIdWidth 'h"3b8") (width := pmp_reg_width) None accessMModeOnly;
         simpleCsr "pmpaddr9" (CsrIdWidth 'h"3b9") (width := pmp_reg_width) None accessMModeOnly;
         simpleCsr "pmpaddrA" (CsrIdWidth 'h"3ba") (width := pmp_reg_width) None accessMModeOnly;
         simpleCsr "pmpaddrB" (CsrIdWidth 'h"3bb") (width := pmp_reg_width) None accessMModeOnly;
         simpleCsr "pmpaddrC" (CsrIdWidth 'h"3bc") (width := pmp_reg_width) None accessMModeOnly;
         simpleCsr "pmpaddrD" (CsrIdWidth 'h"3bd") (width := pmp_reg_width) None accessMModeOnly;
         simpleCsr "pmpaddrE" (CsrIdWidth 'h"3be") (width := pmp_reg_width) None accessMModeOnly;
         simpleCsr "pmpaddrF" (CsrIdWidth 'h"3bf") (width := pmp_reg_width) None accessMModeOnly;
         {|
           csrName := "sstatus";
           csrAddr := CsrIdWidth 'h"100";
           csrViews
             := [
                  let fields
                    := [
                         @csrFieldNoReg _ "reserved0" (Bit 12) (getDefaultConst _);
                         @csrFieldAny _ "mxr" Bool Bool (Some (ConstBool false));
                         @csrFieldAny _ "sum" Bool Bool (Some (ConstBool false));
                         @csrFieldNoReg _ "reserved1" (Bit 9) (getDefaultConst _);
                         @csrFieldAny _ "spp" (Bit 1) (Bit 1) (Some (ConstBit (wzero 1)));
                         @csrFieldNoReg _ "reserved2" (Bit 2) (getDefaultConst _);
                         @csrFieldAny _ "spie" Bool Bool (Some (ConstBool false));
                         @csrFieldAny _ "upie" Bool Bool (Some (ConstBool false));
                         @csrFieldNoReg _ "reserved3" (Bit 2) (getDefaultConst _);
                         @csrFieldAny _ "sie" Bool Bool (Some (ConstBool false));
                         @csrFieldAny _ "uie" Bool Bool (Some (ConstBool false))
                       ] in
                  {|
                    csrViewContext := fun ty => $1;
                    csrViewFields  := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform _ fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform _ fields)
                  |};
                  let fields
                    := [
                         @csrFieldNoReg _ "reserved0" (Bit 30) (getDefaultConst _);
                         xlField "u";
                         @csrFieldNoReg _ "reserved1" (Bit 12) (getDefaultConst _);
                         @csrFieldAny _ "mxr" Bool Bool (Some (ConstBool false));
                         @csrFieldAny _ "sum" Bool Bool (Some (ConstBool false));
                         @csrFieldNoReg _ "reserved2" (Bit 9) (getDefaultConst _);
                         @csrFieldAny _ "spp" (Bit 1) (Bit 1) (Some (ConstBit (wzero 1)));
                         @csrFieldNoReg _ "reserved3" (Bit 2) (getDefaultConst _);
                         @csrFieldAny _ "spie" Bool Bool (Some (ConstBool false));
                         @csrFieldAny _ "upie" Bool Bool (Some (ConstBool false));
                         @csrFieldNoReg _ "reserved4" (Bit 2) (getDefaultConst _);
                         @csrFieldAny _ "sie" Bool Bool (Some (ConstBool false));
                         @csrFieldAny _ "uie" Bool Bool (Some (ConstBool false))
                       ] in
                  {|
                    csrViewContext := fun ty => $2;
                    csrViewFields  := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform _ fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform _ fields)
                  |}
                ];
           csrAccess := accessSMode
         |};
         {|
           csrName := "sedeleg";
           csrAddr := CsrIdWidth 'h"102";
           csrViews
             := [
                  let fields
                    := [
                         @csrFieldNoReg _ "reserved" (Bit 16) (getDefaultConst _);
                         @csrFieldAny _ "sedeleg" (Bit 16) (Bit 16) (Some (ConstBit (wzero 16)))
                       ] in
                  {|
                    csrViewContext := fun ty => $1;
                    csrViewFields  := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform _ fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform _ fields)
                  |};
                  let fields
                    := [
                         @csrFieldNoReg _ "reserved" (Bit 48) (getDefaultConst _);
                         @csrFieldAny _ "sedeleg" (Bit 16) (Bit 16) (Some (ConstBit (wzero 16)))
                       ] in
                  {|
                    csrViewContext := fun ty => $2;
                    csrViewFields  := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform _ fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform _ fields)
                  |}
                ];
           csrAccess := accessSMode
         |};
         {|
           csrName := "sideleg";
           csrAddr := CsrIdWidth 'h"103";
           csrViews
             := [
                  let fields
                    := [
                         @csrFieldNoReg _ "reserved" (Bit 20) (getDefaultConst _);
                         @csrFieldAny _ "sideleg" (Bit 12) (Bit 12) (Some (ConstBit (wzero 12)))
                       ] in
                  {|
                    csrViewContext := fun ty => $1;
                    csrViewFields  := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform _ fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform _ fields)
                  |};
                  let fields
                    := [
                         @csrFieldNoReg _ "reserved" (Bit 52) (getDefaultConst _);
                         @csrFieldAny _ "sideleg" (Bit 12) (Bit 12) (Some (ConstBit (wzero 12)))
                       ] in
                  {|
                    csrViewContext := fun ty => $2;
                    csrViewFields  := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform _ fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform _ fields)
                  |}
                ];
           csrAccess := accessSMode
         |};
         {|
           csrName := "sie";
           csrAddr := CsrIdWidth 'h"104";
           csrViews
             := let lower_fields
                  := [
                       
                       @csrFieldAny _ "seie" Bool Bool (Some (ConstBool false));
                       @csrFieldAny _ "ueie" Bool Bool (Some (ConstBool false));
                       @csrFieldNoReg _ "reserved1" (Bit 2) (getDefaultConst _);
                       @csrFieldAny _ "stie" Bool Bool (Some (ConstBool false));
                       @csrFieldAny _ "utie" Bool Bool (Some (ConstBool false));
                       @csrFieldNoReg _ "reserved2" (Bit 2)  (getDefaultConst _);
                       @csrFieldAny _ "ssie" Bool Bool (Some (ConstBool false));
                       @csrFieldAny _ "usie" Bool Bool (Some (ConstBool false))
                     ] in
                [
                  let fields := @csrFieldNoReg _ "reserved0" (Bit 22) (getDefaultConst _) :: lower_fields in
                  {|
                    csrViewContext := fun ty => $1;
                    csrViewFields  := fields;
                    csrViewReadXform := (@csrViewDefaultReadXform _ fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform _ fields)
                  |};
                  let fields := @csrFieldNoReg _ "reserved0" (Bit 54) (getDefaultConst _) :: lower_fields in
                  {|
                    csrViewContext := fun ty => $2;
                    csrViewFields  := fields;
                    csrViewReadXform := (@csrViewDefaultReadXform _ fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform _ fields)
                  |}
                ];
           csrAccess := accessSMode
         |};
         {|
           csrName := "stvec";
           csrAddr := CsrIdWidth 'h"105";
           csrViews
             := [
                  let fields
                    := [
                         @tvecField _ "s" 30 (Xlen-2);
                         @csrFieldAny _ "stvec_mode" (Bit 2) (Bit 2) None
                       ] in
                  {|
                    csrViewContext := fun ty => $1;
                    csrViewFields  := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform _ fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform _ fields)
                  |};
                  let fields
                    := [
                         @tvecField _ "s" 62 (Xlen-2);
                         @csrFieldAny _ "stvec_mode" (Bit 2) (Bit 2) None
                       ] in
                  {|
                    csrViewContext := fun ty => $2;
                    csrViewFields  := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform _ fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform _ fields)
                  |}
                ];
           csrAccess := accessSMode
         |};
         simpleCsr "scounteren" (CsrIdWidth 'h"106") (Some (ConstBit (wzero 32))) accessSMode;
         {|
           csrName := "sscratch";
           csrAddr := CsrIdWidth 'h"140";
           csrViews
             := [
                  let fields := [ @csrFieldAny _ "sscratch" (Bit 32) (Bit Xlen) None ] in
                  {|
                    csrViewContext := fun ty => $1;
                    csrViewFields  := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform _ fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform _ fields)
                  |};
                  let fields := [ @csrFieldAny _ "sscratch" (Bit 64) (Bit Xlen) None ] in
                  {|
                    csrViewContext := fun ty => $2;
                    csrViewFields  := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform _ fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform _ fields)
                  |}
                ];
           csrAccess := accessSMode
         |};
         {|
           csrName := "sepc";
           csrAddr := CsrIdWidth 'h"141";
           csrViews
             := [
                  let fields := [ @csrFieldAny _ "sepc" (Bit 32) (Bit Xlen) None ] in
                  {|
                    csrViewContext := fun ty => $1;
                    csrViewFields  := fields;
                    csrViewReadXform  := (@epcReadXform _ fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform _ fields)
                  |};
                  let fields := [ @csrFieldAny _ "sepc" (Bit 64) (Bit Xlen) None ] in
                  {|
                    csrViewContext := fun ty => $2;
                    csrViewFields  := fields;
                    csrViewReadXform  := (@epcReadXform _ fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform _ fields)
                  |}
                ];
           csrAccess := accessSMode
         |};
         {|
           csrName := "scause";
           csrAddr := CsrIdWidth 'h"142";
           csrViews
             := [
                  let fields
                    := [
                         @csrFieldAny _ "scause_interrupt" Bool Bool (Some (ConstBool false));
                         @csrFieldAny _ "scause_code" (Bit 31) (Bit (Xlen - 1)) None
                       ] in
                  {|
                    csrViewContext := fun ty => $1;
                    csrViewFields  := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform _ fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform _ fields)
                  |};
                  let fields
                    := [
                         @csrFieldAny _ "scause_interrupt" Bool Bool (Some (ConstBool false));
                         @csrFieldAny _ "scause_code" (Bit 63) (Bit (Xlen - 1)) None
                       ] in
                  {|
                    csrViewContext := fun ty => $2;
                    csrViewFields  := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform _ fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform _ fields)
                  |}
                ];
           csrAccess := accessSMode
         |};
         {|
           csrName := "stval";
           csrAddr := CsrIdWidth 'h"143";
           csrViews
             := [
                  let fields := [ @csrFieldAny _ "stval" (Bit 32) (Bit Xlen) None ] in
                  {|
                    csrViewContext := fun ty => $1;
                    csrViewFields  := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform _ fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform _ fields)
                  |};
                  let fields := [ @csrFieldAny _ "stval" (Bit 64) (Bit Xlen) None ] in
                  {|
                    csrViewContext := fun ty => $2;
                    csrViewFields  := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform _ fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform _ fields)
                  |}
                ];
           csrAccess := accessSMode
         |};
         {|
           csrName := "sip";
           csrAddr := CsrIdWidth 'h"144";
           csrViews
             := let lower_fields
                  := [
                       
                       @csrFieldAny _ "seip" Bool Bool (Some (ConstBool false));
                       @csrFieldAny _ "ueip" Bool Bool (Some (ConstBool false));
                       @csrFieldNoReg _ "reserved1" (Bit 2) (getDefaultConst _);
                       @csrFieldAny _ "stip" Bool Bool (Some (ConstBool false));
                       @csrFieldAny _ "utip" Bool Bool (Some (ConstBool false));
                       @csrFieldNoReg _ "reserved2" (Bit 2)  (getDefaultConst _);
                       @csrFieldAny _ "ssip" Bool Bool (Some (ConstBool false));
                       @csrFieldAny _ "usip" Bool Bool (Some (ConstBool false))
                     ] in
                [
                  let fields := @csrFieldNoReg _ "reserved0" (Bit 22) (getDefaultConst _) :: lower_fields in
                  {|
                    csrViewContext := fun ty => $1;
                    csrViewFields  := fields;
                    csrViewReadXform := (@csrViewDefaultReadXform _ fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform _ fields)
                  |};
                  let fields := @csrFieldNoReg _ "reserved0" (Bit 54) (getDefaultConst _) :: lower_fields in
                  {|
                    csrViewContext := fun ty => $2;
                    csrViewFields  := fields;
                    csrViewReadXform := (@csrViewDefaultReadXform _ fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform _ fields)
                  |}
                ];
           csrAccess := accessSMode
         |};
         {|
           csrName  := satpCsrName;
           csrAddr  := CsrIdWidth 'h"180";
           csrViews := [satpCsrView 32; satpCsrView 64];
           csrAccess
             := fun ty context
                  => context @% "mode" == $MachineMode ||
                     (context @% "mode" == $SupervisorMode && !(context @% "tvm"))
         |};
         {|
           csrName  := "mvendorid";
           csrAddr  := CsrIdWidth 'h"f11";
           csrViews
             := let fields
                  := [ @csrFieldAny _ "mvendorid" (Bit 32) (Bit 32) None] in
                repeatCsrView 2
                  (@csrViewDefaultReadXform _ fields)
                  (@csrViewDefaultWriteXform _ fields);
           csrAccess := accessMModeOnly
         |};
         {|
           csrName := "marchid";
           csrAddr := CsrIdWidth 'h"f12";
           csrViews
             := [
                  let fields := [ @csrFieldAny _ "marchid" (Bit 32) (Bit Xlen) None ] in
                  {|
                    csrViewContext := fun ty => $1;
                    csrViewFields  := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform _ fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform _ fields)
                  |};
                  let fields := [ @csrFieldAny _ "marchid" (Bit 64) (Bit Xlen) None ] in
                  {|
                    csrViewContext := fun ty => $2;
                    csrViewFields  := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform _ fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform _ fields)
                  |}
                ];
           csrAccess := accessMModeOnly
         |};
         {|
           csrName := "mimpid";
           csrAddr := CsrIdWidth 'h"f13";
           csrViews
             := [
                  let fields := [ @csrFieldAny _ "mimpid" (Bit 32) (Bit Xlen) None ] in
                  {|
                    csrViewContext := fun ty => $1;
                    csrViewFields  := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform _ fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform _ fields)
                  |};
                  let fields := [ @csrFieldAny _ "mimpid" (Bit 64) (Bit Xlen) None ] in
                  {|
                    csrViewContext := fun ty => $2;
                    csrViewFields  := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform _ fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform _ fields)
                  |}
                ];
           csrAccess := accessMModeOnly
         |};
         {|
           csrName := "mhartid";
           csrAddr := CsrIdWidth 'h"f14";
           csrViews
             := [
                  let fields := [ @csrFieldAny _ "mhartid" (Bit 32) (Bit Xlen) (Some (ConstBit (wzero Xlen))) ] in
                  {|
                    csrViewContext := fun ty => $1;
                    csrViewFields  := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform _ fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform _ fields)
                  |};
                  let fields := [ @csrFieldAny _ "mhartid" (Bit 64) (Bit Xlen) (Some (ConstBit (wzero Xlen))) ] in
                  {|
                    csrViewContext := fun ty => $2;
                    csrViewFields  := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform _ fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform _ fields)
                  |}
                ];
           csrAccess := accessMModeOnly
         |};
         {|
           csrName  := "mcycle";
           csrAddr  := CsrIdWidth 'h"b00";
           csrViews
             := let fields := [ @csrFieldAny _ "mcycle" (Bit 64) (Bit 64) (Some (ConstBit (wzero 64))) ] in
                repeatCsrView 2
                  (@csrViewDefaultReadXform _ fields)
                  (@csrViewDefaultWriteXform _ fields);
           csrAccess := accessMModeOnly
         |};
         {|
           csrName  := "minstret";
           csrAddr  := CsrIdWidth 'h"b02";
           csrViews
             := let fields := [ @csrFieldAny _ "minstret" (Bit 64) (Bit 64) (Some (ConstBit (wzero 64)))] in
                repeatCsrView 2
                  (@csrViewDefaultReadXform _ fields)
                  (@csrViewDefaultWriteXform _ fields);
           csrAccess := accessMModeOnly
         |};
         nilCsr "mhpmcounter3" (CsrIdWidth 'h"b03") accessMModeOnly;
         nilCsr "mhpmcounter4" (CsrIdWidth 'h"b04") accessMModeOnly;
         nilCsr "mhpmcounter5" (CsrIdWidth 'h"b05") accessMModeOnly;
         nilCsr "mhpmcounter6" (CsrIdWidth 'h"b06") accessMModeOnly;
         nilCsr "mhpmcounter7" (CsrIdWidth 'h"b07") accessMModeOnly;
         nilCsr "mhpmcounter8" (CsrIdWidth 'h"b08") accessMModeOnly;
         nilCsr "mhpmcounter9" (CsrIdWidth 'h"b09") accessMModeOnly;
         nilCsr "mhpmcounter10" (CsrIdWidth 'h"b0a") accessMModeOnly;
         nilCsr "mhpmcounter11" (CsrIdWidth 'h"b0b") accessMModeOnly;
         nilCsr "mhpmcounter12" (CsrIdWidth 'h"b0c") accessMModeOnly;
         nilCsr "mhpmcounter13" (CsrIdWidth 'h"b0d") accessMModeOnly;
         nilCsr "mhpmcounter14" (CsrIdWidth 'h"b03") accessMModeOnly;
         nilCsr "mhpmcounter15" (CsrIdWidth 'h"b0f") accessMModeOnly;
         nilCsr "mhpmcounter16" (CsrIdWidth 'h"b10") accessMModeOnly;
         nilCsr "mhpmcounter17" (CsrIdWidth 'h"b11") accessMModeOnly;
         nilCsr "mhpmcounter18" (CsrIdWidth 'h"b12") accessMModeOnly;
         nilCsr "mhpmcounter19" (CsrIdWidth 'h"b13") accessMModeOnly;
         nilCsr "mhpmcounter20" (CsrIdWidth 'h"b14") accessMModeOnly;
         nilCsr "mhpmcounter21" (CsrIdWidth 'h"b15") accessMModeOnly;
         nilCsr "mhpmcounter22" (CsrIdWidth 'h"b16") accessMModeOnly;
         nilCsr "mhpmcounter23" (CsrIdWidth 'h"b17") accessMModeOnly;
         nilCsr "mhpmcounter24" (CsrIdWidth 'h"b18") accessMModeOnly;
         nilCsr "mhpmcounter25" (CsrIdWidth 'h"b19") accessMModeOnly;
         nilCsr "mhpmcounter26" (CsrIdWidth 'h"b1a") accessMModeOnly;
         nilCsr "mhpmcounter27" (CsrIdWidth 'h"b1b") accessMModeOnly;
         nilCsr "mhpmcounter28" (CsrIdWidth 'h"b1c") accessMModeOnly;
         nilCsr "mhpmcounter29" (CsrIdWidth 'h"b1d") accessMModeOnly;
         nilCsr "mhpmcounter30" (CsrIdWidth 'h"b1e") accessMModeOnly;
         nilCsr "mhpmcounter31" (CsrIdWidth 'h"b1f") accessMModeOnly;
         {|
           csrName  := "mcycleh";
           csrAddr  := CsrIdWidth 'h"b80";
           csrViews
             := let fields := [ @csrFieldAny _ "mcycle" (Bit 64) (Bit 64) (Some (ConstBit (wzero 64))) ] in
                repeatCsrView 2
                  (@csrViewUpperReadXform _ fields)
                  (@csrViewUpperWriteXform _ fields);
           csrAccess := accessMModeOnly
         |};
         {|
           csrName  := "minstreth";
           csrAddr  := CsrIdWidth 'h"b82";
           csrViews
             := let fields := [ @csrFieldAny _ "minstret" (Bit 64) (Bit 64) (Some (ConstBit (wzero 64))) ] in
                repeatCsrView 2
                  (@csrViewUpperReadXform _ fields)
                  (@csrViewUpperWriteXform _ fields);
           csrAccess := accessMModeOnly
         |};
         nilCsr "mhpmevent3" (CsrIdWidth 'h"323") accessMModeOnly;
         nilCsr "mhpmevent4" (CsrIdWidth 'h"324") accessMModeOnly;
         nilCsr "mhpmevent5" (CsrIdWidth 'h"325") accessMModeOnly;
         nilCsr "mhpmevent6" (CsrIdWidth 'h"326") accessMModeOnly;
         nilCsr "mhpmevent7" (CsrIdWidth 'h"327") accessMModeOnly;
         nilCsr "mhpmevent8" (CsrIdWidth 'h"328") accessMModeOnly;
         nilCsr "mhpmevent9" (CsrIdWidth 'h"329") accessMModeOnly;
         nilCsr "mhpmevent10" (CsrIdWidth 'h"32a") accessMModeOnly;
         nilCsr "mhpmevent11" (CsrIdWidth 'h"32b") accessMModeOnly;
         nilCsr "mhpmevent12" (CsrIdWidth 'h"32c") accessMModeOnly;
         nilCsr "mhpmevent13" (CsrIdWidth 'h"32d") accessMModeOnly;
         nilCsr "mhpmevent14" (CsrIdWidth 'h"323") accessMModeOnly;
         nilCsr "mhpmevent15" (CsrIdWidth 'h"32f") accessMModeOnly;
         nilCsr "mhpmevent16" (CsrIdWidth 'h"330") accessMModeOnly;
         nilCsr "mhpmevent17" (CsrIdWidth 'h"331") accessMModeOnly;
         nilCsr "mhpmevent18" (CsrIdWidth 'h"332") accessMModeOnly;
         nilCsr "mhpmevent19" (CsrIdWidth 'h"333") accessMModeOnly;
         nilCsr "mhpmevent20" (CsrIdWidth 'h"334") accessMModeOnly;
         nilCsr "mhpmevent21" (CsrIdWidth 'h"335") accessMModeOnly;
         nilCsr "mhpmevent22" (CsrIdWidth 'h"336") accessMModeOnly;
         nilCsr "mhpmevent23" (CsrIdWidth 'h"337") accessMModeOnly;
         nilCsr "mhpmevent24" (CsrIdWidth 'h"338") accessMModeOnly;
         nilCsr "mhpmevent25" (CsrIdWidth 'h"339") accessMModeOnly;
         nilCsr "mhpmevent26" (CsrIdWidth 'h"33a") accessMModeOnly;
         nilCsr "mhpmevent27" (CsrIdWidth 'h"33b") accessMModeOnly;
         nilCsr "mhpmevent28" (CsrIdWidth 'h"33c") accessMModeOnly;
         nilCsr "mhpmevent29" (CsrIdWidth 'h"33d") accessMModeOnly;
         nilCsr "mhpmevent30" (CsrIdWidth 'h"33e") accessMModeOnly;
         nilCsr "mhpmevent31" (CsrIdWidth 'h"33f") accessMModeOnly;
         nilCsr "tselect" (CsrIdWidth 'h"7a0") accessMModeOnly;
         nilCsr "tdata1" (CsrIdWidth 'h"7a1") accessMModeOnly;
         nilCsr "tdata2" (CsrIdWidth 'h"7a2") accessMModeOnly;
         nilCsr "tdata3" (CsrIdWidth 'h"7a3") accessMModeOnly;
         {|
           csrName := "dcsr";
           csrAddr := CsrIdWidth 'h"7b0";
           csrViews
             := let fields
                  := [
                       @csrFieldNoReg _ "xdebugver" (Bit 4) (natToWord 4 4);
                       @csrFieldNoReg _ "reserved0" (Bit 12) (getDefaultConst _);
                       @csrFieldAny _ "ebreakm" Bool Bool (Some (ConstBool false));
                       @csrFieldNoReg _ "ebreakh" Bool false;
                       @csrFieldAny _ "ebreaks" Bool Bool (Some (ConstBool false));
                       @csrFieldAny _ "ebreaku" Bool Bool (Some (ConstBool false));
                       @csrFieldAny _ "stepie" Bool Bool (Some (ConstBool false));
                       @csrFieldAny _ "stopcount" Bool Bool (Some (ConstBool false));
                       @csrFieldAny _ "stoptime" Bool Bool (Some (ConstBool false));
                       @csrFieldReadOnly _ "cause" (Bit 3) (Bit 3) None;
                       @csrFieldNoReg _ "reserved1" (Bit 1) (getDefaultConst _);
                       @csrFieldAny _ "mprven" Bool Bool (Some (ConstBool false));
                       @csrFieldAny _ "nmip" Bool Bool (Some (ConstBool false));
                       @csrFieldAny _ "step" Bool Bool (Some (ConstBool false));
                       @csrFieldAny _ "prv" (Bit 2) (Bit 2) None
                     ] in
                repeatCsrView 2
                  (@csrViewUpperReadXform _ fields)
                  (@csrViewUpperWriteXform _ fields);
                csrAccess := accessDMode
         |};
         simpleCsr "dpc" (CsrIdWidth 'h"7b1") (width := Xlen) None accessDMode
       ].

  Local Close Scope kami_expr.

End csrs.
