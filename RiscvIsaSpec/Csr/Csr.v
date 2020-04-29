(* Defines the standard Csrs. *)
Require Import Vector.
Import VectorNotations.
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
         {| (* 0 *)
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
         nilCsr "uie" (CsrIdWidth 'h"4") accessAny; (* 1 *)
         {| (* 2 *)
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
         {| (* 3 *)
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
         {| (* 4 *)
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
         {| (* 5 *)
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
         {| (* 6 *)
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
         {| (* 7 *)
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
         {| (* 8 *)
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
         {| (* 9 *)
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
         {| (* 10 *)
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
         simpleCsr "mcycle" (CsrIdWidth 'h"c00") (Some (ConstBit (wzero 64))) (fun ty => accessCounter "CY"); (* 11 *)
         readonlyCsr "mtime" (CsrIdWidth 'h"c01") accessAny (Some (ConstBit (wzero 64))); (* 12 *)
         simpleCsr "minstret" (CsrIdWidth 'h"c02") (Some (ConstBit (wzero 64))) (fun ty => accessCounter "IR"); (* 13 *)
         {| (* 14 *)
           csrName := "cycleh";
           csrAddr := CsrIdWidth 'h"c80";
           csrViews
             := let fields := [ @csrFieldReadOnly _ "mcycle" (Bit 64) (Bit 64) (Some (ConstBit (wzero 64))) ] in
                repeatCsrView 2
                  (@csrViewUpperReadXform _ fields)
                  (@csrViewUpperWriteXform _ fields);
           csrAccess := accessAny
         |};
         {| (* 15 *)
           csrName := "instreth";
           csrAddr := CsrIdWidth 'h"c82";
           csrViews
             := let fields := [ @csrFieldReadOnly _ "minstret" (Bit 64) (Bit 64) (Some (ConstBit (wzero 64))) ] in
                repeatCsrView 2
                  (@csrViewUpperReadXform _ fields)
                  (@csrViewUpperWriteXform _ fields);
           csrAccess := accessAny
         |};
         {| (* 16 *)
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
         {| (* 17 *)
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
         {| (* 18 *)
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
         {| (* 19 *)
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
         {| (* 20 *)
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
         {| (* 21 *)
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
         simpleCsr "mcounteren" (CsrIdWidth 'h"306") (Some (ConstBit (wzero 32))) accessMModeOnly; (* 22 *)
         {| (* 23 *)
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
         {| (* 24 *)
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
         {| (* 25 *)
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
         {| (* 26 *)
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
         {| (* 27 *)
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
         {| (* 28 *)
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
         {| (* 29 *)
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
         {| (* 30 *)
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
         {| (* 30 *)
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
         {| (* 31 *)
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
         simpleCsr "pmpaddr0" (CsrIdWidth 'h"3b0") (width := pmp_reg_width) None accessMModeOnly; (* 32 *)
         simpleCsr "pmpaddr1" (CsrIdWidth 'h"3b1") (width := pmp_reg_width) None accessMModeOnly; (* 33 *)
         simpleCsr "pmpaddr2" (CsrIdWidth 'h"3b2") (width := pmp_reg_width) None accessMModeOnly; (* 34 *)
         simpleCsr "pmpaddr3" (CsrIdWidth 'h"3b3") (width := pmp_reg_width) None accessMModeOnly; (* 35 *)
         simpleCsr "pmpaddr4" (CsrIdWidth 'h"3b4") (width := pmp_reg_width) None accessMModeOnly; (* 36 *)
         simpleCsr "pmpaddr5" (CsrIdWidth 'h"3b5") (width := pmp_reg_width) None accessMModeOnly; (* 37 *)
         simpleCsr "pmpaddr6" (CsrIdWidth 'h"3b6") (width := pmp_reg_width) None accessMModeOnly; (* 38 *)
         simpleCsr "pmpaddr7" (CsrIdWidth 'h"3b7") (width := pmp_reg_width) None accessMModeOnly; (* 39 *)
         simpleCsr "pmpaddr8" (CsrIdWidth 'h"3b8") (width := pmp_reg_width) None accessMModeOnly; (* 40 *)
         simpleCsr "pmpaddr9" (CsrIdWidth 'h"3b9") (width := pmp_reg_width) None accessMModeOnly; (* 41 *)
         simpleCsr "pmpaddrA" (CsrIdWidth 'h"3ba") (width := pmp_reg_width) None accessMModeOnly; (* 42 *)
         simpleCsr "pmpaddrB" (CsrIdWidth 'h"3bb") (width := pmp_reg_width) None accessMModeOnly; (* 43 *)
         simpleCsr "pmpaddrC" (CsrIdWidth 'h"3bc") (width := pmp_reg_width) None accessMModeOnly; (* 44 *)
         simpleCsr "pmpaddrD" (CsrIdWidth 'h"3bd") (width := pmp_reg_width) None accessMModeOnly; (* 45 *)
         simpleCsr "pmpaddrE" (CsrIdWidth 'h"3be") (width := pmp_reg_width) None accessMModeOnly; (* 46 *)
         simpleCsr "pmpaddrF" (CsrIdWidth 'h"3bf") (width := pmp_reg_width) None accessMModeOnly; (* 47 *)
         {| (* 48 *)
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
         {| (* 49 *)
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
         {| (* 50 *)
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
         {| (* 51 *)
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
         {| (* 52 *)
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
         simpleCsr "scounteren" (CsrIdWidth 'h"106") (Some (ConstBit (wzero 32))) accessSMode; (* 53 *)
         {| (* 54 *)
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
         {| (* 55 *)
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
         {| (* 56 *)
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
         {| (* 57 *)
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
         {| (* 58 *)
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
         {| (* 59 *)
           csrName  := satpCsrName;
           csrAddr  := CsrIdWidth 'h"180";
           csrViews := [satpCsrView 32; satpCsrView 64];
           csrAccess
             := fun ty context
                  => context @% "mode" == $MachineMode ||
                     (context @% "mode" == $SupervisorMode && !(context @% "tvm"))
         |};
         {| (* 60 *)
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
         {| (* 61 *)
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
         {| (* 62 *)
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
         {| (* 63 *)
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
         {| (* 64 *)
           csrName  := "mcycle";
           csrAddr  := CsrIdWidth 'h"b00";
           csrViews
             := let fields := [ @csrFieldAny _ "mcycle" (Bit 64) (Bit 64) (Some (ConstBit (wzero 64))) ] in
                repeatCsrView 2
                  (@csrViewDefaultReadXform _ fields)
                  (@csrViewDefaultWriteXform _ fields);
           csrAccess := accessMModeOnly
         |};
         {| (* 65 *)
           csrName  := "minstret";
           csrAddr  := CsrIdWidth 'h"b02";
           csrViews
             := let fields := [ @csrFieldAny _ "minstret" (Bit 64) (Bit 64) (Some (ConstBit (wzero 64)))] in
                repeatCsrView 2
                  (@csrViewDefaultReadXform _ fields)
                  (@csrViewDefaultWriteXform _ fields);
           csrAccess := accessMModeOnly
         |};
         nilCsr "mhpmcounter3" (CsrIdWidth 'h"b03") accessMModeOnly; (* 66 *)
         nilCsr "mhpmcounter4" (CsrIdWidth 'h"b04") accessMModeOnly; (* 67 *)
         nilCsr "mhpmcounter5" (CsrIdWidth 'h"b05") accessMModeOnly; (* 68 *)
         nilCsr "mhpmcounter6" (CsrIdWidth 'h"b06") accessMModeOnly; (* 69 *)
         nilCsr "mhpmcounter7" (CsrIdWidth 'h"b07") accessMModeOnly; (* 70 *)
         nilCsr "mhpmcounter8" (CsrIdWidth 'h"b08") accessMModeOnly; (* 71 *)
         nilCsr "mhpmcounter9" (CsrIdWidth 'h"b09") accessMModeOnly; (* 72 *)
         nilCsr "mhpmcounter10" (CsrIdWidth 'h"b0a") accessMModeOnly; (* 73 *)
         nilCsr "mhpmcounter11" (CsrIdWidth 'h"b0b") accessMModeOnly; (* 74 *)
         nilCsr "mhpmcounter12" (CsrIdWidth 'h"b0c") accessMModeOnly; (* 75 *)
         nilCsr "mhpmcounter13" (CsrIdWidth 'h"b0d") accessMModeOnly; (* 76 *)
         nilCsr "mhpmcounter14" (CsrIdWidth 'h"b03") accessMModeOnly; (* 77 *)
         nilCsr "mhpmcounter15" (CsrIdWidth 'h"b0f") accessMModeOnly; (* 78 *)
         nilCsr "mhpmcounter16" (CsrIdWidth 'h"b10") accessMModeOnly; (* 79 *)
         nilCsr "mhpmcounter17" (CsrIdWidth 'h"b11") accessMModeOnly; (* 80 *)
         nilCsr "mhpmcounter18" (CsrIdWidth 'h"b12") accessMModeOnly; (* 81 *)
         nilCsr "mhpmcounter19" (CsrIdWidth 'h"b13") accessMModeOnly; (* 82 *)
         nilCsr "mhpmcounter20" (CsrIdWidth 'h"b14") accessMModeOnly; (* 83 *)
         nilCsr "mhpmcounter21" (CsrIdWidth 'h"b15") accessMModeOnly; (* 84 *)
         nilCsr "mhpmcounter22" (CsrIdWidth 'h"b16") accessMModeOnly; (* 85 *)
         nilCsr "mhpmcounter23" (CsrIdWidth 'h"b17") accessMModeOnly; (* 86 *)
         nilCsr "mhpmcounter24" (CsrIdWidth 'h"b18") accessMModeOnly; (* 87 *)
         nilCsr "mhpmcounter25" (CsrIdWidth 'h"b19") accessMModeOnly; (* 88 *)
         nilCsr "mhpmcounter26" (CsrIdWidth 'h"b1a") accessMModeOnly; (* 89 *)
         nilCsr "mhpmcounter27" (CsrIdWidth 'h"b1b") accessMModeOnly; (* 90 *)
         nilCsr "mhpmcounter28" (CsrIdWidth 'h"b1c") accessMModeOnly; (* 91 *)
         nilCsr "mhpmcounter29" (CsrIdWidth 'h"b1d") accessMModeOnly; (* 92 *)
         nilCsr "mhpmcounter30" (CsrIdWidth 'h"b1e") accessMModeOnly; (* 93 *)
         nilCsr "mhpmcounter31" (CsrIdWidth 'h"b1f") accessMModeOnly; (* 94 *)
         {| (* 95 *)
           csrName  := "mcycleh";
           csrAddr  := CsrIdWidth 'h"b80";
           csrViews
             := let fields := [ @csrFieldAny _ "mcycle" (Bit 64) (Bit 64) (Some (ConstBit (wzero 64))) ] in
                repeatCsrView 2
                  (@csrViewUpperReadXform _ fields)
                  (@csrViewUpperWriteXform _ fields);
           csrAccess := accessMModeOnly
         |};
         {| (* 96 *)
           csrName  := "minstreth";
           csrAddr  := CsrIdWidth 'h"b82";
           csrViews
             := let fields := [ @csrFieldAny _ "minstret" (Bit 64) (Bit 64) (Some (ConstBit (wzero 64))) ] in
                repeatCsrView 2
                  (@csrViewUpperReadXform _ fields)
                  (@csrViewUpperWriteXform _ fields);
           csrAccess := accessMModeOnly
         |};
         nilCsr "mhpmevent3" (CsrIdWidth 'h"323") accessMModeOnly; (* 97 *)
         nilCsr "mhpmevent4" (CsrIdWidth 'h"324") accessMModeOnly; (* 98 *)
         nilCsr "mhpmevent5" (CsrIdWidth 'h"325") accessMModeOnly; (* 99 *)
         nilCsr "mhpmevent6" (CsrIdWidth 'h"326") accessMModeOnly; (* 100 *)
         nilCsr "mhpmevent7" (CsrIdWidth 'h"327") accessMModeOnly; (* 101 *)
         nilCsr "mhpmevent8" (CsrIdWidth 'h"328") accessMModeOnly; (* 102 *)
         nilCsr "mhpmevent9" (CsrIdWidth 'h"329") accessMModeOnly; (* 103 *)
         nilCsr "mhpmevent10" (CsrIdWidth 'h"32a") accessMModeOnly; (* 104 *)
         nilCsr "mhpmevent11" (CsrIdWidth 'h"32b") accessMModeOnly; (* 105 *)
         nilCsr "mhpmevent12" (CsrIdWidth 'h"32c") accessMModeOnly; (* 106 *)
         nilCsr "mhpmevent13" (CsrIdWidth 'h"32d") accessMModeOnly; (* 107 *)
         nilCsr "mhpmevent14" (CsrIdWidth 'h"323") accessMModeOnly; (* 108 *)
         nilCsr "mhpmevent15" (CsrIdWidth 'h"32f") accessMModeOnly; (* 109 *)
         nilCsr "mhpmevent16" (CsrIdWidth 'h"330") accessMModeOnly; (* 110 *)
         nilCsr "mhpmevent17" (CsrIdWidth 'h"331") accessMModeOnly; (* 111 *)
         nilCsr "mhpmevent18" (CsrIdWidth 'h"332") accessMModeOnly; (* 112 *)
         nilCsr "mhpmevent19" (CsrIdWidth 'h"333") accessMModeOnly; (* 113 *)
         nilCsr "mhpmevent20" (CsrIdWidth 'h"334") accessMModeOnly; (* 114 *)
         nilCsr "mhpmevent21" (CsrIdWidth 'h"335") accessMModeOnly; (* 115 *)
         nilCsr "mhpmevent22" (CsrIdWidth 'h"336") accessMModeOnly; (* 116 *)
         nilCsr "mhpmevent23" (CsrIdWidth 'h"337") accessMModeOnly; (* 117 *)
         nilCsr "mhpmevent24" (CsrIdWidth 'h"338") accessMModeOnly; (* 118 *)
         nilCsr "mhpmevent25" (CsrIdWidth 'h"339") accessMModeOnly; (* 119 *)
         nilCsr "mhpmevent26" (CsrIdWidth 'h"33a") accessMModeOnly; (* 120 *)
         nilCsr "mhpmevent27" (CsrIdWidth 'h"33b") accessMModeOnly; (* 121 *)
         nilCsr "mhpmevent28" (CsrIdWidth 'h"33c") accessMModeOnly; (* 122 *)
         nilCsr "mhpmevent29" (CsrIdWidth 'h"33d") accessMModeOnly; (* 123 *)
         nilCsr "mhpmevent30" (CsrIdWidth 'h"33e") accessMModeOnly; (* 124 *)
         nilCsr "mhpmevent31" (CsrIdWidth 'h"33f") accessMModeOnly; (* 125 *)
         nilCsr "tselect" (CsrIdWidth 'h"7a0") accessMModeOnly; (* 126 *)
         nilCsr "tdata1" (CsrIdWidth 'h"7a1") accessMModeOnly; (* 127 *)
         nilCsr "tdata2" (CsrIdWidth 'h"7a2") accessMModeOnly; (* 128 *)
         nilCsr "tdata3" (CsrIdWidth 'h"7a3") accessMModeOnly; (* 129 *)
         {| (* 130 *)
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
         simpleCsr "dpc" (CsrIdWidth 'h"7b1") (width := Xlen) None accessDMode (* 131 *)
       ].

  Local Close Scope kami_expr.

End csrs.
