Require Import Kami.All.
Require Import FU.
Require Import FuncUnits.MemUnit.

Section Params.
  Variable name: string.
  Local Notation "^ x" := (name ++ "_" ++ x)%string (at level 0).

  Variable Xlen_over_8: nat.
  Variable Flen_over_8: nat.
  Variable Clen_over_8: nat.
  Variable Rlen_over_8: nat.
  Variable mem_params : MemParamsType.
  Variable pmp_addr_ub : option (word 54).

  Local Notation Rlen := (Rlen_over_8 * 8).
  Local Notation Xlen := (Xlen_over_8 * 8).
  Local Notation Flen := (Flen_over_8 * 8).
  Local Notation CsrValueWidth := (Clen_over_8 * 8).
  Local Notation Data := (Bit Rlen).
  Local Notation VAddr := (Bit Xlen).
  Local Notation CsrValue := (Bit CsrValueWidth).
  Local Notation lgMemSz := (mem_params_size mem_params).
  Local Notation PAddrSz := (mem_params_addr_size mem_params).
  Local Notation FUEntry := (FUEntry Xlen_over_8 Rlen_over_8).
  Local Notation FetchPkt := (FetchPkt Xlen_over_8).
  Local Notation ExecContextPkt := (ExecContextPkt Xlen_over_8 Rlen_over_8).
  Local Notation ExecUpdPkt := (ExecUpdPkt Rlen_over_8).
  Local Notation PktWithException := (PktWithException Xlen_over_8).
  (* Local Notation DispNF := (DispNF Flen_over_8). *)
  (* Local Notation initXlen := (initXlen Xlen_over_8). *)
  (* Local Notation pMemDevice := (pMemDevice name Rlen_over_8 mem_params). *)
  (* Local Notation mMappedRegDevice := (mMappedRegDevice name Rlen_over_8 mem_params). *)

  Definition MemState := (Fin.t (pow2 lgMemSz) -> ConstT (Bit 8)).

  Record RegState: Type := mkRegState {
                               (* general context registers *)
                               mode: ConstT PrivMode;
                               pc: ConstT VAddr;
                               (* floating point registers *)
                               fflags: ConstT FflagsValue;
                               frm : ConstT FrmValue;
                               (* machine mode registers *)
                               mxl : ConstT XlenValue;
                               medeleg: ConstT (Bit 16);
                               mideleg: ConstT (Bit 12);
                               mprv: ConstT (Bool);
                               mpp: ConstT (Bit 2);
                               mpie: ConstT (Bool);
                               mie: ConstT (Bool);
                               mtvec_mode: ConstT (Bit 2);
                               mtvec_base: ConstT (Bit (Xlen - 2)%nat);
                               mscratch: ConstT (Bit Xlen);
                               mepc: ConstT (Bit Xlen);
                               mcause_interrupt: ConstT (Bool);
                               mcause_code: ConstT (Bit (Xlen - 1));
                               mtval: ConstT (Bit Xlen);

                               mvendorid: ConstT (Bit 32);
                               marchid: ConstT (Bit Xlen);
                               mimpid: ConstT (Bit Xlen);
                               mhartid: ConstT (Bit Xlen);

                               usip: ConstT (Bool);
                               ssip: ConstT (Bool);
                               msip: ConstT (Bool);
                               utip: ConstT (Bool);
                               stip: ConstT (Bool);
                               mtip: ConstT (Bool);
                               ueip: ConstT (Bool);
                               seip: ConstT (Bool);
                               meip: ConstT (Bool);
                               usie: ConstT (Bool);
                               ssie: ConstT (Bool);
                               msie: ConstT (Bool);
                               utie: ConstT (Bool);
                               stie: ConstT (Bool);
                               mtie: ConstT (Bool);
                               ueie: ConstT (Bool);
                               seie: ConstT (Bool);
                               meie: ConstT (Bool);

                               (* supervisor mode registers *)
                               sxl: ConstT (XlenValue);
                               sedeleg: ConstT (Bit 16);
                               sideleg: ConstT (Bit 16);
                               tsr: ConstT Bool;
                               tw: ConstT Bool;
                               tvm: ConstT (Bool);
                               mxr: ConstT (Bool);
                               sum: ConstT (Bool);
                               spp: ConstT (Bit 1);
                               spie: ConstT (Bool);
                               sie: ConstT (Bool);
                               stvec_mode: ConstT (Bit 2);
                               stvec_base: ConstT (Bit (Xlen - 2)%nat);
                               sscratch: ConstT (Bit Xlen);
                               sepc: ConstT (Bit Xlen);
                               scause_interrupt: ConstT (Bool);
                               scause_code: ConstT (Bit (Xlen - 1));
                               stval: ConstT (Bit Xlen);
                               satp_mode: ConstT (Bit 4);
                               satp_asid: ConstT (Bit 16);
                               satp_ppn: ConstT (Bit 44);

                               (* user mode registers *)
                               uxl: ConstT (XlenValue);
                               upp: ConstT (Bit 0);
                               upie: ConstT (Bool);
                               uie: ConstT (Bool);
                               utvec_mode: ConstT (Bit 2);
                               utvec_base: ConstT (Bit (Xlen - 2)%nat);
                               uscratch: ConstT (Bit Xlen);
                               uepc: ConstT (Bit Xlen);
                               ucause_interrupt: ConstT (Bool);
                               ucause_code: ConstT (Bit (Xlen - 1));
                               utval: ConstT (Bit Xlen);

                               (* preformance monitor registers *)
                               mtime: ConstT (Bit 64);
                               mtimecmp: ConstT (Bit 64);
                               mcounteren: ConstT (Bit 32);
                               scounteren: ConstT (Bit 32);
                               mcycle: ConstT (Bit 64);
                               minstret: ConstT (Bit 64);
                               mcountinhibit_cy: ConstT Bool;
                               mcountinhibit_tm: ConstT Bool;
                               mcountinhibit_ir: ConstT Bool;

                               (* memory protection registers; *)
                               pmp0cfg: ConstT (Bit 8);
                               pmp1cfg: ConstT (Bit 8);
                               pmp2cfg: ConstT (Bit 8);
                               pmp3cfg: ConstT (Bit 8);
                               pmp4cfg: ConstT (Bit 8);
                               pmp5cfg: ConstT (Bit 8);
                               pmp6cfg: ConstT (Bit 8);
                               pmp7cfg: ConstT (Bit 8);
                               pmp8cfg: ConstT (Bit 8);
                               pmp9cfg: ConstT (Bit 8);
                               pmp10cfg: ConstT (Bit 8);
                               pmp11cfg: ConstT (Bit 8);
                               pmp12cfg: ConstT (Bit 8);
                               pmp13cfg: ConstT (Bit 8);
                               pmp14cfg: ConstT (Bit 8);
                               pmp15cfg: ConstT (Bit 8);
                               pmpaddr0: ConstT (Bit 54);
                               pmpaddr1: ConstT (Bit 54);
                               pmpaddr2: ConstT (Bit 54);
                               pmpaddr3: ConstT (Bit 54);
                               pmpaddr4: ConstT (Bit 54);
                               pmpaddr5: ConstT (Bit 54);
                               pmpaddr6: ConstT (Bit 54);
                               pmpaddr7: ConstT (Bit 54);
                               pmpaddr8: ConstT (Bit 54);
                               pmpaddr9: ConstT (Bit 54);
                               pmpaddr10: ConstT (Bit 54);
                               pmpaddr11: ConstT (Bit 54);
                               pmpaddr12: ConstT (Bit 54);
                               pmpaddr13: ConstT (Bit 54);
                               pmpaddr14: ConstT (Bit 54);
                               pmpaddr15: ConstT (Bit 54);
                             }.

  Record ProcState: Type := 
    mkProcState {
        regState: RegState;
        memState: MemState;
      }.

  (* Option monad to make defining the below easier *)
  Delimit Scope monad_scope with monad.
  Local Definition ret {A} := @Some A.
  Local Definition bind {A} {B} (c1: option A) (c2: A -> option B) := match c1 with
                                           | None => None
                                           | Some v => c2 v
                                           end.
  Local Notation "x <- c1 ;; c2" := (@bind _ _ c1 (fun x => c2))
    (at level 61, c1 at next level, right associativity) : monad_scope.

  Local Open Scope monad_scope.
      
End Params.
