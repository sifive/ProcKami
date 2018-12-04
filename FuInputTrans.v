(*
  TODO: Replace the optional packet type with the Maybe kind
  TODO: Use Kami notations where applicable.
  TODO: Replace ITEs with ORs. unpack (IF (input-uniqid == current-inst-id) then pack inputVal else 0 || ...)
  
*)
Require Import Kami.All.
Require Import FU.

Section input_trans.

Variable Xlen_over_8 : nat.

Variable ty : Kind -> Type.

Definition raw_inst_type : Type := LetExprSyntax ty Inst.

Definition func_unit_entry_type : Type := @FUEntry Xlen_over_8 ty.

Definition inst_entry_type (sem_input_kind sem_output_kind : Kind)
  := @InstEntry Xlen_over_8 ty sem_input_kind sem_output_kind.

Definition exec_context_packet_kind : Kind
  := ExecContextPkt Xlen_over_8.

Definition exec_context_packet_type : Type
  := Expr ty (SyntaxKind exec_context_packet_kind).

Definition exec_context_packet_expr_type : Type
  := LetExprSyntax ty exec_context_packet_kind.

Variable trans_optional_packet_enabled
  : forall sem_input_kind sem_output_kind : Kind,
    inst_entry_type sem_input_kind sem_output_kind ->
    exec_context_packet_expr_type ->
    LetExprSyntax ty Bool.

Definition optional_packet_kind (packet_kind : Kind) : Kind
  := STRUCT {"enabled" :: Bool; "packet" :: packet_kind}.

Definition optional_packet_type (packet_kind : Kind) : Type
  := Expr ty (SyntaxKind (optional_packet_kind packet_kind)).

Definition optional_packet_expr_type (packet_kind : Kind) : Type
  := LetExprSyntax ty (optional_packet_kind packet_kind).

Definition valid_packet_type (func_units : list func_unit_entry_type) : Type
  := {packet_kind : Kind |
       exists func_unit, In func_unit func_units /\
                         fuInputK func_unit = packet_kind}.

Definition valid_optional_packet_expr_type (func_units : list func_unit_entry_type) : Type
  := sigT (fun packet_kind : valid_packet_type func_units
            => optional_packet_expr_type (proj1_sig packet_kind)).

Open Scope kami_expr.

Definition optional_packet
  (packet_type : Kind)
  (input_packet : Expr ty (SyntaxKind packet_type))
  (enabled : Expr ty (SyntaxKind Bool))
  :  optional_packet_expr_type packet_type
  := RetE (
       STRUCT {
         "enabled" ::= enabled;
         "packet"  ::= input_packet
       }).

Definition trans_inst
  (sem_input_kind sem_output_kind : Kind)
  (inst_entry : inst_entry_type sem_input_kind sem_output_kind)
  (exec_context_packet : exec_context_packet_expr_type)
  :  optional_packet_expr_type sem_input_kind
  := LETE packet : sem_input_kind <- inputXform inst_entry exec_context_packet;
     LETE enabled : Bool <-
       trans_optional_packet_enabled
         inst_entry
         exec_context_packet;
     (optional_packet (#packet) (#enabled)).

Close Scope kami_expr.

Definition trans_insts (sem_input_kind sem_output_kind : Kind)
  : forall inst_entries : list (inst_entry_type sem_input_kind sem_output_kind),
    0 < length inst_entries ->
    exec_context_packet_expr_type ->
    optional_packet_expr_type sem_input_kind
  := list_rect
       (fun inst_entries
         => 0 < length inst_entries ->
            exec_context_packet_expr_type ->
            optional_packet_expr_type sem_input_kind)
       (fun H _
         => False_rect (optional_packet_expr_type sem_input_kind)
              ((Nat.nlt_0_r 0) H)) 
       (fun inst_entry inst_entries
         (F : 0 < length inst_entries ->
              exec_context_packet_expr_type ->
              optional_packet_expr_type sem_input_kind)
         _ exec_context_packet
         => sumbool_rect 
              (fun _ => optional_packet_expr_type sem_input_kind)
              (fun H : 0 < length inst_entries
                => (LETE inst_entry_packet
                     :  optional_packet_kind sem_input_kind
                     <- trans_inst inst_entry exec_context_packet;
                   LETE insts_entry_packet
                     :  optional_packet_kind sem_input_kind
                     <- F H exec_context_packet;
                   RetE ((ITE
                          (ReadStruct (#inst_entry_packet) Fin.F1) 
                          (#inst_entry_packet)
                          (#insts_entry_packet) : optional_packet_type sem_input_kind)))%kami_expr)
              (fun _ 
                => LETE inst_entry_packet
                     :  optional_packet_kind sem_input_kind
                     <- trans_inst inst_entry exec_context_packet;
                   RetE (#inst_entry_packet))%kami_expr
              (Compare_dec.lt_dec 0 (length inst_entries))).

Definition trans_func_unit
  (func_unit : func_unit_entry_type)
  (func_unit_insts_not_empty : 0 < length (fuInsts func_unit))
  (exec_context_packet : exec_context_packet_expr_type)
  :  optional_packet_expr_type (fuInputK func_unit)
  := list_rect
       (fun insts => 0 < length insts -> optional_packet_expr_type (fuInputK func_unit))
       (fun H : 0 < length nil
         => False_rect (optional_packet_expr_type (fuInputK func_unit))
              (Nat.nlt_0_r 0 H))
       (fun inst insts _ (H : 0 < length (inst :: insts))
         => trans_insts
              (inst :: insts)
              H
              exec_context_packet)
       (fuInsts func_unit)
       func_unit_insts_not_empty.

Definition vec_append (A : Set) (x : A) (n : nat) (ref : Fin.t n -> A) (k : Fin.t (S n))
  :  A
  := Fin.t_rec
       (fun m (_ : Fin.t m) => m = S n -> A)
       (fun m _ => x)
       (fun m index _ (H : S m = S n)
         => ref (@Fin.cast m index n (eq_add_S m n H)))
       (S n)
       k
       (eq_refl (S n)).

Definition trans_func_units_packet_kind (func_units : list func_unit_entry_type)
  :  0 < length func_units -> Kind
  := list_rec
       (fun func_units => 0 < length func_units -> Kind)
       (fun H : 0 < 0
         => False_rec _
              (Nat.nlt_0_r 0 H))
       (fun func_unit func_units
         (F : 0 < length func_units -> Kind)
         (_ : 0 < length (func_unit :: func_units))
         => sumbool_rec
              (fun _ => Kind)
              (fun H : 0 < length func_units
                => @Kind_rec
                     (fun _ => Kind)
                     (Bool)
                     (fun _ => Bool)
                     (fun n
                         (getKind : Fin.t n -> Kind)
                         (_ : Fin.t n -> Kind)
                         (getLabel : Fin.t n -> string)
                       => @Struct (S n)
                            (@vec_append Kind (optional_packet_kind (fuInputK func_unit)) n getKind)
                            (@vec_append string (fuName func_unit) n getLabel)
                            )
                     (fun _ _ _ => Bool) 
                     (F H))
              (fun _ : ~ 0 < length func_units
                => STRUCT {
                     (fuName func_unit) :: (optional_packet_kind (fuInputK func_unit))
                   })
              (Compare_dec.lt_dec 0 (length func_units)))
       func_units.

End input_trans.
