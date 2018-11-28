Require Import Kami.All InstFormat.

Local Open Scope char_scope.

Definition binDigitToNat (c : ascii) : option nat :=
  match c with
    | "0" => Some 0
    | "1" => Some 1
    | _   => None
  end.

Open Scope string_scope.

Fixpoint readBinAux (s : string) (acc : nat) : option nat :=
  match s with
    | "" => Some acc
    | String c s' =>
      match binDigitToNat c with
        | Some n => readBinAux s' (2 * acc + n)
        | None => None
      end
  end.

Definition readBinNat (s : string) : option nat := readBinAux s 0.

Goal readBinNat "01" = Some 1.
Proof. reflexivity. Qed.

Definition forceOption A Err (o : option A) (err : Err) : match o with
                                                            | Some _ => A
                                                            | None => Err
                                                          end :=
  match o with
    | Some a => a
    | None => err
  end.

Inductive parseError := ParseError.

Definition bin (s : string) := @forceOption nat parseError (readBinNat s) ParseError.

Notation "sz ''b' a" := (natToWord sz (bin a)) (at level 50).

Notation "''b' a" := (natToWord _ (bin a)) (at level 50).

Goal 'b"00001010" = WO~0~0~0~0~1~0~1~0.
Proof. reflexivity. Qed.

Goal 'b"1000001" = WO~1~0~0~0~0~0~1.
Proof. reflexivity. Qed.

Local Close Scope char_scope.


Section Alu.
  Variable n: nat.
  Variable ty: Kind -> Type.

  Definition AluType := STRUCT {"arg1" :: Bit n ; "arg2" :: Bit n}.

  Local Open Scope kami_expr.
  Definition AluEntry :=
    {| fuName := "alu" ;
       instEntries :=
         (Build_InstEntry "addi" (IType ('b"0010011") ('b"000"))
                          (fun i =>
                             LETE x: AluType <- i;
                             RetE ((#x @% "arg1") + (#x @% "arg2")))) :: nil
    |}.
  Local Close Scope kami_expr.
End Alu.