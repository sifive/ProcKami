Require Import Kami.All.

Inductive InstFormat :=
| RType (opcode: word 7) (funct3: word 3) (funct7: word 7)
| IType (opcode: word 7) (funct3: word 3)
| SType (opcode: word 7) (funct3: word 3)
| BType (opcode: word 7) (funct3: word 3)
| UType (opcode: word 7)
| JType (opcode: word 7)
| Shift32Type (opcode: word 7) (funct3: word 3) (funct7: word 7)
| Shift64Type (opcode: word 7) (funct3: word 3) (funct6: word 6)
| FenceType
| EType (opcode: word 7) (funct12: word 12)
| CSRType (opcode: word 7) (funct3: word 3)
| CSRIType (oocode: word 7) (funct3: word 3)
| LRType (opcode: word 7) (funct3: word 3) (funct5: word 5)
| AMOType (opcode: word 7) (funct3: word 3) (funct5: word 5)
| R4Type (opcode: word 7) (funct2: word 2)
| FloatSingleRoundType (opcode: word 7) (funct5: word 5) (funct7: word 7)
| FloatSingleType (opcode: word 7) (funct5: word 5) (funct7: word 7) (funct3: word 3)
| FloatRoundType (opcode: word 7) (funct7: word 7).

Notation "k ## ty" := (LetExprSyntax ty k) (no associativity, at level 98, only parsing).


Section Ty.
  Variable ty: Kind -> Type.
  
  Record InstEntry ik ok :=
    { instName     : string ;
      instFormat   : InstFormat ;
      instSemantics: ik ## ty -> ok ## ty }.
  
  Record FUEntry :=
    { fuName: string ;
      input : Kind ;
      output: Kind ;
      instEntries: list (InstEntry input output) }.
End Ty.
