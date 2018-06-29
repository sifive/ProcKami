Require Import Kami.Extraction Decode.

Definition rtlMod := getRtl mkDecoder.
Extraction "Target.hs" RtlModule size rtlMod.

