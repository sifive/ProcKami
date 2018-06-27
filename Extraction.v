Require Import Kami.Extraction Decoder.

Definition rtlMod := getRtl mkDecoder.
Extraction "Target.hs" RtlModule size rtlMod.

