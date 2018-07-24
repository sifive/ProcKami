# !/bin/bash

make -j
ghc --make ../Kami/PrettyPrintVerilog.hs
../Kami/PrettyPrintVerilog > Processor.sv

