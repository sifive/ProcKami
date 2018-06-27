#!/bin/bash

make -j

# Compile Kami and get into $moduleName
echo "Compiling Kami AST"
ghc --make ../Kami/PrettyPrintVerilog.hs
../Kami/PrettyPrintVerilog > Decoder.sv
