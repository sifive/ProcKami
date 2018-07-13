# !/bin/bash
set -x

fn="${1%.S}"

make -j
ghc --make ../Kami/PrettyPrintVerilog.hs
../Kami/PrettyPrintVerilog > Processor.sv
riscv64-unknown-elf-as ${fn}.S -o ${fn}.elf
riscv64-unknown-elf-objcopy -O verilog ${fn}.elf ./MemoryInit.hex
rm ${fn}.elf
rm -rf obj_dir
verilator --top-module system -Wno-CMPCONST -Wno-WIDTH --cc Sys.sv --trace --trace-underscore -Wno-fatal --exe System.cpp
make -j -C obj_dir -f Vsystem.mk Vsystem
./obj_dir/Vsystem

