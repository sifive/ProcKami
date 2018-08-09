# !/bin/bash

fn="${1%.S}"

./doGenerate.sh
echo -ne "\x1B[31;1m"
riscv64-unknown-elf-as ${fn}.S -o ${fn}.elf
riscv64-unknown-elf-objcopy -O verilog ${fn}.elf ./MemoryInit.hex
echo -ne "\x1B[0m"
rm ${fn}.elf
rm -rf obj_dir
set -x
verilator --top-module system -Wno-CMPCONST -Wno-WIDTH --cc System.sv --trace --trace-underscore -Wno-fatal --exe System.cpp
make -j -C obj_dir -f Vsystem.mk Vsystem
./obj_dir/Vsystem

