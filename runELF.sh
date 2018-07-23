# !/bin/bash

#for f in $1/rv64ui-p-*.dump

echo -ne "\x1B[31;1m"
riscv64-unknown-elf-objcopy -O verilog "$1" ./MemoryInit.hex
sed -i '' 's/@800/@000/g;' ./MemoryInit.hex
echo -ne "\x1B[0m"
rm -rf obj_dir
#set -x
verilator --top-module system -Wno-CMPCONST -Wno-WIDTH --cc Sys.sv --trace --trace-underscore -Wno-fatal --exe System.cpp
make -j -C obj_dir -f Vsystem.mk Vsystem
./obj_dir/Vsystem

