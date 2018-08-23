# !/bin/bash

echo -ne "\x1B[31;1m"
riscv64-unknown-elf-objcopy -O verilog "$1" ./MemoryInit.hex
sed -i '' 's/@800/@000/g;' ./MemoryInit.hex
echo -ne "\x1B[0m"
rm -rf obj_dir
verilator --top-module system -Wno-CMPCONST -Wno-WIDTH --cc System.sv --trace --trace-underscore -Wno-fatal --exe System.cpp
make -j -C obj_dir -f Vsystem.mk Vsystem
echo -e "\x1B[34;1mRunning $1\x1B[0m"
./obj_dir/Vsystem
