#touch Processor.v
#make -j
#ghc --make ../Kami/PrettyPrintVerilog.hs
../Kami/PrettyPrintVerilog > Processor.sv
verilator --top-module top -Wno-CMPCONST -Wno-WIDTH --cc Processor.sv --trace --trace-underscore -Wno-fatal --exe Processor.cpp
make -j -C obj_dir -f Vtop.mk Vtop
./obj_dir/Vtop
