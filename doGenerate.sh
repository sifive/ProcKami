#touch Processor.v
#make -j
#ghc --make ../Kami/PrettyPrintVerilog.hs
#../Kami/PrettyPrintVerilog > Processor.sv
verilator --top-module system -Wno-CMPCONST -Wno-WIDTH --cc Sys.sv --trace --trace-underscore -Wno-fatal --exe System.cpp
make -j -C obj_dir -f Vsystem.mk Vsystem
./obj_dir/Vsystem
