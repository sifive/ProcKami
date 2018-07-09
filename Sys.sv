`include "Processor.sv"
`include "Memory.sv"

module system(
    input CLK,
    input RESET
);
    wire [63:0] pc;
    wire [63:0] instr;

    wire wren;
    wire [63:0] addr;
    wire [63:0] data;
    wire [63:0] resp;
    wire [7:0] mask;
    wire void0;
    wire void1;
    wire void2;

    struct packed {logic memWrEn; logic [7:0] memMask; logic [63:0] memAdr; logic [63:0] memDat;} memCtrl;

    assign wren = memCtrl.memWrEn;
    assign mask = memCtrl.memMask;
    assign addr = memCtrl.memAdr;
    assign data = memCtrl.memDat;

    top theTop(.CLK(CLK), .RESET(RESET), .getInstr$_return(instr), .memAction$_return(resp),
        .getInstr$_argument(pc), .memAction$_argument(memCtrl), .getInstr$_enable(void0), .memAction$_enable(wren));

    mkRAM theRAM(.clk(CLK), .pc(pc), .addr(addr), .data(data), .wren(wren), .mask(mask),
          .instr(instr), .iException(void1), .resp(resp), .dException(void2));

endmodule
