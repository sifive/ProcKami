`include "Processor.sv"
`include "Memory.sv"

module system(
    input CLK,
    input RESET
);
    wire [63:0] pc;
    wire [31:0] instr;

    wire [1:0] memo;
    wire [63:0] addr;
    wire [63:0] data;
    wire [63:0] resp;
    wire [7:0] mask;
    wire void0;
    wire void1;
    wire void2;
    wire void3;

    struct packed {logic [1:0] memOp; logic [7:0] memMask; logic [63:0] memAdr; logic [63:0] memDat;} memCtrl;

    assign memo = memCtrl.memOp;
    assign mask = memCtrl.memMask;
    assign addr = memCtrl.memAdr;
    assign data = memCtrl.memDat;

    top theTop(.CLK(CLK), .RESET(RESET), .getInstr$_return(instr), .memAction$_return(resp),
        .getInstr$_argument(pc), .memAction$_argument(memCtrl), .getInstr$_enable(void0), .memAction$_enable(void1));

    mkRAM theRAM(.clk(CLK), .reset(RESET), .pc(pc), .addr(addr), .data(data), .memo(memo), .mask(mask),
          .instr(instr), .iException(void2), .resp(resp), .dException(void3));

endmodule
