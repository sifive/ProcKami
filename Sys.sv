`include "Processor.sv"
`include "Memory.sv"

module system(
    input CLK,
    input RESET
);
    wire [63:0] pc;
    wire [31:0] instr;
    wire [1:0] iException;

    wire [1:0] memo;
    wire [63:0] addr;
    wire [63:0] data;
    wire [63:0] resp;
    wire [7:0] mask;
    wire mem_enable;
    wire [1:0] dException;

    wire void0;

    struct packed {logic [1:0] memOp; logic [7:0] memMask; logic [63:0] memAdr; logic [63:0] memDat;} memCtrl;
    struct packed {logic [31:0] instr; logic [1:0] fault;} iResp;
    struct packed {logic [63:0] data; logic [1:0] fault;} dResp;

    assign memo = memCtrl.memOp;
    assign mask = memCtrl.memMask;
    assign addr = memCtrl.memAdr;
    assign data = memCtrl.memDat;

    assign iResp.instr = instr;
    assign iResp.fault = iException;

    assign dResp.data = resp;
    assign dResp.fault = dException;

    top theTop(.CLK(CLK), .RESET(RESET), .getInstr$_return(iResp), .memAction$_return(dResp),
        .getInstr$_argument(pc), .memAction$_argument(memCtrl), .getInstr$_enable(void0), .memAction$_enable(mem_enable));

    mkRAM theRAM(.clk(CLK), .reset(RESET), .enable(mem_enable), .pc(pc), .addr(addr), .data(data), .memo(memo), .mask(mask),
          .instr(instr), .iException(iException), .resp(resp), .dException(dException));

endmodule
