`include "Processor.sv"
`include "Memory.sv"

module system(
    input CLK,
    input RESET
);
    wire [63:0] pc;
    wire [31:0] instr;
    wire iException;

    wire [1:0] memo;
    wire [63:0] addr;
    wire [63:0] data;
    wire [63:0] resp;
    wire [7:0] mask;
    wire mem_enable;
    wire dException;

    wire [63:0] lateAddr;
    wire [63:0] lateResp;
    wire lateException;

    wire void0;
    wire void1;

    struct packed {logic [1:0] memOp; logic [7:0] memMask; logic [63:0] memAdr; logic [63:0] memDat;} memCtrl;

    assign memo = memCtrl.memOp;
    assign mask = memCtrl.memMask;
    assign addr = memCtrl.memAdr;
    assign data = memCtrl.memDat;

    top theTop(.CLK(CLK), .RESET(RESET), .getInstr$Core0$_return(instr), .memAction$Core0$_return(resp),       .lateMemAction$Core0$_return(lateResp),
                                         .getInstr$Core0$_argument(pc),  .memAction$Core0$_argument(memCtrl),  .lateMemAction$Core0$_argument(lateAddr),
                                         .getInstr$Core0$_enable(void0), .memAction$Core0$_enable(mem_enable), .lateMemAction$Core0$_enable(void1)
              );

    mkRAM theRAM(.clk(CLK),           .reset(RESET),       .enable(mem_enable),
                 .pc(pc),             .instr(instr),       .iException(iException),
                 .lateAddr(lateAddr), .lateResp(lateResp), .lateException(lateException),
                 .addr(addr),         .resp(resp),         .dException(dException),
                   .data(data),         .memo(memo),         .mask(mask)
                );

endmodule

