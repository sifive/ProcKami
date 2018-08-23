module mkRAM(input clk,
             input reset,
             input enable,

             input [63:0] pc,           // Read port
             output reg [31:0] instr,
             output iException,

             input [63:0] addr,         // Read-Write port
             input [63:0] data,
             input [1:0] memo,
             input [7:0] mask,
             output [63:0] resp,
             output dException,

             input [63:0] lateAddr,     // Read port
             output [63:0] lateResp,
             output lateException
            );

    reg [7:0] block [1048575:0];  // 1 MiB mapped to 0x0000,0000,0000,0000 - 0x0000,0000,000F,FFFF

    initial $readmemh("MemoryInit.hex", block);

    wire iOutOfBounds;
    wire dOutOfBounds;
    wire lOutOfBounds;
    assign iOutOfBounds = ({pc[63:32], pc[30:20]} != 43'0);    // Allows instructions in the ranges 0x0000,0000,000x,xxxx
    assign dOutOfBounds = ({addr[63:32], addr[30:20]} != 43'0); // and 0x0000,0000,800x,xxxx. NOTE that they shadow each other.
    assign lOutOfBounds = ({lateAddr[63:32], lateAddr[30:20]} != 43'0);

    assign iException = iOutOfBounds;
    assign dException = dOutOfBounds;
    assign lateException = lOutOfBounds;

    wire wren;
    assign wren = memo[0] && enable;

    // Instruction Read
    wire [19:0] pcL;
    assign pcL = pc[19:0];
    assign instr = {block[pcL+7], block[pcL+6], block[pcL+5], block[pcL+4], block[pcL+3], block[pcL+2], block[pcL+1], block[pcL]};

    // Data Read
    wire [19:0] adL;
    assign adL = addr[19:0];
    assign resp = ({block[adL+7], block[adL+6], block[adL+5], block[adL+4], block[adL+3], block[adL+2], block[adL+1], block[adL]});
    //assign resp = (memo[0] || !enable) ? 64'0 : ({block[adL+7], block[adL+6], block[adL+5], block[adL+4], block[adL+3], block[adL+2], block[adL+1], block[adL]});

    // Data Read
    wire [19:0] laL;
    assign laL = lateAddr[19:0];
    assign lateResp = ({block[laL+7], block[laL+6], block[laL+5], block[laL+4], block[laL+3], block[laL+2], block[laL+1], block[laL]});

    // Data Writeback
    always @(posedge clk) begin
        if (wren && !reset) begin
            if (mask[7])
                block[adL+7] <= data[63:56];
            if (mask[6])
                block[adL+6] <= data[55:48];
            if (mask[5])
                block[adL+5] <= data[47:40];
            if (mask[4])
                block[adL+4] <= data[39:32];
            if (mask[3])
                block[adL+3] <= data[31:24];
            if (mask[2])
                block[adL+2] <= data[23:16];
            if (mask[1])
                block[adL+1] <= data[15:8];
            if (mask[0])
                block[adL]   <= data[7:0];
        end
    end
endmodule
