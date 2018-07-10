module mkRAM(input clk,
             input reset,

             input [63:0] pc,
             output reg [31:0] instr,
             output iException,

             input [63:0] addr,
             input [63:0] data,
             input [1:0] memo,
             input [7:0] mask,
             output [63:0] resp,
             output dException
            );

    reg [7:0] block [1048575:0];  // 1 MiB mapped to 0x0000,0000,0000,0000 - 0x0000,0000,000F,FFFF

    initial $readmemh("MemoryInit.hex", block);

    assign iException = (pc[63:20] != 44'0);
    assign dException = (addr[63:20] != 44'0);

    wire wren;
    assign wren = memo[0];

    // Instruction Read
    wire [19:0] pcL;
    assign pcL = pc[19:0];
    assign instr = {block[pcL+7], block[pcL+6], block[pcL+5], block[pcL+4], block[pcL+3], block[pcL+2], block[pcL+1], block[pcL]};

    // Data Read
    wire [19:0] adL;
    assign adL = addr[19:0];
    assign resp = wren ? 64'0 : ({block[adL+7], block[adL+6], block[adL+5], block[adL+4], block[adL+3], block[adL+2], block[adL+1], block[adL]});

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
