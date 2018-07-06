module mkRAM(input clk,

             input [63:0] pc,
             output [31:0] instr,
             output iException,

             input [63:0] addr,
             input [63:0] data,
             input wren,
             input [7:0] mask,
             output [63:0] resp,
             output dException
            );

    reg [7:0] block [1:0] [1048575:0];  // 1 MiB mapped to 0x0000,0000,0000,0000 - 0x0000,0000,000F,FFFF
                                        // 1 MiB mapped to 0x0000,0000,1000,0000 - 0x0000,0000,100F,FFFF
    initial begin
        $readmemb("ResetVector.bin", block[0]);
        $readmemb("ExceptionHandler.bin", block[1]);
    end

    assign iException = (pc[63:29] != 35'0) || (pc[27:20] != 8'0);
    assign dException = (addr[63:29] != 35'0) || (addr[27:20] != 8'0);

    wire ilevel = pc[28];
    wire dlevel = addr[28];

    // Instruction Read
    wire pcL = pc[19:0];

    assign instr = {block[ilevel][pcL+7], block[ilevel][pcL+6], block[ilevel][pcL+5], block[ilevel][pcL+4], block[ilevel][pcL+3], block[ilevel][pcL+2], block[ilevel][pcL+1], block[ilevel][pcL]}

    // Data Read
    wire adL = addr[19:0];
    assign resp = wren ? 64'0 : ({block[dlevel][adL+7], block[dlevel][adL+6], block[dlevel][adL+5], block[dlevel][adL+4], block[dlevel][adL+3], block[dlevel][adL+2], block[dlevel][adL+1], block[dlevel][adL]});

    // Data Writeback
    always @(posedge clk) begin
        if (wren) begin
            if (mask[7])
                block[dlevel][adL+7] <= data[63:56];
            if (mask[6])
                block[dlevel][adL+6] <= data[55:48];
            if (mask[5])
                block[dlevel][adL+5] <= data[47:40];
            if (mask[4])
                block[dlevel][adL+4] <= data[39:32];
            if (mask[3])
                block[dlevel][adL+3] <= data[31:24];
            if (mask[2])
                block[dlevel][adL+2] <= data[23:16];
            if (mask[1])
                block[dlevel][adL+1] <= data[15:8];
            if (mask[0])
                block[dlevel][adL]   <= data[7:0];
        end
    end
endmodule
