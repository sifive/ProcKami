/*
  This module simulates the 32 bit memory attached to the processor core.
*/
module memory32 (
  input clk,
  input reset,
  input in_write_enable,
  input [31:0] in_read_address,
  input [31:0] in_write_address,
  input [31:0] in_write_data,
  output [31:0] out_read_data,
  output out_reservation, // indicates whether or not a memory reservation was successfull 
  output out_read_exception,
  output out_write_exception
);

parameter integer numBlockBytes = 2 ^ 20;
reg [7:0] block [numBlockBytes:0];
initial $readmemh ("MemoryInit.hex", block);

/*
  This memory unit only supports 64 bit word requests. It returns
  an exception for any request that is not aligned to a 64 bit
  word boundary.

  Note: this restriction prevents 
*/
assign out_read_exception = (in_read_address >= numBlockBytes) || (in_read_address % 8 != 0);
assign out_write_exception = (in_write_address >= numBlockBytes) || (in_write_address % 8 != 0);

/*
  This memory model executes requests in the order in which they
  are recieved and all harts within the executing environment,
  accordingly see memory operations from other harts executing in
  program order. Accordingly, reservation requests always return
  true.
*/
assign out_reservation = 1;

// load operations.
assign out_read_data = {
  block [in_read_address + 7],
  block [in_read_address + 6],
  block [in_read_address + 5],
  block [in_read_address + 4],
  block [in_read_address + 3],
  block [in_read_address + 2],
  block [in_read_address + 1],
  block [in_read_address + 0]
};

/*
  store operations.

  The processor model assumes that each read and write operation
  reads and writes either 32 or 64 bit words depending on the
  processor's XLEN parameter. When the processor needs to write
  smaller units (such as bytes or half-words) it reads the entire
  32/64 bit word, modifies the relevant bits, and writes the entire
  word back as the result.
*/
always @(posedge clk)
begin
  if (in_write_enable && !reset)
  begin
    block [in_write_address] <= in_write_data [31:0];
  end
end
endmodule
