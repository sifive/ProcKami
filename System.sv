/*
  This module combines the register, memory, and procesor cores
  into a composite system model.
*/
`include "Processor.sv"
`include "Memory32.sv"
`include "Register32.sv"

module system(
  input clk,
  input reset
);

// Fetch wires.

logic fetch_enable;
logic[31:0] fetch_address_req;

struct packed {
  logic[31:0] inst;
  struct packed {
    logic valid;
    struct packed {
      logic[3:0] exception;
      logic[31:0] value;
    } data;
  } exception;
} fetch_res;

// Register read wires.

wire logic read_reg_1_enable_req;
wire logic read_reg_2_enable_req;
wire logic read_freg_1_enable_req;
wire logic read_freg_2_enable_req;
wire logic read_freg_3_enable_req;

wire logic[4:0] read_reg_1_id_req;
wire logic[4:0] read_reg_2_id_req;
wire logic[4:0] read_freg_1_id_req;
wire logic[4:0] read_freg_2_id_req;
wire logic[4:0] read_freg_3_id_req;

wire logic[31:0] read_reg_1_res;
wire logic[31:0] read_reg_2_res;
wire logic[31:0] read_freg_1_res;
wire logic[31:0] read_freg_2_res;
wire logic[31:0] read_freg_3_res;

// Register write wires.

struct packed {
  logic[4:0] index;
  logic[31:0] data;
} proc_core_regWrite_req;

struct packed {
  logic[4:0] index;
  logic[31:0] data;
} proc_core_fregWrite_req;

struct packed {
  logic[11:0] index;
  logic[31:0] data;
} proc_core_csrWrite_req;

wire logic proc_core_regWrite_enable_req;
wire logic proc_core_fregWrite_enable_req;
wire logic proc_core_csrWrite_enable_req;

// Memory wires

wire logic[31:0] memRead_address_req;
wire logic memRead_enable_req;

struct packed {
  logic[31:0] data;
  logic[1:0] reservation;
  struct packed {
    logic valid;
    logic[3:0] data;
  } exception$;
} memRead_res;

struct packed {
  logic[31:0] addr;
  logic[31:0] data;
} memWrite_req;

wire logic memWrite_enable_req;

struct packed {
  logic valid;
  logic[3:0] data;
} memWrite_res;

// System components and connections

top system (
  fetch_res,
  read_reg_1_res,
  read_reg_2_res,
  read_freg_1_res,
  read_freg_2_res,
  read_freg_3_res,
  memRead_res,
  memWrite_res,

  fetch_address_req,
  read_reg_1_res,
  read_reg_2_res,
  read_freg_1_res,
  read_freg_2_res,
  read_freg_3_res,
  memRead_address_req,
  memWrite_req,
  proc_core_regWrite_req,
  proc_core_fregWrite_req,
  proc_core_csrWrite_req,
  fetch_enable.
  read_reg_1_enable_req,
  read_reg_2_enable_req,
  read_freg_1_enable_req,
  read_freg_2_enable_req,
  read_freg_3_enable_req,
  memRead_enable_req,
  memWrite_enable_req,
  proc_core_regWrite_enable_req,
  proc_core_fregWrite_enable_req,
  proc_core_csrWrite_enable_req,
  .CLK(clk),
  .RESET(reset),
);

(* TODO: wire up exceptions. *)
(* TODO: WARNING: compressed instructions will trigger misaligned exceptions using this memory module. *)

wire program_memory_void0;
wire program_memory_void1;
wire program_memory_void2;
wire program_memory_void3;
wire program_memory_void4;

memory32 program_memory (
  .clk (clk),
  .reset (reset),
  .in_write_enable (fetch_enable),
  .in_read_address (fetch_address_req),
  .in_write_address (program_memory_void0),
  .in_write_data (program_memory_void1),
  .out_read_data (fetch_res.inst),
  .out_reservation (program_memory_void2),
  .out_read_exception (program_memory_void3),
  .out_write_exception (program_memory_void4)
);

(* TODO: add a second excetion flag to the memory unit so that it can signal exceptions for reads and writes seperately. *)

wire ram_void0;
wire ram_void1;

memory32 ram (
  .clk (clik),
  .reset (reset),
  .in_write_enable (memRead_enable_req),
  .in_read_address (memRead_address_req),
  .in_write_address (memWrite_req.addr),
  .in_write_data (memWrite_req.data),
  .out_read_data (memRead_res.data),
  .out_reservation (memRead_res.reservation),
  .out_read_exception (ram_void0),
  .out_write_exception (ram_void1)
);

wire register_void0;
wire register_void1;

register32 registers (
  .clk (clik),
  .reset (reset),
  .in_write_enable (proc_core_regWrite_enable_req),
  .in_write_register_select (proc_core_regWrite_req.index), (* TODO: check bit width *)
  .in_read_register_select_0 (read_reg_1_id_req),
  .in_read_register_select_1 (read_reg_2_id_req),
  .in_read_register_select_2 (register_void0),
  .in_write_data (proc_core_regWrite_req.data),
  .out_read_data_0 (read_reg_1_res),
  .out_read_data_1 (read_reg_2_res),
  .out_read_data_2 (register_void1)
);

register32 fp_registers (
  .clk (clik),
  .reset (reset),
  .in_write_enable (proc_core_regWrite_enable_req),
  .in_write_register_select (proc_core_fregWrite_req.index), (* TODO: check bit width *)
  .in_read_register_select_0 (read_freg_1_id_req),
  .in_read_register_select_1 (read_freg_2_id_req),
  .in_read_register_select_2 (read_freg_2_id_req),
  .in_write_data (proc_core_fregWrite_req.data),
  .out_read_data_0 (read_reg_1_res),
  .out_read_data_1 (read_reg_2_res),
  .out_read_data_2 (read_reg_2_res)
);

endmodule
