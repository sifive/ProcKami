/*
  This module combines the register, memory, and procesor cores
  into a composite system model.
*/
`include "Processor.sv"
`include "Memory32.sv"
`include "Register32.sv"

module system(
  input CLK,
  input RESET
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
  .fetch$_return(fetch_res),
  .read_reg_1$_return(read_reg_1_res),
  .read_reg_2$_return(read_reg_2_res),
  .read_freg_1$_return(read_freg_1_res),
  .read_freg_2$_return(read_freg_2_res),
  .read_freg_3$_return(read_freg_3_res),
  memRead_res,
  memWrite_res,
  .fetch$_argument(fetch_address_req),
  .read_reg_1$_argument(read_reg_1_res),
  .read_reg_2$_argument(read_reg_2_res),
  .read_freg_1$_argument(read_freg_1_res),
  .read_freg_2$_argument(read_freg_2_res),
  .read_freg_3$_argument(read_freg_3_res),
  memRead_address_req,
  memWrite_req,
  .proc_core_regWrite$_argument(proc_core_regWrite_req),
  .proc_core_fregWrite$_argument(proc_core_fregWrite_req),
  .proc_core_csrWrite$_argument(proc_core_csrWrite_req),
  .fetch$_enable(fetch_enable),
  .read_reg_1$_enable(read_reg_1_enable_req),
  .read_reg_2$_enable(read_reg_2_enable_req),
  .read_freg_1$_enable(read_freg_1_enable_req),
  .read_freg_2$_enable(read_freg_2_enable_req),
  .read_freg_3$_enable(read_freg_3_enable_req),
  memRead_enable_req,
  memWrite_enable_req,
  .proc_core_regWrite$_enable(proc_core_regWrite_enable_req),
  .proc_core_fregWrite$_enable(proc_core_fregWrite_enable_req),
  .proc_core_csrWrite$_enable(proc_core_csrWrite_enable_req),
  .CLK(CLK),
  .RESET(RESET)
);

(* TODO: wire up exceptions. *)

wire ram_void0;
wire ram_void1;
wire ram_void2;

memory32 ram (
  .clk (CLK),
  .reset (RESET),
  .in_fetch_enable (fetch_enable),
  .in_write_enable (memRead_enable_req),
  .in_fetch_address (fetch_address_req),
  .in_read_address (memRead_address_req),
  .in_write_address (memWrite_req.addr),
  .in_write_data (memWrite_req.data),
  .out_fetch_data (fetch_res.inst),
  .out_read_data (memRead_res.data),
  .out_reservation (memRead_res.reservation),
  .out_fetch_exception (ram_void0),
  .out_read_exception (ram_void1),
  .out_write_exception (ram_void2)
);

wire register_void0;
wire register_void1;

register32 registers (
  .clk (CLK),
  .reset (RESET),
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
  .clk (CLK),
  .reset (RESET),
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
