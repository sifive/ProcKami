# ProcKami

## Description

Reference implementation of **RV64I** and **RV32I** with **M** and **M+U** privilege modes.  
Future inclusion of the C, M, A, F, and D extensions is expected (in roughly that order).  
The feature set of the implementation is driven by SiFive's E2 core series.

## Building

ProcKami requires [Coq](https://coq.inria.fr), [bbv](https://github.com/mit-plv/bbv), and [Kami](https://github.com/sifive/Kami]). Extracting Verilog requires [GHC](https://www.haskell.org/downloads) and simulation requires [Verilator](https://www.veripool.org/wiki/verilator).

To compile the Coq objects, simply run `make`.

To synthesize Verilog, run `doGenerate.sh`.

To run programs
- with a .S extension, type `runS.sh FILENAME`
- in the ELF format, type `runELF.sh FILENAME`
- in the [riscv-tests](https://github.com/riscv/riscv-tests) suite, type `runRVtests.sh ISA-TEST-PATH`

(On our machine, `ISA-TEST-PATH` looks like `.../target/share/riscv-tests/isa/`)

## What's Included

ProcKami is organized in the way that most processors are, viz.:

**Decode** (_Decode.v, Control.v_)  
&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;**↓**  
**Execute** (_Execute1.v, Execute2.v_)  
&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;**↓**  
**Retire** (_Status.v_)

The file _CSR-types_ includes a table of fields found in RISC-V control status registers, and is useful to have in mind when reading _Status.v_.

The files _Processor.v_, _Memory.sv_, and _System.sv_ put all of these together.

## Known Issues
_Estimates for completion time given in parentheses._

- XLEN parametrization is not supported for CSRs (1 day).
- `SFENCE.VMA` instructions are not supported (4 hr).
- Access permission for some CSRs depends upon the contents of other CSRs (e.g. `mcounteren`); this is not currently supported (2–4 hr).
- Although User mode exists, it is not possible to switch into it (1 day).
- Most CSR special behavior is incomplete, although rudimentary exception handling works (1 wk).
- There is no mechanism for injecting interrupts (1–2 day).

For more details, see the `TODO`s sprinkled throughout the source.
