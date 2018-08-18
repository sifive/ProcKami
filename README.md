# ProcKami

## Description

Reference implementation of **RV64I** and **RV32I** with **M** and **M+U** privilege modes.  
Future inclusion of the C, M, A, F, and D extensions is expected (in roughly that order).

## Building

ProcKami requires [Coq](https://coq.inria.fr), [bbv](https://github.com/mit-plv/bbv), and [Kami](https://github.com/sifive/Kami]). Extracting Verilog requires [GHC](https://www.haskell.org/downloads) and simulation requires [Verilator](https://www.veripool.org/wiki/verilator).

To compile the Coq objects, simply run `make`.

To synthesize Verilog, run `doGenerate.sh`.

To run programs
- with a .S extension, type `runS.sh FILENAME`
- in the ELF format, type `runELF.sh FILENAME`
- in the [riscv-tests](https://github.com/riscv/riscv-tests) suite, type `runRVtests.sh ISA-TEST-PATH`

(On our machine, `ISA-TEST-PATH` looks like `.../target/share/riscv-tests/isa/`)

## Known Issues

- `SFENCE.VMA` instructions are not supported.
- Access permission for some CSRs depends upon the contents of other CSRs (e.g. `mcounteren`); this is not currently supported.
- Although User mode exists, it is not possible to switch into it.
- Most CSR special behavior is incomplete, although rudimentary exception handling works.
- There is no mechanism for injecting interrupts.
- `minstret` increments on discarded (exception-causing) instructions
