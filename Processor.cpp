#include "verilated.h"
#include <iostream>
#include <cstdio>
#include <cstdlib>
#include "verilated_vcd_c.h"

#include "Vtop.h"

int main(int argc, char ** argv, char **env) {
  Verilated::commandArgs(argc, argv);
  Verilated::traceEverOn(true);

  Vtop* top = new Vtop;
  VerilatedVcdC* tfp = new VerilatedVcdC;
  top->trace(tfp,99);
  tfp->open("trace.vcd");

  
  uint32_t in;
  uint8_t roundMode;

  uint8_t outtop_exp, outchisel_exp, outtop_flags, outchisel_flags;
  uint32_t outtop_sig, outchisel_sig;
  bool outtop_sign, outchisel_sign, tiny;

  vluint64_t main_time = 0;
  int ready_chisel = 0;
  int ready_top = 0;
  uint32_t outtop, outchisel;

  uint64_t iMem = 240;
  uint64_t dMem = 0;


  while(!Verilated::gotFinish() && main_time < 1000){
    top->CLK = main_time%2;
    if(main_time < 10)
      top->RESET = 1;
    else top->RESET = 0;
    
    top->eval();

    printf("inst: %x\n", top->getInstr__024_argument);
    top->getInstr__024_return = iMem;
    iMem ++;

    top->eval();

    printf("memAction_en: %d\n", top->memAction__024_enable);
    printf("memAction_argument %x%x%x%x%x\n",
      top->memAction__024_argument[4],
      top->memAction__024_argument[3],
      top->memAction__024_argument[2],
      top->memAction__024_argument[1],
      top->memAction__024_argument[0]
    );
    top->memAction__024_return = dMem;
    dMem ++;

    tfp->dump(main_time);
    main_time++;
  }

  tfp->dump(main_time);

  top->final();
  tfp->close();
  delete top;
  delete tfp;
  return 0;
}
