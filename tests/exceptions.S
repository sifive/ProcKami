.section .text
.global .main

#      x1   ASCII output: test number
#      x2   ASCII output: test name
#      x3   ASCII output: test result
#      x4   Link register
#      x7   Expected exception cause
#      x8   Exception handler scratch register
#      x9   Alternate return register
# x16-x31   Program scratch registers (not guaranteed to be saved)

# Test Listing
#
#   #0  Instruction address misaligned
#   #1  Instruction access fault
#   #2  Illegal instruction: attempt to write a read-only CSR
#   #3  Illegal instruction: attempt to access a debug-reserved CSR
#   #4  Illegal instruction: attempt to access a non-existent CSR
#   #5  Breakpoint
#   #6  Environment call from M mode
#   #7  Load access fault

main:
    li      x16, 0x400
    csrw    mtvec, x16

test0:
    addi    x7, x0, 0x000   # set expected [mcause]
    jalr    x4, x0, 0x300   # call header
    j       .+0x002

test1:
    addi    x7, x0, 0x001   # set expected [mcause]
    jalr    x4, x0, 0x300   # call header
    addi    x9, x0, 0x030   # set return address
    jalr    x0, x0,-0x004
    j       halt

. = 0x030
test2:
    addi    x7, x0, 0x002   # set expected [mcause]
    jalr    x4, x0, 0x300   # call header
    csrrw   x16,0xF11,x16

test3:
    addi    x7, x0, 0x002   # set expected [mcause]
    jalr    x4, x0, 0x300   # call header
    csrrw   x16,0x7A1,x16

test4:
    addi    x7, x0, 0x002   # set expected [mcause]
    jalr    x4, x0, 0x300   # call header
    csrrw   x16,0x000,x16

test5:
    addi    x7, x0, 0x003   # set expected [mcause]
    jalr    x4, x0, 0x300   # call header
    ebreak

test6:
    addi    x7, x0, 0x00B   # set expected [mcause]
    jalr    x4, x0, 0x300   # call header
    ecall

test7:
    addi    x7, x0, 0x005   # set expected [mcause]
    jalr    x4, x0, 0x300   # call header
    ld      x16,-0x004(x0)

halt:
    ld      x16, 0x200(x0)
    addi    x16, x16, -1
    slli    x17, x16, 56
    ld      x16, 0x228(x0)

    ld      x18, 0x208(x0)
    addi    x18, x18, -1
    slli    x19, x18, 56
    ld      x18, 0x230(x0)

    ld      x1, 0x220(x0)
    add     x2, x18, x19
    add     x3, x16, x17

resultGood:
    ld      x16, 0x200(x0)
    andi    x16, x16, 0x0FF
    addi    x16, x16, -0x031
    addi    x17, x0, 8
    bne     x16, x17, resultBad

    ld      x16, 0x208(x0)
    andi    x16, x16, 0x0FF
    addi    x16, x16, -0x031
    bne     x16, x0, resultBad

    ld      x2, 0x238(x0)
    ld      x3, 0x240(x0)
    j       .

resultBad:
    ld      x2, 0x238(x0)
    ld      x3, 0x248(x0)
    j       .

. = 0x200
.ascii "1 DESSAP"   # 200
.ascii "1 DELIAF"   # 208
.ascii "0 # TSET"   # 210
.ascii "0 NTPCXE"   # 218
.ascii "  DETLAH"   # 220
.ascii "SSAP 8/"    # 228
    .byte 0
.ascii "LIAF 8/"    # 230
    .byte 0
.ascii " STLUSER"   # 238
.ascii "    YAKO"   # 240
.ascii "YAKO TON"   # 248

. = 0x300
header:
    addi    x3,  x0, 0x000  # clear test result
    ld      x1,  0x210(x0)  # display test number
    addi    x16, x1, 0x001  # increment test counter
    sd      x16, 0x210(x0)

    ld      x16, 0x218(x0)
    add     x2, x7, x16     # display test name

    jalr    x0, x4, 0x000   # return to main

. = 0x400
handler:
    csrrw   x8, 0x342, x0   # load and clear [mcause]
    beq     x7, x8, success # is [mcause] what we expect?

failure:
    ld      x3, 0x208(x0)   # display test result
    addi    x8, x3, 0x001   # increment fail counter
    sd      x8, 0x208(x0)
    j       return

success:
    ld      x3, 0x200(x0)   # display test result
    addi    x8, x3, 0x001   # increment pass counter
    sd      x8, 0x200(x0)

return:
    beq     x0, x9, normal  # if a special return address is given, use that instead of [mepc]+4
    addi    x8, x9, 0x000
    addi    x9, x0, 0x000
    jalr    x0, x8, 0x000
normal:
    csrrw   x8, 0x341, x0   # load and clear [mepc]
    andi    x8, x8,-0x004   # clear lower two bits to obtain legal address
    jalr    x0, x8, 0x004   # return to main
