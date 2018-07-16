.section .text
.global .main

main:
    ld      x1, 0x100(x0)
    addi    x2, x1, 0x001
    sd      x2, 0x100(x0)

    ld      x0, 0x100(x0)   # this should pass

    ld      x1, 0x100(x0)
    addi    x2, x1, 0x001
    sd      x2, 0x100(x0)

    ld      x0, 0x100(x0)   # this should fail
    j       .

. = 0x100
.ascii "1 DESSAP"
.ascii "DELIAF.."

. = 0x400
except:
    csrrw   x2, 0x341, x0
    addi    x3, x0, 0x00C
    beq     x2, x3, success

    ld      x1, 0x108(x0)
    j       .

success:
    ld      x1, 0x100(x0)
    addi    x4, x1, 0x001
    sd      x4, 0x100(x0)
    jalr    x0, x2, 0x004
