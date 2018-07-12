.section .text
.global .main

main:
    addi    x1, x0, 0x001
    addi    x1, x1, -0x001
    addi    x1, x1, -0x001
    addi    x2, x1, -0x001
    addi    x0, x1, 0x000

. = 0x400
loop:
    j       loop
