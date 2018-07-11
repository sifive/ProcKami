.section .text
.global .main

main:
    ld      x1, 0x100(x0)
    addi    x2, x0, 0x0AA
    sd      x2, 0x100(x0)

loop:
    j       loop

. = 0x100
msg:
.ascii "SSAP"

. = 0x400
except:
    j       except
