
    .text
    .globl _start
_start:
    jump #reset
    jump #nmi
    jump #error
    jump #0
    jump #tlbmissx
    jump #0
    jump #tlbmissrw

reset:
   r2 = #_dtb_loc
   memd(r2) = r1:0

   r2 = #emerged
   elr = r2
   rte

emerged:
# TODO: allocate a call stack, initialize SP and call `main` here:
   jump main
error:
nmi:
tlbmissx:
tlbmissrw:
   jump .


    .global _get_dtb_loc
_get_dtb_loc:
    r6 = #_dtb_loc
    r1:0 = memd(r6)
    jumpr r31

.align 8
_dtb_loc:
.quad 0x0

