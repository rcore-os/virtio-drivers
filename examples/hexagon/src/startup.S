
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
   // Store incoming DTB pointer (r1:0) for later use
   r2 = #_dtb_loc
   memd(r2) = r1:0

   r2 = #emerged
   elr = r2
   rte

emerged:
   r29 = #(_stack_end)
   r28 = #(_stack)
   framelimit = r28
   r0 = #sbss
   r1 = #ebss
   call clear_bss

   r6 = #_dtb_loc
   r1:0 = memd(r6)
   call main
   stop(r0)
error:
nmi:
tlbmissx:
tlbmissrw:
   jump .


clear_bss:
    r2 = sub(r1, r0)
    p0 = cmp.eq(r2, #0)
    if (p0) jumpr r31
    r3 = #0
clear_bss_loop:
    memb(r0++#1) = r3
    r2 = add(r2, #-1)
    p0 = cmp.gt(r2, #0)
    if (p0) jump clear_bss_loop
    jumpr r31

.align 8
_dtb_loc:
.quad 0

.align 8
.globl _incoming_dtb
_incoming_dtb:
.quad 0

.section .bss.stack
.align 8
_stack:
.space 0x8000
_stack_end:

