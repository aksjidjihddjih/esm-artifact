OUTPUT_ARCH(riscv)
ENTRY(_start)
/* 256 MiB flat RAM.  heap: [_heap_start, 0x0E000000)   input: 0x0E000000   output: 0x0F000000   stack top: 0x0FFF0000 */
MEMORY { RAM (rwx) : ORIGIN = 0x00010000, LENGTH = 0x0FFF0000 }
SECTIONS {
  .text   : { *(.text.init) *(.text .text.*) } > RAM
  .rodata : { *(.rodata .rodata.*) *(.srodata .srodata.*) } > RAM
  .data   : { *(.data .data.*) *(.sdata .sdata.*) } > RAM
  .bss (NOLOAD) : { *(.bss .bss.*) *(.sbss .sbss.*) *(COMMON) } > RAM
  . = ALIGN(16);
  _heap_start = .;
  _stack_top = 0x0FFF0000;
  /DISCARD/ : { *(.eh_frame) *(.eh_frame_hdr) *(.comment) *(.riscv.attributes) }
}
