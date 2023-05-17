/*
 * Code will start running at this symbol which is placed at the start of the
 * image.
 */
ENTRY(entry)

SECTIONS
{
	/*
	 * Collect together the code.
	 */
	.init : ALIGN(4096) {
		text_begin = .;
		*(.init.entry)
		*(.init.*)
	} >image
	.text : {
		*(.text.*)
	} >image
	text_end = .;

	/*
	 * Collect together read-only data.
	 */
	.rodata : ALIGN(4096) {
		rodata_begin = .;
		*(.rodata.*)
	} >image
	.got : {
		*(.got)
	} >image
	rodata_end = .;

	/*
	 * Collect together the read-write data including .bss at the end which
	 * will be zero'd by the entry code.
	 */
	.data : ALIGN(4096) {
		data_begin = .;
		*(.data.*)
		/*
		 * The entry point code assumes that .data is a multiple of 32
		 * bytes long.
		 */
		. = ALIGN(32);
		data_end = .;
	} >image

	/* Everything beyond this point will not be included in the binary. */
	bin_end = .;

	/* The entry point code assumes that .bss is 16-byte aligned. */
	.bss : ALIGN(16)  {
		bss_begin = .;
		*(.bss.*)
		*(COMMON)
		. = ALIGN(16);
		bss_end = .;
	} >image

	.stack (NOLOAD) : ALIGN(4096) {
		boot_stack_begin = .;
		. += 40 * 4096;
		. = ALIGN(4096);
		boot_stack_end = .;
	} >image

	. = ALIGN(4K);

	/*
	 * Remove unused sections from the image.
	 */
	/DISCARD/ : {
		/* The image loads itself so doesn't need these sections. */
		*(.gnu.hash)
		*(.hash)
		*(.interp)
		*(.eh_frame_hdr)
		*(.eh_frame)
		*(.note.gnu.build-id)
	}
}
