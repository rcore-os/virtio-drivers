target := aarch64-unknown-none
mode := release
kernel := target/$(target)/$(mode)/aarch64
kernel_bin := target/$(target)/$(mode)/aarch64.bin

sysroot := $(shell rustc --print sysroot)
objdump := $(shell find $(sysroot) -name llvm-objdump) --arch-name=aarch64
objcopy := $(shell find $(sysroot) -name llvm-objcopy)

BUILD_ARGS += --target $(target)
ifeq ($(mode), release)
	BUILD_ARGS += --release
endif

.PHONY: kernel clean qemu run env

env:
	rustup component add llvm-tools-preview rustfmt
	rustup target add $(target)

kernel:
	cargo build $(BUILD_ARGS)

$(kernel_bin): kernel
	aarch64-linux-gnu-objcopy -O binary $(kernel) $(kernel_bin)

asm: kernel
	$(objdump) -d $(kernel) | less

sym: kernel
	$(objdump) -t $(kernel) | less

header: kernel
	$(objdump) -x $(kernel) | less

clean:
	cargo clean

qemu: $(kernel_bin)
	qemu-system-aarch64 \
		-machine virt \
		-cpu max \
		-serial mon:stdio \
		-kernel $(kernel_bin)

run: qemu
