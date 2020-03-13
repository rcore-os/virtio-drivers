arch ?= riscv64
target := $(arch)imac-unknown-none-elf
mode := release
kernel := target/$(target)/$(mode)/riscv
bin := target/$(target)/$(mode)/kernel.bin
img := target/$(target)/$(mode)/img

sysroot := $(shell rustc --print sysroot)
objdump := $(shell find $(sysroot) -name llvm-objdump) --arch-name=$(arch)
objcopy := $(shell find $(sysroot) -name llvm-objcopy)

BUILD_ARGS += --target $(target)
ifeq ($(mode), release)
	BUILD_ARGS += --release
endif

ifeq ($(arch), riscv32)
	START_ADDR := 0x80400000
else ifeq ($(arch), riscv64)
	START_ADDR := 0x80200000
endif

.PHONY: kernel build clean qemu run env

build: $(bin)

env:
	rustup component add llvm-tools-preview rustfmt
	rustup target add $(target)

kernel:
	cargo build $(BUILD_ARGS)

$(bin): kernel
	$(objcopy) $(kernel) --strip-all -O binary $@

asm:
	$(objdump) -d $(kernel) | less

sym:
	$(objdump) -t $(kernel) | less

header:
	$(objdump) -x $(kernel) | less

clean:
	cargo clean

qemu: $(bin) $(img)
	qemu-system-$(arch) \
		-machine virt \
		-serial mon:stdio \
		-bios default \
		-device loader,file=$(bin),addr=$(START_ADDR) \
		-drive file=$(img),if=none,format=raw,id=x0 \
		-device virtio-blk-device,drive=x0 \
		-device virtio-gpu-device \
		-device virtio-mouse-device

$(img):
	dd if=/dev/zero of=$@ bs=512 count=32

run: build qemu
