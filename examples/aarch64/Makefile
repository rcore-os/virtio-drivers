target := aarch64-unknown-none
mode := release
kernel := target/$(target)/$(mode)/aarch64
kernel_bin := target/$(target)/$(mode)/aarch64.bin
img := target/$(target)/$(mode)/img

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

qemu: $(kernel_bin) $(img)
	qemu-system-aarch64 \
	  $(QEMU_ARGS) \
		-machine virt \
		-cpu max \
		-serial chardev:char0 \
		-kernel $(kernel_bin) \
		-global virtio-mmio.force-legacy=false \
		-nic none \
		-drive file=$(img),if=none,format=raw,id=x0 \
		-device virtio-blk-device,drive=x0 \
		-device virtio-gpu-device \
		-device virtio-serial,id=virtio-serial0 \
		-chardev stdio,id=char0,mux=on \
		-device virtconsole,chardev=char0

qemu-pci: $(kernel_bin) $(img)
	qemu-system-aarch64 \
		-machine virt \
		-cpu max \
		-serial chardev:char0 \
		-kernel $(kernel_bin) \
		-nic none \
		-drive file=$(img),if=none,format=raw,id=x0 \
		-device virtio-blk-pci,drive=x0 \
		-device virtio-gpu-pci \
		-device virtio-serial,id=virtio-serial0 \
		-chardev stdio,id=char0,mux=on \
		-device virtconsole,chardev=char0

$(img):
	dd if=/dev/zero of=$@ bs=512 count=32

run: qemu
