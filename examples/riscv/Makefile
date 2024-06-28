arch ?= riscv64
target := $(arch)imac-unknown-none-elf
mode := release
kernel := target/$(target)/$(mode)/riscv
img := target/$(target)/$(mode)/img

tcp ?= on

sysroot := $(shell rustc --print sysroot)
objdump := $(shell find $(sysroot) -name llvm-objdump) --arch-name=$(arch)
objcopy := $(shell find $(sysroot) -name llvm-objcopy)

BUILD_ARGS += --target $(target)
ifeq ($(mode), release)
	BUILD_ARGS += --release
endif

ifeq ($(tcp), on)
	BUILD_ARGS += --features tcp
else
	BUILD_ARGS += --no-default-features
endif

.PHONY: kernel build clean qemu run env

build: $(bin)

env:
	rustup component add llvm-tools-preview rustfmt
	rustup target add $(target)

kernel:
	cargo build $(BUILD_ARGS)

asm:
	$(objdump) -d $(kernel) | less

sym:
	$(objdump) -t $(kernel) | less

header:
	$(objdump) -x $(kernel) | less

clean:
	cargo clean

qemu-legacy: kernel $(img)
# Wait a few seconds, then try to open a connection to the VM so it can test its networking.
	( sleep 4 && echo "hello" | nc localhost 5555 -N -v) &
	qemu-system-$(arch) \
	  $(QEMU_ARGS) \
		-machine virt \
		-serial mon:stdio \
		-bios default \
		-kernel $(kernel) \
		-drive file=$(img),if=none,format=raw,id=x0 \
		-device virtio-blk-device,drive=x0 \
		-device virtio-gpu-device \
		-device virtio-mouse-device \
		-device virtio-net-device,netdev=net0 \
		-netdev user,id=net0,hostfwd=tcp::5555-:5555\
		-device virtio-sound-device,audiodev=audio0 \
		-audiodev alsa,id=audio0

qemu: kernel $(img)
# Wait a few seconds, then try to open a connection to the VM so it can test its networking.
	( sleep 4 && echo "hello" | nc localhost 5555 -N -v) &
	qemu-system-$(arch) \
	  $(QEMU_ARGS) \
		-machine virt \
		-serial mon:stdio \
		-bios default \
		-kernel $(kernel) \
		-global virtio-mmio.force-legacy=false \
		-drive file=$(img),if=none,format=raw,id=x0 \
		-device virtio-blk-device,drive=x0 \
		-device virtio-gpu-device \
		-device virtio-mouse-device \
		-device virtio-net-device,netdev=net0 \
		-netdev user,id=net0,hostfwd=tcp::5555-:5555\
		-device virtio-sound-device,audiodev=audio0 \
		-audiodev alsa,id=audio0

$(img):
	dd if=/dev/zero of=$@ bs=512 count=32

run: build qemu-legacy qemu
