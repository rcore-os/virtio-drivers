arch ?= hexagon
target := $(arch)-unknown-none-elf
mode := release
kernel := target/$(target)/$(mode)/hexagon
img := target/$(target)/$(mode)/img
vsock_server_path := ../vsock_server
vsock_server_bin := $(vsock_server_path)/target/$(mode)/vsock_server

tcp ?= off

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

VSOCK_BUILD_ARGS =
ifeq ($(mode), release)
	VSOCK_BUILD_ARGS += --release
endif

.PHONY: kernel build clean qemu run env

build: $(bin)

env:
	rustup component add llvm-tools-preview rustfmt
	rustup target add $(target)

kernel:
	cargo +nightly build $(BUILD_ARGS)

$(vsock_server_bin):
	(cd $(vsock_server_path) && cargo +nightly build $(VSOCK_BUILD_ARGS))

asm:
	$(objdump) -d $(kernel) | less

sym:
	$(objdump) -t $(kernel) | less

header:
	$(objdump) -x $(kernel) | less

clean:
	cargo clean

qemu: kernel $(img)
# Wait a few seconds, then try to open a connection to the VM so it can test its networking.
	( sleep 4 && echo "hello" | nc localhost 5555 -N -v) &
	qemu-system-$(arch) \
	  $(QEMU_ARGS) \
		-machine virt \
		-nographic \
		-bios default \
		-kernel $(kernel) \
		-global virtio-mmio.force-legacy=false \
		-drive file=$(img),if=none,format=raw,id=x0 \
		-device virtio-blk-device,drive=x0 \
		-device virtio-rng-device \
		-netdev user,id=net0,hostfwd=tcp::5555-:5555 \
		-device virtio-net-device,netdev=net0 \


$(img):
	dd if=/dev/zero of=$@ bs=512 count=32

run: build qemu
