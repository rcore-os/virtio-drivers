arch := x86_64
target := x86_64-unknown-none
mode := release
kernel := target/$(target)/$(mode)/$(arch)
img := target/$(target)/$(mode)/img
accel ?= on
tcp ?= on
gl ?= off

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

# virgl (3D) testing requires a GL-capable QEMU; default to the plain 2D device
# so that hosts without GL support can still run the 2D example.
ifeq ($(gl), on)
	GPU_DEVICE := -device virtio-gpu-gl-pci,blob=on -display egl-headless
else
	GPU_DEVICE := -device virtio-gpu-pci
endif

QEMU_ARGS += \
	-machine q35 \
	-serial mon:stdio \
	-kernel $(kernel) \
	-fsdev local,id=fsdev0,path=$(PWD),security_model=none \
	$(GPU_DEVICE) -vga none \
	-device virtio-blk-pci,drive=x0 -drive file=$(img),if=none,format=raw,id=x0 \
	-device virtio-9p-pci,fsdev=fsdev0,mount_tag=p9_tmp \
	-device virtio-rng-pci \
	-device virtio-net-pci,netdev=net0 -netdev user,id=net0,hostfwd=tcp::5555-:5555

ifeq ($(accel), on)
	QEMU_ARGS += -cpu host -accel kvm
endif

.PHONY: kernel clean qemu run env

kernel:
	cargo build $(BUILD_ARGS) --config 'build.rustflags="--cfg platform=\"qemu\" -Clink-args=-Tlinker.ld -Clink-args=-no-pie"'

env:
	rustup component add llvm-tools-preview rustfmt
	rustup target add $(target)

asm: kernel
	$(objdump) -d $(kernel) | less

sym: kernel
	$(objdump) -t $(kernel) | less

header: kernel
	$(objdump) -x $(kernel) | less

clean:
	cargo clean

qemu: kernel $(img)
# Wait a few seconds, then try to open a connection to the VM so it can test its networking.
	( sleep 4 && echo "hello" | nc localhost 5555 -4 -w 1 -v) &
	qemu-system-$(arch) $(QEMU_ARGS)

$(img):
	dd if=/dev/zero of=$@ bs=512 count=32

run: qemu
