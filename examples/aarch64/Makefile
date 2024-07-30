target := aarch64-unknown-none
mode := release
kernel := target/$(target)/$(mode)/aarch64
kernel_qemu_bin := target/$(target)/$(mode)/aarch64_qemu.bin
kernel_crosvm_bin := target/$(target)/$(mode)/aarch64_crosvm.bin
img := target/$(target)/$(mode)/img
vsock_server_path := ../vsock_server
vsock_server_bin := $(vsock_server_path)/target/$(mode)/vsock_server

sysroot := $(shell rustc --print sysroot)
objdump := $(shell find $(sysroot) -name llvm-objdump) --arch-name=aarch64
objcopy := $(shell find $(sysroot) -name llvm-objcopy)

BUILD_ARGS += --target $(target)
ifeq ($(mode), release)
	BUILD_ARGS += --release
endif

VSOCK_BUILD_ARGS =
ifeq ($(mode), release)
	VSOCK_BUILD_ARGS += --release
endif

.PHONY: kernel clean qemu run env

env:
	rustup component add llvm-tools-preview rustfmt
	rustup target add $(target)

kernel_qemu:
	cargo clean
	cargo build $(BUILD_ARGS) --config 'build.rustflags="--cfg platform=\"qemu\""'

kernel_crosvm:
	cargo clean
	cargo build $(BUILD_ARGS) --config 'build.rustflags="--cfg platform=\"crosvm\""'

$(kernel_qemu_bin): kernel_qemu
	aarch64-linux-gnu-objcopy -O binary $(kernel) $(kernel_qemu_bin)

$(kernel_crosvm_bin): kernel_crosvm
	aarch64-linux-gnu-objcopy -O binary $(kernel) $(kernel_crosvm_bin)

$(vsock_server_bin):
	(cd $(vsock_server_path) && cargo build $(VSOCK_BUILD_ARGS))

asm: kernel
	$(objdump) -d $(kernel) | less

sym: kernel
	$(objdump) -t $(kernel) | less

header: kernel
	$(objdump) -x $(kernel) | less

clean:
	cargo clean

# This target is used to test the vsock driver manually. See vsock_server/README.md
# for more information.
qemu-vsock: $(kernel_qemu_bin) $(img)
	qemu-system-aarch64 \
	  $(QEMU_ARGS) \
		-machine virt \
		-cpu max \
		-serial chardev:char0 \
		-kernel $(kernel_qemu_bin) \
		-global virtio-mmio.force-legacy=false \
		-nic none \
		-drive file=$(img),if=none,format=raw,id=x0 \
		-device vhost-vsock-device,id=virtiosocket0,guest-cid=102 \
		-chardev stdio,id=char0,mux=on

qemu: $(kernel_qemu_bin) $(img) $(vsock_server_bin)
	$(vsock_server_bin) &
	qemu-system-aarch64 \
	  $(QEMU_ARGS) \
		-machine virt \
		-cpu max \
		-serial chardev:char0 \
		-kernel $(kernel_qemu_bin) \
		-global virtio-mmio.force-legacy=false \
		-nic none \
		-drive file=$(img),if=none,format=raw,id=x0 \
		-device vhost-vsock-device,id=virtiosocket0,guest-cid=102 \
		-device virtio-blk-device,drive=x0 \
		-device virtio-gpu-device \
		-device virtio-serial,id=virtio-serial0 \
		-chardev stdio,id=char0,mux=on \
		-device virtconsole,chardev=char0

qemu-pci: $(kernel_qemu_bin) $(img)
	$(vsock_server_bin) &
	qemu-system-aarch64 \
		$(QEMU_ARGS) \
		-machine virt \
		-cpu max \
		-serial chardev:char0 \
		-kernel $(kernel_qemu_bin) \
		-nic none \
		-drive file=$(img),if=none,format=raw,id=x0 \
		-device vhost-vsock-pci,id=virtiosocket0,guest-cid=103 \
		-device virtio-blk-pci,drive=x0 \
		-device virtio-gpu-pci \
		-device virtio-serial,id=virtio-serial0 \
		-chardev stdio,id=char0,mux=on \
		-device virtconsole,chardev=char0

crosvm: $(kernel_crosvm_bin) $(img)
	adb shell 'mkdir -p /data/local/tmp/virt_raw'
	adb push $(kernel_crosvm_bin) /data/local/tmp/virt_raw/aarch64_example
	adb push $(img) /data/local/tmp/virt_raw/disk_img
	adb shell "/apex/com.android.virt/bin/crosvm --log-level=info --extended-status run --disable-sandbox --serial=stdout,hardware=serial,num=1 --rwdisk=/data/local/tmp/virt_raw/disk_img --bios=/data/local/tmp/virt_raw/aarch64_example"

$(img):
	dd if=/dev/zero of=$@ bs=512 count=32

run: qemu
