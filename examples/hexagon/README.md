
# virtio-devices for hexagon

Here's how to run the `virtio-devices` example for hexagon:

[Install rust using the instructions from the Rust Project website](https://www.rust-lang.org/learn/get-started)
and then install the nightly:

    rustup toolchain install nightly
    rustup override set nightly
    rustup component add rust-src --toolchain nightly-x86_64-unknown-linux-gnu

Download and install the hexagon open source toolchain from https://github.com/quic/toolchain_for_hexagon/releases - version 20.1.4 or later.

Once you have that toolchain installed, build and run the hexagon example
from the `virtio-devices` repo:

    git clone https://github.com/androm3da/virtio-drivers/
    cd virtio-devices
    git checkout bcain/hexagon_support
    cd examples/hexagon

    PATH=/local/mnt/workspace/install/clang+llvm-20.1.4-cross-hexagon-unknown-linux-musl/x86_64-linux-gnu/bin/:$PATH make run

# Troubleshooting

If you get an error like below, you may be using the wrong host operating
system for the QEMU hexagon build.  You can [rebuild it from source](https://github.com/quic/qemu/),
or try installing required dependencies or updating your OS.

```
qemu-system-hexagon: error while loading shared libraries: libbrlapi.so.0.7: cannot open shared object file: No such file or directory
```

If you get an error like below, it means that your QEMU
hexagon release probably has too few virtio slots.  Try removing some of
the virtio devices referenced in the `examples/hexagon/Makefile`.

```
qemu-system-hexagon: -device virtio-net-device,netdev=net0: No 'virtio-bus' bus found for device 'virtio-net-device'
```

Example Makefile patch:
```
diff --git a/examples/hexagon/Makefile b/examples/hexagon/Makefile
index be826eb..0dbca7e 100644
--- a/examples/hexagon/Makefile
+++ b/examples/hexagon/Makefile
@@ -66,9 +66,6 @@ qemu: kernel $(img)
                -global virtio-mmio.force-legacy=false \
                -drive file=$(img),if=none,format=raw,id=x0 \
                -device virtio-blk-device,drive=x0 \
-               -device virtio-rng-device \
-               -netdev user,id=net0,hostfwd=tcp::5555-:5555 \
-               -device virtio-net-device,netdev=net0 \
```
