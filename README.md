# VirtIO-drivers-rs

[![crates.io page](https://img.shields.io/crates/v/virtio-drivers.svg)](https://crates.io/crates/virtio-drivers)
[![docs.rs page](https://docs.rs/virtio-drivers/badge.svg)](https://docs.rs/virtio-drivers)
[![CI](https://github.com/rcore-os/virtio-drivers/workflows/CI/badge.svg?branch=master)](https://github.com/rcore-os/virtio-drivers/actions)

VirtIO guest drivers in Rust. For **no_std** environment.

## Support status

### Device types

| Device  | Supported |
| ------- | --------- |
| Block   | ✅        |
| Net     | ✅        |
| GPU     | ✅        |
| Input   | ✅        |
| Console | ✅        |
| Socket  | ✅        |
| Sound   | ✅        |
| RNG     | ✅        |
| 9P      | ✅        |
| ...     | ❌        |

### Transports

| Transport   | Supported |                                                   |
| ----------- | --------- | ------------------------------------------------- |
| Legacy MMIO | ✅        | version 1                                         |
| MMIO        | ✅        | version 2                                         |
| PCI         | ✅        | Memory-mapped CAM only, e.g. aarch64 or PCIe ECAM |

### Device-independent features

| Feature flag                 | Supported |                                         |
| ---------------------------- | --------- | --------------------------------------- |
| `VIRTIO_F_INDIRECT_DESC`     | ✅        | Indirect descriptors                    |
| `VIRTIO_F_EVENT_IDX`         | ✅        | `avail_event` and `used_event` fields   |
| `VIRTIO_F_VERSION_1`         | TODO      | VirtIO version 1 compliance             |
| `VIRTIO_F_ACCESS_PLATFORM`   | ✅        | Limited device access to memory         |
| `VIRTIO_F_RING_PACKED`       | ❌        | Packed virtqueue layout                 |
| `VIRTIO_F_IN_ORDER`          | ❌        | Optimisations for in-order buffer usage |
| `VIRTIO_F_ORDER_PLATFORM`    | ❌        | Platform ordering for memory access     |
| `VIRTIO_F_SR_IOV`            | ❌        | Single root I/O virtualization          |
| `VIRTIO_F_NOTIFICATION_DATA` | ❌        | Extra data in device notifications      |

## Cargo features

All features are enabled by default. Individual device drivers and transports
can be selected independently via `--no-default-features` to minimize the build
footprint.

| Feature          | Description                                                                            |
| -------          | -----------                                                                            |
| `alloc`          | Use memory allocation features, requires global allocator                              |
| `embedded-io`    | Implement `embedded-io` traits for console, depends on the `embedded-io` crate.        |
| `all-drivers`    | Enable all device drivers, see below                                                   |
| `blk`            | Enable block device driver                                                             |
| `console`        | Enable console device driver (requires `alloc`)                                        |
| `gpu`            | Enable GPU device driver (requires `alloc`)                                            |
| `input`          | Enable input device driver (requires `alloc`)                                          |
| `net`            | Enable network device driver                                                           |
| `rng`            | Enable random number generator device driver                                           |
| `rtc`            | Enable real time clock device driver                                                   |
| `socket`         | Enable vsock device driver                                                             |
| `sound`          | Enable sound device driver (requires `alloc`)                                          |
| `virtio_9p`      | Enable virtio 9p driver (requires `alloc`)                                             |
| `all-transports` | Enable all transports, see below                                                       |
| `mmio`           | Enable MMIO transport                                                                  |
| `pci`            | Enable PCI transport                                                                   |

## Examples & Tests

### [x86_64](./examples/x86_64)

```bash
cd examples/x86_64
make qemu
```

### [aarch64](./examples/aarch64)

```bash
cd examples/aarch64
make qemu
```

### [RISCV](./examples/riscv)

```bash
cd examples/riscv
make qemu
```

### [hexagon](./examples/hexagon)

```bash
cd examples/hexagon
make qemu
```

You will see device info & GUI Window in qemu.

<img decoding="async" src="https://github.com/rcore-os/virtio-drivers/raw/master/examples/riscv/virtio-test-gpu.png" width="50%">
