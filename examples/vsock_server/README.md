# Running Virtio Vsock Example

The binary `vsock_server` sets up a vsock server on the host. It can be used to run the virtio vsock example in `examples/aarch64`

## Build and Run the Example

Run the server on the host:
```bash
/examples/vsock_server$ cargo run
```

Run the guest:
```bash
examples/aarch64$ make qemu-vsock
```

## Sample log

Host:
```
[Host] Setting up listening socket on port 1221
[Host] Accept connection: VsockStream { socket: 4 }, peer addr: Ok(cid: 102 port: 1221), local addr: Ok(cid: 2 port: 1221)
[Host] Sent message:[72, 101, 108, 108, 111, 32, 102, 114, 111, 109, 32, 104, 111, 115, 116].
[Host] Received message: [65, 99, 107, 46, 32, 72, 101, 108, 108, 111, 32, 102, 114, 111, 109, 32, 103, 117, 101, 115, 116, 46, 0, 0, 0, 0, 0, 0, 0, 0], len:22, str: Ok("Ack. Hello from guest.")
[Host] End.
```

Guest:
```
[INFO] guest cid: 102
[INFO] Connecting to host on port 1221...
[INFO] Connection to host: Ok(())
[DEBUG] Connection info Some(ConnectionInfo { dst: VsockAddr { cid: 2, port: 1221 }, src_port: 1221, buf_alloc: 262144, fwd_cnt: 0 })
...
[INFO] Received message: Ok(15). Message: [72, 101, 108, 108, 111, 32, 102, 114, 111, 109, 32, 104, 111, 115, 116, 0, 0, 0, 0, 0, 0, 0, 0, 0]
[INFO] Send message '[65, 99, 107, 46, 32, 72, 101, 108, 108, 111, 32, 102, 114, 111, 109, 32, 103, 117, 101, 115, 116, 46]': Ok(())
```
