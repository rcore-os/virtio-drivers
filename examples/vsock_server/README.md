# Running Virtio Vsock Example

The binary `vsock_server` sets up a vsock server on the host. It can be used to run the virtio vsock example in `examples/aarch64`

## Build and Run the Example

Run the server on the host:
```bash
examples/vsock_server$ cargo run
```

Run the guest:
```bash
examples/aarch64$ make qemu-vsock
```

## Sample Log

The example demonstrates two rounds of message exchange between the host and the guest.

Host:
```
[Host] Setting up listening socket on port 1221
[Host] Accept connection: VsockStream { socket: 4 }, peer addr: Ok(cid: 102 port: 1221), local addr: Ok(cid: 2 port: 1221)
[Host] Sent message: "0-Hello from host".
[Host] Flushed.
[Host] Received message: [48, 45, 65, 99, 107, 46, 32, 72, 101, 108, 108, 111, 32, 102, 114, 111, 109, 32, 103, 117, 101, 115, 116, 46, 0, 0, 0, 0, 0, 0](Ok("0-Ack. Hello from guest.")), len: 24
[Host] Sent message: "1-Hello from host".
[Host] Flushed.
[Host] Received message: [49, 45, 65, 99, 107, 46, 32, 82, 101, 99, 101, 105, 118, 101, 100, 32, 97, 103, 97, 105, 110, 46, 0, 0, 0, 0, 0, 0, 0, 0](Ok("1-Ack. Received again.")), len: 22
[Host] End.
```

Guest:
```
[INFO] guest cid: 102
[INFO] Connecting to host on port 1221...
[DEBUG] Connection established: Some(ConnectionInfo { dst: VsockAddr { cid: 2, port: 1221 }, src_port: 1221, peer_buf_alloc: 0, peer_fwd_cnt: 0 })
[INFO] Connected to the host
...
[INFO] Received message: [48, 45, 72, 101, 108, 108, 111, 32, 102, 114, 111, 109, 32, 104, 111, 115, 116, 0, 0, 0, 0, 0, 0, 0](Ok("0-Hello from host")), len: 17
[DEBUG] Connection info updated: Some(ConnectionInfo { dst: VsockAddr { cid: 2, port: 1221 }, src_port: 1221, peer_buf_alloc: 262144, peer_fwd_cnt: 0 })
[INFO] Sent message: "0-Ack. Hello from guest."
[INFO] Received message: [49, 45, 72, 101, 108, 108, 111, 32, 102, 114, 111, 109, 32, 104, 111, 115, 116, 0, 0, 0, 0, 0, 0, 0](Ok("1-Hello from host")), len: 17
[INFO] Sent message: "1-Ack. Received again."
[INFO] Disconnected from the peer
[INFO] Shutdown the connection
```
