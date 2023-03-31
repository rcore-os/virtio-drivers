/// Sets a listening socket on host.
use std::{
    io::{Read, Write},
    time::Duration,
};
use vsock::{VsockAddr, VsockListener, VMADDR_CID_HOST};

const PORT: u32 = 1221;

fn main() {
    println!("[Host] Setting up listening socket on port {PORT}");
    let listener = VsockListener::bind(&VsockAddr::new(VMADDR_CID_HOST, PORT))
        .expect("Failed to set up listening port");
    for vsock_stream in listener.incoming() {
        let mut vsock_stream = vsock_stream.expect("Failed to extract vsock_stream");
        println!(
            "[Host] Accept connection: {:?}, peer addr: {:?}, local addr: {:?}",
            vsock_stream,
            vsock_stream.peer_addr(),
            vsock_stream.local_addr()
        );

        let message = b"Hello from host\0";
        vsock_stream.write_all(message).expect("write_all");
        println!("[Host] Sent message:{:?}.", message);
        vsock_stream.flush().expect("flush");
        println!("[Host] Flushed.");

        let mut message = Vec::new();
        vsock_stream
            .set_read_timeout(Some(Duration::from_millis(3_000)))
            .expect("set_read_timeout");
        for i in 0..10 {
            match vsock_stream.read_to_end(&mut message) {
                Ok(len) => {
                    println!("[Host] Received message: {:?}, len:{}", message, len);
                    break;
                }
                Err(e) => {
                    println!("{i} {e:?}");
                    std::thread::sleep(Duration::from_millis(200))
                }
            }
        }
        println!("[Host] End.");
        return;
    }
}
