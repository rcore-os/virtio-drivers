//! Sets up a listening socket on host.
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

    let Some(Ok(mut vsock_stream)) = listener.incoming().next() else {
        println!("[Host] Failed to get vsock_stream");
        return;
    };
    println!(
        "[Host] Accept connection: {:?}, peer addr: {:?}, local addr: {:?}",
        vsock_stream,
        vsock_stream.peer_addr(),
        vsock_stream.local_addr()
    );

    const EXCHANGE_NUM: usize = 2;
    for k in 0..EXCHANGE_NUM {
        let message = &format!("{k}-Hello from host");
        vsock_stream
            .write_all(message.as_bytes())
            .expect("write_all");
        println!("[Host] Sent message: {:?}.", message);
        vsock_stream.flush().expect("flush");
        println!("[Host] Flushed.");

        let mut message = vec![0u8; 30];
        vsock_stream
            .set_read_timeout(Some(Duration::from_millis(3_000)))
            .expect("set_read_timeout");
        for i in 0..10 {
            match vsock_stream.read(&mut message) {
                Ok(len) => {
                    println!(
                        "[Host] Received message: {:?}({:?}), len: {:?}",
                        message,
                        std::str::from_utf8(&message[..len]),
                        len,
                    );
                    break;
                }
                Err(e) => {
                    println!("{i} {e:?}");
                    std::thread::sleep(Duration::from_millis(200))
                }
            }
        }
    }
    println!("[Host] End.");
}
