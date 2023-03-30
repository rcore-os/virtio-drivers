// Sets a listening socket on host.
use vsock::{VsockAddr, VsockListener, VMADDR_CID_HOST};

const PORT: u32 = 1221;

fn main() {
    println!("Setting up listening socket on port {PORT}");
    let listener = VsockListener::bind(&VsockAddr::new(VMADDR_CID_HOST, PORT))
        .expect("Failed to set up listening port");
    for vsock_stream in listener.incoming() {
        let mut vsock_stream = vsock_stream.expect("Failed to extract vsock_stream");
        println!("Accept connection: {vsock_stream:?}");
    }
}
