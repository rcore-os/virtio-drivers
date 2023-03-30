// Sets a listening socket on host.
use vsock::{VsockAddr, VsockListener, VMADDR_CID_HOST};

const PORT: u32 = 1221;

fn main() {
    println!("Setting up listening socket on port {PORT}");
    let listener = VsockListener::bind(&VsockAddr::new(VMADDR_CID_HOST, PORT))
        .expect("Failed to set up listening port");
    for incoming in listener.incoming() {
        println!("Accept connection: {incoming:?}");
    }
}
