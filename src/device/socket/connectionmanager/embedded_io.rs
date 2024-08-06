//! Implementation of `embedded-io` traits for `VsockConnection`.

use super::VsockConnection;
use crate::{transport::Transport, Error, Hal};
use core::cmp::min;
use embedded_io::{ErrorType, Read, ReadReady, Write};

impl<H: Hal, T: Transport> ErrorType for VsockConnection<'_, H, T> {
    type Error = Error;
}

impl<H: Hal, T: Transport> Write for VsockConnection<'_, H, T> {
    fn write(&mut self, buf: &[u8]) -> Result<usize, Self::Error> {
        if buf.is_empty() {
            Ok(0)
        } else {
            let mut peer_buffer_available = self.peer_buffer_available()?;
            while peer_buffer_available == 0 {
                // TODO: This may block forever, as there is no other thread polling the connection
                // manager.
                peer_buffer_available = self.peer_buffer_available()?
            }
            let length_to_send = min(peer_buffer_available, buf.len());
            self.send(&buf[..length_to_send])?;
            Ok(length_to_send)
        }
    }

    fn flush(&mut self) -> Result<(), Self::Error> {
        // We don't buffer writes so this is a no-op.
        Ok(())
    }
}

impl<H: Hal, T: Transport> Read for VsockConnection<'_, H, T> {
    fn read(&mut self, buf: &mut [u8]) -> Result<usize, Self::Error> {
        if buf.is_empty() {
            Ok(0)
        } else {
            let mut bytes_read = 0;
            while bytes_read == 0 {
                bytes_read = self.recv(buf)?;
                // TODO: This may block forever, as there is no other thread polling the connection
                // manager.
            }
            Ok(bytes_read)
        }
    }
}

impl<H: Hal, T: Transport> ReadReady for VsockConnection<'_, H, T> {
    fn read_ready(&mut self) -> Result<bool, Self::Error> {
        let available = self
            .manager
            .recv_buffer_available_bytes(self.peer, self.local_port)?;
        Ok(available > 0)
    }
}
