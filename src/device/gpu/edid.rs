//! EDID (Extended Display Identification Data) parsing.
//!
//! Provides types for extracting display information from raw EDID blobs,
//! including preferred resolution and standard timing modes.
//!
//! Reference: VESA Enhanced EDID Standard (E-EDID), Release A, Rev. 2.

use crate::{Error, Result};
use alloc::vec::Vec;

/// The number of standard timing entries in the base EDID block.
const NUM_STANDARD_TIMINGS: usize = 8;

/// The byte offset of the first Detailed Timing Descriptor in the base block.
const DTD1_OFFSET: usize = 0x36;

/// The byte length of a single Detailed Timing Descriptor.
const DTD_LEN: usize = 18;

/// The byte offset of the first Standard Timing entry in the base block.
const STANDARD_TIMINGS_OFFSET: usize = 38;

/// The byte length of a single Standard Timing entry.
const STANDARD_TIMING_LEN: usize = 2;

/// Aspect ratio encoded in a Standard Timing entry.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum AspectRatio {
    /// 16:10
    Ratio16x10,
    /// 4:3
    Ratio4x3,
    /// 5:4
    Ratio5x4,
    /// 16:9
    Ratio16x9,
}

impl AspectRatio {
    fn from_bits(bits: u8) -> Self {
        match bits {
            0 => Self::Ratio16x10,
            1 => Self::Ratio4x3,
            2 => Self::Ratio5x4,
            3 => Self::Ratio16x9,
            _ => unreachable!(),
        }
    }

    /// Compute vertical pixels from horizontal pixels and this aspect ratio.
    fn v_pixels(self, h_pixels: u32) -> u32 {
        match self {
            Self::Ratio16x10 => h_pixels * 10 / 16,
            Self::Ratio4x3 => h_pixels * 3 / 4,
            Self::Ratio5x4 => h_pixels * 4 / 5,
            Self::Ratio16x9 => h_pixels * 9 / 16,
        }
    }
}

/// A single standard timing entry from the EDID.
///
/// Reference: VESA E-EDID, Section 3.9 "Standard Timing Identification".
struct StandardTiming {
    /// Horizontal active pixels.
    h_pixels: u32,
    /// Vertical active pixels (derived from aspect ratio).
    v_pixels: u32,
}

impl StandardTiming {
    /// The marker value for an unused standard timing slot.
    const UNUSED: [u8; 2] = [0x01, 0x01];

    /// Parse a standard timing from its 2-byte encoding.
    ///
    /// Returns `None` for unused entries (0x0101).
    fn parse(bytes: &[u8; 2]) -> Option<Self> {
        if *bytes == Self::UNUSED {
            return None;
        }
        let h_pixels = (bytes[0] as u32 + 31) * 8;
        let aspect = AspectRatio::from_bits((bytes[1] >> 6) & 0x03);
        let v_pixels = aspect.v_pixels(h_pixels);
        Some(Self { h_pixels, v_pixels })
    }
}

/// A Detailed Timing Descriptor from the EDID base block.
///
/// Reference: VESA E-EDID, Section 3.10.2 "Detailed Timing Definitions".
struct DetailedTiming {
    /// Horizontal active pixels.
    h_active: u32,
    /// Vertical active pixels.
    v_active: u32,
}

impl DetailedTiming {
    /// Parse a detailed timing descriptor from its 18-byte encoding.
    ///
    /// Returns `None` if the active pixel counts are zero.
    fn parse(bytes: &[u8; DTD_LEN]) -> Option<Self> {
        // Horizontal active: lower 8 bits at byte 2, upper 4 bits in high nibble of byte 4.
        let h_active = bytes[2] as u32 | ((bytes[4] as u32 & 0xF0) << 4);
        // Vertical active: lower 8 bits at byte 5, upper 4 bits in high nibble of byte 7.
        let v_active = bytes[5] as u32 | ((bytes[7] as u32 & 0xF0) << 4);
        if h_active == 0 || v_active == 0 {
            return None;
        }
        Some(Self { h_active, v_active })
    }
}

/// Parsed EDID data from a display device.
///
/// Wraps the raw EDID byte blob and provides methods to extract display
/// information such as preferred resolution and supported standard timings.
pub struct Edid {
    pub(super) data: [u8; 1024],
    pub(super) size: u32,
}

impl Edid {
    /// Whether the base EDID block (128 bytes) is present.
    fn has_base_block(&self) -> bool {
        self.size >= 128
    }

    /// Parse the first Detailed Timing Descriptor.
    fn first_detailed_timing(&self) -> Option<DetailedTiming> {
        if !self.has_base_block() {
            return None;
        }
        let bytes = &self.data[DTD1_OFFSET..][..DTD_LEN].try_into().unwrap();
        DetailedTiming::parse(bytes)
    }

    /// Parse a single standard timing entry by index (0-7).
    fn standard_timing(&self, index: usize) -> Option<StandardTiming> {
        let offset = STANDARD_TIMINGS_OFFSET + index * STANDARD_TIMING_LEN;
        let bytes = &self.data[offset..][..STANDARD_TIMING_LEN]
            .try_into()
            .unwrap();
        StandardTiming::parse(bytes)
    }

    /// Get the preferred resolution from the EDID data.
    ///
    /// Returns the resolution from the first Detailed Timing Descriptor,
    /// which per the EDID spec represents the display's preferred mode.
    pub fn preferred_resolution(&self) -> Result<(u32, u32)> {
        let dtd = self.first_detailed_timing().ok_or(Error::IoError)?;
        Ok((dtd.h_active, dtd.v_active))
    }

    /// Get the list of supported resolutions from EDID standard timings.
    ///
    /// Returns up to 8 (width, height) pairs sorted by total pixel count
    /// (largest first).
    pub fn standard_timings(&self) -> Vec<(u32, u32)> {
        if !self.has_base_block() {
            return Vec::new();
        }
        let mut resolutions: Vec<(u32, u32)> = (0..NUM_STANDARD_TIMINGS)
            .filter_map(|i| self.standard_timing(i))
            .map(|st| (st.h_pixels, st.v_pixels))
            .collect();
        resolutions.sort_by(|a, b| (b.0 as u64 * b.1 as u64).cmp(&(a.0 as u64 * a.1 as u64)));
        resolutions
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Real EDID captured from QEMU virtio-GPU with `-device virtio-gpu,xres=1920,yres=1080`.
    /// QEMU generates this EDID dynamically. The base block (bytes 0-127) contains:
    /// - Manufacturer: "RHT" (Red Hat), product code 0x1234
    /// - DTD1 preferred mode: 1920x1080 @ 60Hz
    /// - 8 Standard Timings: 2048x1152, 1920x1080, 1920x1200, 1600x1200,
    ///   1680x1050, 1440x900, 1280x1024, 1280x960
    /// - CEA extension block (bytes 128-255) with SVDs for additional modes
    /// Remaining bytes (256-1023) are zero-padded by the virtio-GPU device.
    fn qemu_edid() -> [u8; 1024] {
        let mut edid = [0u8; 1024];
        let data: [u8; 256] = [
            // Base EDID block (128 bytes)
            0x00, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x00, 0x49, 0x14, 0x34, 0x12, 0x00, 0x00,
            0x00, 0x00, 0x2a, 0x18, 0x01, 0x04, 0xa5, 0x30, 0x1b, 0x78, 0x06, 0xee, 0x91, 0xa3,
            0x54, 0x4c, 0x99, 0x26, 0x0f, 0x50, 0x54, 0x21, 0x08, 0x00, 0xe1, 0xc0, 0xd1, 0xc0,
            0xd1, 0x00, 0xa9, 0x40, 0xb3, 0x00, 0x95, 0x00, 0x81, 0x80, 0x81, 0x40, 0xd2, 0x54,
            0x80, 0xa0, 0x72, 0x38, 0x25, 0x40, 0xe0, 0x39, 0x55, 0x40, 0xe7, 0x12, 0x11, 0x00,
            0x00, 0x18, 0x00, 0x00, 0x00, 0xf7, 0x00, 0x0a, 0x00, 0x40, 0x82, 0x00, 0x28, 0x20,
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xfd, 0x00, 0x32, 0x7d, 0x1e,
            0xa0, 0xff, 0x01, 0x0a, 0x20, 0x20, 0x20, 0x20, 0x20, 0x20, 0x00, 0x00, 0x00, 0xfc,
            0x00, 0x51, 0x45, 0x4d, 0x55, 0x20, 0x4d, 0x6f, 0x6e, 0x69, 0x74, 0x6f, 0x72, 0x0a,
            0x01, 0xb0, // CEA extension block (128 bytes)
            0x02, 0x03, 0x0b, 0x00, 0x46, 0x7d, 0x65, 0x60, 0x59, 0x1f, 0x61, 0x00, 0x00, 0x00,
            0x10, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00, 0x10, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x10, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x10, 0x00,
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x10, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x10, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x2f,
        ];
        edid[..256].copy_from_slice(&data);
        edid
    }

    fn make_edid(data: [u8; 1024], size: u32) -> Edid {
        Edid { data, size }
    }

    /// Extract the DTD1 bytes from the QEMU EDID for direct DetailedTiming tests.
    fn qemu_dtd1_bytes() -> [u8; DTD_LEN] {
        let data = qemu_edid();
        data[DTD1_OFFSET..DTD1_OFFSET + DTD_LEN].try_into().unwrap()
    }

    // ---- AspectRatio tests ----

    #[test]
    fn aspect_ratio_from_bits() {
        assert_eq!(AspectRatio::from_bits(0), AspectRatio::Ratio16x10);
        assert_eq!(AspectRatio::from_bits(1), AspectRatio::Ratio4x3);
        assert_eq!(AspectRatio::from_bits(2), AspectRatio::Ratio5x4);
        assert_eq!(AspectRatio::from_bits(3), AspectRatio::Ratio16x9);
    }

    #[test]
    fn aspect_ratio_v_pixels() {
        assert_eq!(AspectRatio::Ratio16x10.v_pixels(1920), 1200);
        assert_eq!(AspectRatio::Ratio4x3.v_pixels(1600), 1200);
        assert_eq!(AspectRatio::Ratio5x4.v_pixels(1280), 1024);
        assert_eq!(AspectRatio::Ratio16x9.v_pixels(1920), 1080);
    }

    // ---- StandardTiming tests ----

    #[test]
    fn standard_timing_unused_entry() {
        assert!(StandardTiming::parse(&[0x01, 0x01]).is_none());
    }

    #[test]
    fn standard_timing_known_entry() {
        // First standard timing from QEMU EDID: 0xe1, 0xc0
        // h_pixels = (0xe1 + 31) * 8 = (225 + 31) * 8 = 2048
        // aspect bits = 0xc0 >> 6 = 3 => 16:9
        // v_pixels = 2048 * 9 / 16 = 1152
        let st = StandardTiming::parse(&[0xe1, 0xc0]).unwrap();
        assert_eq!(st.h_pixels, 2048);
        assert_eq!(st.v_pixels, 1152);
    }

    #[test]
    fn standard_timing_each_aspect_ratio() {
        // 16:10: byte1 bits 7:6 = 0b00
        let st = StandardTiming::parse(&[0xd1, 0x00]).unwrap();
        assert_eq!((st.h_pixels, st.v_pixels), (1920, 1200));

        // 4:3: byte1 bits 7:6 = 0b01
        let st = StandardTiming::parse(&[0xa9, 0x40]).unwrap();
        assert_eq!((st.h_pixels, st.v_pixels), (1600, 1200));

        // 5:4: byte1 bits 7:6 = 0b10
        let st = StandardTiming::parse(&[0x81, 0x80]).unwrap();
        assert_eq!((st.h_pixels, st.v_pixels), (1280, 1024));

        // 16:9: byte1 bits 7:6 = 0b11
        let st = StandardTiming::parse(&[0xd1, 0xc0]).unwrap();
        assert_eq!((st.h_pixels, st.v_pixels), (1920, 1080));
    }

    // ---- DetailedTiming tests ----

    #[test]
    fn detailed_timing_zeroed() {
        assert!(DetailedTiming::parse(&[0u8; DTD_LEN]).is_none());
    }

    #[test]
    fn detailed_timing_known_1920x1080() {
        let dtd = DetailedTiming::parse(&qemu_dtd1_bytes()).unwrap();
        assert_eq!(dtd.h_active, 1920);
        assert_eq!(dtd.v_active, 1080);
    }

    #[test]
    fn detailed_timing_h_active_uses_upper_nibble() {
        // Construct a DTD where h_active requires the upper nibble.
        // h_active_low = 0x00, upper nibble of byte 4 = 0x50 => h_active = 0x500 = 1280
        // v_active_low = 0x00, upper nibble of byte 7 = 0x40 => v_active = 0x400 = 1024
        let mut bytes = [0u8; DTD_LEN];
        bytes[0] = 0x01; // non-zero pixel clock so it's not a display descriptor
        bytes[2] = 0x00; // h_active low = 0
        bytes[4] = 0x50; // h_active upper nibble = 5, h_blanking upper nibble = 0
        bytes[5] = 0x00; // v_active low = 0
        bytes[7] = 0x40; // v_active upper nibble = 4, v_blanking upper nibble = 0
        let dtd = DetailedTiming::parse(&bytes).unwrap();
        assert_eq!(dtd.h_active, 1280);
        assert_eq!(dtd.v_active, 1024);
    }

    // ---- Edid tests ----

    #[test]
    fn edid_size_exactly_128() {
        let edid = make_edid(qemu_edid(), 128);
        assert!(edid.preferred_resolution().is_ok());
        assert!(!edid.standard_timings().is_empty());
    }

    #[test]
    fn edid_size_127_fails() {
        let edid = make_edid(qemu_edid(), 127);
        assert!(edid.preferred_resolution().is_err());
        assert!(edid.standard_timings().is_empty());
    }

    #[test]
    fn qemu_edid_preferred_resolution() {
        let edid = make_edid(qemu_edid(), 256);
        let (w, h) = edid.preferred_resolution().unwrap();
        assert_eq!((w, h), (1920, 1080));
    }

    #[test]
    fn qemu_edid_standard_timings() {
        let edid = make_edid(qemu_edid(), 256);
        let res = edid.standard_timings();
        // QEMU advertises 8 standard timings, sorted by total pixel count (largest first).
        // Note: 1600x1200 (1,920,000 px) > 1680x1050 (1,764,000 px) despite narrower width,
        // and 1280x1024 (1,310,720 px) > 1440x900 (1,296,000 px) for the same reason.
        assert_eq!(
            res,
            vec![
                (2048, 1152), // 16:9,  2,359,296 px
                (1920, 1200), // 16:10, 2,304,000 px
                (1920, 1080), // 16:9,  2,073,600 px
                (1600, 1200), // 4:3,   1,920,000 px
                (1680, 1050), // 16:10, 1,764,000 px
                (1280, 1024), // 5:4,   1,310,720 px
                (1440, 900),  // 16:10, 1,296,000 px
                (1280, 960),  // 4:3,   1,228,800 px
            ]
        );
    }

    #[test]
    fn qemu_edid_highest_resolution_is_2048x1152() {
        let edid = make_edid(qemu_edid(), 256);
        let res = edid.standard_timings();
        assert_eq!(res.first(), Some(&(2048, 1152)));
    }

    #[test]
    fn preferred_resolution_too_short() {
        let edid = make_edid([0u8; 1024], 64);
        assert!(edid.preferred_resolution().is_err());
    }

    #[test]
    fn preferred_resolution_zeroed_active_pixels() {
        // Zero out horizontal and vertical active pixels in DTD1
        let mut data = qemu_edid();
        data[0x38] = 0x00; // h_active low
        data[0x3A] &= 0x0F; // h_active high nibble = 0
        data[0x3B] = 0x00; // v_active low
        data[0x3D] &= 0x0F; // v_active high nibble = 0
        let edid = make_edid(data, 256);
        assert!(edid.preferred_resolution().is_err());
    }

    #[test]
    fn standard_timings_too_short() {
        let edid = make_edid([0u8; 1024], 32);
        let res = edid.standard_timings();
        assert!(res.is_empty());
    }

    #[test]
    fn standard_timings_all_unused() {
        // Overwrite all standard timing slots with 0x0101 (unused marker)
        let mut data = qemu_edid();
        for i in 0..8 {
            data[38 + i * 2] = 0x01;
            data[38 + i * 2 + 1] = 0x01;
        }
        let edid = make_edid(data, 256);
        let res = edid.standard_timings();
        assert!(res.is_empty());
    }

    #[test]
    fn standard_timings_partial_entries() {
        // Keep only the first two standard timing entries, mark rest unused
        let mut data = qemu_edid();
        for i in 2..8 {
            data[38 + i * 2] = 0x01;
            data[38 + i * 2 + 1] = 0x01;
        }
        let edid = make_edid(data, 256);
        let res = edid.standard_timings();
        // First two entries from QEMU: 2048x1152 (16:9) and 1920x1080 (16:9)
        assert_eq!(res, vec![(2048, 1152), (1920, 1080)]);
    }
}
