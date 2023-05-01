use linked_list_allocator::LockedHeap;

#[global_allocator]
static ALLOCATOR: LockedHeap = LockedHeap::empty();

const HEAP_SIZE: usize = 0x10000; // 64K

static mut HEAP: [u64; HEAP_SIZE / 8] = [0; HEAP_SIZE / 8];

pub fn init_heap() {
    unsafe {
        let heap_start = HEAP.as_ptr() as *mut u8;
        ALLOCATOR.lock().init(heap_start, HEAP_SIZE);
    }
}
