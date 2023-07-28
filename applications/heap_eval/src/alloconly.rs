use alloc::{
    vec::Vec,
    string::String,
    alloc::Layout,
};
#[cfg(not(direct_access_to_multiple_heaps))]
use alloc::alloc::GlobalAlloc;
use core::sync::atomic::{AtomicUsize, Ordering};
// use core::ptr;
use hpet::get_hpet;
use libtest::{hpet_2_us, calculate_stats, hpet_timing_overhead};
use crate::{NTHREADS, ALLOCATOR, TRIES};
#[cfg(direct_access_to_multiple_heaps)]
use crate::overhead_of_accessing_multiple_heaps;

pub(crate) static NITERATIONS: AtomicUsize = AtomicUsize::new(1000);
pub(crate) static MAX_BLOCK_SIZE: AtomicUsize = AtomicUsize::new(MAX_REGULAR);
pub(crate) static MIN_BLOCK_SIZE: AtomicUsize = AtomicUsize::new(MIN_REGULAR);
/// The default smallest size of object to allocate
const MIN_REGULAR: usize = 1;
/// The default maximum size of object to allocate
const MAX_REGULAR: usize = 1000;
/// The minimum size allocated when the large allocations option is chosen
pub const MIN_LARGE: usize = 8192;
/// The maximum size allocated when the large allocations option is chosen
pub const MAX_LARGE: usize = 16384;
/// The number of allocations that take place in one iteration
const ALLOCATIONS_PER_ITER: usize = 19_300;

pub fn do_alloconly() -> Result<(), &'static str> {

    let nthreads = NTHREADS.load(Ordering::SeqCst);
    let niterations = NITERATIONS.load(Ordering::SeqCst);
    let mut tries = Vec::with_capacity(TRIES as usize);

    let hpet_overhead = hpet_timing_overhead()?;
    let hpet = get_hpet().ok_or("couldn't get HPET timer")?;

    println!("Running alloconly for {} threads, {} total iterations, {} iterations per thread, {} total objects allocated by all threads, {} max block size, {} min block size ...", 
        nthreads, niterations, niterations/nthreads, ALLOCATIONS_PER_ITER * niterations, MAX_BLOCK_SIZE.load(Ordering::SeqCst), MIN_BLOCK_SIZE.load(Ordering::SeqCst));
    
    #[cfg(direct_access_to_multiple_heaps)]
    {
        let overhead = overhead_of_accessing_multiple_heaps()?;
        println!("Overhead of accessing multiple heaps is: {} ticks, {} ns", overhead, hpet_2_us(overhead));
    }

    for try in 0..TRIES {

        let mut threads = Vec::with_capacity(nthreads);

        let start = hpet.get_counter();

        for _ in 0..nthreads {
            // The alloc only test
            threads.push(spawn::new_task_builder(alloc_only_test, ()).name(String::from("worker thread")).spawn()?);
        }  

        for i in 0..nthreads {
            threads[i].join()?;
        }

        let end = hpet.get_counter() - hpet_overhead;

        let diff = hpet_2_us(end - start);
        println!("[{}] alloconly time: {} us", try, diff);
        tries.push(diff);
    }

    println!("alloconly stats (us)");
    println!("{:?}", calculate_stats(&tries));

    Ok(())
}


fn alloc_only_test(_: ()) {
    #[cfg(not(direct_access_to_multiple_heaps))]
    let allocator = &ALLOCATOR;

    // In the case of directly accessing the multiple heaps, we do have to access them through the Once wrapper
    // at the beginning, but the time it takes to do this once at the beginning of thread is
    // insignificant compared to the number of iterations we run. It also printed above.
    #[cfg(direct_access_to_multiple_heaps)]
    let allocator = match ALLOCATOR.get() {
        Some(allocator) => allocator,
        None => {
            error!("Multiple heaps not initialized!");
            return;
        }
    };

    let nthreads = NTHREADS.load(Ordering::SeqCst);
    let niterations = NITERATIONS.load(Ordering::SeqCst) / nthreads;
    let min_block_size = MIN_BLOCK_SIZE.load(Ordering::SeqCst);
    let max_block_size = MAX_BLOCK_SIZE.load(Ordering::SeqCst);

    for _ in 0..niterations {
        println!("allocating");
        let mut size_base = min_block_size;
        while size_base < max_block_size {
            let mut size = size_base;
            while size > 0 {
                let mut iterations = 1;

                // smaller sizes will be allocated a larger amount
                if size < 10000 { iterations = 10; }
                if size < 1000 { iterations *= 5; }
                if size < 100 {iterations *= 5; }

                for _ in 0..iterations {
                    let layout = Layout::from_size_align(size, 2).unwrap();
                    let ptr = unsafe{ allocator.alloc(layout) };
                    if ptr.is_null() {
                        error!("Out of Heap Memory");
                        return;
                    }
                }
                size /= 2;
            }
            size_base = size_base * 3 / 2 + 1
        }
    }
}
