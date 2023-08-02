// Prusti environment flags for verification:
//   -Penable_type_invariants=true
//   -Pcheck_overflows=true
//   -Passert_timeout=20

// Prusti compiler flags:
//   --edition-2018
//   --crate-type=lib
//   --cfg="prusti"

// ../prusti_local_build/prusti-rustc ./libs/trusted_bitfield/src/lib.rs -Penable_type_invariants=true -Pcheck_overflows=false -Passert_timeout=20 --edition=2018 --crate-type=lib --cfg="prusti"

#![cfg_attr(not(prusti), no_std)]

use prusti_contracts::*;
use core::sync::atomic::Ordering;

#[cfg(prusti)]
mod external_spec;

#[cfg(prusti)]
#[allow(unused_imports)]
use external_spec::{trusted_option::*, trusted_num::*};

#[cfg(not(prusti))]
use core::{sync::atomic::AtomicU64, option::Option, option::Option::*};

#[cfg(prusti)]
#[derive(Clone, Copy)]
#[invariant(self.0 <= u64::MAX)]
struct AtomicU64(u64);

#[cfg(prusti)]
impl AtomicU64 {
    #[pure]
    #[trusted]
    fn new (val: u64) -> Self {
        AtomicU64(val)
    }

    #[pure]
    #[trusted]
    #[ensures(result == self.0)]
    fn load(&self, _order: Ordering) -> u64 {
        self.0
    }

    #[trusted]
    #[ensures(self.load(_order) == val)]
    #[ensures(self.0 == val)]
    fn store(&self, val: u64, _order: Ordering) {
        let raw = self as *const AtomicU64 as *mut AtomicU64;
        unsafe{(*raw).0 = val};
    }

    #[trusted]
    fn fetch_and(&self, val: u64, _order: Ordering) -> u64 {
        let prev = self.0;
        let raw = self as *const AtomicU64 as *mut AtomicU64;
        unsafe{(*raw).0 &= val};
        prev
    }

    #[trusted]
    fn fetch_or(&self, val: u64, _order: Ordering) -> u64 {
        let prev = self.0;
        let raw = self as *const AtomicU64 as *mut AtomicU64;
        unsafe{(*raw).0 |= val};
        prev
    }
}

pub struct VerifiedAllocAddr(usize);

pub fn addr_from_verified_alloc_addr(addr: VerifiedAllocAddr) -> usize {
    addr.0
}

pub struct VerifiedDeallocAddr(usize);

fn new_verified_dealloc_addr(addr: usize) -> VerifiedDeallocAddr {
    VerifiedDeallocAddr(addr)
}

// Basic bitfield operations with properties verified externally with Verus.

#[allow(dead_code)]
#[pure]
#[trusted]
#[requires(k < 64)]
#[ensures(k == 0 ==> result == 1)]
#[ensures(result > 0)]  // This is the case when k < 64, as the single 1 cannot be shifted out.
#[ensures(result < u64::MAX)]  // Follows from u64::MAX being a sum of unique powers of 2
fn power_of_two_u64(k: usize) -> u64 {
    1 << (k as u64)
}

#[pure]
#[trusted]
#[requires(idx < 64)]
#[ensures(forall(|i: usize| i < 64 ==> is_allocated_u64(u, i)) ==> *u == u64::MAX)]  // If all bits are set, u should be u64::MAX.
#[ensures(!result ==> *u < u64::MAX)]  // If any bit is not set, u should be less than u64::MAX.
fn is_allocated_u64(u: &u64, idx: usize) -> bool {
    *u & (1 << idx) > 0
}

#[trusted]
#[requires(idx < 64)]
#[ensures({  // If the bit is previously set, there should be no change to u.
    is_allocated_u64(old(&u.0), idx) <==> old(u.0) == u.0
})]
#[ensures({  // If the bit is not set, u should be changed to u + 2^idx.
    let p = power_of_two_u64(idx);
    !is_allocated_u64(old(&u.0), idx) ==> old(u.0) + p == u.0
})]
#[ensures(is_allocated_u64(&u.0, idx))]  // Regardless of whether u is updated or not, the bit should be 1 when the function returns.
fn set_bit_atomic_u64(u: &AtomicU64, idx: usize) {
    u.fetch_or(1 << idx, Ordering::Relaxed);
}

#[trusted]
#[requires(idx < 64)]
#[ensures({  // If the bit is previously cleared, there should be no change to u.
    !is_allocated_u64(old(&u.0), idx) ==> old(u.0) == u.0
})]
#[ensures({  // If the bit is set, u should be changed to u - 2^idx.
    let p = power_of_two_u64(idx);
    is_allocated_u64(old(&u.0), idx) ==> old(u.0) - p == u.0
})]
#[ensures(!is_allocated_u64(&u.0, idx))]  // Regardless of whether u is updated or not, the bit should be 0 when the function returns.
fn clear_bit_atomic_u64(u: &AtomicU64, idx: usize) {
    u.fetch_and(!(1 << idx), Ordering::Relaxed);
}

#[pure]
#[trusted]
#[requires(k <= 64)]
#[ensures(k == 0 ==> result == u64::MAX)]  // If k == 0, all bits should be set.
#[ensures(k == 64 ==> result == 0)]       // If k == 64, all bits should be cleared.
#[ensures(forall(|j: usize| j < k ==> !is_allocated_u64(&result, j)))]  // All bits before the kth bit should be cleared.
#[ensures(forall(|j: usize| j >= k && j < 64 ==> is_allocated_u64(&result, j)))]  // All bits including and after the kth bit should be set.
fn make_trailing_zeros_u64(k: usize) -> u64 {
    if k == 64 {0}
    else {u64::MAX << k}
}

#[trusted]
#[ensures(result <= 64)]  // The result should be within the range of the u64.
#[ensures(*u < u64::MAX ==> result < 64)]  // If u is not u64::MAX, the result should be less than 64.
#[ensures(forall(|k: usize| k < result ==> is_allocated_u64(u, k)))]  // All bits before the result should be set.
#[ensures(result < 64 ==> !is_allocated_u64(u, result))]  // The bit at the result position should be cleared.
fn my_trailing_ones(u: &u64) -> usize {
    u.trailing_ones() as usize
    // let mut k = 0;
    // while k < 64 {
    //     body_invariant!(k < 64);
    //     body_invariant!(forall(|j: usize| j < k ==> is_allocated_u64(u, j)));
    //     if !is_allocated_u64(u, k) {
    //         prusti_assert!(k < 64);
    //         prusti_assert!(*u < u64::MAX);
    //         break;
    //     }
    //     prusti_assert!(is_allocated_u64(u, k));
    //     prusti_assert!(forall(|j: usize| j <= k ==> is_allocated_u64(u, j)));
    //     prusti_assert!(k == 63 ==> forall(|j: usize| j < 64 ==> is_allocated_u64(u, j)));
    //     k += 1
    // };
    // prusti_assert!(k == 64 ==> *u == u64::MAX);
    // prusti_assert!(k < 64 ==> !is_allocated_u64(u, k));
    // k
}

#[trusted]
#[ensures(result <= 64)]  // The result should be within the range of the u64.
#[ensures(forall(|k: usize| k < result ==> !is_allocated_u64(u, k)))]  // All bits before the result should be cleared.
#[ensures(result < 64 ==> is_allocated_u64(u, result))]  // The bit at the result position should be cleared.
fn my_trailing_zeros(u: &u64) -> usize {
    u.trailing_zeros() as usize
    // let mut k = 0;
    // while k < 64 {
    //     body_invariant!(k < 64);
    //     body_invariant!(forall(|j: usize| j < k ==> !is_allocated_u64(u, j)));
    //     if is_allocated_u64(u, k) {break;}
    //     prusti_assert!(!is_allocated_u64(u, k));
    //     k += 1
    // }; k
}

#[requires(bitfield.len() > 0)]
#[requires(relevant_bits > 0)]
#[requires(relevant_bits <= bitfield.len() * 64)]  // Relevant bits within array bounds.
#[ensures(bitfield.len() == old(bitfield.len()))]  // No change to the length of the u64 array.
#[ensures(forall(|i: usize| ((i + 1) * 64 <= relevant_bits ==> bitfield[i].0 == 0)))]  // All relevant bits in u64's before the one containing the final relevant bit must be set to 0.
#[ensures(forall(|i: usize| (i < bitfield.len() && i * 64 >= relevant_bits ==> bitfield[i].0 == u64::MAX)))] // All bits after the u64 containing the final relevant bit must be set to allocated.
#[ensures(forall(|j: usize| (j * 64 < relevant_bits && (j + 1) * 64 > relevant_bits ==>  // The u64 containing the final relevant bit is set correctly.
    forall(|k: usize| (k < relevant_bits - j * 64 ==> !is_allocated_u64(&bitfield[j].0, k)))
)))]
#[ensures(forall(|j: usize| (j * 64 < relevant_bits && (j + 1) * 64 > relevant_bits ==> 
    forall(|k: usize| (k >= relevant_bits - j * 64 && k < 64 ==> is_allocated_u64(&bitfield[j].0, k)))
)))]
fn initialize(bitfield: &[AtomicU64], relevant_bits: usize) {
    let mut i: usize = 0;
    let zero_u64 = 0u64;  // Prusti requires these to be variables, not constants.
    let max_u64 = u64::MAX;
    while i < bitfield.len() {

        body_invariant!(i < bitfield.len());
        body_invariant!(bitfield.len() == old(bitfield.len()));
        body_invariant!(i * 64 < relevant_bits ==> forall(|j: usize| j < i ==> bitfield[j].0 == 0));
        body_invariant!(i * 64 >= relevant_bits ==> forall(|j: usize| ((j + 1) * 64 <= relevant_bits ==> bitfield[j].0 == 0)));
        body_invariant!(i * 64 >= relevant_bits ==> forall(|j: usize| (j * 64 >= relevant_bits && j < i ==> bitfield[j].0 == u64::MAX)));
        body_invariant!(i * 64 >= relevant_bits ==> 
            forall(|j: usize| (j * 64 < relevant_bits && (j + 1) * 64 > relevant_bits ==> 
                forall(|k: usize| k < (relevant_bits - j * 64) ==> !is_allocated_u64(&bitfield[j].0, k))    
            ))
        );
        body_invariant!(i * 64 >= relevant_bits ==> 
            forall(|j: usize| (j * 64 < relevant_bits && (j + 1) * 64 > relevant_bits ==> 
                forall(|k: usize| k >= (relevant_bits - j * 64) && k < 64 ==> is_allocated_u64(&bitfield[j].0, k))    
            ))
        );

        let bit_idx = i * 64;
        if bit_idx <= relevant_bits {
            let remaining_bits = relevant_bits - bit_idx;
            if remaining_bits >= 64 {bitfield[i].store(zero_u64, Ordering::Relaxed);}
            else {
                bitfield[i].store(make_trailing_zeros_u64(remaining_bits), Ordering::Relaxed);
                prusti_assert!(forall(|j: usize| j < remaining_bits ==> !is_allocated_u64(&bitfield[i].0, j)));
                prusti_assert!(forall(|j: usize| (j >= remaining_bits && j < 64) ==> is_allocated_u64(&bitfield[i].0, j)));
            }
        } else {
            bitfield[i].store(max_u64, Ordering::Relaxed);
            prusti_assert!(i * 64 >= relevant_bits);
            prusti_assert!(bitfield[i].0 == u64::MAX);
        }

        prusti_assert!(i * 64 >= relevant_bits ==> bitfield[i].0 == u64::MAX);
        prusti_assert!((i + 1) * 64 <= relevant_bits ==> bitfield[i].0 == 0);
        prusti_assert!(i * 64 < relevant_bits && (i + 1) * 64 > relevant_bits ==>
            forall(|j: usize| j < relevant_bits - bit_idx ==> !is_allocated_u64(&bitfield[i].0, j)));
        prusti_assert!(i * 64 < relevant_bits && (i + 1) * 64 > relevant_bits ==>
            forall(|j: usize| j >= relevant_bits - bit_idx && j < 64 ==> is_allocated_u64(&bitfield[i].0, j)));

        i += 1;
    }
    prusti_assert!(i > 0);
    prusti_assert!(i == bitfield.len());
    prusti_assert!(forall(|j: usize| ((j + 1) * 64 <= relevant_bits ==> bitfield[j].0 == 0)));
    prusti_assert!(forall(|j: usize| (j * 64 >= relevant_bits && j < bitfield.len() ==> bitfield[j].0 == u64::MAX)));
    prusti_assert!(forall(|j: usize| (j * 64 < relevant_bits && (j + 1) * 64 > relevant_bits ==> 
        forall(|k: usize| (k < relevant_bits - j * 64 ==> !is_allocated_u64(&bitfield[j].0, k)))
    )));
    prusti_assert!(forall(|j: usize| (j * 64 < relevant_bits && (j + 1) * 64 > relevant_bits ==> 
        forall(|k: usize| (k >= relevant_bits - j * 64 && k < 64 ==> is_allocated_u64(&bitfield[j].0, k)))
    )));
}

#[pure]
#[requires(bitfield.len() > 0)]
#[ensures(result.is_some() ==> peek_option(&result) ==> is_allocated_u64(&bitfield[idx / 64].0, idx % 64))]
fn is_allocated(bitfield: &[AtomicU64], idx: usize) -> Option<bool> {
    if idx < bitfield.len() * 64 {
        Some(is_allocated_u64(&bitfield[idx / 64].load(Ordering::Relaxed), idx % 64))
    } else {None}
}

#[requires(bitfield.len() > 0)]
#[requires(relevant_bits <= bitfield.len() * 64)]
#[requires(relevant_bits > 0)]
#[ensures(!result ==> exists(|i: usize| (  // If the bitfield is not full, there must be at least one bit within the relevant_bits range that is not set.
    ((i + 1) * 64 <= relevant_bits && bitfield[i].0 != u64::MAX) ||
    (i * 64 < relevant_bits && (i + 1) * 64 > relevant_bits &&
        exists(|j: usize| j < relevant_bits - i * 64 ==> !is_allocated_u64(&bitfield[i].0, j)))
)))]
#[ensures(result ==> forall(|i: usize| ((i + 1) * 64 <= relevant_bits ==> bitfield[i].0 == u64::MAX)))]  // If the bitfield is full, all u64's before the one containing the last relevant bit must be set to u64::MAX.
#[ensures(result ==> forall(|j: usize| (j * 64 < relevant_bits && (j + 1) * 64 > relevant_bits ==>  // If the bitfield is full, the u64 containing the last relevant bit must be set correctly (all bits before the last relevant bit are set to 1).
    forall(|k: usize| (k < relevant_bits - j * 64 ==> is_allocated_u64(&bitfield[j].0, k)))
)))]
fn is_full(bitfield: &[AtomicU64], relevant_bits: usize) -> bool {
    let mut i = 0;
    while i < bitfield.len() {

        body_invariant!(i < bitfield.len());
        body_invariant!(i * 64 < relevant_bits ==> forall(|j: usize| j < i ==> bitfield[j].0 == u64::MAX));
        body_invariant!(i * 64 >= relevant_bits ==> forall(|j: usize| ((j + 1) * 64 <= relevant_bits ==> bitfield[j].0 == u64::MAX)));
        body_invariant!(i * 64 >= relevant_bits ==> 
            forall(|j: usize| (j * 64 < relevant_bits && (j + 1) * 64 > relevant_bits ==> 
                forall(|k: usize| k < (relevant_bits - j * 64) ==> is_allocated_u64(&bitfield[j].0, k))    
            ))
        );
        
        let bit_idx = i * 64;
        if bit_idx <= relevant_bits {
            let remaining_bits = relevant_bits - bit_idx;
            if remaining_bits >= 64 {if bitfield[i].load(Ordering::Relaxed) != u64::MAX {return false;}}
            else if my_trailing_ones(&bitfield[i].load(Ordering::Relaxed)) < remaining_bits {return false;}
            else {
                prusti_assert!(forall(|j: usize| j < remaining_bits ==> is_allocated_u64(&bitfield[i].0, j)));
            }
        } else {}

        prusti_assert!((i + 1) * 64 <= relevant_bits ==> bitfield[i].0 == u64::MAX);
        prusti_assert!(i * 64 < relevant_bits && (i + 1) * 64 > relevant_bits ==>
            forall(|j: usize| j < relevant_bits - bit_idx ==> is_allocated_u64(&bitfield[i].0, j)));
        
        i += 1;
    }
    prusti_assert!(i > 0);
    prusti_assert!(i == bitfield.len());
    prusti_assert!(forall(|j: usize| ((j + 1) * 64 <= relevant_bits ==> bitfield[j].0 == u64::MAX)));
    prusti_assert!(forall(|j: usize| (j * 64 < relevant_bits && (j + 1) * 64 > relevant_bits ==> 
        forall(|k: usize| (k < relevant_bits - j * 64 ==> is_allocated_u64(&bitfield[j].0, k)))
    )));

    true
}

#[requires(bitfield.len() > 0)]
#[requires(relevant_bits <= bitfield.len() * 64)]
#[requires(relevant_bits > 0)]
#[ensures(!result ==> exists(|i: usize| (  // If the bitfield is not empty, there must be at least one bit within the relevant_bits range that is set.
    ((i + 1) * 64 <= relevant_bits && bitfield[i].0 > 0) ||
    (i * 64 < relevant_bits && (i + 1) * 64 > relevant_bits &&
        exists(|j: usize| j < relevant_bits - i * 64 ==> is_allocated_u64(&bitfield[i].0, j)))
)))]
#[ensures(result ==> forall(|i: usize| ((i + 1) * 64 <= relevant_bits ==> bitfield[i].0 == 0)))]  // If the bitfield is empty, all u64's before the one containing the last relevant bit must be set to 0.
#[ensures(result ==> forall(|j: usize| (j * 64 < relevant_bits && (j + 1) * 64 > relevant_bits ==>  // If the bitfield is empty, the u64 containing the last relevant bit must be set correctly (all bits before the last relevant bit are set to 0).
    forall(|k: usize| (k < relevant_bits - j * 64 ==> !is_allocated_u64(&bitfield[j].0, k)))
)))]
fn all_free(bitfield: &[AtomicU64], relevant_bits: usize) -> bool {
    let mut i = 0;
    while i < bitfield.len() {

        body_invariant!(i < bitfield.len());
        body_invariant!(bitfield.len() == old(bitfield.len()));
        body_invariant!(i * 64 <= relevant_bits ==> forall(|j: usize| (j < i ==> bitfield[j].0 == 0)));
        body_invariant!(i * 64 >= relevant_bits ==> forall(|j: usize| ((j + 1) * 64 <= relevant_bits ==> bitfield[j].0 == 0)));
        body_invariant!(i * 64 >= relevant_bits ==> 
            forall(|j: usize| (j * 64 < relevant_bits && (j + 1) * 64 > relevant_bits ==> 
                forall(|k: usize| k < (relevant_bits - j * 64) ==> !is_allocated_u64(&bitfield[j].0, k))    
            ))
        );

        let bit_idx = i * 64;
        if bit_idx <= relevant_bits {
            let remaining_bits = relevant_bits - bit_idx;
            if remaining_bits >= 64 {if bitfield[i].load(Ordering::Relaxed) != 0 {return false;}}
            else {
                let tz = my_trailing_zeros(&bitfield[i].load(Ordering::Relaxed));
                if tz < remaining_bits {
                    prusti_assert!(tz < 64);
                    prusti_assert!(is_allocated_u64(&bitfield[i].0, tz));
                    prusti_assert!(exists(|j: usize| j < remaining_bits && is_allocated_u64(&bitfield[i].0, j)));
                    return false;
                }
                else {
                    prusti_assert!(forall(|j: usize| j < tz ==> !is_allocated_u64(&bitfield[i].0, j)));
                    prusti_assert!(remaining_bits <= tz);
                    prusti_assert!(forall(|j: usize| j < remaining_bits ==> !is_allocated_u64(&bitfield[i].0, j)));
                }
            }
        } else {}

        prusti_assert!((i + 1) * 64 <= relevant_bits ==> bitfield[i].0 == 0);
        prusti_assert!(i * 64 < relevant_bits && (i + 1) * 64 > relevant_bits ==>
            forall(|j: usize| j < relevant_bits - bit_idx ==> !is_allocated_u64(&bitfield[i].0, j)));

        i += 1;
    }
    prusti_assert!(i > 0);
    prusti_assert!(i == bitfield.len());
    prusti_assert!(forall(|j: usize| ((j + 1) * 64 <= relevant_bits ==> bitfield[j].0 == 0)));
    prusti_assert!(forall(|j: usize| (j * 64 < relevant_bits && (j + 1) * 64 > relevant_bits ==> 
        forall(|k: usize| (k < relevant_bits - j * 64 ==> !is_allocated_u64(&bitfield[j].0, k)))
    )));

    true
}

#[ensures(idx < bitfield.len() * 64 ==> {  // Check that the bitfield isn't changed if the bit
    let base_idx = idx / 64;               // is already 0.
    let bit_idx = idx % 64;
    !is_allocated_u64(old(&bitfield[base_idx].0), bit_idx) ==>
        bitfield[base_idx].0 == old(bitfield[base_idx].0)
})]
#[ensures(idx < bitfield.len() * 64 ==> {  // Check that the bitfield value decreased if the bit
    let base_idx = idx / 64;               // was previously set to 1.
    let bit_idx = idx % 64;
    is_allocated_u64(old(&bitfield[base_idx].0), bit_idx) ==>
        bitfield[base_idx].0 < old(bitfield[base_idx].0)
})]
#[ensures(idx < bitfield.len() * 64 ==> {  // Check that the correct bit was flipped.
    let base_idx = idx / 64;
    let bit_idx = idx % 64;
    let p = power_of_two_u64(bit_idx);
    is_allocated_u64(old(&bitfield[base_idx].0), bit_idx) ==>
        old(bitfield[base_idx].0) - bitfield[base_idx].0 == p
})]
fn clear_bit(bitfield: &[AtomicU64], idx: usize) -> bool {
    if idx >= bitfield.len() * 64 {return false}
    let base_idx = idx / 64;
    let bit_idx = idx % 64;
    clear_bit_atomic_u64(&bitfield[base_idx], bit_idx);
    true
}

#[ensures(idx < bitfield.len() * 64 ==> {  // Check that the bitfield isn't changed if the bit
    let base_idx = idx / 64;               // is already set.
    let bit_idx = idx % 64;
    is_allocated_u64(old(&bitfield[base_idx].0), bit_idx) ==> bitfield[base_idx].0 == old(bitfield[base_idx].0)
})]
#[ensures(idx < bitfield.len() * 64 ==> {  // Check that the bitfield value increased if the bit
    let base_idx = idx / 64;               // wasn't previously set.
    let bit_idx = idx % 64;
    !is_allocated_u64(old(&bitfield[base_idx].0), bit_idx) ==> bitfield[base_idx].0 > old(bitfield[base_idx].0)
})]
#[ensures(idx < bitfield.len() * 64 ==> {  // Check that the correct bit was flipped.
    let base_idx = idx / 64;
    let bit_idx = idx % 64;
    let p = power_of_two_u64(bit_idx);
    !is_allocated_u64(old(&bitfield[base_idx].0), bit_idx) ==> bitfield[base_idx].0 - old(bitfield[base_idx].0) == p
})]
fn set_bit(bitfield: &[AtomicU64], idx: usize) -> bool {
    if idx >= bitfield.len() * 64 {return false}
    let base_idx = idx / 64;
    let bit_idx = idx % 64;
    set_bit_atomic_u64(&bitfield[base_idx], bit_idx);
    true
}

#[requires(u < u64::MAX)]
#[ensures(result < 64)]  // Correct range for result
#[ensures(!is_allocated_u64(&u, result))] // Check that the result index is available
#[ensures(forall(|j: usize| j < result ==> is_allocated_u64(&u, j)))]  // Check that the result index is the first one available (all previous indices allocated)
fn first_fit_idx(u: u64) -> usize {
    let i = my_trailing_ones(&u);
    prusti_assert!(i < 64);
    prusti_assert!(!is_allocated_u64(&u, i));
    prusti_assert!(forall(|j: usize| j < i ==> is_allocated_u64(&u, j)));
    i
}

#[requires(layout_size > 0)]
#[requires(layout_align > 0)]
#[requires(u < u64::MAX)]
#[ensures(result.is_some() ==> {  // The returned index should within the bounds of the current u64.
    let (idx, addr) = peek_option(&result);
    idx >= base_idx * 64 && idx < base_idx * 64 + 64
})]
#[ensures(result.is_some() ==> {  // The index is mapped to the correct address.
    let (idx, addr) = peek_option(&result);
    addr == base_addr + idx * layout_size
})]
#[ensures(result.is_some() ==> {  // Check that the returned address does not overlap with metadata. 
    let (idx, addr) = peek_option(&result);
    addr - base_addr <= page_size - metadata_size - layout_size && addr % layout_align == 0
})]
#[ensures(result.is_some() ==> {  // Check that the result index is available
    let (idx, addr) = peek_option(&result);
    !is_allocated_u64(&u, idx - base_idx * 64)
})]
#[ensures(result.is_some() ==> {  // Check that the result index is the first one available (all previous indices allocated)
    let (idx, addr) = peek_option(&result);
    forall(|j: usize| j < idx - base_idx * 64 ==> is_allocated_u64(&u, j))
})]
fn first_fit_in_u64 (
    u: u64,
    base_idx: usize,
    base_addr: usize,
    layout_size: usize,
    layout_align: usize,
    page_size: usize,
    metadata_size: usize
) -> Option<(usize, usize)> {
    let first_free = first_fit_idx(u);
    let idx = base_idx * 64 + first_free;
    let offset = idx * layout_size;
    let addr = base_addr + offset;
    if offset <= (page_size - metadata_size - layout_size) && addr % layout_align == 0 {
        Some((idx, addr))
    } else {None}
}

#[requires(forall(|i: usize| i < bitfield.len() ==> bitfield[i].0 <= u64::MAX))]
#[requires(layout_size > 0)]
#[ensures(result.is_some() ==> {  // Check that the returned index is within range and that the address is correct.
    let (idx, addr) = peek_option(&result);
    idx < bitfield.len() * 64 && addr == base_addr + idx * layout_size
})]
#[ensures(result.is_some() ==> {  // Check that the returned address does not overlap with metadata.
    let (idx, addr) = peek_option(&result);
    addr - base_addr <= page_size - metadata_size - layout_size && addr % layout_align == 0
})]
#[ensures(result.is_some() ==> {  // Ensure that all u64 before the returned index is full. The result being the first free bit of its u64 is already guaranteed by `first_fit_in_u64`.
    let (idx, addr) = peek_option(&result);
    let base_idx = idx / 64;
    forall(|i: usize| i < base_idx ==> bitfield[i].0 == u64::MAX)
})]
#[ensures(forall(|i: usize| i < bitfield.len() ==> bitfield[i].0 == u64::MAX) ==> !result.is_some())]  // No result if the bitfield is full.
#[ensures(result.is_some() ==> {  // Check that the result index is available
    let (idx, addr) = peek_option(&result);
    !is_allocated_u64(&bitfield[idx / 64].0, idx % 64)
})]
#[ensures(result.is_some() ==> {  // Check that the result index is the first one available in the u64 containing it (all previous indices allocated)
    let (idx, addr) = peek_option(&result);
    forall(|j: usize| j < idx % 64 ==> is_allocated_u64(&bitfield[idx / 64].0, j))
})]
fn first_fit(
    bitfield: &[AtomicU64],
    base_addr: usize,
    layout_size: usize,
    layout_align: usize,
    page_size: usize,
    metadata_size: usize
) -> Option<(usize, usize)> {
    if layout_align == 0 {return None};
    let mut base_idx = 0;
    while base_idx < bitfield.len() {

        body_invariant!(base_idx < bitfield.len());
        body_invariant!(forall(|i: usize| i < bitfield.len() ==> bitfield[i].0 <= u64::MAX));
        body_invariant!(forall(|i: usize| i < base_idx ==> bitfield[i].0 == u64::MAX));  // All previous u64 must have max value

        let current_val = bitfield[base_idx].load(Ordering::Relaxed);
        if current_val < u64::MAX {
            return first_fit_in_u64(current_val, base_idx, base_addr, layout_size, layout_align, page_size, metadata_size)
        }

        prusti_assert!(current_val == u64::MAX);
        prusti_assert!(forall(|i: usize| i <= base_idx ==> bitfield[i].0 == u64::MAX));

        base_idx += 1;
    }

    prusti_assert!(forall(|i: usize| i < bitfield.len() ==> bitfield[i].0 == u64::MAX));

    None
}


// This code allows for easy expansion of the TrustedBitfield structs. To have trusted bitfields with longer or shorter lengths
// than 8 * 64, simply copy paste the struct and its `impl` block and rename and change size where needed. The new trusted bitfields
// will have the same correctness guarantees as TrustedBitfield8.

#[invariant(self.relevant_bits <= self.bitfield.len() * 64)]  // The number of used bits cannot exceed the maximum number of available bits.
#[invariant(self.relevant_bits > 0)]  // The number of used bits should be more than 0.
#[invariant(self.layout_size > 0)]
pub struct TrustedBitfield8 {  // Change name for other bitfield types
    bitfield: [AtomicU64; TrustedBitfield8::SIZE],  // Change name for other bitfield sizes
    relevant_bits: usize,
    layout_size: usize,
    dealloc_callback_generated: bool
}

impl TrustedBitfield8 {
    const SIZE: usize = 8;  // Change this for other bitfield sizes

    pub fn is_allocated(&self, idx: usize) -> Option<bool> {is_allocated(&self.bitfield, idx)}
    pub fn is_full(&self) -> bool {is_full(&self.bitfield, self.relevant_bits)}
    pub fn all_free(&self) -> bool {all_free(&self.bitfield, self.relevant_bits)}

    pub fn new(
        for_size: usize,
        capacity: usize
    ) -> Option<Self> {
        let valid_args =
            for_size > 0 && capacity > 0 && for_size <= capacity;
        if valid_args {
            let bitfield =
                [AtomicU64::new(0), AtomicU64::new(0), AtomicU64::new(0), AtomicU64::new(0),
                AtomicU64::new(0), AtomicU64::new(0), AtomicU64::new(0), AtomicU64::new(0)];  // Change this for other bitfield sizes
            let available_bits = bitfield.len() * 64;
            let wanted_bits = capacity / for_size;
            let relevant_bits = if wanted_bits <= available_bits {wanted_bits} else {available_bits};
            let trusted_bitfield = TrustedBitfield8 {  // Change this for other bitfield types
                bitfield, relevant_bits, layout_size: for_size,
                dealloc_callback_generated: false
            };
            initialize(&trusted_bitfield.bitfield, relevant_bits);
            Some(trusted_bitfield)
        } else {None}
    }

    pub fn first_fit_and_set(&self, layout_align: usize, base_addr: usize, page_size: usize, metadata_size: usize) -> Option<VerifiedAllocAddr> {
        if let Some((idx, addr)) = first_fit(&self.bitfield, base_addr, self.layout_size, layout_align, page_size, metadata_size) {
            set_bit(&self.bitfield, idx);
            Some(VerifiedAllocAddr(addr))
        } else {None}
    }

    pub fn clear_verified_addr(&self, addr: VerifiedDeallocAddr, base_addr: usize) -> bool {  // Should take ownership of the VerifiedDeallocAddr
        if addr.0 >= base_addr {
            clear_bit(&self.bitfield, (addr.0 - base_addr) / self.layout_size)
        } else {false}
    }
    
    #[trusted]
    pub fn dealloc_callback(&mut self) -> Option<fn(addr: usize) -> VerifiedDeallocAddr> {
        if self.dealloc_callback_generated {None} else {self.dealloc_callback_generated = true; Some(new_verified_dealloc_addr)}
    }
}