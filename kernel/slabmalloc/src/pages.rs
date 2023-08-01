use crate::*;
use core::sync::atomic::{AtomicU64, Ordering};
use prusti_contracts::*;

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

#[ensures(result <= 64)]  // The result should be within the range of the u64.
#[ensures(*u < u64::MAX ==> result < 64)]  // If u is not u64::MAX, the result should be less than 64.
#[ensures(forall(|k: usize| k < result ==> is_allocated_u64(u, k)))]  // All bits before the result should be set.
#[ensures(result < 64 ==> !is_allocated_u64(u, result))]  // The bit at the result position should be cleared.
fn my_trailing_ones(u: &u64) -> usize {
    let mut k = 0;
    while k < 64 {
        body_invariant!(k < 64);
        body_invariant!(forall(|j: usize| j < k ==> is_allocated_u64(u, j)));
        if !is_allocated_u64(u, k) {
            prusti_assert!(k < 64);
            prusti_assert!(*u < u64::MAX);
            break;
        }
        prusti_assert!(is_allocated_u64(u, k));
        prusti_assert!(forall(|j: usize| j <= k ==> is_allocated_u64(u, j)));
        prusti_assert!(k == 63 ==> forall(|j: usize| j < 64 ==> is_allocated_u64(u, j)));
        k += 1
    };
    prusti_assert!(k == 64 ==> *u == u64::MAX);
    prusti_assert!(k < 64 ==> !is_allocated_u64(u, k));
    k
}

#[ensures(result <= 64)]  // The result should be within the range of the u64.
#[ensures(forall(|k: usize| k < result ==> !is_allocated_u64(u, k)))]  // All bits before the result should be cleared.
#[ensures(result < 64 ==> is_allocated_u64(u, result))]  // The bit at the result position should be cleared.
fn my_trailing_zeros(u: &u64) -> usize {
    let mut k = 0;
    while k < 64 {
        body_invariant!(k < 64);
        body_invariant!(forall(|j: usize| j < k ==> !is_allocated_u64(u, j)));
        if is_allocated_u64(u, k) {break;}
        prusti_assert!(!is_allocated_u64(u, k));
        k += 1
    }; k
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

/// A trait defining bitfield operations we need for tracking allocated objects within a page.
pub(crate) trait Bitfield {
    fn initialize(&mut self, for_size: usize, capacity: usize);
    fn first_fit(
        &self,
        base_addr: usize,
        layout: Layout,
        page_size: usize,
        metadata_size: usize,
    ) -> Option<(usize, usize)>;
    fn is_allocated(&self, idx: usize) -> bool;
    fn set_bit(&self, idx: usize);
    fn clear_bit(&self, idx: usize);
    fn is_full(&self) -> bool;
    fn all_free(&self, relevant_bits: usize) -> bool;
}

/// Implementation of bit operations on u64 slices.
///
/// We allow deallocations (i.e. clearing a bit in the field)
/// from any thread. That's why the bitfield is a bunch of AtomicU64.
impl Bitfield for [AtomicU64] {
    /// Initialize the bitfield
    ///
    /// # Arguments
    ///  * `for_size`: Object size we want to allocate
    ///  * `capacity`: Maximum size of the buffer the bitmap maintains.
    ///
    /// Ensures that we only have free slots for what we can allocate
    /// within the page (by marking everything else allocated).
    // fn initialize(&mut self, for_size: usize, capacity: usize) {
    //     // Set everything to allocated
    //     for bitmap in self.iter_mut() {
    //         *bitmap = AtomicU64::new(u64::max_value());
    //     }

    //     // Mark actual slots as free
    //     let relevant_bits = core::cmp::min(capacity / for_size, self.len() * 64);
    //     for idx in 0..relevant_bits {
    //         self.clear_bit(idx);
    //     }
    // }
    fn initialize(&mut self, for_size: usize, capacity: usize) {
        initialize(self, core::cmp::min(capacity / for_size, self.len() * 64))
    }

    /// Tries to find a free block of memory that satisfies `alignment` requirement.
    ///
    /// # Notes
    /// * We pass size here to be able to calculate the resulting address within `data`.
    // fn first_fit(
    //     &self,
    //     base_addr: usize,
    //     layout: Layout,
    //     page_size: usize,
    //     metadata_size: usize
    // ) -> Option<(usize, usize)> {
    //     for (base_idx, b) in self.iter().enumerate() {
    //         let bitval = b.load(Ordering::Relaxed);
    //         if bitval == u64::max_value() {
    //             continue;
    //         } else {
    //             let negated = !bitval;
    //             let first_free = negated.trailing_zeros() as usize;
    //             let idx: usize = base_idx * 64 + first_free;
    //             let offset = idx * layout.size();

    //             // TODO(bad): psize needs to be passed as arg
    //             let offset_inside_data_area = offset <= (page_size - metadata_size - layout.size());
    //             if !offset_inside_data_area {
    //                 return None;
    //             }

    //             let addr: usize = base_addr + offset;
    //             let alignment_ok = addr % layout.align() == 0;
    //             let block_is_free = bitval & (1 << first_free) == 0;
    //             if alignment_ok && block_is_free {
    //                 return Some((idx, addr));
    //             }
    //         }
    //     }
    //     None
    // }
    fn first_fit(
        &self,
        base_addr: usize,
        layout: Layout,
        page_size: usize,
        metadata_size: usize
    ) -> Option<(usize, usize)> {
        first_fit(self, base_addr, layout.size(), layout.align(), page_size, metadata_size)
    }

    /// Check if the bit `idx` is set.
    // #[inline(always)]
    // fn is_allocated(&self, idx: usize) -> bool {
    //     let base_idx = idx / 64;
    //     let bit_idx = idx % 64;
    //     (self[base_idx].load(Ordering::Relaxed) & (1 << bit_idx)) > 0
    // }
    fn is_allocated(&self, idx: usize) -> bool {
        is_allocated(self, idx).unwrap()
    }

    /// Sets the bit number `idx` in the bit-field.
    // #[inline(always)]
    // fn set_bit(&self, idx: usize) {
    //     let base_idx = idx / 64;
    //     let bit_idx = idx % 64;
    //     self[base_idx].fetch_or(1 << bit_idx, Ordering::Relaxed);
    // }
    fn set_bit(&self, idx: usize) {
        set_bit(self, idx);
    }

    /// Clears bit number `idx` in the bit-field.
    // #[inline(always)]
    // fn clear_bit(&self, idx: usize) {
    //     let base_idx = idx / 64;
    //     let bit_idx = idx % 64;
    //     self[base_idx].fetch_and(!(1 << bit_idx), Ordering::Relaxed);
    // }
    fn clear_bit(&self, idx: usize) {
        clear_bit(self, idx);
    }

    /// Checks if we could allocate more objects of a given `alloc_size` within the
    /// `capacity` of the memory allocator.
    ///
    /// # Note
    /// The ObjectPage will make sure to mark the top-most bits as allocated
    /// for large sizes (i.e., a size 512 SCAllocator will only really need 3 bits)
    /// to track allocated objects). That's why this function can be simpler
    /// than it would need to be in practice.
    #[inline(always)]
    // fn is_full(&self) -> bool {
    //     self.iter()
    //         .filter(|&x| x.load(Ordering::Relaxed) != u64::max_value())
    //         .count()
    //         == 0
    // }
    fn is_full(&self) -> bool {
        is_full(self, self.len() * 64)
    }

    /// Checks if the page has currently no allocations.
    ///
    /// This is called `all_free` rather than `is_emtpy` because
    /// we already have an is_empty fn as part of the slice.
    // fn all_free(&self, relevant_bits: usize) -> bool {
    //     for (idx, bitmap) in self.iter().enumerate() {
    //         let checking_bit_range = (idx * 64, (idx + 1) * 64);
    //         if relevant_bits >= checking_bit_range.0 && relevant_bits < checking_bit_range.1 {
    //             // Last relevant bitmap, here we only have to check that a subset of bitmap is marked free
    //             // the rest will be marked full
    //             let bits_that_should_be_free = relevant_bits - checking_bit_range.0;
    //             let free_mask = (1 << bits_that_should_be_free) - 1;
    //             return (free_mask & bitmap.load(Ordering::Relaxed)) == 0;
    //         }

    //         if bitmap.load(Ordering::Relaxed) == 0 {
    //             continue;
    //         } else {
    //             return false;
    //         }
    //     }

    //     true
    // }
    fn all_free(&self, relevant_bits: usize) -> bool {
        all_free(self, relevant_bits)
    }
}

/// This trait is used to define a page from which objects are allocated
/// in an `SCAllocator`.
///
/// The implementor of this trait needs to provide access to the page meta-data,
/// which consists of:
/// - `MappedPages8k` object that owns this memory
/// - A bitfield (to track allocations),
/// - `prev` and `next` pointers to insert the page in free lists
pub trait AllocablePage {
    /// The total size (in bytes) of the page.
    ///
    /// # Note
    /// We also assume that the address of the page will be aligned to `SIZE`.
    const SIZE: usize;

    const METADATA_SIZE: usize;

    const HEAP_ID_OFFSET: usize;

    fn new(mp: MappedPages8k, heap_id: usize) -> Self 
    where
        Self: core::marker::Sized;
    fn retrieve_mapped_pages(&mut self) -> Option<MappedPages8k>;
    fn clear_metadata(&mut self);
    fn set_heap_id(&mut self, heap_id: usize);
    fn heap_id(&self) -> usize;
    fn bitfield(&self) -> &[AtomicU64; 8];
    fn bitfield_mut(&mut self) -> &mut [AtomicU64; 8];
    fn prev(&mut self) -> &mut Rawlink<Self>
    where
        Self: core::marker::Sized;
    fn next(&mut self) -> &mut Rawlink<Self>
    where
        Self: core::marker::Sized;
    fn buffer_size() -> usize;

    /// Tries to find a free block within `data` that satisfies `alignment` requirement.
    fn first_fit(&self, layout: Layout) -> Option<(usize, usize)> {
        let base_addr = (self as *const Self as *const u8) as usize;
        self.bitfield().first_fit(base_addr, layout, Self::SIZE, Self::METADATA_SIZE)
    }

    /// Tries to allocate an object within this page.
    ///
    /// In case the slab is full, returns a null ptr.
    fn allocate(&mut self, layout: Layout) -> *mut u8 {
        match self.first_fit(layout) {
            Some((idx, addr)) => {
                self.bitfield().set_bit(idx);
                addr as *mut u8
            }
            None => ptr::null_mut(),
        }
    }

    /// Checks if we can still allocate more objects of a given layout within the page.
    fn is_full(&self) -> bool {
        self.bitfield().is_full()
    }

    /// Checks if the page has currently no allocations.
    fn is_empty(&self, relevant_bits: usize) -> bool {
        self.bitfield().all_free(relevant_bits)
    }

    /// Deallocates a memory object within this page.
    fn deallocate(&self, ptr: NonNull<u8>, layout: Layout) -> Result<(), &'static str> {
        // trace!(
        //     "AllocablePage deallocating ptr = {:p} with {:?}",
        //     ptr,
        //     layout
        // );
        let page_offset = (ptr.as_ptr() as usize) & (Self::SIZE - 1);
        assert!(page_offset % layout.size() == 0);
        let idx = page_offset / layout.size();
        assert!(
            self.bitfield().is_allocated(idx),
            "{:p} not marked allocated?",
            ptr
        );

        self.bitfield().clear_bit(idx);
        Ok(())
    }
}


/// Holds allocated data within 2 4-KiB pages.
///
/// Has a data-section where objects are allocated from
/// and a small amount of meta-data in form of a bitmap
/// to track allocations at the end of the page.
///
/// # Notes
/// An object of this type will be exactly 8 KiB.
/// It is marked `repr(C)` because we rely on a well defined order of struct
/// members (e.g., dealloc does a cast to find the bitfield).
#[repr(C)]
pub struct ObjectPage8k<'a> {
    /// Holds memory objects.
    #[allow(dead_code)]
    data: [u8; ObjectPage8k::SIZE - ObjectPage8k::METADATA_SIZE],
    
    /// The MappedPages this memory area belongs to
    pub mp: Option<MappedPages8k>,

    pub heap_id: usize,

    /// Next element in list (used by `PageList`).
    next: Rawlink<ObjectPage8k<'a>>,
    /// Previous element in  list (used by `PageList`)
    prev: Rawlink<ObjectPage8k<'a>>,

    /// A bit-field to track free/allocated memory within `data`.
    pub(crate) bitfield: [AtomicU64; 8],
}


// These needs some more work to be really safe...
unsafe impl<'a> Send for ObjectPage8k<'a> {}
unsafe impl<'a> Sync for ObjectPage8k<'a> {}

impl<'a> AllocablePage for ObjectPage8k<'a> {
    const SIZE: usize = 8192;
    const METADATA_SIZE: usize = core::mem::size_of::<Option<MappedPages8k>>() + core::mem::size_of::<usize>() + (2*core::mem::size_of::<Rawlink<ObjectPage8k<'a>>>()) + (8*8);
    const HEAP_ID_OFFSET: usize = Self::SIZE - (core::mem::size_of::<usize>() + (2*core::mem::size_of::<Rawlink<ObjectPage8k<'a>>>()) + (8*8));

    /// Creates a new 8KiB allocable page and stores the MappedPages object in the metadata portion.
    fn new(mp: MappedPages8k, heap_id: usize) -> ObjectPage8k<'a> {
        ObjectPage8k {
            data: [0; ObjectPage8k::SIZE -ObjectPage8k::METADATA_SIZE],
            mp: Some(mp),
            heap_id,
            next: Rawlink::default(),
            prev: Rawlink::default(),
            bitfield: [AtomicU64::new(0), AtomicU64::new(0), AtomicU64::new(0), AtomicU64::new(0), AtomicU64::new(0), AtomicU64::new(0), AtomicU64::new(0),AtomicU64::new(0) ],
        }
    }

    /// Returns the MappedPages object that was stored in the metadata portion of the page.
    fn retrieve_mapped_pages(&mut self) -> Option<MappedPages8k> {
        let mut mp = None;
        core::mem::swap(&mut self.mp, &mut mp);
        mp
    }

    /// clears the metadata section of the page
    fn clear_metadata(&mut self) {
        self.heap_id = 0;
        self.next = Rawlink::default();
        self.prev = Rawlink::default();
        for bf in &self.bitfield {
            bf.store(0, Ordering::SeqCst);
        }
    }

    fn set_heap_id(&mut self, heap_id: usize){
        self.heap_id = heap_id;
    }

    fn heap_id(&self) -> usize {
        self.heap_id
    }

    fn bitfield(&self) -> &[AtomicU64; 8] {
        &self.bitfield
    }
    fn bitfield_mut(&mut self) -> &mut [AtomicU64; 8] {
        &mut self.bitfield
    }

    fn prev(&mut self) -> &mut Rawlink<Self> {
        &mut self.prev
    }

    fn next(&mut self) -> &mut Rawlink<Self> {
        &mut self.next
    }

    fn buffer_size() -> usize {
        ObjectPage8k::SIZE - ObjectPage8k::METADATA_SIZE
    }
}

impl<'a> Default for ObjectPage8k<'a> {
    fn default() -> ObjectPage8k<'a> {
        unsafe { mem::MaybeUninit::zeroed().assume_init() }
    }
}

impl<'a> fmt::Debug for ObjectPage8k<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "ObjectPage8k")
    }
}


/// A wrapper type around MappedPages which ensures that the MappedPages
/// have a size and alignment of 8 KiB and are writable.
pub struct MappedPages8k(MappedPages);

impl MappedPages8k {
    pub const SIZE: usize = ObjectPage8k::SIZE;
    pub const BUFFER_SIZE: usize = ObjectPage8k::SIZE - ObjectPage8k::METADATA_SIZE;
    pub const METADATA_SIZE: usize = ObjectPage8k::METADATA_SIZE;
    pub const HEAP_ID_OFFSET: usize = ObjectPage8k::HEAP_ID_OFFSET;
    
    /// Creates a MappedPages8k object from MappedPages that have a size and alignment of 8 KiB and are writable.
    pub fn new(mp: MappedPages) -> Result<MappedPages8k, &'static str> {
        let vaddr = mp.start_address().value();
        
        // check that the mapped pages are aligned to 8k
        if vaddr % Self::SIZE != 0 {
            error!("Trying to create a MappedPages8k but MappedPages were not aligned at 8k bytes");
            return Err("Trying to create a MappedPages8k but MappedPages were not aligned at 8k bytes");
        }

        // check that the mapped pages is writable
        if !mp.flags().is_writable() {
            error!("Trying to create a MappedPages8k but MappedPages were not writable (flags: {:?})",  mp.flags());
            return Err("Trying to create a MappedPages8k but MappedPages were not writable");
        }
        
        // check that the mapped pages size is equal in size to the page
        if Self::SIZE != mp.size_in_bytes() {
            error!("Trying to create a MappedPages8k but MappedPages were not 8 KiB (size: {} bytes)", mp.size_in_bytes());
            return Err("Trying to create a MappedPages8k but MappedPages were not 8 KiB");
        }

        let mut mp_8k = MappedPages8k(mp);
        mp_8k.as_objectpage8k_mut().clear_metadata();
        Ok(mp_8k)
    }

    // /// Return the pages represented by the MappedPages8k as an ObjectPage8k reference
    // fn as_objectpage8k(&self) -> &ObjectPage8k {
    //     // SAFE: we guarantee the size and lifetime are within that of this MappedPages object
    //     unsafe {
    //         mem::transmute(self.0.start_address())
    //     }
    // }

    /// Return the pages represented by the MappedPages8k as a mutable ObjectPage8k reference
    fn as_objectpage8k_mut(&mut self) -> &mut ObjectPage8k {
        // SAFE: we guarantee the size and lifetime are within that of this MappedPages object
        unsafe {
            mem::transmute(self.0.start_address())
        }
    }

    pub fn start_address(&self) -> VirtualAddress {
        self.0.start_address()
    }
}


/// A list of pages.
pub(crate) struct PageList<'a, T: AllocablePage> {
    /// Points to the head of the list.
    pub(crate) head: Option<&'a mut T>,
    /// Number of elements in the list.
    pub(crate) elements: usize,
}

impl<'a, T: AllocablePage> PageList<'a, T> {
    #[cfg(feature = "unstable")]
    pub(crate) const fn new() -> PageList<'a, T> {
        PageList {
            head: None,
            elements: 0,
        }
    }

    #[cfg(not(feature = "unstable"))]
    pub(crate) fn new() -> PageList<'a, T> {
        PageList {
            head: None,
            elements: 0,
        }
    }

    pub(crate) fn iter_mut<'b: 'a>(&mut self) -> ObjectPageIterMut<'b, T> {
        let m = match self.head {
            None => Rawlink::none(),
            Some(ref mut m) => Rawlink::some(*m),
        };

        ObjectPageIterMut {
            head: m,
            phantom: core::marker::PhantomData,
        }
    }

    /// Inserts `new_head` at the front of the list.
    pub(crate) fn insert_front<'b>(&'b mut self, mut new_head: &'a mut T) {
        match self.head {
            None => {
                *new_head.prev() = Rawlink::none();
                self.head = Some(new_head);
            }
            Some(ref mut head) => {
                *new_head.prev() = Rawlink::none();
                *head.prev() = Rawlink::some(new_head);
                mem::swap(head, &mut new_head);
                *head.next() = Rawlink::some(new_head);
            }
        }

        self.elements += 1;
    }

    /// Removes `slab_page` from the list.
    pub(crate) fn remove_from_list(&mut self, slab_page: &mut T) {
        unsafe {
            match slab_page.prev().resolve_mut() {
                None => {
                    self.head = slab_page.next().resolve_mut();
                }
                Some(prev) => {
                    *prev.next() = match slab_page.next().resolve_mut() {
                        None => Rawlink::none(),
                        Some(next) => Rawlink::some(next),
                    };
                }
            }

            match slab_page.next().resolve_mut() {
                None => (),
                Some(next) => {
                    *next.prev() = match slab_page.prev().resolve_mut() {
                        None => Rawlink::none(),
                        Some(prev) => Rawlink::some(prev),
                    };
                }
            }
        }

        *slab_page.prev() = Rawlink::none();
        *slab_page.next() = Rawlink::none();
        self.elements -= 1;
    }

    /// Removes `slab_page` from the list.
    pub(crate) fn pop<'b>(&'b mut self) -> Option<&'a mut T> {
        match self.head {
            None => None,
            Some(ref mut head) => {
                let head_next = head.next();
                let mut new_head = unsafe { head_next.resolve_mut() };
                mem::swap(&mut self.head, &mut new_head);
                let _ = self.head.as_mut().map(|n| {
                    *n.prev() = Rawlink::none();
                });

                self.elements -= 1;
                new_head.map(|node| {
                    *node.prev() = Rawlink::none();
                    *node.next() = Rawlink::none();
                    node
                })
            }
        }
    }

    /// Does the list contain `s`?
    pub(crate) fn contains(&mut self, s: *const T) -> bool {
        for slab_page in self.iter_mut() {
            if core::ptr::eq(slab_page, s) {
                return true;
            }
        }

        false
    }
}

/// Iterate over all the pages inside a slab allocator
pub(crate) struct ObjectPageIterMut<'a, P: AllocablePage> {
    head: Rawlink<P>,
    phantom: core::marker::PhantomData<&'a P>,
}

impl<'a, P: AllocablePage + 'a> Iterator for ObjectPageIterMut<'a, P> {
    type Item = &'a mut P;

    #[inline]
    fn next(&mut self) -> Option<&'a mut P> {
        unsafe {
            self.head.resolve_mut().map(|next| {
                self.head = match next.next().resolve_mut() {
                    None => Rawlink::none(),
                    Some(ref mut sp) => Rawlink::some(*sp),
                };
                next
            })
        }
    }
}

/// Rawlink is a type like `Option<T>` but for holding a raw pointer.
///
/// We use it to link AllocablePages together. You probably won't need
/// to use this type if you're not implementing AllocablePage
/// for a custom page-size.
pub struct Rawlink<T> {
    p: *mut T,
}

impl<T> Default for Rawlink<T> {
    fn default() -> Self {
        Rawlink { p: ptr::null_mut() }
    }
}

impl<T> Rawlink<T> {
    /// Like Option::None for Rawlink
    pub(crate) fn none() -> Rawlink<T> {
        Rawlink { p: ptr::null_mut() }
    }

    /// Like Option::Some for Rawlink
    pub(crate) fn some(n: &mut T) -> Rawlink<T> {
        Rawlink { p: n }
    }

    /// Convert the `Rawlink` into an Option value
    ///
    /// **unsafe** because:
    ///
    /// - Dereference of raw pointer.
    /// - Returns reference of arbitrary lifetime.
    #[allow(dead_code)]
    pub(crate) unsafe fn resolve<'a>(&self) -> Option<&'a T> {
        self.p.as_ref()
    }

    /// Convert the `Rawlink` into an Option value
    ///
    /// **unsafe** because:
    ///
    /// - Dereference of raw pointer.
    /// - Returns reference of arbitrary lifetime.
    pub(crate) unsafe fn resolve_mut<'a>(&mut self) -> Option<&'a mut T> {
        self.p.as_mut()
    }

    /// Return the `Rawlink` and replace with `Rawlink::none()`
    #[allow(dead_code)]
    pub(crate) fn take(&mut self) -> Rawlink<T> {
        mem::replace(self, Rawlink::none())
    }
}

