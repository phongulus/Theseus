use vstd::prelude::*;

// Verify with:
// ../verus/source/tools/rust-verify.sh ./libs/trusted_bitfield/src/verus_verified.rs --profile

verus! {

    fn main() {

        // Basic assertions on bitshifting by one position.
        assert(forall|i: u64| i >> 1u64 == i / 2) by (bit_vector);
        assert(forall|i: u64| i << 1u64 == mul(i, 2)) by (bit_vector);

        // Equivalence of bit shifting 1u64 with power of 2 function
        // We work with the following specification for the power of 2 function:
        //   - f(0) = 1
        //   - f(n) = 2 * f(n - 1) where n > 0 and n < 64 (due to the limitation of the u64 type)
        // We assume this specification is satisfied by ONE unique function, hence the
        // equivalence between the bitshift expression and the power of 2 function.
        // (Do we need to formally prove the uniqueness of this function?)
        assert(1u64 << 0u64 == 1u64) by (bit_vector);  // Base case
        assert(forall|i: u64| i > 0 && i < 64 ==>      // Induction hypothesis
            1u64 << i == mul(2, 1u64 << sub(i, 1u64))) by (bit_vector);

        // Some other properties of the power of 2 function
        assert(forall|i: u64| i < 64 ==> (1u64 << i) > 0) by (bit_vector);
        assert(forall|i: u64| i < 64 ==> (1u64 << i) < u64::MAX) by (bit_vector);

        // From now, we consider the expression (1u64 << k) to be equivalent to 2u64.pow(k)
        // given the above proof.

        // Set bit function properties
        // If the bit was previously set, setting the bit does NOT change anything.
        assert(forall|i: u64, k: u64| #![auto] k < 64 ==> (i & (1u64 << k) > 0 <==> i | (1u64 << k) == i)) by (bit_vector);
        // If the bit was not previously set, setting the bit adds 2^k.
        assert(forall|i: u64, k: u64| #![auto] k < 64 ==> (i & (1u64 << k) == 0 <==> i | (1u64 << k) == add(i, 1u64 << k))) by (bit_vector);
        // Setting the bit, whether changing anything or not, always results in the bit reading 1 afterwards.
        assert(forall|i: u64, k: u64| #![auto] k < 64 ==> ((i | (1u64 << k)) & (1u64 << k) > 0)) by (bit_vector); // R: are the parentheses correct?

        // Clear bit function properties
        // If the bit was previously cleared, clearing the bit does NOT change anything.
        assert(forall|i: u64, k: u64| #![auto] k < 64 ==> (i & (1u64 << k) == 0 <==> i & !(1u64 << k) == i)) by (bit_vector);
        // If the bit was not previously cleared, clearing the bit subtracts 2^k.
        assert(forall|i: u64, k: u64| #![auto] k < 64 ==> (i & (1u64 << k) > 0 <==> i & !(1u64 << k) == sub(i, 1u64 << k))) by (bit_vector);
        // Clearing the bit, whether changing anything or not, always results in the bit reading 0 afterwards.
        assert(forall|i: u64, k: u64| #![auto] k < 64 ==> ((i & !(1u64 << k)) & (1u64 << k) == 0)) by (bit_vector); // R: parentheses?

        // Relationship between bitshifting and addition
        assert(forall|i: u64, k: u64| #![auto] k < 63 ==> (i << k) << 1u64 == i << add(k, 1u64)) by (bit_vector);

        // Generate trailing zeroes function
        assert(forall|j: u64, k: u64| j < 64 && k < j ==> (u64::MAX << j) & (1u64 << k) == 0) by (bit_vector);
        assert(forall|j: u64, k: u64| j < 64 && k >= j && k < 64 ==> (u64::MAX << j) & (1u64 << k) > 0) by (bit_vector);

        // Generate trailing ones function
        assert(forall|j: u64, k: u64| j < 64 && k < j ==> !(u64::MAX << j) & (1u64 << k) > 0) by (bit_vector);
        assert(forall|j: u64, k: u64| j < 64 && k >= j && k < 64 ==> !(u64::MAX << j) & (1u64 << k) == 0) by (bit_vector);

        // is_allocated properties
        assert(forall|j: u64, k: u64| k < 64 ==> (j & (1u64 << k) == 0) || (j & (1u64 << k) > 0));
        assert(forall|j: u64, k: u64| k < 64 && (j & (1u64 << k) == 0) ==> j <= sub(u64::MAX, 1u64 << k)) by (bit_vector);
        assert(forall|j: u64, k: u64| k < 64 && (j & (1u64 << k) == 0) ==> j < u64::MAX) by (bit_vector);
        assert(forall|u: u64| u == 3 ==> u & (1u64 << 0) > 0 && u & (1u64 << 1) > 0) by (bit_vector);
        assert(forall|u: u64|
            u & (1u64 << 0) > 0 && u & (1u64 << 1) > 0 && u & (1u64 << 2) > 0 && u & (1u64 << 3) > 0 && u & (1u64 << 4) > 0 &&
            u & (1u64 << 5) > 0 && u & (1u64 << 6) > 0 && u & (1u64 << 7) > 0 && u & (1u64 << 8) > 0 && u & (1u64 << 9) > 0 &&
            u & (1u64 << 10) > 0 && u & (1u64 << 11) > 0 && u & (1u64 << 12) > 0 && u & (1u64 << 13) > 0 && u & (1u64 << 14) > 0 &&
            u & (1u64 << 15) > 0 && u & (1u64 << 16) > 0 && u & (1u64 << 17) > 0 && u & (1u64 << 18) > 0 && u & (1u64 << 19) > 0 &&
            u & (1u64 << 20) > 0 && u & (1u64 << 21) > 0 && u & (1u64 << 22) > 0 && u & (1u64 << 23) > 0 && u & (1u64 << 24) > 0 &&
            u & (1u64 << 25) > 0 && u & (1u64 << 26) > 0 && u & (1u64 << 27) > 0 && u & (1u64 << 28) > 0 && u & (1u64 << 29) > 0 &&
            u & (1u64 << 30) > 0 && u & (1u64 << 31) > 0 && u & (1u64 << 32) > 0 && u & (1u64 << 33) > 0 && u & (1u64 << 34) > 0 &&
            u & (1u64 << 35) > 0 && u & (1u64 << 36) > 0 && u & (1u64 << 37) > 0 && u & (1u64 << 38) > 0 && u & (1u64 << 39) > 0 &&
            u & (1u64 << 40) > 0 && u & (1u64 << 41) > 0 && u & (1u64 << 42) > 0 && u & (1u64 << 43) > 0 && u & (1u64 << 44) > 0 &&
            u & (1u64 << 45) > 0 && u & (1u64 << 46) > 0 && u & (1u64 << 47) > 0 && u & (1u64 << 48) > 0 && u & (1u64 << 49) > 0 &&
            u & (1u64 << 50) > 0 && u & (1u64 << 51) > 0 && u & (1u64 << 52) > 0 && u & (1u64 << 53) > 0 && u & (1u64 << 54) > 0 &&
            u & (1u64 << 55) > 0 && u & (1u64 << 56) > 0 && u & (1u64 << 57) > 0 && u & (1u64 << 58) > 0 && u & (1u64 << 59) > 0 &&
            u & (1u64 << 60) > 0 && u & (1u64 << 61) > 0 && u & (1u64 << 62) > 0 && u & (1u64 << 63) > 0
                ==> u == u64::MAX) by (bit_vector);

        // assert(forall|u: u64|
        //     u & (1u64 << 0) == 0 || u & (1u64 << 1) == 0 || u & (1u64 << 2) == 0 || u & (1u64 << 3) == 0 || u & (1u64 << 4) == 0 ||
        //     u & (1u64 << 5) == 0 || u & (1u64 << 6) == 0 || u & (1u64 << 7) == 0 || u & (1u64 << 8) == 0 || u & (1u64 << 9) == 0 ||
        //     u & (1u64 << 10) == 0 || u & (1u64 << 11) == 0 || u & (1u64 << 12) == 0 || u & (1u64 << 13) == 0 || u & (1u64 << 14) == 0 ||
        //     u & (1u64 << 15) == 0 || u & (1u64 << 16) == 0 || u & (1u64 << 17) == 0 || u & (1u64 << 18) == 0 || u & (1u64 << 19) == 0 ||
        //     u & (1u64 << 20) == 0 || u & (1u64 << 21) == 0 || u & (1u64 << 22) == 0 || u & (1u64 << 23) == 0 || u & (1u64 << 24) == 0 ||
        //     u & (1u64 << 25) == 0 || u & (1u64 << 26) == 0 || u & (1u64 << 27) == 0 || u & (1u64 << 28) == 0 || u & (1u64 << 29) == 0 ||
        //     u & (1u64 << 30) == 0 || u & (1u64 << 31) == 0 || u & (1u64 << 32) == 0 || u & (1u64 << 33) == 0 || u & (1u64 << 34) == 0 ||
        //     u & (1u64 << 35) == 0 || u & (1u64 << 36) == 0 || u & (1u64 << 37) == 0 || u & (1u64 << 38) == 0 || u & (1u64 << 39) == 0 ||
        //     u & (1u64 << 40) == 0 || u & (1u64 << 41) == 0 || u & (1u64 << 42) == 0 || u & (1u64 << 43) == 0 || u & (1u64 << 44) == 0 ||
        //     u & (1u64 << 45) == 0 || u & (1u64 << 46) == 0 || u & (1u64 << 47) == 0 || u & (1u64 << 48) == 0 || u & (1u64 << 49) == 0 ||
        //     u & (1u64 << 50) == 0 || u & (1u64 << 51) == 0 || u & (1u64 << 52) == 0 || u & (1u64 << 53) == 0 || u & (1u64 << 54) == 0 ||
        //     u & (1u64 << 55) == 0 || u & (1u64 << 56) == 0 || u & (1u64 << 57) == 0 || u & (1u64 << 58) == 0 || u & (1u64 << 59) == 0 ||
        //     u & (1u64 << 60) == 0 || u & (1u64 << 61) == 0 || u & (1u64 << 62) == 0 || u & (1u64 << 63) == 0
        //         ==> u < u64::MAX) by (bit_vector);
    }
    
}