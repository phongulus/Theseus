use prusti_contracts::*;
use crate::external_spec::trusted_option::*;

const U64_MAX: u64 = 18_446_744_073_709_551_615u64;

#[extern_spec]
impl u64 {
    #[pure]
    #[ensures(self == 0 ==> matches!(result, None))]
    #[ensures(self > 0 ==> matches!(result, Some(_)))]
    #[ensures(result.is_some() ==> peek_option(&result) <= 63)] // Maximum u64 value is 2 ^ 64 - 1, hence this property
    pub fn checked_ilog2(self) -> Option<u32>;


    #[pure]
    #[ensures(exp > 63 ==> matches!(result, None))]
    #[ensures(self <= 2 && exp <= 63 ==> matches!(result, Some(_)))]
    #[ensures(matches!(result, Some(_)) ==> peek_option(&result) < U64_MAX)]
    #[ensures(matches!(result, Some(_)) && exp > 0 ==> peek_option(&result) >= self)]
    #[ensures(matches!(result, Some(_)) && self > 0 && exp <= 63 ==> peek_option(&result) > 0)]
    pub fn checked_pow(self, exp: u32) -> Option<u64>;


    #[pure]
    pub fn is_power_of_two(self) -> bool;


    #[pure]

    // Trivial stuff
    #[ensures(result <= 64)]
    #[ensures(self == 0 ==> result == 0)]
    #[ensures(self == U64_MAX <==> result == 64)]
    #[ensures(self < U64_MAX <==> result < 64)]
    #[ensures(result < 64 ==> forall(|r: u32| (r == result ==> 2u64.checked_pow(r).is_some())))]

    // Write out formal proofs?
    #[ensures(result < 64 ==> forall(|r: u32| (r == result ==> {
        let p = peek_option(&2u64.checked_pow(r));
        self % p == p - 1
    })))]
    #[ensures(result < 64 ==> forall(|r: u32| (r == result ==> {
        let p = peek_option(&2u64.checked_pow(r));
        (self / p) % 2 == 0
    })))]
    pub fn trailing_ones(self) -> u32;


    #[pure]
    #[trusted]
    #[ensures(self == 0 ==> result == 64)]
    #[ensures(self == U64_MAX ==> result == 0)]
    #[ensures(self > 0 ==> result < 64)]
    pub fn trailing_zeros(self) -> u32;
}

#[extern_spec]
impl usize {
    #[pure]
    #[ensures(result.is_some() <==> rhs <= self)]
    #[ensures(result.is_some() ==> peek_option(&result) == self - rhs)]
    #[ensures(result.is_some() ==> peek_option(&result) <= self)]
    pub fn checked_sub(self, rhs: usize) -> Option<usize>;

    #[pure]
    pub fn is_power_of_two(self) -> bool;
}