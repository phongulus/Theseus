use prusti_contracts::*;

#[extern_spec]
impl u64 {
    #[pure]
    pub fn is_power_of_two(self) -> bool;
}

#[extern_spec]
impl usize {
    #[pure]
    pub fn is_power_of_two(self) -> bool;
}