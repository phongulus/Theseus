use prusti_contracts::*;

#[extern_spec]
impl<T: PartialEq + Copy> core::option::Option<T> {
    #[pure]
    #[ensures(matches!(*self, Some(_)) == result)]
    pub fn is_some(&self) -> bool;

    #[pure]
    #[ensures(self.is_some() == !result)]
    pub fn is_none(&self) -> bool;
}

#[pure]
#[requires(val.is_some())]
pub(crate) fn peek_option<T: Copy>(val: &Option<T>) -> T {
    match val {
        Some(val) => *val,
        None => unreachable!(),
    }
}
