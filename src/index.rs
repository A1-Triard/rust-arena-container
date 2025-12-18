use core::fmt::Debug;
use core::num::{NonZeroU8, NonZeroU16, NonZeroU32, NonZeroU64, NonZeroU128, NonZeroUsize};

pub trait ArenaIndex: Copy + Debug where Self: Sized {
    #[doc(hidden)]
    type Optional: Copy + Debug;

    #[doc(hidden)]
    const NONE: Self::Optional;

    #[doc(hidden)]
    fn try_from_usize(x: usize) -> Option<Self>;

    #[doc(hidden)]
    fn try_to_usize(x: Self) -> Option<usize>;

    #[doc(hidden)]
    fn to_option(x: Self::Optional) -> Option<Self>;

    #[doc(hidden)]
    fn some(x: Self) -> Self::Optional;
}

impl ArenaIndex for usize {
    type Optional = Option<usize>;

    const NONE: Self::Optional = None;

    fn try_from_usize(x: usize) -> Option<Self> {
        Some(x)
    }

    fn try_to_usize(x: Self) -> Option<usize> {
        Some(x)
    }

    fn to_option(x: Self::Optional) -> Option<Self> { x }

    fn some(x: Self) -> Self::Optional { Some(x) }
}

impl ArenaIndex for u8 {
    type Optional = Option<u8>;

    const NONE: Self::Optional = None;

    fn try_from_usize(x: usize) -> Option<Self> {
        u8::try_from(x).ok()
    }

    fn try_to_usize(x: Self) -> Option<usize> {
        Some(usize::from(x))
    }

    fn to_option(x: Self::Optional) -> Option<Self> { x }

    fn some(x: Self) -> Self::Optional { Some(x) }
}

impl ArenaIndex for u16 {
    type Optional = Option<u16>;

    const NONE: Self::Optional = None;

    fn try_from_usize(x: usize) -> Option<Self> {
        u16::try_from(x).ok()
    }

    fn try_to_usize(x: Self) -> Option<usize> {
        Some(usize::from(x))
    }

    fn to_option(x: Self::Optional) -> Option<Self> { x }

    fn some(x: Self) -> Self::Optional { Some(x) }
}

#[cfg(target_pointer_width="16")]
impl ArenaIndex for u32 {
    type Optional = Option<usize>;

    const NONE: Self::Optional = None;

    fn try_from_usize(x: usize) -> Option<Self> {
        u32::try_from(x).ok()
    }

    fn try_to_usize(x: Self) -> Option<usize> {
        usize::try_from(x).ok()
    }

    fn to_option(x: Self::Optional) -> Option<Self> { x.map(|x| u32::try_from(x).unwrap()) }

    fn some(x: Self) -> Self::Optional { Some(usize::try_from(x).unwrap()) }
}

#[cfg(any(
    target_pointer_width="32",
    target_pointer_width="64",
    all(not(target_pointer_width="16"), not(target_pointer_width="32"), not(target_pointer_width="64"))
))]
impl ArenaIndex for u32 {
    type Optional = Option<u32>;

    const NONE: Self::Optional = None;

    fn try_from_usize(x: usize) -> Option<Self> {
        u32::try_from(x).ok()
    }

    fn try_to_usize(x: Self) -> Option<usize> {
        usize::try_from(x).ok()
    }

    fn to_option(x: Self::Optional) -> Option<Self> { x }

    fn some(x: Self) -> Self::Optional { Some(x) }
}

#[cfg(any(target_pointer_width="16", target_pointer_width="32"))]
impl ArenaIndex for u64 {
    type Optional = Option<usize>;

    const NONE: Self::Optional = None;

    fn try_from_usize(x: usize) -> Option<Self> {
        u64::try_from(x).ok()
    }

    fn try_to_usize(x: Self) -> Option<usize> {
        usize::try_from(x).ok()
    }

    fn to_option(x: Self::Optional) -> Option<Self> { x.map(|x| u64::try_from(x).unwrap()) }

    fn some(x: Self) -> Self::Optional { Some(usize::try_from(x).unwrap()) }
}

#[cfg(any(
    target_pointer_width="64",
    all(not(target_pointer_width="16"), not(target_pointer_width="32"), not(target_pointer_width="64"))
))]
impl ArenaIndex for u64 {
    type Optional = Option<u64>;

    const NONE: Self::Optional = None;

    fn try_from_usize(x: usize) -> Option<Self> {
        u64::try_from(x).ok()
    }

    fn try_to_usize(x: Self) -> Option<usize> {
        usize::try_from(x).ok()
    }

    fn to_option(x: Self::Optional) -> Option<Self> { x }

    fn some(x: Self) -> Self::Optional { Some(x) }
}

impl ArenaIndex for u128 {
    type Optional = Option<usize>;

    const NONE: Self::Optional = None;

    fn try_from_usize(x: usize) -> Option<Self> {
        u128::try_from(x).ok()
    }

    fn try_to_usize(x: Self) -> Option<usize> {
        usize::try_from(x).ok()
    }

    fn to_option(x: Self::Optional) -> Option<Self> { x.map(|x| u128::try_from(x).unwrap()) }

    fn some(x: Self) -> Self::Optional { Some(usize::try_from(x).unwrap()) }
}

impl ArenaIndex for isize {
    type Optional = isize;

    const NONE: Self::Optional = -1;

    fn try_from_usize(x: usize) -> Option<Self> {
        isize::try_from(x).ok()
    }

    fn try_to_usize(x: Self) -> Option<usize> {
        usize::try_from(x).ok()
    }

    fn to_option(x: Self::Optional) -> Option<Self> { if x < 0 { None } else { Some(x) } }

    fn some(x: Self) -> Self::Optional { x }
}

impl ArenaIndex for i8 {
    type Optional = i8;

    const NONE: Self::Optional = -1;

    fn try_from_usize(x: usize) -> Option<Self> {
        i8::try_from(x).ok()
    }

    fn try_to_usize(x: Self) -> Option<usize> {
        usize::try_from(x).ok()
    }

    fn to_option(x: Self::Optional) -> Option<Self> { if x < 0 { None } else { Some(x) } }

    fn some(x: Self) -> Self::Optional { x }
}

impl ArenaIndex for i16 {
    type Optional = i16;

    const NONE: Self::Optional = -1;

    fn try_from_usize(x: usize) -> Option<Self> {
        i16::try_from(x).ok()
    }

    fn try_to_usize(x: Self) -> Option<usize> {
        usize::try_from(x).ok()
    }

    fn to_option(x: Self::Optional) -> Option<Self> { if x < 0 { None } else { Some(x) } }

    fn some(x: Self) -> Self::Optional { x }
}

#[cfg(target_pointer_width="16")]
impl ArenaIndex for i32 {
    type Optional = Option<usize>;

    const NONE: Self::Optional = None;

    fn try_from_usize(x: usize) -> Option<Self> {
        i32::try_from(x).ok()
    }

    fn try_to_usize(x: Self) -> Option<usize> {
        usize::try_from(x).ok()
    }

    fn to_option(x: Self::Optional) -> Option<Self> { x.map(|x| i32::try_from(x).unwrap()) }

    fn some(x: Self) -> Self::Optional { Some(usize::try_from(x).unwrap()) }
}

#[cfg(any(
    target_pointer_width="32",
    target_pointer_width="64",
    all(not(target_pointer_width="16"), not(target_pointer_width="32"), not(target_pointer_width="64"))
))]
impl ArenaIndex for i32 {
    type Optional = i32;

    const NONE: Self::Optional = -1;

    fn try_from_usize(x: usize) -> Option<Self> {
        i32::try_from(x).ok()
    }

    fn try_to_usize(x: Self) -> Option<usize> {
        usize::try_from(x).ok()
    }

    fn to_option(x: Self::Optional) -> Option<Self> { if x < 0 { None } else { Some(x) } }

    fn some(x: Self) -> Self::Optional { x }
}

#[cfg(any(target_pointer_width="16", target_pointer_width="32"))]
impl ArenaIndex for i64 {
    type Optional = Option<usize>;

    const NONE: Self::Optional = None;

    fn try_from_usize(x: usize) -> Option<Self> {
        i64::try_from(x).ok()
    }

    fn try_to_usize(x: Self) -> Option<usize> {
        usize::try_from(x).ok()
    }

    fn to_option(x: Self::Optional) -> Option<Self> { x.map(|x| i64::try_from(x).unwrap()) }

    fn some(x: Self) -> Self::Optional { Some(usize::try_from(x).unwrap()) }
}

#[cfg(any(
    target_pointer_width="64",
    all(not(target_pointer_width="16"), not(target_pointer_width="32"), not(target_pointer_width="64"))
))]
impl ArenaIndex for i64 {
    type Optional = i64;

    const NONE: Self::Optional = -1;

    fn try_from_usize(x: usize) -> Option<Self> {
        i64::try_from(x).ok()
    }

    fn try_to_usize(x: Self) -> Option<usize> {
        usize::try_from(x).ok()
    }

    fn to_option(x: Self::Optional) -> Option<Self> { if x < 0 { None } else { Some(x) } }

    fn some(x: Self) -> Self::Optional { x }
}

#[cfg(any(target_pointer_width="16", target_pointer_width="32", target_pointer_width="64"))]
impl ArenaIndex for i128 {
    type Optional = Option<usize>;

    const NONE: Self::Optional = None;

    fn try_from_usize(x: usize) -> Option<Self> {
        i128::try_from(x).ok()
    }

    fn try_to_usize(x: Self) -> Option<usize> {
        usize::try_from(x).ok()
    }

    fn to_option(x: Self::Optional) -> Option<Self> { x.map(|x| i128::try_from(x).unwrap()) }

    fn some(x: Self) -> Self::Optional { Some(usize::try_from(x).unwrap()) }
}

#[cfg(all(not(target_pointer_width="16"), not(target_pointer_width="32"), not(target_pointer_width="64")))]
impl ArenaIndex for i128 {
    type Optional = i128;

    const NONE: Self::Optional = -1;

    fn try_from_usize(x: usize) -> Option<Self> {
        i128::try_from(x).ok()
    }

    fn try_to_usize(x: Self) -> Option<usize> {
        usize::try_from(x).ok()
    }

    fn to_option(x: Self::Optional) -> Option<Self> { if x < 0 { None } else { Some(x) } }

    fn some(x: Self) -> Self::Optional { x }
}

impl ArenaIndex for NonZeroUsize {
    type Optional = Option<NonZeroUsize>;

    const NONE: Self::Optional = None;

    fn try_from_usize(x: usize) -> Option<Self> {
        x.checked_add(1).map(|x| NonZeroUsize::new(x).unwrap())
    }

    fn try_to_usize(x: Self) -> Option<usize> {
        Some(x.get() - 1)
    }

    fn to_option(x: Self::Optional) -> Option<Self> { x }

    fn some(x: Self) -> Self::Optional { Some(x) }
}

impl ArenaIndex for NonZeroU8 {
    type Optional = Option<NonZeroU8>;

    const NONE: Self::Optional = None;

    fn try_from_usize(x: usize) -> Option<Self> {
        x.checked_add(1).and_then(|x| u8::try_from(x).ok()).map(|x| NonZeroU8::new(x).unwrap())
    }

    fn try_to_usize(x: Self) -> Option<usize> {
        Some(usize::from(x.get() - 1))
    }

    fn to_option(x: Self::Optional) -> Option<Self> { x }

    fn some(x: Self) -> Self::Optional { Some(x) }
}

impl ArenaIndex for NonZeroU16 {
    type Optional = Option<NonZeroU16>;

    const NONE: Self::Optional = None;

    fn try_from_usize(x: usize) -> Option<Self> {
        x.checked_add(1).and_then(|x| u16::try_from(x).ok()).map(|x| NonZeroU16::new(x).unwrap())
    }

    fn try_to_usize(x: Self) -> Option<usize> {
        Some(usize::from(x.get() - 1))
    }

    fn to_option(x: Self::Optional) -> Option<Self> { x }

    fn some(x: Self) -> Self::Optional { Some(x) }
}

#[cfg(target_pointer_width="16")]
impl ArenaIndex for NonZeroU32 {
    type Optional = Option<usize>;

    const NONE: Self::Optional = None;

    fn try_from_usize(x: usize) -> Option<Self> {
        x.checked_add(1).and_then(|x| u32::try_from(x).ok()).map(|x| NonZeroU32::new(x).unwrap())
    }

    fn try_to_usize(x: Self) -> Option<usize> {
        usize::try_from(x.get() - 1).ok()
    }

    fn to_option(x: Self::Optional) -> Option<Self> {
        x.map(|x| NonZeroU32::new(u32::try_from(x).unwrap() + 1).unwrap())
    }

    fn some(x: Self) -> Self::Optional { Some(usize::try_from(x.get() - 1).unwrap()) }
}

#[cfg(any(
    target_pointer_width="32",
    target_pointer_width="64",
    all(not(target_pointer_width="16"), not(target_pointer_width="32"), not(target_pointer_width="64"))
))]
impl ArenaIndex for NonZeroU32 {
    type Optional = Option<NonZeroU32>;

    const NONE: Self::Optional = None;

    fn try_from_usize(x: usize) -> Option<Self> {
        x.checked_add(1).and_then(|x| u32::try_from(x).ok()).map(|x| NonZeroU32::new(x).unwrap())
    }

    fn try_to_usize(x: Self) -> Option<usize> {
        usize::try_from(x.get() - 1).ok()
    }

    fn to_option(x: Self::Optional) -> Option<Self> { x }

    fn some(x: Self) -> Self::Optional { Some(x) }
}

#[cfg(any(target_pointer_width="16", target_pointer_width="32"))]
impl ArenaIndex for NonZeroU64 {
    type Optional = Option<usize>;

    const NONE: Self::Optional = None;

    fn try_from_usize(x: usize) -> Option<Self> {
        x.checked_add(1).and_then(|x| u64::try_from(x).ok()).map(|x| NonZeroU64::new(x).unwrap())
    }

    fn try_to_usize(x: Self) -> Option<usize> {
        usize::try_from(x.get() - 1).ok()
    }

    fn to_option(x: Self::Optional) -> Option<Self> {
        x.map(|x| NonZeroU64::new(u64::try_from(x).unwrap() + 1).unwrap())
    }

    fn some(x: Self) -> Self::Optional { Some(usize::try_from(x.get() - 1).unwrap()) }
}

#[cfg(any(
    target_pointer_width="64",
    all(not(target_pointer_width="16"), not(target_pointer_width="32"), not(target_pointer_width="64"))
))]
impl ArenaIndex for NonZeroU64 {
    type Optional = Option<NonZeroU64>;

    const NONE: Self::Optional = None;

    fn try_from_usize(x: usize) -> Option<Self> {
        x.checked_add(1).and_then(|x| u64::try_from(x).ok()).map(|x| NonZeroU64::new(x).unwrap())
    }

    fn try_to_usize(x: Self) -> Option<usize> {
        usize::try_from(x.get() - 1).ok()
    }

    fn to_option(x: Self::Optional) -> Option<Self> { x }

    fn some(x: Self) -> Self::Optional { Some(x) }
}

#[cfg(any(target_pointer_width="16", target_pointer_width="32", target_pointer_width="64"))]
impl ArenaIndex for NonZeroU128 {
    type Optional = Option<usize>;

    const NONE: Self::Optional = None;

    fn try_from_usize(x: usize) -> Option<Self> {
        x.checked_add(1).and_then(|x| u128::try_from(x).ok()).map(|x| NonZeroU128::new(x).unwrap())
    }

    fn try_to_usize(x: Self) -> Option<usize> {
        usize::try_from(x.get() - 1).ok()
    }

    fn to_option(x: Self::Optional) -> Option<Self> {
        x.map(|x| NonZeroU128::new(u128::try_from(x).unwrap() + 1).unwrap())
    }

    fn some(x: Self) -> Self::Optional { Some(usize::try_from(x.get() - 1).unwrap()) }
}

#[cfg(all(not(target_pointer_width="16"), not(target_pointer_width="32"), not(target_pointer_width="64")))]
impl ArenaIndex for NonZeroU128 {
    type Optional = Option<NonZeroU128>;

    const NONE: Self::Optional = None;

    fn try_from_usize(x: usize) -> Option<Self> {
        x.checked_add(1).and_then(|x| u128::try_from(x).ok()).map(|x| NonZeroU128::new(x).unwrap())
    }

    fn try_to_usize(x: Self) -> Option<usize> {
        usize::try_from(x.get() - 1).ok()
    }

    fn to_option(x: Self::Optional) -> Option<Self> { x }

    fn some(x: Self) -> Self::Optional { Some(x) }
}
