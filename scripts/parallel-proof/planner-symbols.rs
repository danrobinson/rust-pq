// Symbolic terms are used only by the observer. The production queue builder is
// compiled with an abstract word type that cannot be compared or used as an index.
mod symbolic {
    use std::ops::{Add, BitXor, Shl, Shr};

    #[derive(Debug, Eq, PartialEq)]
    enum Expr {
        Choice(usize),
        ShiftRight(Word, u32),
        Xor(Word, u32),
        AddBase(u32, Word),
        ShiftLeft(Word, u32),
        AddOffset(Word, u32),
    }

    #[derive(Clone, Copy, Debug, Eq, PartialEq)]
    pub struct Word(&'static Expr);

    impl Word {
        fn new(expr: Expr) -> Self {
            Self(Box::leak(Box::new(expr)))
        }
        pub fn choice(t: usize) -> Self {
            Self::new(Expr::Choice(t))
        }
    }

    impl Add<Word> for u32 {
        type Output = Word;
        fn add(self, rhs: Word) -> Word { Word::new(Expr::AddBase(self, rhs)) }
    }
    impl Add<u32> for Word {
        type Output = Word;
        fn add(self, rhs: u32) -> Word { Word::new(Expr::AddOffset(self, rhs)) }
    }
    impl BitXor<u32> for Word {
        type Output = Word;
        fn bitxor(self, rhs: u32) -> Word { Word::new(Expr::Xor(self, rhs)) }
    }
    impl Shl<u32> for Word {
        type Output = Word;
        fn shl(self, rhs: u32) -> Word { Word::new(Expr::ShiftLeft(self, rhs)) }
    }
    impl Shr<u32> for Word {
        type Output = Word;
        fn shr(self, rhs: u32) -> Word { Word::new(Expr::ShiftRight(self, rhs)) }
    }
    impl Shl<u8> for Word {
        type Output = Word;
        fn shl(self, rhs: u8) -> Word { self << u32::from(rhs) }
    }
    impl Shr<u8> for Word {
        type Output = Word;
        fn shr(self, rhs: u8) -> Word { self >> u32::from(rhs) }
    }
}
