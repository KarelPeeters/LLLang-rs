#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash)]
pub enum RSize {
    S8,
    S16,
    S32,
    S64,
}

impl RSize {
    pub const FULL: RSize = RSize::S64;
    pub const ALL_DECREASING: &'static [RSize] = &[RSize::S64, RSize::S32, RSize::S16, RSize::S8];

    pub const fn index(self) -> usize {
        self as usize
    }

    pub const fn bits(self) -> u32 {
        self.bytes() * 8
    }

    pub const fn bytes(self) -> u32 {
        match self {
            RSize::S8 => 1,
            RSize::S16 => 2,
            RSize::S32 => 4,
            RSize::S64 => 8,
        }
    }

    pub const fn from_bytes(bytes: u32) -> Option<Self> {
        match bytes {
            1 => Some(Self::S8),
            2 => Some(Self::S16),
            4 => Some(Self::S32),
            8 => Some(Self::S64),
            _ => None,
        }
    }

    pub const fn keyword(self) -> &'static str {
        match self {
            RSize::S8 => "byte",
            RSize::S16 => "word",
            RSize::S32 => "dword",
            RSize::S64 => "qword",
        }
    }
}

macro_rules! register_table [
    ($(($id:ident, $n64:literal, $n32:literal, $n16:literal, $n8:literal),)*) => {
        #[derive(Debug, Copy, Clone, Eq, PartialEq, Hash)]
        pub enum Register {
            $($id),+
        }

        impl Register {
            pub const ALL: &[Register] = &[$(Register::$id),+];

            pub const fn index(self) -> usize {
                self as usize
            }

            pub const fn from_index(index: usize) -> Self {
                Self::ALL[index]
            }

            pub const fn to_symbol(self, size: RSize) -> &'static str {
                const ARRAY: &[[&str; 4]] = &[$([$n8, $n16, $n32, $n64]),+];
                ARRAY[self.index()][size.index()]
            }
        }
    }
];

register_table![
    (A, "rax", "eax", "ax", "al"),
    (B, "rbx", "ebx", "bx", "bl"),
    (C, "rcx", "ecx", "cx", "cl"),
    (D, "rdx", "edx", "dx", "dl"),
    (SI, "rsi", "esi", "si", "sil"),
    (DI, "rdi", "edi", "di", "dil"),
    (BP, "rbp", "ebp", "bp", "bpl"),
    (SP, "rsp", "esp", "sp", "spl"),
    (R8, "r8", "r8d", "r8w", "r8b"),
    (R9, "r9", "r9d", "r9w", "r9b"),
    (R10, "r10", "r10d", "r10w", "r10b"),
    (R11, "r11", "r11d", "r11w", "r11b"),
    (R12, "r12", "r12d", "r12w", "r12b"),
    (R13, "r13", "r13d", "r13w", "r13b"),
    (R14, "r14", "r14d", "r14w", "r14b"),
    (R15, "r15", "r15d", "r15w", "r15b"),
];
