use win32;
use io::init_stdout;

const CHAR_NEWLINE: u8 = 10;
const CHAR_ZERO: u8 = 48;
const CHAR_MINUS: u8 = 45;

fn print_str(str: &u8, len: u32) -> bool {
    let stdout = get_stdout();
    let written;
    return win32::WriteFile(stdout, str as &void, len, &written, null) != 0;
}

fn print_char(char: u8) {
    print_str(&char, 1);
}

fn println() {
    print_char(CHAR_NEWLINE);
}

fn print_int(x: i64) {
    if x == 0 {
        print_char(CHAR_ZERO);
        return;
    }
    if x < 0 {
        print_char(CHAR_MINUS);
        x = -x;
    }

    let buffer: [u8; 16];
    let buffer_size: u32 = 16;

    let i = buffer_size;

    while x != 0 {
        i = i - 1;
        buffer[i as usize] = CHAR_ZERO + (x % 10) as u8;
        x = x / 10;
    }

    print_str(&buffer[i as usize], (buffer_size - i));
}

fn println_str(s: &u8, len: u32) {
    print_str(s, len);
    println();
}

fn println_int(x: i64) {
    print_int(x);
    println();
}