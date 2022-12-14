use win32;

const CHAR_NEWLINE: u8 = 10;
const CHAR_ZERO: u8 = 48;
const CHAR_MINUS: u8 = 45;

fn println() {
    print_char(CHAR_NEWLINE);
}

fn print_str(str: &u8, len: u32) -> bool {
    let stdout = win32::_GetStdHandle@4(win32::STD_OUTPUT_HANDLE);
    let written;
    return win32::_WriteFile@20(stdout, str as &void, len, &written, null) != 0;
}

fn print_char(char: u8) {
    print_str(&char, 1);
}

fn print_int(x: i32) {
    if x == 0 {
        print_char(CHAR_ZERO);
        return;
    }
    if x < 0 {
        print_char(CHAR_MINUS);
        x = -x;
    }

    let buffer: [u8; 16];
    let buffer_size = 16;

    let i = buffer_size;

    while x != 0 {
        i = i - 1;
        buffer[i] = CHAR_ZERO + (x % 10) as u8;
        x = x / 10;
    }

    print_str(&buffer[i], buffer_size - i);
}

fn println_str(s: &u8, len: u32) {
    print_str(s, len);
    println();
}

fn println_int(x: i32) {
    print_int(x);
    println();
}