use win32::io;

const CHAR_NEWLINE: byte = 10;
const CHAR_ZERO: byte = 48;
const CHAR_MINUS: byte = 45;

fn println() {
    let newline = CHAR_NEWLINE;
    print_str(&newline, 1);
}

fn print_str(str: &byte, len: int) {
    let stdout = io::_GetStdHandle@4(-io::STD_OUTPUT_HANDLE_NEG);
    let tmp;
    io::_WriteFile@20(stdout, str, len, &tmp, null);
}

fn print_char(char: byte) {
    print_str(&char, 1);
}

fn print_int(x: int) {
    if x == 0 {
        print_char(CHAR_ZERO);
        return;
    }
    if x < 0 {
        print_char(CHAR_MINUS);
        x = -x;
    }

    let buffer: [byte; 16];
    let buffer_size = 16;

    let i = buffer_size;

    while x != 0 {
        i = i - 1;

        let tmp: int = (x % 10);
        buffer[i] = CHAR_ZERO + *((&tmp) as &byte);
        x = x / 10;
    }

    print_str(&buffer[i], buffer_size - i);
}

fn println_str(s: &byte, len: int) {
    print_str(s, len);
    println();
}

fn println_int(x: int) {
    print_int(x);
    println();
}