use win32;

static STDOUT: &void = null;
static STDOUT_INIT: bool = false;

static STDIN: &void = null;
static STDIN_INIT: bool = false;

fn get_stdout() -> &void {
    return init_impl(&STDOUT, &STDOUT_INIT, win32::STD_OUTPUT_HANDLE);
}

fn get_stdin() -> &void {
    return init_impl(&STDIN, &STDIN_INIT, win32::STD_INPUT_HANDLE);
}

// just to give the compiler some work
fn init_impl(result: &&void, init: &bool, handle: u32) -> &void {
    if !*init {
        *result = win32::GetStdHandle(handle);
        *init = true;
    }
    return *result;
}
