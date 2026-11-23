unsafe extern "C" {
    fn traced_f(ctx: *const (), a: *const u8, x: *const u8, n: usize, out: *mut u8);
    fn traced_prf(ctx: *const (), a: *const u8, sk: *const u8, n: usize, out: *mut u8);
    fn traced_t(ctx: *const (), a: *const u8, rows: *const u8, len: usize, n: usize, out: *mut u8);
    fn traced_chain(
        ctx: *const (),
        a: *const u8,
        x: *const u8,
        start: u32,
        count: u32,
        n: usize,
        out: *mut u8,
    );
}
