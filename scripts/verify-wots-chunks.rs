//! Verify the Rust standard-library operations represented in Shakebatch.WotsChunks.
//! Run with `kani scripts/verify-wots-chunks.rs`. The scope is the full domain seen
//! by the three verified production WOTS backends.

#[kani::proof]
#[kani::unwind(70)]
fn every_wots_chunk() {
    let order: [usize; 67] = kani::any();
    let length: usize = kani::any();
    let width: usize = kani::any();
    kani::assume(length <= order.len() && matches!(width, 2 | 3 | 8));
    let mut concrete = order[..length].chunks(width);
    let mut rest = &order[..length];
    while !rest.is_empty() {
        let take = core::cmp::min(rest.len(), width);
        let (expected, next) = rest.split_at(take);
        let actual = concrete.next().unwrap();
        assert_eq!(actual.len(), expected.len());
        assert_eq!(actual.as_ptr(), expected.as_ptr());
        rest = next;
    }
    assert!(concrete.next().is_none());
    assert!(concrete.next().is_none());
}
