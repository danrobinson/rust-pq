// Match complete published rows against independent symbolic primitive calls.
// The first token carries the result identity and the comparison includes every byte.
type Blocks = Vec<Vec<Token>>;
static EXPECTED_CELLS: Mutex<Option<(Blocks, Blocks, Blocks)>> = Mutex::new(None);

fn row_numbers<'a>(
    expected: &[Vec<Token>],
    actual: impl Iterator<Item = &'a [Token]>,
) -> Vec<usize> {
    let lookup: HashMap<_, _> = expected.iter().enumerate()
        .map(|(i, row)| (row.as_slice(), i)).collect();
    assert_eq!(lookup.len(), expected.len(), "ambiguous row identity");
    actual.map(|row| *lookup.get(row).expect("unknown published row")).collect()
}

fn observe_cells<const N: usize>(
    p: &Params,
    forest: &[Token],
    auth: &[[Token; N]],
    wots: &[OnceLock<Vec<Token>>],
) {
    let expected = EXPECTED_CELLS.lock().unwrap();
    let (f, a, w) = expected.as_ref().unwrap();
    assert_eq!(forest.len() % N, 0);
    let forest = row_numbers(f, forest.chunks_exact(N));
    let auth = row_numbers(a, auth.iter().map(|row| row.as_slice()));
    let wots = row_numbers(w, wots.iter().map(|cell| cell.get().unwrap().as_slice()));
    println!("JOIN {} {} {:?}|{:?}|{:?}", N, p.d, forest, auth, wots);
}
