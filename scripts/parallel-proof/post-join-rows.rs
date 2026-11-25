// Match complete published rows against independent symbolic primitive calls.
// The first token carries the result identity and the comparison includes every byte.
type Blocks = Vec<Vec<Token>>;
static EXPECTED_CELLS: Mutex<Option<(Blocks, Blocks, Blocks)>> = Mutex::new(None);

static EXPECTED_TICKETS: Mutex<Vec<(Adrs, Word, Vec<Token>)>> = Mutex::new(Vec::new());

static EXPECTED_LEAVES: Mutex<Blocks> = Mutex::new(Vec::new());

fn observe_root_inputs<const N: usize>(
    forest: &[Token],
    auth: &[[Token; N]],
    leaves: &[OnceLock<[Token; N]>],
) {
    let expected = EXPECTED_CELLS.lock().unwrap();
    let (f, a, _) = expected.as_ref().unwrap();
    assert_eq!(forest, f.concat(), "phase-one FORS bytes");
    assert!(auth.iter().map(|x| x.as_slice()).eq(a.iter().map(Vec::as_slice)));
    let expected_leaves = EXPECTED_LEAVES.lock().unwrap();
    assert!(leaves.iter().map(|x| x.get().expect("published leaf").as_slice())
        .eq(expected_leaves.iter().map(Vec::as_slice)), "phase-one leaf public keys");
}

fn observe_ticket_inputs<const N: usize>(layers: &[(Adrs, Word)], roots: &[[Token; N]]) {
    let expected = EXPECTED_TICKETS.lock().unwrap();
    assert_eq!(layers.len(), expected.len());
    assert_eq!(roots.len(), expected.len());
    for (j, (address, leaf, root)) in expected.iter().enumerate() {
        assert_eq!(layers[j], (*address, *leaf), "phase-two address and keypair");
        assert_eq!(roots[j].as_slice(), root.as_slice(), "phase-two signing message");
    }
}

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
