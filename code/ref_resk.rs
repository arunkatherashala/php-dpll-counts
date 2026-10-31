// ref_resk.rs -- Res(k)-JW conflict leaves for PHP(n+1,n), memoised on canonical residual states (see ref_resk.py).
// usage: ref_resk <k> <nmin> <nmax>
use std::collections::HashMap;
use std::env;
use std::time::Instant;

#[derive(Clone)]
struct Row { sat: bool, cols: Vec<u8> }
type State = Vec<Row>;

fn key(s: &State) -> Vec<u8> {
    let mut k = Vec::with_capacity(s.len() * 6);
    for r in s { k.push(r.sat as u8 | ((r.cols.len() as u8) << 1)); k.extend_from_slice(&r.cols); }
    k
}

// relabel holes by first appearance, drop empty rows (must be sat). returns None if unsat row empty.
fn up_and_canon(mut s: State) -> Option<State> {
    loop {
        let mut changed = false;
        for i in 0..s.len() {
            if !s[i].sat {
                if s[i].cols.is_empty() { return None; }
                if s[i].cols.len() == 1 {
                    let c = s[i].cols[0];
                    s[i].sat = true;
                    for r in s.iter_mut() { r.cols.retain(|&x| x != c); }
                    changed = true; break;
                }
            }
        }
        if !changed { break; }
    }
    s.retain(|r| !r.cols.is_empty() || !r.sat);
    // (unsat with empty cols impossible here)
    let mut map = [255u8; 64]; let mut nxt = 0u8;
    for r in s.iter_mut() {
        for c in r.cols.iter_mut() {
            if map[*c as usize] == 255 { map[*c as usize] = nxt; nxt += 1; }
            *c = map[*c as usize];
        }
    }
    Some(s)
}

const M: u32 = 50;
fn go(s: &State, kk: usize, memo: &mut HashMap<Vec<u8>, u128>) -> u128 {
    let k = key(s);
    if let Some(&v) = memo.get(&k) { return v; }
    // scores
    let mut colcnt = [0u32; 64];
    for r in s { for &c in &r.cols { colcnt[c as usize] += 1; } }
    let mut cells: Vec<(u64, usize, usize)> = Vec::new(); // (score, row, idx)
    let mut ordinal = 0usize;
    let mut sc_list: Vec<(u64, usize)> = Vec::new();
    let mut pos_of: Vec<(usize, usize)> = Vec::new();
    for (i, r) in s.iter().enumerate() {
        for (j, &c) in r.cols.iter().enumerate() {
            let mut sc: u64 = 0;
            if !r.sat { sc += 1u64 << (M - r.cols.len() as u32); }
            sc += (colcnt[c as usize] as u64 - 1) * (1u64 << (M - 2));
            sc_list.push((sc, ordinal)); pos_of.push((i, j)); ordinal += 1;
        }
    }
    let _ = &mut cells;
    sc_list.sort_by(|a, b| b.0.cmp(&a.0).then(a.1.cmp(&b.1)));
    let m = kk.min(sc_list.len());
    let chosen: Vec<(usize, usize)> = sc_list[..m].iter().map(|x| pos_of[x.1]).collect();
    let mut tot: u128 = 0;
    for mask in 0..(1u32 << m) {
        // bit set = true
        let mut ns = s.clone();
        let mut trues: Vec<u8> = Vec::new();
        let mut falses: Vec<(usize, u8)> = Vec::new();
        let mut bad = false;
        for (b, &(i, j)) in chosen.iter().enumerate() {
            let c = s[i].cols[j];
            if (mask >> b) & 1 == 1 { if trues.contains(&c) { bad = true; } trues.push(c); ns[i].sat = true; }
            else { falses.push((i, c)); }
        }
        if bad { tot += 1; continue; }
        for &(i, c) in &falses { ns[i].cols.retain(|&x| x != c); }
        for &c in &trues { for r in ns.iter_mut() { r.cols.retain(|&x| x != c); } }
        match up_and_canon(ns) { None => tot += 1, Some(t) => tot += go(&t, kk, memo) }
    }
    memo.insert(k, tot);
    tot
}

fn main() {
    let a: Vec<String> = env::args().collect();
    let kk: usize = a[1].parse().unwrap();
    let n0: usize = a[2].parse().unwrap(); let n1: usize = a[3].parse().unwrap();
    for n in n0..=n1 {
        let t = Instant::now();
        let init: State = (0..=n).map(|_| Row { sat: false, cols: (0..n as u8).collect() }).collect();
        let r = match up_and_canon(init) { None => 1u128, Some(s) => { let mut memo = HashMap::new(); let v = go(&s, kk, &mut memo); eprintln!("  states={}", memo.len()); v } };
        println!("resk k={} n={} {} time={:.1}s", kk, n, r, t.elapsed().as_secs_f64());
        use std::io::Write; std::io::stdout().flush().unwrap();
    }
}
