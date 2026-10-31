// ref_dp.rs -- exact forward layered DP for the static-order DPLL+UP conflict count of PHP(n+1,n).
// State (pos, U, O): pos = index of next undecided candidate cell in the static order, U = unsatisfied pigeons, O = occupied holes.
// Same state semantics as ref_mask.py (verified against the clause-level brute force ref_brute.py).
// usage: ref_dp <kind: pig|hole|diag|diagdec|maindiag> <nmin> <nmax> [threads]
use std::env;
use std::time::Instant;

struct Ctx { n: usize, p: usize, nc: usize, cp: Vec<u8>, ch: Vec<u8>, ahead: Vec<u32>, colmask: Vec<u32> }

fn build(n: usize, kind: &str) -> Ctx {
    let p = n + 1;
    let mut cells: Vec<(usize, usize)> = Vec::new();
    for a in 0..p { for h in 0..n { cells.push((a, h)); } }
    let key = |c: &(usize, usize)| -> (i64, i64, i64) {
        let (a, h) = (c.0 as i64, c.1 as i64);
        match kind {
            "pig" => (a, h, 0),
            "hole" => (h, a, 0),
            "diag" => (a + h, a, 0),
            "diagdec" => (a + h, -a, 0),
            "maindiag" => ((h - a).abs(), h - a, a),
            _ => panic!("kind"),
        }
    };
    cells.sort_by_key(|c| key(c));
    let nc = cells.len();
    let mut ahead = vec![0u32; (nc + 1) * p];
    let mut colmask = vec![0u32; nc + 1];
    for pos in (0..nc).rev() {
        for a in 0..p { ahead[pos * p + a] = ahead[(pos + 1) * p + a]; }
        colmask[pos] = colmask[pos + 1];
        let (a, h) = cells[pos];
        ahead[pos * p + a] |= 1 << h;
        colmask[pos] |= 1 << h;
    }
    Ctx { n, p, nc, cp: cells.iter().map(|c| c.0 as u8).collect(), ch: cells.iter().map(|c| c.1 as u8).collect(), ahead, colmask }
}

// returns None on conflict, Some((pos,U,O)) otherwise
#[inline]
fn settle(c: &Ctx, mut pos: usize, mut u_: u32, mut o: u32) -> Option<(usize, u32, u32)> {
    loop {
        let mut changed = false;
        let mut u = u_;
        while u != 0 {
            let a = u.trailing_zeros() as usize;
            u &= u - 1;
            let m = c.ahead[pos * c.p + a] & !o;
            if m == 0 { return None; }
            if m & (m - 1) == 0 { u_ &= !(1u32 << a); o |= m; changed = true; }
        }
        if !changed { break; }
    }
    while pos < c.nc && (o >> c.ch[pos]) & 1 == 1 { pos += 1; }
    if pos >= c.nc { panic!("SAT leaf reached"); }
    o &= c.colmask[pos];
    Some((pos, u_, o))
}

fn run(n: usize, kind: &str, threads: usize) -> (u128, u64) {
    let c = build(n, kind);
    let mut layers: Vec<Vec<(u64, u128)>> = vec![Vec::new(); c.nc + 1];
    let allu: u32 = ((1u64 << c.p) - 1) as u32;
    let mut leaves: u128 = 0;
    let mut states: u64 = 0;
    match settle(&c, 0, allu, 0) {
        None => return (1, 0),
        Some((pos, u, o)) => layers[pos].push((((u as u64) << n) | o as u64, 1)),
    }
    let mask_o = (1u64 << n) - 1;
    for pos in 0..c.nc {
        let mut lay = std::mem::take(&mut layers[pos]);
        if lay.is_empty() { continue; }
        lay.sort_unstable_by_key(|x| x.0);
        let mut merged: Vec<(u64, u128)> = Vec::with_capacity(lay.len());
        for (k, v) in lay.into_iter() {
            if let Some(l) = merged.last_mut() { if l.0 == k { l.1 += v; continue; } }
            merged.push((k, v));
        }
        states += merged.len() as u64;
        let (a, h) = (c.cp[pos] as u32, c.ch[pos] as u32);
        let te = if merged.len() < 40000 { 1 } else { threads.max(1) };
        let chunk = (merged.len() + te - 1) / te;
        let chunk = chunk.max(1);
        let results: Vec<(u128, Vec<(usize, u64, u128)>)> = std::thread::scope(|s| {
            let hs: Vec<_> = merged.chunks(chunk).map(|part| {
                let c = &c;
                s.spawn(move || {
                    let mut lv: u128 = 0;
                    let mut out: Vec<(usize, u64, u128)> = Vec::with_capacity(part.len() * 2);
                    for &(k, cnt) in part {
                        let u = (k >> n) as u32; let o = (k & mask_o) as u32;
                        // true branch
                        match settle(c, pos + 1, u & !(1u32 << a), o | (1u32 << h)) {
                            None => lv += cnt,
                            Some((p2, u2, o2)) => out.push((p2, ((u2 as u64) << n) | o2 as u64, cnt)),
                        }
                        // false branch
                        match settle(c, pos + 1, u, o) {
                            None => lv += cnt,
                            Some((p2, u2, o2)) => out.push((p2, ((u2 as u64) << n) | o2 as u64, cnt)),
                        }
                    }
                    (lv, out)
                })
            }).collect();
            hs.into_iter().map(|h| h.join().unwrap()).collect()
        });
        for (lv, out) in results {
            leaves += lv;
            for (p2, k, v) in out { layers[p2].push((k, v)); }
        }
    }
    (leaves, states)
}

fn main() {
    let a: Vec<String> = env::args().collect();
    let kind = a[1].as_str();
    let n0: usize = a[2].parse().unwrap();
    let n1: usize = a[3].parse().unwrap();
    let th: usize = if a.len() > 4 { a[4].parse().unwrap() } else { 8 };
    for n in n0..=n1 {
        let t = Instant::now();
        let (l, s) = run(n, kind, th);
        println!("{} {} {} states={} time={:.1}s", kind, n, l, s, t.elapsed().as_secs_f64());
        use std::io::Write; std::io::stdout().flush().unwrap();
    }
}
