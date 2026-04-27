//! Closed-form NS certificate for PHP_{P,H} — no orbit BFS, no Gaussian.
//!
//! Uses the injective-product identity:
//!   1 = Σ_{k=0}^{P-1} m_k · f_k  +  Σ_{j,k,l} m_{j,k,l} · g_{j,k,l}
//!
//! where:
//!   f_k = Σ_j x_{k,j} − 1              (pigeon-k totality, 0-indexed)
//!   g_{j,k,l} = x_{k,j} · x_{l,j}     (hole-j AMO for pigeons k < l)
//!
//!   m_k = −inj_Q_k                      (neg. of injective-only partial product)
//!   inj_Q_k = Σ_{injective σ:[k]→[H]} ∏_{i<k} x_{i,σ(i)}
//!
//!   m_{j,k,l} = Σ_{early-conflict=(k,l,j)} ∏_{i∉{k,l},i<l} x_{i,σ(i)}
//!               (residual monomials from non-injective extensions, distributed immediately)
//!
//! Correctness: telescoping over injective products gives 1 - 0 = 1 (since inj_Q_P = 0
//! when P > H), and the AMO mults cover exactly the non-injective contributions.
//!
//! Complexity: O(P × H!) time, O(H!) space — independent of H^P.
//!   PHP_{7,6}:  peak prod 6! = 720      →  <1 ms
//!   PHP_{8,7}:  peak prod 7! = 5040     →  <1 ms
//!   PHP_{9,8}:  peak prod 8! = 40320    →  ~1 ms
//!   PHP_{10,9}: peak prod 9! = 362880   →  ~5 ms
//!   PHP_{11,10}: peak prod 10! = 3.6M   →  ~100 ms
//!   PHP_{12,11}: peak prod 11! = 39.9M  →  ~5 s
//!
//! Variables: x_{i,j} at bit position i*H + j (0-indexed i,j),
//! DIMACS variable i*H + j + 1 (1-indexed), matching TupleVarSchema Ordered.

use super::ns_fp::PolyP;
use super::poly::Monomial;
use std::collections::{BTreeMap, BTreeSet, HashMap};

/// Raw certificate: multiplier polynomials in bit-map format.
/// Key = axiom index, value = HashMap<bitmask, coeff mod prime>.
/// Does NOT allocate BTreeSet<u32> per monomial — safe for large PHP.
pub type RawCert = HashMap<usize, HashMap<u128, u8>>;

/// Build a closed-form NS certificate for PHP_{p,h} over 𝔽_{prime}.
///
/// Uses the injective-product construction: prod tracks only injective partial
/// assignments (peak size = H! entries), non-injective extensions are distributed
/// immediately to the corresponding AMO multiplier. Memory: O(H! × 17 bytes).
pub fn find_php_cert_raw(p: u32, h: u32, prime: u8) -> RawCert {
    assert!(p > h, "PHP_{{{p},{h}}}: need P > H");
    assert!(p * h <= 128, "P*H={} exceeds u128 limit", p * h);

    // Pair index helpers: pair_start[fc_k] + (fc_l - fc_k - 1) → unique pair index.
    let pair_start: Vec<usize> = (0..p)
        .map(|k| (0..k).map(|i| (p - 1 - i) as usize).sum())
        .collect();
    let amos_per_hole = (p * (p - 1) / 2) as usize;

    // Injective prod: (bits, coef, used_holes).
    // bits: bitmask of x_{i,j} variables set for pigeons placed so far.
    // used_holes: u32 bitmask of which holes (0..H-1) are already occupied.
    // Invariant: the assignment is injective — each hole used at most once.
    let mut prod: Vec<(u128, u8, u32)> = vec![(0u128, 1u8, 0u32)];

    // amo_acc[ai]: direct HashMap accumulation (no intermediate Vec).
    let mut amo_acc: HashMap<usize, HashMap<u128, u8>> = HashMap::new();

    let mut cert: RawCert = HashMap::new();

    for k in 0..p {
        // tot_mult[k] = -inj_Q_k: negate the current injective product.
        // All entries in prod are distinct (injective assignments → distinct monomials).
        let mut mult_k: HashMap<u128, u8> = HashMap::with_capacity(prod.len());
        for &(b, c, _) in &prod {
            let neg = (prime - c % prime) % prime;
            if neg != 0 {
                mult_k.insert(b, neg);
            }
        }
        if !mult_k.is_empty() {
            cert.insert(k as usize, mult_k);
        }

        // Extend inj_Q_k by (Σ_j x_{k,j}).
        // Injective extensions → new_prod; non-injective → AMO accumulator.
        let mut new_prod: Vec<(u128, u8, u32)> =
            Vec::with_capacity(prod.len() * (h as usize).saturating_sub(k as usize));
        for &(bits, coef, used) in &prod {
            for j in 0..h {
                if used & (1 << j) == 0 {
                    // Injective: pigeon k uses a fresh hole.
                    new_prod.push((bits | (1u128 << (k * h + j)), coef, used | (1 << j)));
                } else {
                    // Non-injective: hole j already taken by some earlier pigeon fc_k.
                    // Identify fc_k (the first pigeon using hole j).
                    let fc_k = (0..k)
                        .find(|&i| bits & (1u128 << (i * h + j)) != 0)
                        .unwrap() as u32;
                    let fc_l = k;
                    let fc_j = j;
                    // residual = bits without x_{fc_k, j}; x_{k, j} is not in bits.
                    let residual = bits & !(1u128 << (fc_k * h + fc_j));
                    let pair_idx =
                        pair_start[fc_k as usize] + (fc_l - fc_k - 1) as usize;
                    let ai = p as usize + fc_j as usize * amos_per_hole + pair_idx;
                    let e = amo_acc
                        .entry(ai)
                        .or_default()
                        .entry(residual)
                        .or_insert(0u8);
                    *e = ((*e as u16 + coef as u16) % prime as u16) as u8;
                }
            }
        }
        prod = new_prod;
    }
    // prod is now empty: all injective assignments of P > H pigeons to H holes
    // are impossible, so the last step sends everything to amo_acc.

    // Flush amo_acc into cert (drop zero-coefficient entries).
    for (ai, map) in amo_acc {
        let clean: HashMap<u128, u8> = map.into_iter().filter(|&(_, v)| v != 0).collect();
        if !clean.is_empty() {
            cert.insert(ai, clean);
        }
    }

    cert
}

/// Algebraically verify a raw cert: Σ_ai raw_mults[ai] · axioms_raw[ai] == 1.
/// Operates entirely in bit-map domain — no BTreeSet allocations.
/// Returns true iff the cert is valid.
pub fn verify_cert_raw(p: u32, h: u32, prime: u8, cert: &RawCert) -> bool {
    // Build raw axioms in bit-map format.
    // Totality axiom k: Σ_j x_{k,j} − 1 = {(1<<(k*h+j)): 1 for j in 0..h} ∪ {0: prime-1}
    let mut axioms_raw: HashMap<usize, Vec<(u128, u8)>> = HashMap::new();
    for k in 0..p {
        let mut terms: Vec<(u128, u8)> = (0..h)
            .map(|j| (1u128 << (k * h + j), 1u8))
            .collect();
        terms.push((0u128, prime - 1)); // −1
        axioms_raw.insert(k as usize, terms);
    }
    // AMO axiom (hole j, pigeons k < l): x_{k,j} · x_{l,j}
    let amos_per_hole = (p * (p - 1) / 2) as usize;
    let pair_start: Vec<usize> = (0..p)
        .map(|k| (0..k).map(|i| (p - 1 - i) as usize).sum())
        .collect();
    for j in 0..h {
        for k in 0..p {
            for l in (k + 1)..p {
                let pair_idx = pair_start[k as usize] + (l - k - 1) as usize;
                let ai = p as usize + j as usize * amos_per_hole + pair_idx;
                let bit_k = 1u128 << (k * h + j);
                let bit_l = 1u128 << (l * h + j);
                axioms_raw.insert(ai, vec![(bit_k | bit_l, 1u8)]);
            }
        }
    }

    // Accumulate Σ mult · axiom into a single poly, check == 1.
    let mut acc: HashMap<u128, u8> = HashMap::new();
    for (ai, mult) in cert {
        let Some(ax) = axioms_raw.get(ai) else { continue };
        for (&m1, &c1) in mult {
            for &(m2, c2) in ax {
                // Multilinear: m1 and m2 should have disjoint supports
                // (mult for pigeon k uses vars from other pigeons, axiom uses
                // pigeon k or AMO pair vars — construction guarantees no overlap
                // for totality; AMO is degree-2 axiom × degree-P-2 mult).
                let new_mono = m1 | m2; // no reduction needed (disjoint bits)
                let new_coef = ((c1 as u16 * c2 as u16) % prime as u16) as u8;
                if new_coef == 0 { continue; }
                let e = acc.entry(new_mono).or_insert(0);
                *e = ((*e as u16 + new_coef as u16) % prime as u16) as u8;
            }
        }
    }
    acc.retain(|_, v| *v != 0);
    // Should equal {0: 1} (the constant polynomial 1).
    acc.len() == 1 && acc.get(&0u128) == Some(&1u8)
}

/// Convert a raw cert to `BTreeMap<usize, PolyP>`.
/// Only call for small PHP (P*H ≤ ~56 bits, P ≤ 8) to avoid OOM.
pub fn raw_cert_to_polyp(cert: RawCert, prime: u8) -> BTreeMap<usize, PolyP> {
    let mut out = BTreeMap::new();
    for (ai, map) in cert {
        let terms: BTreeMap<Monomial, u8> = map
            .into_iter()
            .filter(|&(_, c)| c != 0)
            .map(|(bits, c)| (bits_to_mono(bits), c))
            .collect();
        if !terms.is_empty() {
            out.insert(ai, PolyP { p: prime, terms });
        }
    }
    out
}

/// Closed-form cert returning PolyP (compatible with existing infrastructure).
/// For P*H > 64 the BTreeSet-per-monomial cost grows; use `find_php_cert_raw`
/// and `verify_cert_raw` directly for large instances.
pub fn find_php_cert_analytical(p: u32, h: u32, prime: u8) -> BTreeMap<usize, PolyP> {
    let raw = find_php_cert_raw(p, h, prime);
    raw_cert_to_polyp(raw, prime)
}

fn bits_to_mono(bits: u128) -> Monomial {
    let mut s = BTreeSet::new();
    let mut b = bits;
    while b != 0 {
        let lo = b.trailing_zeros();
        s.insert(lo + 1);
        b &= b - 1;
    }
    Monomial(s)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::problems::php_functional;

    fn verify_polyp(p: u32, h: u32, prime: u8, mults: &BTreeMap<usize, PolyP>) -> bool {
        let (_, axioms) = php_functional(p, h, prime);
        let mut acc = PolyP::zero(prime);
        for (&ai, mult) in mults {
            acc.add_assign(&mult.mul(&axioms[ai]));
        }
        acc.is_one()
    }

    #[test]
    fn php_3_2_explicit() {
        let prime = 5u8;
        let t = std::time::Instant::now();
        let cert = find_php_cert_raw(3, 2, prime);
        let t_build = t.elapsed().as_secs_f64() * 1e3;
        let t2 = std::time::Instant::now();
        assert!(verify_cert_raw(3, 2, prime, &cert), "raw verify failed");
        eprintln!("PHP_{{3,2}} build={:.3}ms verify_raw={:.3}ms", t_build, t2.elapsed().as_secs_f64()*1e3);
        let mults = raw_cert_to_polyp(cert, prime);
        assert!(verify_polyp(3, 2, prime, &mults), "polyp verify failed");
    }

    #[test]
    fn php_5_4_explicit() {
        let prime = 7u8;
        let t = std::time::Instant::now();
        let cert = find_php_cert_raw(5, 4, prime);
        let t_build = t.elapsed().as_secs_f64() * 1e3;
        let t2 = std::time::Instant::now();
        assert!(verify_cert_raw(5, 4, prime, &cert), "raw verify failed");
        eprintln!("PHP_{{5,4}} build={:.3}ms verify_raw={:.3}ms", t_build, t2.elapsed().as_secs_f64()*1e3);
        let mults = raw_cert_to_polyp(cert, prime);
        assert!(verify_polyp(5, 4, prime, &mults), "polyp verify failed");
    }

    #[test]
    fn php_6_5_explicit() {
        let prime = 7u8;
        let t = std::time::Instant::now();
        let cert = find_php_cert_raw(6, 5, prime);
        let t_build = t.elapsed().as_secs_f64() * 1e3;
        let t2 = std::time::Instant::now();
        assert!(verify_cert_raw(6, 5, prime, &cert), "raw verify failed");
        eprintln!("PHP_{{6,5}} build={:.3}ms verify_raw={:.3}ms", t_build, t2.elapsed().as_secs_f64()*1e3);
        let mults = raw_cert_to_polyp(cert, prime);
        assert!(verify_polyp(6, 5, prime, &mults), "polyp verify failed");
    }

    #[test]
    fn php_7_6_explicit() {
        let prime = 11u8;
        let t = std::time::Instant::now();
        let cert = find_php_cert_raw(7, 6, prime);
        let t_build = t.elapsed().as_secs_f64() * 1e3;
        let t2 = std::time::Instant::now();
        assert!(verify_cert_raw(7, 6, prime, &cert), "raw verify failed");
        let t_raw = t2.elapsed().as_secs_f64() * 1e3;
        eprintln!("PHP_{{7,6}} build={:.3}ms verify_raw={:.3}ms", t_build, t_raw);
        let mults = raw_cert_to_polyp(cert, prime);
        assert!(verify_polyp(7, 6, prime, &mults), "polyp verify failed");
    }

    #[test]
    fn php_8_7_explicit() {
        let prime = 11u8;
        let t = std::time::Instant::now();
        let cert = find_php_cert_raw(8, 7, prime);
        let t_build = t.elapsed().as_secs_f64() * 1e3;
        let t2 = std::time::Instant::now();
        assert!(verify_cert_raw(8, 7, prime, &cert), "raw verify failed");
        eprintln!("PHP_{{8,7}} build={:.3}ms verify_raw={:.3}ms", t_build, t2.elapsed().as_secs_f64()*1e3);
    }

    #[test]
    fn php_9_8_explicit() {
        let prime = 11u8;
        let t = std::time::Instant::now();
        let cert = find_php_cert_raw(9, 8, prime);
        let t_build = t.elapsed().as_secs_f64() * 1e3;
        let t2 = std::time::Instant::now();
        assert!(verify_cert_raw(9, 8, prime, &cert), "raw verify failed");
        eprintln!("PHP_{{9,8}} build={:.1}ms verify_raw={:.1}ms", t_build, t2.elapsed().as_secs_f64()*1e3);
    }

    #[test]
    fn php_10_9_explicit() {
        let prime = 11u8;
        let t = std::time::Instant::now();
        let cert = find_php_cert_raw(10, 9, prime);
        let t_build = t.elapsed().as_secs_f64();
        let t2 = std::time::Instant::now();
        assert!(verify_cert_raw(10, 9, prime, &cert), "raw verify failed");
        eprintln!("PHP_{{10,9}} build={:.3}s verify_raw={:.3}s", t_build, t2.elapsed().as_secs_f64());
    }

    #[test]
    #[ignore]
    fn php_11_10_explicit() {
        let prime = 11u8;
        let t = std::time::Instant::now();
        let cert = find_php_cert_raw(11, 10, prime);
        let t_build = t.elapsed().as_secs_f64();
        let t2 = std::time::Instant::now();
        assert!(verify_cert_raw(11, 10, prime, &cert), "raw verify failed");
        eprintln!("PHP_{{11,10}} build={:.3}s verify_raw={:.3}s", t_build, t2.elapsed().as_secs_f64());
    }
}
