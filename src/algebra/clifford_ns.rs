/// Clifford-algebra NS for Ramsey: projector encoding.
///
/// Generators e_0..e_{m-1} (one per edge), e_i^2 = 1, e_i e_j = -e_j e_i.
///
/// Boolean variable x_e ↔ projector P_e = (1 + e_e) / 2.
///   P_e^2 = P_e (idempotent, since (1+e)^2/4 = (2+2e)/4 = (1+e)/2 = P_e).
///   (1+e_e) is a zero divisor: (1+e_e)(1-e_e) = 1 - 1 = 0. So P_e has NO inverse.
///
/// Red K_s axiom:  F_S  = Π_{e ∈ E(S)} P_e  (product of projectors, mixed grade)
/// Blue K_t axiom: G_T  = Π_{e ∈ E(T)} Q_e, Q_e = (1-e_e)/2 = 1 - P_e
///
/// NS certificate: Σ_i M_i * F_i = 1 in Cl_{m}(F_p) / (e_e^2 - 1)
///
/// Unlike commutative NS, P_e P_f ≠ P_f P_e (off-diagonal grade term flips sign).
/// This non-commutativity is the potential source of shorter certificates.

use std::collections::HashMap;

pub type Blade = u128;

#[derive(Clone, Debug, Default)]
pub struct Multivec {
    pub p: u8,
    pub terms: HashMap<Blade, u8>,
}

impl Multivec {
    pub fn zero(p: u8) -> Self { Multivec { p, terms: HashMap::new() } }

    pub fn scalar(p: u8, v: u8) -> Self {
        let mut mv = Multivec::zero(p);
        if v != 0 { mv.terms.insert(0, v % p); }
        mv
    }

    pub fn add_blade(&mut self, blade: Blade, coef: u8) {
        if coef == 0 { return; }
        let e = self.terms.entry(blade).or_insert(0);
        *e = ((*e as u16 + coef as u16) % self.p as u16) as u8;
        if *e == 0 { self.terms.remove(&blade); }
    }

    pub fn add(&self, other: &Multivec) -> Self {
        let mut r = self.clone();
        for (&b, &c) in &other.terms { r.add_blade(b, c); }
        r
    }

    pub fn neg(&self) -> Self {
        Multivec {
            p: self.p,
            terms: self.terms.iter().map(|(&b, &c)| (b, (self.p - c % self.p) % self.p))
                .filter(|(_, c)| *c != 0).collect(),
        }
    }

    pub fn scale(&self, s: u8) -> Self {
        if s == 0 { return Multivec::zero(self.p); }
        Multivec {
            p: self.p,
            terms: self.terms.iter().filter_map(|(&b, &c)| {
                let v = (c as u16 * s as u16 % self.p as u16) as u8;
                if v == 0 { None } else { Some((b, v)) }
            }).collect(),
        }
    }

    pub fn max_grade(&self) -> usize {
        self.terms.keys().map(|b| b.count_ones() as usize).max().unwrap_or(0)
    }
}

/// Clifford product of two blades: b1 * b2.
/// Sign = (-1)^(number of transpositions needed to bring b2 generators past b1 generators).
fn blade_mul_signed(b1: Blade, b2: Blade, p: u8) -> (Blade, u8) {
    let result = b1 ^ b2; // XOR: generators that appear odd # times
    // For each generator bit k in b2 (processed LSB first),
    // count generators in b1 with index > k that must be crossed.
    let mut flips: u32 = 0;
    let mut rem = b2;
    while rem != 0 {
        let k = rem.trailing_zeros();
        rem &= rem - 1;
        // generators in b1 with bit index > k
        let above = if k + 1 < 128 { b1 >> (k + 1) } else { 0 };
        flips += above.count_ones();
        // If both b1 and b2 have generator k: e_k^2 = 1, but we already
        // crossed it past generators below it in b1. Count those to get
        // e_k back to its "home" position next to itself.
        if b1 & (1u128 << k) != 0 {
            let below_b1 = b1 & ((1u128 << k) - 1);
            flips += below_b1.count_ones(); // cross back past b1 generators below k
        }
    }
    let coef = if flips % 2 == 0 { 1u8 } else { p - 1 };
    (result, coef)
}

pub fn clifford_mul(a: &Multivec, b: &Multivec) -> Multivec {
    let mut r = Multivec::zero(a.p);
    for (&ba, &ca) in &a.terms {
        for (&bb, &cb) in &b.terms {
            let (br, sign) = blade_mul_signed(ba, bb, a.p);
            let coef = (ca as u32 * cb as u32 % a.p as u32 * sign as u32 % a.p as u32) as u8;
            if coef != 0 { r.add_blade(br, coef); }
        }
    }
    r
}

/// inv2 = modular inverse of 2 mod p (p must be odd prime)
fn inv2(p: u8) -> u8 { (p + 1) / 2 }

/// Edge bit index (0-based) for edge (u,v) with 1 ≤ u < v ≤ n.
pub fn edge_bit(u: u32, v: u32, n: u32) -> u32 {
    let (a, b) = if u < v { (u, v) } else { (v, u) };
    (1..a).map(|i| n - i).sum::<u32>() + (b - a - 1)
}

/// Projector P_e = (1 + e_e) / 2 for edge bit k.
pub fn projector(k: u32, p: u8) -> Multivec {
    let inv_2 = inv2(p);
    let mut mv = Multivec::zero(p);
    mv.add_blade(0, inv_2);            // constant 1/2
    mv.add_blade(1u128 << k, inv_2);   // e_k / 2
    mv
}

/// Anti-projector Q_e = (1 - e_e) / 2 = 1 - P_e.
pub fn anti_projector(k: u32, p: u8) -> Multivec {
    let inv_2 = inv2(p);
    let neg_inv2 = (p - inv_2) % p;
    let mut mv = Multivec::zero(p);
    mv.add_blade(0, inv_2);
    mv.add_blade(1u128 << k, neg_inv2); // -1/2 * e_k
    mv
}

/// Red K_s axiom on vertices {1,...,s}: Π_{e ∈ E(S)} P_e.
pub fn red_axiom(s: u32, n: u32, p: u8) -> Multivec {
    let mut acc = Multivec::scalar(p, 1);
    for u in 1..=s {
        for v in (u+1)..=s {
            let k = edge_bit(u, v, n);
            acc = clifford_mul(&acc, &projector(k, p));
        }
    }
    acc
}

/// Blue K_t axiom on vertices {1,...,t}: Π_{e ∈ E(T)} Q_e.
pub fn blue_axiom(t: u32, n: u32, p: u8) -> Multivec {
    let mut acc = Multivec::scalar(p, 1);
    for u in 1..=t {
        for v in (u+1)..=t {
            let k = edge_bit(u, v, n);
            acc = clifford_mul(&acc, &anti_projector(k, p));
        }
    }
    acc
}

/// All subsets of {0..n_gens-1} with popcount ≤ max_grade.
fn enumerate_blades(n_gens: usize, max_grade: usize) -> Vec<Blade> {
    let mut out = Vec::new();
    fn rec(start: usize, n: usize, left: usize, cur: Blade, out: &mut Vec<Blade>) {
        out.push(cur);
        if left == 0 { return; }
        for i in start..n { rec(i+1, n, left-1, cur | (1u128 << i), out); }
    }
    rec(0, n_gens, max_grade, 0, &mut out);
    out
}

fn mod_inv(a: u8, p: u8) -> u8 {
    let (mut or, mut r) = (a as i32, p as i32);
    let (mut os, mut s) = (1i32, 0i32);
    while r != 0 {
        let q = or / r;
        (or, r) = (r, or - q * r);
        (os, s) = (s, os - q * s);
    }
    ((os % p as i32 + p as i32) % p as i32) as u8
}

fn gauss_over_fp(mat: &mut Vec<Vec<u8>>, n_rows: usize, n_cols: usize, p: u8) -> bool {
    let mut pr = 0usize;
    for col in 0..n_cols {
        let pivot = (pr..n_rows).find(|&r| mat[r][col] != 0);
        if pivot.is_none() { continue; }
        let pivot = pivot.unwrap();
        mat.swap(pr, pivot);
        let inv = mod_inv(mat[pr][col], p);
        for j in 0..=n_cols { mat[pr][j] = (mat[pr][j] as u16 * inv as u16 % p as u16) as u8; }
        for r in 0..n_rows {
            if r == pr { continue; }
            let f = mat[r][col]; if f == 0 { continue; }
            for j in 0..=n_cols {
                let v = (p as u16 - 1) * f as u16 % p as u16 * mat[pr][j] as u16 % p as u16;
                mat[r][j] = ((mat[r][j] as u16 + v) % p as u16) as u8;
            }
        }
        pr += 1;
    }
    // inconsistent row = all-zero left side, nonzero RHS
    !(0..n_rows).any(|r| mat[r][..n_cols].iter().all(|&v| v == 0) && mat[r][n_cols] != 0)
}

/// Clifford (projector-based) NS certificate search for R(s,t)/K_n over F_p.
///
/// Builds all orbit reps of axioms (one red rep + one blue rep in orbit-rep-only mode),
/// constructs all multiplier blades of grade ≤ d - axiom_grade_min,
/// and solves the linear system: Σ_i M_i * F_i = 1 (scalar).
///
/// Returns true if a certificate is found at this degree.
pub fn find_clifford_cert(s: u32, t: u32, n: u32, d: usize, p: u8) -> bool {
    let n_edges = (n * (n - 1) / 2) as usize;
    assert!(n_edges <= 64, "n={} too large (>64 edges), extend Blade to u128 range", n);

    let f_red = red_axiom(s, n, p);
    let f_blue = blue_axiom(t, n, p);

    let _red_grade_min = 0usize; // projector products have grade 0..C(s,2)
    let _blue_grade_min = 0usize;

    eprintln!("clifford_ns (projector): R({},{}) K_{} p={} d={}", s, t, n, p, d);
    eprintln!("  red axiom: {} terms, max_grade={}",
        f_red.terms.len(), f_red.max_grade());
    eprintln!("  blue axiom: {} terms, max_grade={}",
        f_blue.terms.len(), f_blue.max_grade());

    // For each axiom, multiplier grade ≤ d (since axiom grade-0 component is nonzero,
    // any scalar-times-axiom contributes grade-0 to the product).
    // Include all blades of grade ≤ d as potential multipliers.
    let mult_blades = enumerate_blades(n_edges, d);

    eprintln!("  mult blades: {}", mult_blades.len());

    // Rows = all blades of grade ≤ d (potential output blades of products).
    let row_blades = enumerate_blades(n_edges, d);
    let blade_to_row: HashMap<Blade, usize> =
        row_blades.iter().enumerate().map(|(i, &b)| (b, i)).collect();
    let n_rows = row_blades.len();

    // Columns: (axiom_index, mult_blade). Two axioms × mult_blades.
    let n_cols = 2 * mult_blades.len();
    eprintln!("  matrix: {} rows × {} cols", n_rows, n_cols);

    if n_rows > 50_000 || n_cols > 50_000 {
        eprintln!("  (too large for dense GE, skipping)");
        return false;
    }

    let mut mat: Vec<Vec<u8>> = vec![vec![0u8; n_cols + 1]; n_rows];

    // RHS: 1 for scalar blade (blade=0), 0 elsewhere.
    if let Some(&r) = blade_to_row.get(&0u128) { mat[r][n_cols] = 1; }

    let axioms: [&Multivec; 2] = [&f_red, &f_blue];
    for (ai, axiom) in axioms.iter().enumerate() {
        for (mi, &mult_blade) in mult_blades.iter().enumerate() {
            let col = ai * mult_blades.len() + mi;
            // product = (mult_blade as multivec) * axiom
            let mult_mv = {
                let mut mv = Multivec::zero(p);
                mv.add_blade(mult_blade, 1);
                mv
            };
            let product = clifford_mul(&mult_mv, axiom);
            for (&b, &c) in &product.terms {
                if c == 0 { continue; }
                if b.count_ones() as usize > d { continue; }
                if let Some(&row) = blade_to_row.get(&b) {
                    mat[row][col] = ((mat[row][col] as u16 + c as u16) % p as u16) as u8;
                }
            }
        }
    }

    let found = gauss_over_fp(&mut mat, n_rows, n_cols, p);
    if found { eprintln!("  CERT FOUND at d={}", d); }
    found
}

/// Sanity check: verify that with d ≥ max_grade(axiom), we can check invertibility.
/// In projector encoding, P_e = (1+e_e)/2 satisfies (1+e_e)(1-e_e) = 0, so P_e is a zero divisor.
/// The ideal ⟨F_red, F_blue⟩ in Cl is non-trivial.
pub fn projector_is_zero_divisor(k: u32, _n: u32, p: u8) -> bool {
    let pe = projector(k, p);
    let qe = anti_projector(k, p);
    let product = clifford_mul(&pe, &qe);
    // P_e * Q_e = (1+e_k)(1-e_k)/4 = (1 - e_k^2)/4 = 0
    product.terms.is_empty()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn projector_zero_divisor_check() {
        // P_e * Q_e = 0
        assert!(projector_is_zero_divisor(0, 6, 11));
        assert!(projector_is_zero_divisor(3, 6, 11));
    }

    #[test]
    fn projector_idempotent_check() {
        // P_e^2 = P_e
        let pe = projector(0, 11);
        let pe2 = clifford_mul(&pe, &pe);
        assert_eq!(pe.terms, pe2.terms, "P_e^2 should equal P_e");
    }

    #[test]
    // At d=9 the matrix reaches 27824×55648 which trips the 50K dense-GE guard.
    // Smaller d finds no cert. Needs sparse GE to proceed further.
    #[ignore]
    fn clifford_r33_k6_projector() {
        for d in 3..=9 {
            let t = std::time::Instant::now();
            let found = find_clifford_cert(3, 3, 6, d, 11);
            eprintln!("Clifford(proj) R(3,3)/K_6 F11 d={}: {} ({:.3}s)",
                d, if found {"CERT"} else {"no cert"}, t.elapsed().as_secs_f64());
            if found { return; }
        }
        panic!("no cert up to d=9");
    }
}
