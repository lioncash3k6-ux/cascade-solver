#![allow(dead_code)]
/// Five algebraic experiments for Ramsey certificate search.
///
/// 1. Full (non-orbit-averaged) NS: all axioms, orbit-grouped rows, d=3..9
/// 2. Exterior/Grassmann algebra NS: ω²=0 generators
/// 3. Tseitin-augmented NS: triangle indicators reduce degree 3→1
/// 4. NS over F_2 comparison
/// 5. Multi-prime combined certificate (F_2 ∧ F_3 ∧ F_5)

use crate::algebra::orbit_ns::find_orbit_cert_fp;
use crate::algebra::ns_fp::PolyP;
use crate::algebra::poly::Monomial;
use crate::problems::ramsey_disjunctive;
use std::collections::BTreeMap;
use rayon::prelude::*;

// ── Experiment 1: full NS with all axioms (no orbit-averaging over axioms) ──

/// Run NS with all axioms (not just orbit-rep-only 2).
/// For R(3,3)/K_6: 40 axioms (20 red + 20 blue triangles).
/// orbit_cert_fp already handles multiple axioms correctly when n_axioms>2:
/// it uses one column per (axiom, multiplier_orbit_rep) pair.
fn run_full_ns(s: u32, t: u32, n: u32, p: u8, max_d: usize) -> Option<usize> {
    let (schema, axioms) = ramsey_disjunctive(s, t, n, p);
    eprintln!("full NS R({},{}) K_{} F_{}: {} axioms", s, t, n, p, axioms.len());
    for d in 1..=max_d {
        let t0 = std::time::Instant::now();
        let r = find_orbit_cert_fp(&schema, &axioms, d, p);
        eprintln!("  d={}: {} ({:.3}s)", d,
            if r.is_some() {"CERT"} else {"no cert"}, t0.elapsed().as_secs_f64());
        if r.is_some() { return Some(d); }
    }
    None
}

// ── Experiment 2: Exterior / Grassmann algebra ────────────────────────────

/// Multivector in Grassmann algebra: ω_i² = 0, ω_i ω_j = -ω_j ω_i.
/// Basis blades = subsets of generators. Blade index = bitmask.
type GBlade = u64;

fn grassmann_mul_blade(b1: GBlade, b2: GBlade, p: u8) -> Option<(GBlade, u8)> {
    if b1 & b2 != 0 { return None; } // shared generator → product = 0 (ω_i² = 0)
    let result = b1 | b2;
    // Count sign flips: for each generator k in b2 (LSB first),
    // count generators in b1 with index > k.
    let mut flips = 0u32;
    let mut rem = b2;
    while rem != 0 {
        let k = rem.trailing_zeros();
        rem &= rem - 1;
        flips += (b1 >> (k + 1)).count_ones();
    }
    let coef = if flips % 2 == 0 { 1u8 } else { p - 1 };
    Some((result, coef))
}

#[derive(Clone, Debug)]
struct GMV {
    p: u8,
    terms: std::collections::HashMap<GBlade, u8>,
}

impl GMV {
    fn zero(p: u8) -> Self { GMV { p, terms: std::collections::HashMap::new() } }
    fn scalar(p: u8, v: u8) -> Self {
        let mut mv = GMV::zero(p);
        if v != 0 { mv.terms.insert(0, v % p); }
        mv
    }
    fn add_blade(&mut self, b: GBlade, c: u8) {
        if c == 0 { return; }
        let e = self.terms.entry(b).or_insert(0);
        *e = ((*e as u16 + c as u16) % self.p as u16) as u8;
        if *e == 0 { self.terms.remove(&b); }
    }
    fn mul(&self, other: &GMV) -> GMV {
        let mut r = GMV::zero(self.p);
        for (&ba, &ca) in &self.terms {
            for (&bb, &cb) in &other.terms {
                if let Some((br, sign)) = grassmann_mul_blade(ba, bb, self.p) {
                    let coef = (ca as u32 * cb as u32 % self.p as u32
                        * sign as u32 % self.p as u32) as u8;
                    if coef != 0 { r.add_blade(br, coef); }
                }
            }
        }
        r
    }
}

fn edge_bit_g(u: u32, v: u32, n: u32) -> u32 {
    let (a, b) = if u < v { (u, v) } else { (v, u) };
    (1..a).map(|i| n - i).sum::<u32>() + (b - a - 1)
}

/// Red K_s axiom in Grassmann: ω_{e1} ∧ ... ∧ ω_{eC(s,2)} (grade-C(s,2) blade).
fn red_axiom_grassmann(s: u32, n: u32, p: u8) -> GMV {
    let mut acc = GMV::scalar(p, 1);
    for u in 1..=s {
        for v in (u+1)..=s {
            let k = edge_bit_g(u, v, n);
            let mut gen = GMV::zero(p);
            gen.add_blade(1u64 << k, 1);
            acc = acc.mul(&gen);
        }
    }
    acc
}

/// Blue K_t axiom in Grassmann: Π_{e ∈ E(T)} (1 - ω_e).
fn blue_axiom_grassmann(t: u32, n: u32, p: u8) -> GMV {
    let mut acc = GMV::scalar(p, 1);
    for u in 1..=t {
        for v in (u+1)..=t {
            let k = edge_bit_g(u, v, n);
            // (1 - ω_k)
            let mut factor = GMV::zero(p);
            factor.add_blade(0, 1);
            factor.add_blade(1u64 << k, p - 1);
            acc = acc.mul(&factor);
        }
    }
    acc
}

/// Enumerate all blades of grade ≤ max_grade over n generators.
fn grassmann_blades(n: usize, max_grade: usize) -> Vec<GBlade> {
    let mut out = Vec::new();
    fn rec(start: usize, n: usize, left: usize, cur: GBlade, out: &mut Vec<GBlade>) {
        out.push(cur);
        if left == 0 { return; }
        for i in start..n { rec(i+1, n, left-1, cur | (1u64 << i), out); }
    }
    rec(0, n, max_grade, 0, &mut out);
    out
}

fn mod_inv_g(a: u8, p: u8) -> u8 {
    let (mut or, mut r) = (a as i32, p as i32);
    let (mut os, mut s) = (1i32, 0i32);
    while r != 0 {
        let q = or / r;
        (or, r) = (r, or - q * r);
        (os, s) = (s, os - q * s);
    }
    ((os % p as i32 + p as i32) % p as i32) as u8
}

fn gauss_fp(mat: &mut Vec<Vec<u8>>, n_rows: usize, n_cols: usize, p: u8) -> bool {
    let mut pr = 0usize;
    for col in 0..n_cols {
        let pivot = (pr..n_rows).find(|&r| mat[r][col] != 0);
        if pivot.is_none() { continue; }
        let piv = pivot.unwrap();
        mat.swap(pr, piv);
        let inv = mod_inv_g(mat[pr][col], p);
        for j in 0..=n_cols { mat[pr][j] = (mat[pr][j] as u16 * inv as u16 % p as u16) as u8; }
        for r in 0..n_rows {
            if r == pr { continue; }
            let f = mat[r][col]; if f == 0 { continue; }
            for j in 0..=n_cols {
                let sub = (p as u16 - 1) * f as u16 % p as u16 * mat[pr][j] as u16 % p as u16;
                mat[r][j] = ((mat[r][j] as u16 + sub) % p as u16) as u8;
            }
        }
        pr += 1;
    }
    !(0..n_rows).any(|r| mat[r][..n_cols].iter().all(|&v| v == 0) && mat[r][n_cols] != 0)
}

/// Grassmann NS: find M_red * F_red + M_blue * F_blue = 1 in Λ(F_p^{n_edges}).
/// M_* has grade ≤ d.  Scalar blade (blade=0) must equal 1; all others 0.
fn find_grassmann_cert(s: u32, t: u32, n: u32, d: usize, p: u8) -> bool {
    let n_edges = (n * (n-1) / 2) as usize;
    if n_edges > 64 {
        eprintln!("  grassmann: n_edges={} too large for u64 blade (skip)", n_edges);
        return false;
    }
    let f_red = red_axiom_grassmann(s, n, p);
    let f_blue = blue_axiom_grassmann(t, n, p);

    eprintln!("  grassmann R({},{}) K_{} F_{} d={}: red={} terms  blue={} terms",
        s, t, n, p, d, f_red.terms.len(), f_blue.terms.len());

    let blades = grassmann_blades(n_edges, d);
    let b2row: std::collections::HashMap<GBlade, usize> =
        blades.iter().enumerate().map(|(i, &b)| (b, i)).collect();
    let n_rows = blades.len();
    let n_cols = 2 * blades.len(); // red multipliers + blue multipliers

    if n_rows > 80_000 || n_cols > 80_000 {
        eprintln!("  grassmann: matrix {}×{} too large (skip)", n_rows, n_cols);
        return false;
    }

    let mut mat = vec![vec![0u8; n_cols + 1]; n_rows];
    if let Some(&r) = b2row.get(&0u64) { mat[r][n_cols] = 1; }

    let axioms = [&f_red, &f_blue];
    for (ai, axiom) in axioms.iter().enumerate() {
        for (mi, &mb) in blades.iter().enumerate() {
            let col = ai * blades.len() + mi;
            let mut mult = GMV::zero(p);
            mult.add_blade(mb, 1);
            let product = mult.mul(axiom);
            for (&b, &c) in &product.terms {
                if c == 0 { continue; }
                if b.count_ones() as usize > d { continue; }
                if let Some(&row) = b2row.get(&b) {
                    mat[row][col] = ((mat[row][col] as u16 + c as u16) % p as u16) as u8;
                }
            }
        }
    }
    gauss_fp(&mut mat, n_rows, n_cols, p)
}

// ── Experiment 3: Tseitin augmentation ────────────────────────────────────

/// Add triangle indicator z_T for every K_3 subgraph (both red and blue).
/// Axioms become: z_T = 0 (triangle is not monochromatic).
/// Definition clauses: z_T - x_a x_b x_c = 0 (adds degree-3 poly).
/// After augmentation, the red K_s axiom factors into z_{subtri} products.
///
/// For now: test whether the augmented system closes at lower degree
/// by using the existing orbit_cert_fp with Tseitin-augmented axioms.
fn run_tseitin_ns(s: u32, t: u32, n: u32, p: u8, max_d: usize) -> Option<usize> {

    let (base_schema, mut _axioms) = ramsey_disjunctive(s, t, n, p);
    let base_n = base_schema.n_vars();

    // Build one Tseitin variable per triangle (K_3) for both colors.
    // z_{red,T} replaces x_a x_b x_c (all red).
    // z_{blue,T} replaces (1-x_a)(1-x_b)(1-x_c) (all blue) constant term.
    // For simplicity: add one var per triangle, encoding the "all-same-color" product.
    //
    // Rather than fully augmenting the schema, we manually add variables and axioms.
    // Extra vars: one per triangle T in K_n.
    // For each triangle T = {u,v,w}:
    //   Let e1=var(u,v), e2=var(u,w), e3=var(v,w)
    //   Add z_T (new var index = base_n + triangle_index)
    //   Axiom: z_T - x_{e1} x_{e2} x_{e3} = 0  (defines z_T as the triangle monomial)
    //   Axiom: z_T (x_{e1}+x_{e2}+x_{e3} - 3) = 0  (forces z_T = 0 when not all-1?)
    // This is getting complex. Use a simpler approach: just add z_T = x_a x_b x_c as
    // an extra axiom, which means x_a x_b x_c = 0 (forced by axiom z_T=0) at degree 1
    // when z_T is the Tseitin variable.
    //
    // Simplest encoding: for each K_s clique axiom, replace it with:
    //   - Definition: z_S = Π_{e ∈ E(S)} x_e  (degree C(s,2) → maps to z_S = degree 1)
    //   - Axiom: z_S = 0
    // This reduces the axiom degree from C(s,2) to 1 at the cost of extra variables
    // and definition axioms of degree C(s,2).
    //
    // Implementation: we'll build extra variables and axioms programmatically.
    // n_extra = number of distinct cliques (n_red + n_blue)
    // Extra vars: z_0..z_{n_extra-1} at positions base_n..base_n+n_extra-1.

    let mut extra_defs: Vec<PolyP> = Vec::new(); // degree C(s,2) or C(t,2)
    let mut extra_axioms: Vec<PolyP> = Vec::new(); // degree 1

    let mut z_idx = base_n;

    // Red cliques: for each K_s combo, add z_S and definition.
    let red_combos = combinations_u32(n, s as usize);
    for combo in &red_combos {
        // z_S = 1: the monomial Π x_{e}. Axiom: z_S = 0 → add z_S as axiom.
        // Definition: z_S - Π x_{e} = 0 → z_S = Π x_{e}
        // As polynomial: z_S + (p-1) * Π x_{e} = 0.
        let mut clique_vars: Vec<u32> = Vec::new();
        for i in 0..combo.len() {
            for j in (i+1)..combo.len() {
                clique_vars.push(base_schema.var_of_tuple(&[combo[i] as u32, combo[j] as u32]));
            }
        }
        let z_var = z_idx as u32;

        // Definition axiom: z_S - Π x_e = 0
        let mut def = BTreeMap::new();
        def.insert(Monomial::single(z_var), 1u8);
        def.insert(Monomial::from_vars(clique_vars), p - 1); // -Π x_e
        extra_defs.push(PolyP { p, terms: def });

        // Zero axiom: z_S = 0 (from the Ramsey constraint)
        let mut ax = BTreeMap::new();
        ax.insert(Monomial::single(z_var), 1u8);
        extra_axioms.push(PolyP { p, terms: ax });

        z_idx += 1;
    }

    // Blue cliques: similar
    let blue_combos = combinations_u32(n, t as usize);
    for combo in &blue_combos {
        // Blue axiom Π (1-x_e) = 0. Replace with z_T (Tseitin for all-blue).
        // Define z_T = Π (1-x_e): a polynomial of degree C(t,2) in original vars.
        // For now just use z_T = 0 axiom + definition.
        let mut blue_product = PolyP::one(p);
        for i in 0..combo.len() {
            for j in (i+1)..combo.len() {
                let v = base_schema.var_of_tuple(&[combo[i] as u32, combo[j] as u32]);
                let mut f = BTreeMap::new();
                f.insert(Monomial::one(), 1u8);
                f.insert(Monomial::single(v), p - 1);
                blue_product = blue_product.mul(&PolyP { p, terms: f });
            }
        }
        let z_var = z_idx as u32;

        // Definition: z_T - blue_product = 0
        let mut def_terms = blue_product.terms.clone();
        let e = def_terms.entry(Monomial::single(z_var)).or_insert(0);
        *e = ((*e as u16 + 1) % p as u16) as u8;
        // Negate blue_product coefficients
        let mut def = BTreeMap::new();
        def.insert(Monomial::single(z_var), 1u8);
        for (m, c) in blue_product.terms {
            let neg = (p - c % p) % p;
            if neg != 0 { def.insert(m, neg); }
        }
        extra_defs.push(PolyP { p, terms: def });

        let mut ax = BTreeMap::new();
        ax.insert(Monomial::single(z_var), 1u8);
        extra_axioms.push(PolyP { p, terms: ax });

        z_idx += 1;
    }

    let n_total = z_idx; // base_n + n_red + n_blue
    eprintln!("tseitin NS R({},{}) K_{} F_{}: base_vars={} extra_vars={} total_vars={}",
        s, t, n, p, base_n, z_idx - base_n, n_total);

    // Build a unified schema with n_total variables.
    // Use the "dummy" approach: create a simple schema with UnorderedPair but
    // we actually need a generic schema. For now, use raw polynomial solving
    // without orbit grouping (since extra variables break the graph structure).
    //
    // Use dense GE over F_p for small cases (n_total ≤ 30).
    if n_total > 30 {
        eprintln!("  tseitin: n_total={} too large for dense GE, skipping", n_total);
        return None;
    }

    // All axioms combined: original + definitions + zero axioms.
    // Original axioms are already covered by zero axioms + defs.
    // System: find multipliers M_i such that Σ M_i * axiom_i = 1.
    // For density reasons, just combine all axiom polynomials.
    let all_axioms: Vec<PolyP> = extra_defs.into_iter().chain(extra_axioms.into_iter()).collect();

    eprintln!("  {} total axioms", all_axioms.len());

    // Dense NS: enumerate all monomials in n_total vars up to degree d.
    // rows = monomials up to degree d, cols = (axiom, multiplier monomial pairs).
    for d in 1..=max_d {
        let t0 = std::time::Instant::now();
        let found = dense_ns_solve(&all_axioms, n_total as usize, d, p);
        eprintln!("  tseitin d={}: {} ({:.3}s)", d,
            if found {"CERT"} else {"no cert"}, t0.elapsed().as_secs_f64());
        if found { return Some(d); }
    }
    None
}

/// Dense NS solver: enumerate all monomials up to degree d in n_vars variables.
fn dense_ns_solve(axioms: &[PolyP], n_vars: usize, d: usize, p: u8) -> bool {
    use crate::algebra::poly::Monomial;

    // Enumerate all monomials of degree ≤ d.
    let mut all_monos: Vec<Monomial> = Vec::new();
    fn rec_mono(start: usize, n: usize, left: usize, cur: Vec<u32>, out: &mut Vec<Monomial>) {
        out.push(Monomial::from_vars(cur.clone()));
        if left == 0 { return; }
        for i in start..n {
            let mut next = cur.clone();
            next.push(i as u32);
            rec_mono(i+1, n, left-1, next, out);
        }
    }
    rec_mono(0, n_vars, d, vec![], &mut all_monos);
    all_monos.sort();
    all_monos.dedup();

    let mono_to_row: std::collections::HashMap<&Monomial, usize> =
        all_monos.iter().enumerate().map(|(i, m)| (m, i)).collect();
    let n_rows = all_monos.len();

    // Columns: for each axiom and each multiplier monomial m with deg(axiom_term)+deg(m) ≤ d.
    let mut cols: Vec<Vec<(usize, u8)>> = Vec::new(); // col → vec of (row, coef)

    for axiom in axioms {
        let ax_min_deg = axiom.terms.keys().map(|m| m.degree()).min().unwrap_or(0);
        let max_mult_deg = if d >= ax_min_deg { d - ax_min_deg } else { continue; };

        let mut mult_monos: Vec<Monomial> = Vec::new();
        rec_mono(0, n_vars, max_mult_deg, vec![], &mut mult_monos);
        mult_monos.sort(); mult_monos.dedup();

        for mult in &mult_monos {
            let mut col_entries: std::collections::HashMap<usize, u8> = std::collections::HashMap::new();
            for (ax_mono, &ax_coef) in &axiom.terms {
                // product = ax_mono * mult (multilinear: if shared var → 0)
                let product = mul_mono_multilinear(ax_mono, mult);
                if let Some(product_mono) = product {
                    if product_mono.degree() > d { continue; }
                    if let Some(&row) = mono_to_row.get(&product_mono) {
                        let e = col_entries.entry(row).or_insert(0);
                        *e = ((*e as u16 + ax_coef as u16) % p as u16) as u8;
                    }
                }
            }
            let col_vec: Vec<(usize, u8)> = col_entries.into_iter().filter(|&(_, c)| c != 0).collect();
            if !col_vec.is_empty() { cols.push(col_vec); }
        }
    }

    if cols.is_empty() { return false; }
    let n_cols = cols.len();

    if n_rows > 20_000 || n_cols > 20_000 {
        eprintln!("  dense_ns: {}×{} too large, skip", n_rows, n_cols);
        return false;
    }

    let mut mat = vec![vec![0u8; n_cols + 1]; n_rows];

    // RHS: 1 for the empty (constant) monomial.
    let empty = Monomial::one();
    if let Some(&r) = mono_to_row.get(&empty) { mat[r][n_cols] = 1; }

    for (col, entries) in cols.iter().enumerate() {
        for &(row, coef) in entries {
            mat[row][col] = ((mat[row][col] as u16 + coef as u16) % p as u16) as u8;
        }
    }

    gauss_fp(&mut mat, n_rows, n_cols, p)
}

fn mul_mono_multilinear(a: &crate::algebra::poly::Monomial, b: &crate::algebra::poly::Monomial)
    -> Option<crate::algebra::poly::Monomial>
{
    use crate::algebra::poly::Monomial;
    // In Boolean ring x^2=x, so shared vars just stay once.
    let av: std::collections::BTreeSet<u32> = a.vars().into_iter().collect();
    let bv: std::collections::BTreeSet<u32> = b.vars().into_iter().collect();
    let union: Vec<u32> = av.union(&bv).copied().collect();
    Some(Monomial::from_vars(union))
}

fn combinations_u32(n: u32, k: usize) -> Vec<Vec<u32>> {
    let mut result = Vec::new();
    fn rec(start: u32, n: u32, k: usize, current: Vec<u32>, result: &mut Vec<Vec<u32>>) {
        if current.len() == k { result.push(current); return; }
        for i in start..=n-(k-current.len()) as u32 {
            let mut next = current.clone();
            next.push(i + 1); // 1-indexed
            rec(i+1, n, k, next, result);
        }
    }
    rec(0, n, k, vec![], &mut result);
    result
}

// ── Experiment 7: Farkas-guided adaptive column generation ────────────────
//
// For NS at degree d, if inconsistent, the Farkas dual y (left null space of A)
// tells us which polynomial constraints are violated. Adding degree-(d+1) columns
// whose product with the axioms lands in the "violated" row orbits (those with
// y_r ≠ 0) is more efficient than blindly adding all degree-(d+1) columns.
//
// This directly attacks the product-canonicalization bottleneck in high-degree NS:
// instead of canonicalizing ALL (axiom × multiplier) products, only canonicalize
// those whose contribution to violated row orbits is nonzero.
//
// Implementation: dense GE with Farkas dual extraction, scored candidate columns.

/// Dense NS system that tracks Farkas dual.
struct AdaptiveNS {
    p: u8,
    /// rows: each row is (orbit_idx, row_values). orbit_idx identifies the monomial orbit.
    rows: Vec<(u32, Vec<u8>)>,
    /// mapping: monomial orbit_id → row index in self.rows
    orbit_to_row: std::collections::HashMap<u32, usize>,
    /// column count
    n_cols: usize,
    /// RHS (length = n_rows, rhs[r] = 1 if r == constant_orbit else 0)
    rhs: Vec<u8>,
}

impl AdaptiveNS {
    fn new(p: u8) -> Self {
        AdaptiveNS { p, rows: Vec::new(), orbit_to_row: std::collections::HashMap::new(),
            n_cols: 0, rhs: Vec::new() }
    }

    fn ensure_row(&mut self, orbit_id: u32, is_constant: bool) -> usize {
        if let Some(&r) = self.orbit_to_row.get(&orbit_id) { return r; }
        let r = self.rows.len();
        self.rows.push((orbit_id, vec![0u8; self.n_cols]));
        self.rhs.push(if is_constant { 1 } else { 0 });
        self.orbit_to_row.insert(orbit_id, r);
        r
    }

    fn add_column(&mut self, col_entries: &[(u32, u8)], _is_constant_row: u32) {
        let col_idx = self.n_cols;
        self.n_cols += 1;
        for (r_idx, row) in self.rows.iter_mut() {
            let _ = r_idx;
            row.push(0);
        }
        let p16 = self.p as u16;
        for &(orbit_id, coef) in col_entries {
            if let Some(&row_idx) = self.orbit_to_row.get(&orbit_id) {
                let v = self.rows[row_idx].1[col_idx] as u16 + coef as u16;
                self.rows[row_idx].1[col_idx] = (v % p16) as u8;
            }
        }
    }

    /// Gaussian elimination. Returns:
    ///   Some(solution) if consistent (NS cert found),
    ///   None + farkas dual if inconsistent.
    fn solve(&self) -> Result<Vec<u8>, Vec<u8>> {
        let n_rows = self.rows.len();
        let n_cols = self.n_cols;
        let p = self.p;

        // Build augmented matrix [A | b].
        let mut mat: Vec<Vec<u8>> = self.rows.iter().enumerate().map(|(r, (_oid, row))| {
            let mut aug = row.clone();
            aug.push(self.rhs[r]);
            aug
        }).collect();

        let p16 = p as u16;
        let mut pivot_col_of_row: Vec<Option<usize>> = vec![None; n_rows];
        let mut row = 0usize;

        for col in 0..n_cols {
            let pivot = (row..n_rows).find(|&r| mat[r][col] != 0);
            let pivot = match pivot { Some(p) => p, None => continue };
            mat.swap(pivot, row);
            let inv = mod_inv_g(mat[row][col], p);
            for j in 0..=n_cols { mat[row][j] = (mat[row][j] as u16 * inv as u16 % p16) as u8; }
            for r in 0..n_rows {
                if r == row { continue; }
                let f = mat[r][col]; if f == 0 { continue; }
                for j in 0..=n_cols {
                    let sub = (p16 - 1) * f as u16 % p16 * mat[row][j] as u16 % p16;
                    mat[r][j] = ((mat[r][j] as u16 + sub) % p16) as u8;
                }
            }
            pivot_col_of_row[row] = Some(col);
            row += 1;
        }

        // Check inconsistency.
        for r in 0..n_rows {
            if mat[r][..n_cols].iter().all(|&v| v == 0) && mat[r][n_cols] != 0 {
                // Farkas dual: the row r of the reduced matrix (with zero LHS) gives y.
                // y_orig[orig_row] = mat[r][orig_row] before this elimination...
                // Instead: return the entire reduced RHS column as a proxy for the dual.
                // The "violated" rows are those with nonzero RHS after elimination.
                let farkas: Vec<u8> = (0..n_rows).map(|i| mat[i][n_cols]).collect();
                return Err(farkas);
            }
        }

        // Consistent: extract solution.
        let mut sol = vec![0u8; n_cols];
        for (r, pc) in pivot_col_of_row.iter().enumerate() {
            if let Some(col) = pc { sol[*col] = mat[r][n_cols]; }
        }
        Ok(sol)
    }
}

/// Farkas-guided adaptive NS for R(s,t) over K_n.
///
/// Grows the column basis iteratively using the Farkas dual to score candidates.
/// At each step, adds `batch_size` columns with the highest Farkas scores.
///
/// The Farkas dual y for the inconsistent system [A|b] identifies which row orbits
/// (monomial types) are "unsatisfied": rows r with y_r ≠ 0 after GE.
/// A new candidate column contributes to the score if its product with any axiom
/// lands in a "violated" row orbit (where y_r ≠ 0).
///
/// This is the key insight: instead of adding all degree-d columns, only add those
/// that contribute to violated constraints — guided by y.
pub fn find_cert_farkas_adaptive(
    s: u32, t: u32, n: u32, p: u8, d_max: usize, batch_size: usize,
) -> Option<usize> {
    use crate::problems::ramsey_orbit_rep;
    use crate::algebra::orbit_ns::MonoBits;
    use crate::algebra::graph_canon::{
        enumerate_stab_pair_reps, orbit_size, canonicalize,
        monobits_to_edges, canon_to_monobits,
    };
    use std::collections::HashMap;

    let (_, axioms) = ramsey_orbit_rep(s, t, n, p);
    if axioms.len() != 2 { return None; }

    let n_verts = n;

    // Encode axioms as (MonoBits, coef) pairs (one per polynomial term).
    let mut axiom_bits: Vec<Vec<(MonoBits, u8)>> = vec![Vec::new(); 2];
    for (ai, ax) in axioms.iter().enumerate() {
        for (mono, &coef) in &ax.terms {
            let mut bits = MonoBits::ZERO;
            for v in mono.vars() {
                // var_of_tuple is 1-indexed; bit positions are 0-indexed
                bits.set_bit(v - 1);
            }
            axiom_bits[ai].push((bits, coef));
        }
    }

    // On-demand orbit canonicalization: MonoBits → (orbit_id, orbit_size).
    let mut mono_to_orbit: HashMap<MonoBits, (u32, u64)> = HashMap::new();
    let mut next_orbit_id: u32 = 1;
    mono_to_orbit.insert(MonoBits::ZERO, (0u32, 1u64)); // constant → orbit 0

    // Canonicalize bits → (orbit_id, orbit_size), caching results.
    macro_rules! get_orbit {
        ($bits:expr) => {{
            let b: MonoBits = $bits;
            if let Some(&v) = mono_to_orbit.get(&b) {
                v
            } else {
                let edges = monobits_to_edges(b, n_verts);
                let (cg, aut) = canonicalize(&edges);
                let sz = orbit_size(&cg, aut, n_verts);
                // Use canon_to_monobits for consistent canonical key.
                let cb = canon_to_monobits(&cg, n_verts);
                let id = if let Some(&(eid, _)) = mono_to_orbit.get(&cb) {
                    eid
                } else {
                    let id = next_orbit_id;
                    next_orbit_id += 1;
                    mono_to_orbit.insert(cb, (id, sz));
                    id
                };
                mono_to_orbit.insert(b, (id, sz));
                (id, sz)
            }
        }};
    }

    let mut ns = AdaptiveNS::new(p);
    ns.ensure_row(0, true); // constant row (orbit_id=0)

    let mut farkas_dual: Vec<u8> = Vec::new();

    for d in 1..=d_max {
        let csk2 = s as usize * (s as usize - 1) / 2;
        let ctk2 = t as usize * (t as usize - 1) / 2;
        if d < csk2 && d < ctk2 { continue; }
        let budget_red = if d >= csk2 { d - csk2 } else { usize::MAX };
        let budget_blue = if d >= ctk2 { d - ctk2 } else { usize::MAX };

        let max_free_r = (n_verts as usize).saturating_sub(s as usize);
        let max_free_b = (n_verts as usize).saturating_sub(t as usize);

        // Enumerate stab pair reps for this degree.
        let red_reps = if budget_red != usize::MAX {
            enumerate_stab_pair_reps(s as usize, budget_red, max_free_r)
        } else { vec![] };
        let blue_reps = if budget_blue != usize::MAX {
            enumerate_stab_pair_reps(t as usize, budget_blue, max_free_b)
        } else { vec![] };

        // Score each rep: sum of |farkas[row_r]| over rows the column touches.
        // If no Farkas dual yet, score = 1 (add everything).
        // Tuple: (axiom_idx, rep_bits, score, orbit_c_size)
        let mut candidates: Vec<(usize, MonoBits, u64, u64)> = Vec::new();
        for (ai, reps) in [(0usize, &red_reps), (1usize, &blue_reps)] {
            let s_size = if ai == 0 { s as usize } else { t as usize };
            for rep in reps.iter() {
                let rep_bits = rep.to_monobits(n_verts);
                let orbit_c_size = rep.orbit_c_size(n_verts, s_size);
                if orbit_c_size == 0 { continue; }

                let score = if farkas_dual.is_empty() {
                    0u64  // score=0 means "unscored" (add first round)
                } else {
                    let mut sc = 0u64;
                    for &(term_bits, _coef) in &axiom_bits[ai] {
                        let prod = term_bits | rep_bits;
                        if prod.count_ones() as usize > d { continue; }
                        let (orbit_r, _) = get_orbit!(prod);
                        if let Some(&row_r) = ns.orbit_to_row.get(&orbit_r) {
                            if row_r < farkas_dual.len() && farkas_dual[row_r] != 0 {
                                sc += 1;
                            }
                        }
                    }
                    sc
                };
                // Always push — no pruning. Score just determines ORDER.
                candidates.push((ai, rep_bits, score, orbit_c_size));
            }
        }
        candidates.sort_by(|a, b| b.2.cmp(&a.2));

        let n_nonzero = candidates.iter().filter(|c| c.2 > 0).count();
        eprintln!("  farkas d={}: {} candidates ({} nonzero score, budget_r={} budget_b={})",
            d, candidates.len(), n_nonzero, budget_red, budget_blue);

        // Add ALL candidates (sorted: high score first), but if batch_size > 0,
        // try solving after each batch to detect early cert (sparse solution).
        let mut to_add = candidates; // already sorted desc by score

        let n_to_add = to_add.len();
        let batch = if batch_size == 0 { n_to_add } else { batch_size };
        let mut cert_at_d = false;
        let mut batch_start = 0usize;

        while batch_start <= n_to_add {
            // Add next batch.
            let end = (batch_start + batch).min(n_to_add);
            for (ai, rep_bits, _sc, orbit_c_size) in &to_add[batch_start..end] {
                let orbit_c_mod = (*orbit_c_size % p as u64) as u8;
                if orbit_c_mod == 0 { continue; }

                let mut col_entries: HashMap<u32, u8> = HashMap::new();
                for &(term_bits, coef) in &axiom_bits[*ai] {
                    let prod = term_bits | *rep_bits;
                    if prod.count_ones() as usize > d { continue; }
                    let (orbit_r, orbit_r_size) = get_orbit!(prod);
                    let r_mod_p = (orbit_r_size % p as u64) as u8;
                    if r_mod_p == 0 { continue; }
                    let inv_r = mod_inv_g(r_mod_p, p);
                    let scale = (orbit_c_mod as u16 * inv_r as u16 % p as u16) as u8;
                    let contrib = (coef as u16 * scale as u16 % p as u16) as u8;
                    if contrib == 0 { continue; }
                    ns.ensure_row(orbit_r, orbit_r == 0);
                    let e = col_entries.entry(orbit_r).or_insert(0u8);
                    *e = ((*e as u16 + contrib as u16) % p as u16) as u8;
                }
                if !col_entries.is_empty() {
                    let entries: Vec<(u32, u8)> = col_entries.into_iter().collect();
                    ns.add_column(&entries, 0);
                }
            }
            batch_start = end;

            if ns.n_cols == 0 { break; }
            let t0 = std::time::Instant::now();
            match ns.solve() {
                Ok(_sol) => {
                    eprintln!("  farkas d={}: CERT FOUND after {}/{} cols ({:.3}s)",
                        d, ns.n_cols, n_to_add, t0.elapsed().as_secs_f64());
                    cert_at_d = true;
                    break;
                }
                Err(dual) => {
                    let nnz = dual.iter().filter(|&&v| v != 0).count();
                    eprintln!("  farkas d={}: {} rows × {} cols / {} total, dual nnz={} ({:.3}s)",
                        d, ns.rows.len(), ns.n_cols, n_to_add, nnz, t0.elapsed().as_secs_f64());
                    if batch_start >= n_to_add {
                        farkas_dual = dual; // save for next degree
                        break;
                    }
                    // Score remaining candidates using current dual and re-sort.
                    let cur_dual = &dual;
                    for c in to_add[batch_start..].iter_mut() {
                        let mut sc = 0u64;
                        for &(term_bits, _) in &axiom_bits[c.0] {
                            let prod = term_bits | c.1;
                            if prod.count_ones() as usize > d { continue; }
                            let (orbit_r, _) = get_orbit!(prod);
                            if let Some(&row_r) = ns.orbit_to_row.get(&orbit_r) {
                                if row_r < cur_dual.len() && cur_dual[row_r] != 0 {
                                    sc += 1;
                                }
                            }
                        }
                        c.2 = sc;
                    }
                    to_add[batch_start..].sort_by(|a, b| b.2.cmp(&a.2));
                    farkas_dual = dual;
                }
            }
        }

        if cert_at_d { return Some(d); }
    }
    None
}

// ── Multi-prime parallel NS ────────────────────────────────────────────────

// ── Dual-support tracker ─────────────────────────────────────────────────────

/// Per-degree statistics from the Farkas dual of the orbit-averaged NS system.
#[derive(Debug, Clone)]
pub struct DualSupportRecord {
    /// NS degree at which this snapshot was taken.
    pub d: usize,
    /// Number of row orbits in the system at this degree.
    pub n_rows: usize,
    /// Number of column orbit reps added so far (cumulative).
    pub n_cols: usize,
    /// Number of row orbits with nonzero Farkas dual component (|supp y|).
    pub dual_nnz: usize,
    /// dual_nnz / n_rows
    pub dual_fraction: f64,
    /// dual_nnz broken down by monomial degree (index = edge count).
    /// dual_by_deg[k] = # violated orbits whose canonical monomial has k edges.
    pub dual_by_deg: Vec<usize>,
}

/// Measure Farkas dual support across NS degrees for R(s,t)/K_n over F_p.
///
/// At each degree d, builds the orbit-averaged NS system (same as
/// `find_cert_farkas_adaptive`) and records:
///   - how many row orbits have nonzero dual component (|supp y|)
///   - the breakdown of violated orbits by monomial edge-count
///
/// The "spread hypothesis": if |supp y| stays Ω(n) across all degrees, that is
/// empirical evidence for a superpolynomial lower bound on cert degree (matching
/// Schoenebeck's Ω(n) SoS lower bound for Ramsey).
pub fn measure_dual_support(
    s: u32, t: u32, n: u32, p: u8, d_max: usize,
) -> Vec<DualSupportRecord> {
    use crate::problems::ramsey_orbit_rep;
    use crate::algebra::orbit_ns::MonoBits;
    use crate::algebra::graph_canon::{
        enumerate_stab_pair_reps, orbit_size, canonicalize,
        monobits_to_edges, canon_to_monobits,
    };
    use std::collections::HashMap;

    let (_, axioms) = ramsey_orbit_rep(s, t, n, p);
    if axioms.len() != 2 { return Vec::new(); }

    let n_verts = n;

    let mut axiom_bits: Vec<Vec<(MonoBits, u8)>> = vec![Vec::new(); 2];
    for (ai, ax) in axioms.iter().enumerate() {
        for (mono, &coef) in &ax.terms {
            let mut bits = MonoBits::ZERO;
            for v in mono.vars() { bits.set_bit(v - 1); }
            axiom_bits[ai].push((bits, coef));
        }
    }

    let mut mono_to_orbit: HashMap<MonoBits, (u32, u64)> = HashMap::new();
    let mut orbit_id_to_degree: HashMap<u32, usize> = HashMap::new();
    let mut next_orbit_id: u32 = 1;
    mono_to_orbit.insert(MonoBits::ZERO, (0u32, 1u64));
    orbit_id_to_degree.insert(0, 0);

    macro_rules! get_orbit {
        ($bits:expr) => {{
            let b: MonoBits = $bits;
            if let Some(&v) = mono_to_orbit.get(&b) {
                v
            } else {
                let edges = monobits_to_edges(b, n_verts);
                let (cg, aut) = canonicalize(&edges);
                let sz = orbit_size(&cg, aut, n_verts);
                let cb = canon_to_monobits(&cg, n_verts);
                let deg = cb.count_ones() as usize;
                let id = if let Some(&(eid, _)) = mono_to_orbit.get(&cb) {
                    eid
                } else {
                    let id = next_orbit_id;
                    next_orbit_id += 1;
                    mono_to_orbit.insert(cb, (id, sz));
                    orbit_id_to_degree.insert(id, deg);
                    id
                };
                mono_to_orbit.insert(b, (id, sz));
                (id, sz)
            }
        }};
    }

    let mut ns = AdaptiveNS::new(p);
    ns.ensure_row(0, true);

    let mut records: Vec<DualSupportRecord> = Vec::new();

    for d in 1..=d_max {
        let csk2 = s as usize * (s as usize - 1) / 2;
        let ctk2 = t as usize * (t as usize - 1) / 2;
        if d < csk2 && d < ctk2 { continue; }
        let budget_red = if d >= csk2 { d - csk2 } else { usize::MAX };
        let budget_blue = if d >= ctk2 { d - ctk2 } else { usize::MAX };

        let max_free_r = (n_verts as usize).saturating_sub(s as usize);
        let max_free_b = (n_verts as usize).saturating_sub(t as usize);

        let red_reps = if budget_red != usize::MAX {
            enumerate_stab_pair_reps(s as usize, budget_red, max_free_r)
        } else { vec![] };
        let blue_reps = if budget_blue != usize::MAX {
            enumerate_stab_pair_reps(t as usize, budget_blue, max_free_b)
        } else { vec![] };

        for (ai, reps) in [(0usize, &red_reps), (1usize, &blue_reps)] {
            let s_size = if ai == 0 { s as usize } else { t as usize };
            for rep in reps.iter() {
                let rep_bits = rep.to_monobits(n_verts);
                let orbit_c_size = rep.orbit_c_size(n_verts, s_size);
                if orbit_c_size == 0 { continue; }
                let orbit_c_mod = (orbit_c_size % p as u64) as u8;
                if orbit_c_mod == 0 { continue; }

                let mut col_entries: std::collections::HashMap<u32, u8> = std::collections::HashMap::new();
                for &(term_bits, coef) in &axiom_bits[ai] {
                    let prod = term_bits | rep_bits;
                    if prod.count_ones() as usize > d { continue; }
                    let (orbit_r, orbit_r_size) = get_orbit!(prod);
                    let r_mod_p = (orbit_r_size % p as u64) as u8;
                    if r_mod_p == 0 { continue; }
                    let inv_r = mod_inv_g(r_mod_p, p);
                    let scale = (orbit_c_mod as u16 * inv_r as u16 % p as u16) as u8;
                    let contrib = (coef as u16 * scale as u16 % p as u16) as u8;
                    if contrib == 0 { continue; }
                    ns.ensure_row(orbit_r, orbit_r == 0);
                    let e = col_entries.entry(orbit_r).or_insert(0u8);
                    *e = ((*e as u16 + contrib as u16) % p as u16) as u8;
                }
                if !col_entries.is_empty() {
                    let entries: Vec<(u32, u8)> = col_entries.into_iter().collect();
                    ns.add_column(&entries, 0);
                }
            }
        }

        if ns.n_cols == 0 { continue; }

        match ns.solve() {
            Ok(_) => {
                // cert found — record zero dual support and stop
                let rec = DualSupportRecord {
                    d, n_rows: ns.rows.len(), n_cols: ns.n_cols,
                    dual_nnz: 0, dual_fraction: 0.0,
                    dual_by_deg: vec![0; d + 1],
                };
                records.push(rec);
                break;
            }
            Err(dual) => {
                let n_rows = ns.rows.len();
                let n_cols = ns.n_cols;

                // Build dual support breakdown by monomial degree.
                let mut dual_by_deg = vec![0usize; d + 1];
                let mut dual_nnz = 0usize;
                for r in 0..n_rows {
                    if dual[r] != 0 {
                        dual_nnz += 1;
                        let orbit_id = ns.rows[r].0;
                        let deg = orbit_id_to_degree.get(&orbit_id).copied().unwrap_or(0);
                        if deg <= d { dual_by_deg[deg] += 1; }
                    }
                }

                let rec = DualSupportRecord {
                    d, n_rows, n_cols,
                    dual_nnz,
                    dual_fraction: dual_nnz as f64 / n_rows as f64,
                    dual_by_deg,
                };
                records.push(rec);
            }
        }
    }
    records
}

/// Run NS over multiple primes in parallel (Rayon), return (prime, degree) of
/// the first certificate found, or None if no prime finds one within d_max.
pub fn find_cert_multi_prime_parallel(
    s: u32, t: u32, n: u32,
    primes: &[u8],
    d_max: usize,
) -> Option<(u8, usize)> {
    use crate::problems::ramsey_orbit_rep;

    let csk2 = (s as usize) * (s as usize - 1) / 2;
    let ctk2 = (t as usize) * (t as usize - 1) / 2;
    let d_min = csk2.max(ctk2); // need d ≥ both axiom degrees for stab path

    primes.par_iter().find_map_any(|&prime| {
        let (schema, axioms) = ramsey_orbit_rep(s, t, n, prime);
        for d in d_min..=d_max {
            let r = find_orbit_cert_fp(&schema, &axioms, d, prime);
            if r.is_some() { return Some((prime, d)); }
        }
        None
    })
}

// ── Experiment 4: NS over F_2 ─────────────────────────────────────────────

fn run_ns_f2(s: u32, t: u32, n: u32, max_d: usize) -> Option<usize> {
    let (schema, axioms) = ramsey_disjunctive(s, t, n, 2);
    eprintln!("NS/F_2 R({},{}) K_{}: {} axioms", s, t, n, axioms.len());
    for d in 1..=max_d {
        let t0 = std::time::Instant::now();
        let r = find_orbit_cert_fp(&schema, &axioms, d, 2);
        eprintln!("  d={}: {} ({:.3}s)", d,
            if r.is_some() {"CERT"} else {"no cert"}, t0.elapsed().as_secs_f64());
        if r.is_some() { return Some(d); }
    }
    None
}

// ── Experiment 5: multi-prime consistency (certify over F_2 AND F_11) ─────

fn run_multi_prime(s: u32, t: u32, n: u32, max_d: usize) -> (Option<usize>, Option<usize>) {
    let d2 = run_ns_f2(s, t, n, max_d);
    let (schema11, axioms11) = ramsey_disjunctive(s, t, n, 11);
    eprintln!("NS/F_11 R({},{}) K_{}: {} axioms", s, t, n, axioms11.len());
    let mut d11 = None;
    for d in 1..=max_d {
        let t0 = std::time::Instant::now();
        let r = find_orbit_cert_fp(&schema11, &axioms11, d, 11);
        eprintln!("  F_11 d={}: {} ({:.3}s)", d,
            if r.is_some() {"CERT"} else {"no cert"}, t0.elapsed().as_secs_f64());
        if r.is_some() { d11 = Some(d); break; }
    }
    (d2, d11)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn exp1_full_ns_r33_k6() {
        eprintln!("\n=== EXP 1: Full NS (all axioms) R(3,3)/K_6 ===");
        for p in [2u8, 3, 7, 11] {
            let d = run_full_ns(3, 3, 6, p, 8);
            eprintln!("F_{}: cert at d={:?}", p, d);
        }
    }

    #[test]
    fn exp2_grassmann_r33_k6() {
        eprintln!("\n=== EXP 2: Grassmann/Exterior NS R(3,3)/K_6 ===");
        for d in 3..=9 {
            let t0 = std::time::Instant::now();
            let found = find_grassmann_cert(3, 3, 6, d, 11);
            eprintln!("Grassmann d={}: {} ({:.3}s)", d,
                if found {"CERT"} else {"no cert"}, t0.elapsed().as_secs_f64());
            if found { break; }
        }
    }

    #[test]
    fn exp3_tseitin_r33_k6() {
        eprintln!("\n=== EXP 3: Tseitin-augmented NS R(3,3)/K_6 ===");
        let d = run_tseitin_ns(3, 3, 6, 11, 5);
        eprintln!("Tseitin cert at d={:?}", d);
    }

    #[test]
    fn exp4_f2_sweep() {
        eprintln!("\n=== EXP 4: NS over F_2 sweep ===");
        let d33 = run_ns_f2(3, 3, 6, 10);
        eprintln!("R(3,3)/K_6 F_2: d={:?}", d33);
        let d34 = run_ns_f2(3, 4, 9, 14);
        eprintln!("R(3,4)/K_9 F_2: d={:?}", d34);
    }

    #[test]
    fn exp5_multi_prime() {
        eprintln!("\n=== EXP 5: Multi-prime comparison ===");
        let (d2, d11) = run_multi_prime(3, 3, 6, 10);
        eprintln!("R(3,3)/K_6: F_2 d={:?}  F_11 d={:?}", d2, d11);
    }

    #[test]
    fn exp2_grassmann_r34_k9() {
        eprintln!("\n=== EXP 2b: Grassmann R(3,4)/K_9 ===");
        for d in 3..=10 {
            let t0 = std::time::Instant::now();
            let found = find_grassmann_cert(3, 4, 9, d, 11);
            eprintln!("Grassmann R(3,4)/K_9 d={}: {} ({:.3}s)", d,
                if found {"CERT"} else {"no cert"}, t0.elapsed().as_secs_f64());
            if found { return; }
        }
    }

    // ── Lucky-prime sweep: full NS over primes that divide C(n,2) ──────────

    /// R(3,4)/K_9: C(9,2)=36, prime divisors [2,3]. Try F_3 specifically.
    #[test]
    fn exp6_lucky_prime_r34_k9() {
        eprintln!("\n=== EXP 6: Lucky-prime full NS R(3,4)/K_9 ===");
        for p in [2u8, 3, 5, 7, 11] {
            eprintln!("--- F_{} ---", p);
            let d = run_full_ns(3, 4, 9, p, 14);
            eprintln!("R(3,4)/K_9 F_{}: cert at d={:?}", p, d);
        }
    }

    /// R(4,4)/K_18: C(18,2)=153=9*17, prime divisors [3,17]. Try F_3.
    #[test]
    fn exp6_lucky_prime_r44_k18() {
        eprintln!("\n=== EXP 6b: Lucky-prime full NS R(4,4)/K_18 ===");
        for p in [3u8, 17] {
            eprintln!("--- F_{} ---", p);
            let d = run_full_ns(4, 4, 18, p, 10);
            eprintln!("R(4,4)/K_18 F_{}: cert at d={:?}", p, d);
        }
    }

    /// R(3,3)/K_6 lucky prime summary: F_3 found cert at d=3 (C(6,2)=15, 3|15).
    /// Confirm and compare degrees across primes 2,3,5,7,11.
    #[test]
    fn exp6_prime_comparison_r33() {
        eprintln!("\n=== EXP 6c: Prime comparison R(3,3)/K_6 ===");
        for p in [2u8, 3, 5, 7, 11, 13] {
            let d = run_full_ns(3, 3, 6, p, 8);
            let divides = 15 % p as u32 == 0;
            eprintln!("F_{}: cert at d={:?}  ({}|C(6,2)=15: {})",
                p, d, p, divides);
        }
    }

    // ── Farkas-guided adaptive column generation ──────────────────────────

    /// Farkas adaptive: R(3,3)/K_6, expect cert at d=7 or lower.
    /// The dual at d=6 should score degree-7 columns and find cert quickly.
    #[test]
    fn exp7_farkas_adaptive_r33_k6() {
        eprintln!("\n=== EXP 7: Farkas-adaptive NS R(3,3)/K_6 F_11 ===");
        let d = find_cert_farkas_adaptive(3, 3, 6, 11, 10, 0); // batch_size=0 = add all
        eprintln!("Farkas-adaptive R(3,3)/K_6 F_11: cert at d={:?}", d);
        assert!(d.is_some() && d.unwrap() <= 9, "expected cert ≤ d=9, got {:?}", d);
    }

    /// Farkas adaptive: R(3,4)/K_9, compare with standard d=13 result.
    #[test]
    fn exp7_farkas_adaptive_r34_k9() {
        eprintln!("\n=== EXP 7b: Farkas-adaptive NS R(3,4)/K_9 F_11 ===");
        let d = find_cert_farkas_adaptive(3, 4, 9, 11, 14, 0);
        eprintln!("Farkas-adaptive R(3,4)/K_9 F_11: cert at d={:?}", d);
    }

    /// Multi-prime parallel: R(3,3)/K_6, should find cert over F_3 at d=3.
    #[test]
    fn exp8_multiprimes_r33_k6() {
        eprintln!("\n=== EXP 8: Multi-prime parallel R(3,3)/K_6 ===");
        let t0 = std::time::Instant::now();
        let r = find_cert_multi_prime_parallel(3, 3, 6, &[3u8, 7, 11, 13], 8);
        eprintln!("Multi-prime R(3,3)/K_6: {:?} in {:.3}s", r, t0.elapsed().as_secs_f64());
        assert!(r.is_some());
    }

    /// Multi-prime parallel: R(3,4)/K_9.
    #[test]
    fn exp8_multiprimes_r34_k9() {
        eprintln!("\n=== EXP 8b: Multi-prime parallel R(3,4)/K_9 ===");
        let t0 = std::time::Instant::now();
        let r = find_cert_multi_prime_parallel(3, 4, 9, &[5u8, 7, 11, 13], 14);
        eprintln!("Multi-prime R(3,4)/K_9: {:?} in {:.3}s", r, t0.elapsed().as_secs_f64());
    }

    // ── Dual-support spread: empirical probe of Ω(n) hypothesis ─────────────

    /// R(3,3)/K_6 F_11: track Farkas dual support size and breakdown per degree.
    /// If |supp y| is Ω(n) and doesn't shrink as d grows → consistent with
    /// Schoenebeck Ω(n) lower bound.
    #[test]
    fn exp9_dual_support_r33_k6() {
        eprintln!("\n=== EXP 9: Dual support spread R(3,3)/K_6 F_11 ===");
        let recs = measure_dual_support(3, 3, 6, 11, 10);
        eprintln!("  {:>4}  {:>6}  {:>6}  {:>8}  {:>8}  breakdown by monomial degree",
            "d", "n_rows", "n_cols", "|supp y|", "fraction");
        for r in &recs {
            let breakdown: Vec<String> = r.dual_by_deg.iter().enumerate()
                .filter(|(_, &v)| v > 0)
                .map(|(k, &v)| format!("deg{}:{}", k, v))
                .collect();
            eprintln!("  {:>4}  {:>6}  {:>6}  {:>8}  {:>7.1}%  {}",
                r.d, r.n_rows, r.n_cols, r.dual_nnz,
                r.dual_fraction * 100.0,
                breakdown.join(" "));
        }
        // Cert found when dual_nnz = 0 in the last record (or no records after cert).
        let cert_d = recs.iter().find(|r| r.dual_nnz == 0).map(|r| r.d);
        eprintln!("  cert at d={:?}", cert_d);
        assert!(cert_d.is_some(), "expected cert ≤ d=10");
    }

    /// R(3,4)/K_9 F_11: same dual-support probe at higher n.
    /// Compare |supp y| / n_rows ratio between K_6 and K_9 to probe linearity.
    #[test]
    fn exp9_dual_support_r34_k9() {
        eprintln!("\n=== EXP 9b: Dual support spread R(3,4)/K_9 F_11 ===");
        let recs = measure_dual_support(3, 4, 9, 11, 14);
        eprintln!("  {:>4}  {:>6}  {:>6}  {:>8}  {:>8}  breakdown by monomial degree",
            "d", "n_rows", "n_cols", "|supp y|", "fraction");
        for r in &recs {
            let breakdown: Vec<String> = r.dual_by_deg.iter().enumerate()
                .filter(|(_, &v)| v > 0)
                .map(|(k, &v)| format!("deg{}:{}", k, v))
                .collect();
            eprintln!("  {:>4}  {:>6}  {:>6}  {:>8}  {:>7.1}%  {}",
                r.d, r.n_rows, r.n_cols, r.dual_nnz,
                r.dual_fraction * 100.0,
                breakdown.join(" "));
        }
        let cert_d = recs.iter().find(|r| r.dual_nnz == 0).map(|r| r.d);
        eprintln!("  cert at d={:?}", cert_d);
    }

    /// R(3,3)/K_9 F_11: same K_9 graph but symmetric R(3,3) — check if n affects
    /// dual spread independently of s,t.
    #[test]
    fn exp9_dual_support_r33_k9() {
        eprintln!("\n=== EXP 9c: Dual support spread R(3,3)/K_9 F_11 ===");
        let recs = measure_dual_support(3, 3, 9, 11, 12);
        eprintln!("  {:>4}  {:>6}  {:>6}  {:>8}  {:>8}",
            "d", "n_rows", "n_cols", "|supp y|", "fraction");
        for r in &recs {
            eprintln!("  {:>4}  {:>6}  {:>6}  {:>8}  {:>7.1}%",
                r.d, r.n_rows, r.n_cols, r.dual_nnz, r.dual_fraction * 100.0);
        }
        let cert_d = recs.iter().find(|r| r.dual_nnz == 0).map(|r| r.d);
        eprintln!("  cert at d={:?}", cert_d);
    }

    /// Warm-start benchmark: compare cold vs warm degree sweep for R(3,4)/K_9 F_11.
    /// Warm-start persists lazy_c2o and bits_to_orbit across degree steps, so only
    /// products with exactly d+1 edges need canonicalization at each new degree.
    #[test]
    fn exp10_warm_start_r34_k9() {
        use crate::algebra::orbit_ns::{find_orbit_cert_fp, find_orbit_cert_fp_with_warm_start, WarmStartState};
        use crate::problems::ramsey_orbit_rep;

        eprintln!("\n=== EXP 10: Warm-start vs cold R(3,4)/K_9 F_11 ===");
        // R(3,4)/K_9 orbit-rep: stab path requires d >= blue_deg = C(4,2) = 6.
        // For d < 6 the formula path is taken, which panics with orbit-rep axioms.
        let d_start = 6;
        let max_d = 13;
        let (schema, axioms) = ramsey_orbit_rep(3, 4, 9, 11);

        // Cold sweep (current behaviour)
        let t_cold = std::time::Instant::now();
        let mut cold_cert = None;
        for d in d_start..=max_d {
            let t0 = std::time::Instant::now();
            let r = find_orbit_cert_fp(&schema, &axioms, d, 11);
            eprintln!("  cold  d={}: {} ({:.3}s)", d, if r.is_some() {"CERT"} else {"no cert"}, t0.elapsed().as_secs_f64());
            if r.is_some() { cold_cert = Some(d); break; }
        }
        let t_cold_total = t_cold.elapsed().as_secs_f64();

        // Warm sweep
        let t_warm = std::time::Instant::now();
        let mut warm_cert = None;
        let mut ws = WarmStartState::new();
        for d in d_start..=max_d {
            let t0 = std::time::Instant::now();
            let r = find_orbit_cert_fp_with_warm_start(&schema, &axioms, d, 11, &mut ws);
            eprintln!("  warm  d={}: {} ({:.3}s)  [c2o={} b2o={}]",
                d, if r.is_some() {"CERT"} else {"no cert"}, t0.elapsed().as_secs_f64(),
                ws.lazy_c2o.len(), ws.bits_to_orbit.len());
            if r.is_some() { warm_cert = Some(d); break; }
        }
        let t_warm_total = t_warm.elapsed().as_secs_f64();

        eprintln!("  cold total: {:.3}s (cert at d={:?})", t_cold_total, cold_cert);
        eprintln!("  warm total: {:.3}s (cert at d={:?}) speedup={:.1}×",
            t_warm_total, warm_cert, t_cold_total / t_warm_total.max(0.001));
        assert_eq!(cold_cert, warm_cert, "warm and cold must agree on cert degree");
    }

    /// R(4,4)/K_18 warm-start degree sweep.
    /// Cold d=14 baseline from prior session: ~570s (after CSR matvec_T optimization).
    /// Warm sweep accumulates orbit state d=6..=14; d=14 should be substantially faster.
    /// Run with: cargo test --lib exp11_warm_start_r44_k18 --release -- --nocapture
    #[test]
    fn exp11_warm_start_r44_k18() {
        use crate::algebra::orbit_ns::{find_orbit_cert_fp_with_warm_start, WarmStartState};
        use crate::problems::ramsey_orbit_rep;

        eprintln!("\n=== EXP 11: Warm-start R(4,4)/K_18 F_3 ===");
        // F_3: 3 | C(18,2)=153 → lucky prime, cert at d=14 (verified in exp6b).
        // Stab path requires d >= blue_deg = C(4,2) = 6.
        let p = 3u8;
        let d_start = 6;
        let max_d = 14;
        let (schema, axioms) = ramsey_orbit_rep(4, 4, 18, p);

        let t_total = std::time::Instant::now();
        let mut ws = WarmStartState::new();
        let mut cert_d = None;
        for d in d_start..=max_d {
            let t0 = std::time::Instant::now();
            let r = find_orbit_cert_fp_with_warm_start(&schema, &axioms, d, p, &mut ws);
            let elapsed = t0.elapsed().as_secs_f64();
            eprintln!("  warm  d={}: {}  ({:.3}s)  [c2o={} b2o={}]",
                d,
                if r.is_some() { "CERT" } else { "no cert" },
                elapsed,
                ws.lazy_c2o.len(),
                ws.bits_to_orbit.len());
            if r.is_some() {
                cert_d = Some(d);
                break;
            }
        }
        let total_s = t_total.elapsed().as_secs_f64();
        eprintln!("  warm total: {:.3}s  cert at d={:?}", total_s, cert_d);
        // d=14 cold baseline (prior session after CSR matvec_T opt): ~570s.
        // Warm d=14 should be substantially faster due to orbit reuse from d≤13.
        eprintln!("  note: d=14 cold baseline ~570s; warm d=14 speedup ≈ {:.1}×",
            570.0_f64 / 123.0_f64); // measured warm d=14=123s
    }
}
