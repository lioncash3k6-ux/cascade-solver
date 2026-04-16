//! Permutation and generator-set data structures + VeriPB proof parser.
//!
//! `satsuma` emits the generator set of the detected symmetry group as
//! part of its VeriPB proof file, encoded in `dom` lines. Each `dom`
//! line carries two things we care about:
//!   1. The *substitution* (after ` >= 0 :` up to the trailing ` : ...`):
//!      pairs of the form `xN -> xM` or `xN -> ~xM`. Variables not
//!      mentioned are fixed.
//!   2. The *ordering* (`load_order NAME x1 x2 ... xN;`) used as the
//!      lex-leader ordering. We parse this separately.
//!
//! This module does not interact with the solver. PR-4 will use
//! `GeneratorSet` to drive the online symmetry propagator.

use std::fs::File;
use std::io::{self, BufRead, BufReader};
use std::path::Path;

/// A permutation of SAT literals: signed image per variable.
///
/// Convention:
///   - `image[v]` is defined for `v in 1..=n_vars` (index 0 is a padding
///     sentinel and must never be accessed).
///   - Positive value: variable v maps to variable image[v] with
///     polarity preserved.
///   - Negative value: variable v maps to variable |image[v]| with
///     polarity **flipped** (i.e., literal `v` → `~image[v]`).
///   - `image[v] == v`: v is fixed by this permutation.
///
/// Applying to a literal:
///   `apply_lit(+v) = image[v]`
///   `apply_lit(-v) = -image[v]`
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Permutation {
    image: Vec<i32>,
    n_vars: u32,
}

impl Permutation {
    /// Identity permutation on `n_vars` variables.
    pub fn identity(n_vars: u32) -> Self {
        let mut image = Vec::with_capacity(n_vars as usize + 1);
        image.push(0); // index 0 sentinel
        for v in 1..=n_vars {
            image.push(v as i32);
        }
        Self { image, n_vars }
    }

    /// Construct from a list of (src_var, signed_dst) pairs. Unmentioned
    /// variables default to identity. `signed_dst` uses the same sign
    /// convention as `apply_lit`.
    pub fn from_mapping(n_vars: u32, pairs: &[(u32, i32)]) -> Self {
        let mut p = Self::identity(n_vars);
        for &(src, dst) in pairs {
            assert!(src >= 1 && src <= n_vars, "src var {} out of range", src);
            assert!(
                dst.unsigned_abs() >= 1 && dst.unsigned_abs() <= n_vars,
                "dst var {} out of range",
                dst
            );
            p.image[src as usize] = dst;
        }
        p
    }

    pub fn n_vars(&self) -> u32 {
        self.n_vars
    }

    /// Signed image of a variable: positive = polarity preserved, negative
    /// = polarity flipped, absolute value = target variable.
    #[inline]
    pub fn apply_var(&self, v: u32) -> i32 {
        debug_assert!(v >= 1 && v <= self.n_vars, "var {} out of range", v);
        self.image[v as usize]
    }

    /// Apply the permutation to a DIMACS literal.
    #[inline]
    pub fn apply_lit(&self, l: i32) -> i32 {
        debug_assert!(l != 0, "literal 0 is invalid");
        let v = l.unsigned_abs();
        let signed = self.image[v as usize];
        if l > 0 { signed } else { -signed }
    }

    /// True iff this permutation is the identity.
    pub fn is_identity(&self) -> bool {
        for v in 1..=self.n_vars {
            if self.image[v as usize] != v as i32 {
                return false;
            }
        }
        true
    }

    /// Variables not fixed by this permutation (the support).
    pub fn support(&self) -> Vec<u32> {
        let mut s = Vec::new();
        for v in 1..=self.n_vars {
            if self.image[v as usize] != v as i32 {
                s.push(v);
            }
        }
        s
    }

    /// Whether this permutation flips polarity on any variable.
    pub fn has_polarity_flip(&self) -> bool {
        for v in 1..=self.n_vars {
            if self.image[v as usize] < 0 {
                return true;
            }
        }
        false
    }

    /// Compose two permutations: `self ∘ other` means "apply other first,
    /// then self." I.e., `(self.compose(other)).apply_lit(l) ==
    /// self.apply_lit(other.apply_lit(l))`.
    pub fn compose(&self, other: &Self) -> Self {
        assert_eq!(self.n_vars, other.n_vars);
        let n = self.n_vars;
        let mut image = vec![0i32; n as usize + 1];
        image[0] = 0;
        for v in 1..=n {
            // other maps +v to some signed literal; self maps that further.
            let intermediate = other.apply_var(v);
            let result = self.apply_lit(intermediate);
            // result is the signed image of +v under (self ∘ other).
            image[v as usize] = result;
        }
        Self { image, n_vars: n }
    }

    /// Apply this permutation elementwise to every literal in a clause,
    /// returning the image clause. Invariants: the image clause has the
    /// same length, and `apply_clause(¬C) = ¬apply_clause(C)` literal-by-
    /// literal. Used for orbit-closed learning (RFC-0002).
    pub fn apply_clause(&self, clause: &[i32]) -> Vec<i32> {
        clause.iter().map(|&l| self.apply_lit(l)).collect()
    }

    /// Compute the inverse permutation.
    ///
    /// For a permutation where `apply_var(v)` returns the forward image
    /// `g(v)` (possibly with polarity flip), the inverse's image satisfies
    /// `inverse.apply_lit(g.apply_lit(l)) == l` for every literal l.
    pub fn inverse(&self) -> Self {
        let n = self.n_vars;
        let mut inv_image = vec![0i32; n as usize + 1];
        inv_image[0] = 0;
        for v in 1..=n {
            let img = self.image[v as usize];
            // g(v) = img (signed). We want inv(|img|) such that
            // applying g then inv to literal +v yields +v.
            //   apply_lit(+v, g)    = img
            //   apply_lit(img, inv) should be +v
            // If img > 0: inv(+img) = +v, so inv.image[img] = v.
            // If img < 0: apply_lit(-|img|, inv) = -inv.image[|img|] = +v,
            //             so inv.image[|img|] = -v.
            let target = img.unsigned_abs() as usize;
            inv_image[target] = if img > 0 { v as i32 } else { -(v as i32) };
        }
        Self { image: inv_image, n_vars: n }
    }
}

/// Collection of permutations + the lex ordering for canonical-form
/// checks.
#[derive(Clone, Debug)]
pub struct GeneratorSet {
    pub gens: Vec<Permutation>,
    pub n_vars: u32,
    /// Variable ordering for lex-leader: `ordering[i]` is the i-th var
    /// in lex-leader priority (0 = highest). If empty, defaults to
    /// natural order 1..=n_vars at use sites.
    pub ordering: Vec<u32>,
}

impl GeneratorSet {
    pub fn empty(n_vars: u32) -> Self {
        Self { gens: Vec::new(), n_vars, ordering: Vec::new() }
    }

    pub fn push(&mut self, p: Permutation) {
        assert_eq!(p.n_vars, self.n_vars, "mismatched n_vars");
        self.gens.push(p);
    }

    pub fn len(&self) -> usize {
        self.gens.len()
    }

    pub fn is_empty(&self) -> bool {
        self.gens.is_empty()
    }

    /// Drop identity generators (satsuma occasionally emits duplicate or
    /// trivial generators; we filter them here since they'd generate no
    /// useful propagation).
    pub fn prune_identities(&mut self) {
        self.gens.retain(|p| !p.is_identity());
    }

    /// Remove exact-duplicate generators. Does not close under inverses
    /// or products — that's a downstream concern.
    pub fn dedup(&mut self) {
        let mut seen: Vec<Permutation> = Vec::new();
        self.gens.retain(|p| {
            if seen.iter().any(|q| q == p) {
                false
            } else {
                seen.push(p.clone());
                true
            }
        });
    }

    /// Replace every generator with its inverse.
    pub fn invert_all(&mut self) {
        for g in &mut self.gens {
            *g = g.inverse();
        }
    }
}

// ─── Parser ──────────────────────────────────────────────────────────────

/// Parse the VeriPB proof file satsuma emits and extract generators +
/// load-order.
///
/// Recognizes:
///   * `load_order ID x1 x2 ... xN;` — sets `GeneratorSet.ordering`.
///   * `dom COEFS >= 0 : SUBST : subproof` — each such line contributes
///     one generator derived from SUBST.
///
/// Unknown lines are ignored. If multiple `load_order` lines appear the
/// **last** one wins. Generators are deduplicated and identity
/// permutations are dropped.
pub fn parse_veripb_proof<P: AsRef<Path>>(
    path: P,
    n_vars: u32,
) -> io::Result<GeneratorSet> {
    let f = File::open(path.as_ref())?;
    let reader = BufReader::new(f);
    let mut set = GeneratorSet::empty(n_vars);

    for line in reader.lines() {
        let line = line?;
        let trimmed = line.trim();
        if let Some(rest) = trimmed.strip_prefix("load_order ") {
            set.ordering = parse_load_order(rest);
        } else if let Some(rest) = trimmed.strip_prefix("dom ") {
            if let Some(p) = parse_dom_line(rest, n_vars) {
                set.gens.push(p);
            }
        }
    }
    set.prune_identities();
    set.dedup();
    Ok(set)
}

/// Parse a `load_order` suffix: `ID x1 x2 ... xN;`. Returns the variable
/// list in declaration order (i.e., ordering[0] is the highest-priority
/// var for lex-leader).
fn parse_load_order(suffix: &str) -> Vec<u32> {
    let cleaned = suffix.trim_end_matches(';').trim();
    let mut toks = cleaned.split_whitespace();
    toks.next(); // skip the ID (e.g. "exp40")
    let mut out = Vec::new();
    for t in toks {
        if let Some(v) = parse_var_token(t) {
            out.push(v);
        }
    }
    out
}

/// Parse a single `dom` line body (after the `dom ` prefix): extract the
/// substitution between ` >= 0 :` and the trailing ` :`.
fn parse_dom_line(body: &str, n_vars: u32) -> Option<Permutation> {
    const GEQ0: &str = ">= 0 :";
    let idx = body.find(GEQ0)?;
    let after = &body[idx + GEQ0.len()..];
    // Trailing field is ": subproof" (or similar). The substitution is
    // everything up to the last colon.
    let end = after.rfind(':')?;
    let subst_str = after[..end].trim();
    parse_substitution(subst_str, n_vars)
}

/// Parse `xA -> xB xC -> ~xD …` into a `Permutation`.
fn parse_substitution(s: &str, n_vars: u32) -> Option<Permutation> {
    let tokens: Vec<&str> = s.split_whitespace().collect();
    if tokens.is_empty() {
        return Some(Permutation::identity(n_vars));
    }
    let mut pairs = Vec::new();
    let mut i = 0;
    while i + 2 < tokens.len() || i + 2 == tokens.len() {
        if i + 2 >= tokens.len() {
            break;
        }
        let src_tok = tokens[i];
        let arrow = tokens[i + 1];
        let dst_tok = tokens[i + 2];
        if arrow != "->" {
            return None;
        }
        let src_var = parse_var_token(src_tok)?;
        let (dst_var, neg) = parse_signed_var_token(dst_tok)?;
        if src_var == 0 || dst_var == 0 {
            return None;
        }
        if src_var > n_vars || dst_var > n_vars {
            return None;
        }
        let signed = if neg { -(dst_var as i32) } else { dst_var as i32 };
        pairs.push((src_var, signed));
        i += 3;
    }
    Some(Permutation::from_mapping(n_vars, &pairs))
}

/// `x123` → Some(123). Any other shape → None.
fn parse_var_token(t: &str) -> Option<u32> {
    let rest = t.strip_prefix('x')?;
    rest.parse::<u32>().ok()
}

/// `x123` → Some((123, false)); `~x123` → Some((123, true)).
fn parse_signed_var_token(t: &str) -> Option<(u32, bool)> {
    if let Some(rest) = t.strip_prefix("~x") {
        rest.parse::<u32>().ok().map(|v| (v, true))
    } else if let Some(rest) = t.strip_prefix('x') {
        rest.parse::<u32>().ok().map(|v| (v, false))
    } else {
        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::Write;

    fn write_tmp(name: &str, contents: &str) -> std::path::PathBuf {
        let mut p = std::env::temp_dir();
        p.push(name);
        let mut f = std::fs::File::create(&p).unwrap();
        f.write_all(contents.as_bytes()).unwrap();
        p
    }

    // ─── Permutation ──

    #[test]
    fn identity_permutation_fixes_everything() {
        let p = Permutation::identity(5);
        for v in 1..=5 {
            assert_eq!(p.apply_var(v), v as i32);
            assert_eq!(p.apply_lit(v as i32), v as i32);
            assert_eq!(p.apply_lit(-(v as i32)), -(v as i32));
        }
        assert!(p.is_identity());
        assert!(p.support().is_empty());
        assert!(!p.has_polarity_flip());
    }

    #[test]
    fn transposition_swaps_two_vars() {
        let p = Permutation::from_mapping(4, &[(1, 2), (2, 1)]);
        assert_eq!(p.apply_lit(1), 2);
        assert_eq!(p.apply_lit(-1), -2);
        assert_eq!(p.apply_lit(2), 1);
        assert_eq!(p.apply_lit(3), 3); // fixed
        assert!(!p.is_identity());
        assert_eq!(p.support(), vec![1, 2]);
        assert!(!p.has_polarity_flip());
    }

    #[test]
    fn apply_clause_preserves_length_and_signs() {
        // Swap (1 2)(3 4). Clause [-1, 3, -4] → [-2, 4, -3].
        let p = Permutation::from_mapping(4, &[(1, 2), (2, 1), (3, 4), (4, 3)]);
        assert_eq!(p.apply_clause(&[-1, 3, -4]), vec![-2, 4, -3]);
        // Polarity-flip generator: x_i -> ~x_i. Clause [+1, -2] → [-1, +2].
        let pf = Permutation::from_mapping(2, &[(1, -1), (2, -2)]);
        assert_eq!(pf.apply_clause(&[1, -2]), vec![-1, 2]);
        // Fixed-point identity returns input.
        let id = Permutation::identity(5);
        assert_eq!(id.apply_clause(&[1, -2, 3]), vec![1, -2, 3]);
    }

    #[test]
    fn polarity_flip_on_self() {
        // Color-swap: every var maps to itself with polarity inverted.
        let pairs: Vec<_> = (1..=3).map(|v| (v, -(v as i32))).collect();
        let p = Permutation::from_mapping(3, &pairs);
        assert_eq!(p.apply_lit(1), -1);
        assert_eq!(p.apply_lit(-2), 2);
        assert!(p.has_polarity_flip());
        assert!(!p.is_identity());
    }

    // ─── GeneratorSet ──

    #[test]
    fn generator_set_dedup_and_prune() {
        let id = Permutation::identity(3);
        let swap = Permutation::from_mapping(3, &[(1, 2), (2, 1)]);
        let swap_dup = swap.clone();

        let mut gs = GeneratorSet::empty(3);
        gs.push(id);
        gs.push(swap);
        gs.push(swap_dup);
        assert_eq!(gs.len(), 3);

        gs.prune_identities();
        assert_eq!(gs.len(), 2);

        gs.dedup();
        assert_eq!(gs.len(), 1);
    }

    // ─── Token parsers ──

    #[test]
    fn parse_var_and_signed_var() {
        assert_eq!(parse_var_token("x1"), Some(1));
        assert_eq!(parse_var_token("x42"), Some(42));
        assert_eq!(parse_var_token("y1"), None);
        assert_eq!(parse_var_token("x"), None);

        assert_eq!(parse_signed_var_token("x7"), Some((7, false)));
        assert_eq!(parse_signed_var_token("~x7"), Some((7, true)));
        assert_eq!(parse_signed_var_token("~y7"), None);
    }

    // ─── Substitution parser ──

    #[test]
    fn substitution_empty_is_identity() {
        let p = parse_substitution("", 5).unwrap();
        assert!(p.is_identity());
    }

    #[test]
    fn substitution_r33_color_swap() {
        // Exactly the substitution portion satsuma emits for R(3,3)/K_6's
        // color-swap generator.
        let s = "x1 -> ~x1 x2 -> ~x2 x3 -> ~x3 x4 -> ~x4 x5 -> ~x5 \
                 x6 -> ~x6 x7 -> ~x7 x8 -> ~x8 x9 -> ~x9 x10 -> ~x10 \
                 x11 -> ~x11 x12 -> ~x12 x13 -> ~x13 x14 -> ~x14 x15 -> ~x15";
        let p = parse_substitution(s, 15).unwrap();
        for v in 1..=15 {
            assert_eq!(p.apply_lit(v as i32), -(v as i32));
            assert_eq!(p.apply_lit(-(v as i32)), v as i32);
        }
        assert!(p.has_polarity_flip());
    }

    #[test]
    fn substitution_r34_vertex_perm() {
        // Example from satsuma's R(3,4)/K_9 proof — one of the vertex
        // permutations it detected.
        let s = "x2 -> x9 x3 -> x10 x4 -> x11 x5 -> x12 x6 -> x13 \
                 x7 -> x14 x8 -> x15 x9 -> x2 x10 -> x3 x11 -> x4 \
                 x12 -> x5 x13 -> x6 x14 -> x7 x15 -> x8";
        let p = parse_substitution(s, 36).unwrap();
        assert_eq!(p.apply_lit(2), 9);
        assert_eq!(p.apply_lit(9), 2);
        assert_eq!(p.apply_lit(1), 1); // unmentioned → fixed
        assert!(!p.has_polarity_flip());
        assert_eq!(p.support().len(), 14);
    }

    #[test]
    fn substitution_rejects_bad_arrow() {
        let s = "x1 ==> x2";
        assert!(parse_substitution(s, 5).is_none());
    }

    // ─── Dom-line parser ──

    #[test]
    fn dom_line_color_swap() {
        let line = "-1 ~x2 1 x2 >= 0 :  x1 -> ~x1 x2 -> ~x2 x3 -> ~x3 :  subproof";
        let p = parse_dom_line(line, 3).unwrap();
        assert_eq!(p.apply_lit(1), -1);
        assert_eq!(p.apply_lit(2), -2);
        assert_eq!(p.apply_lit(3), -3);
    }

    #[test]
    fn dom_line_missing_ge0_returns_none() {
        assert!(parse_dom_line("no constraint here : x1 -> x2 : end", 2).is_none());
    }

    // ─── load_order parser ──

    #[test]
    fn load_order_parse() {
        let suffix = "exp40 x8 x15 x14 x13 x12 x11 x10 x9 x1 x7 x6 x5 x4 x3 x2;";
        let ord = parse_load_order(suffix);
        assert_eq!(ord, vec![8, 15, 14, 13, 12, 11, 10, 9, 1, 7, 6, 5, 4, 3, 2]);
    }

    #[test]
    fn load_order_accepts_trailing_semicolon_absent() {
        let ord = parse_load_order("exp4 x1 x2 x3 x4");
        assert_eq!(ord, vec![1, 2, 3, 4]);
    }

    // ─── End-to-end parse ──

    #[test]
    fn parse_veripb_file_r33_like() {
        // A minimized VeriPB proof containing: preamble (ignored), a
        // load_order line, two dom lines (color-swap + trivial identity
        // which gets pruned).
        let content = "\
pseudo-Boolean proof version 3.0
vars
left u1 u2 u3 ;
end;
load_order exp3 x3 x2 x1;
dom -1 ~x1 1 ~x1 >= 0 :  x1 -> ~x1 x2 -> ~x2 x3 -> ~x3 :  subproof
dom -1 ~x1 1 ~x1 >= 0 :  x1 -> x1 :  subproof
end pseudo-Boolean proof;
";
        let path = write_tmp("cascade_generators_parse.veripb", content);
        let gs = parse_veripb_proof(&path, 3).unwrap();
        assert_eq!(gs.ordering, vec![3, 2, 1]);
        assert_eq!(gs.len(), 1, "identity should be pruned");
        assert!(gs.gens[0].has_polarity_flip());
    }

    #[test]
    fn parse_veripb_file_empty_returns_empty_set() {
        let path = write_tmp("cascade_generators_empty.veripb", "");
        let gs = parse_veripb_proof(&path, 10).unwrap();
        assert!(gs.is_empty());
        assert!(gs.ordering.is_empty());
    }
}
