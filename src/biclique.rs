//! Biclique decomposition of Ramsey clique-ban constraints.
//!
//! A K_s ban clause on vertices {v1, ..., vs} says "not all C(s,2) edges
//! can be the same color." For a complete graph K_n, there are C(n,s) such
//! bans — exponentially many.
//!
//! Biclique decomposition replaces these with a compact propagation structure.
//! For each vertex v and each subset S of its neighbors of size R(s-1,t)-1,
//! we enforce: "at most |S|-1 edges from v to S are red." This is equivalent
//! to: if all edges from v to S are red, then the induced subgraph on S
//! contains a red K_{s-1}, contradicting the Ramsey bound.
//!
//! The key insight: instead of one clause per K_s, we have one *group* per
//! (vertex, neighbor-subset) pair, and each group acts as an at-most-k
//! constraint on the star edges. When the (k+1)-th edge in a group becomes
//! red, we propagate the remaining edges to blue.
//!
//! For the IPASIR-UP propagator, each group is:
//!   - A set of edge variables (the star edges from v to S)
//!   - A threshold k (at most k can be true/red)
//!   - When k+1 are assigned true, propagate the rest to false
//!   - Reason clause: the k+1 true edges imply ¬remaining

use crate::cardinality;
use crate::dimacs::Cnf;

/// A single biclique group: at-most-k constraint on a set of edge variables.
#[derive(Debug, Clone)]
pub struct BiclGroup {
    /// The edge variable indices in this group.
    pub edges: Vec<u32>,
    /// At most this many can be true (red). When threshold+1 are true,
    /// propagate the rest to false (blue).
    pub threshold: u32,
}

/// Full biclique decomposition for a Ramsey instance.
#[derive(Debug)]
pub struct BiclDecomp {
    /// Number of vertices in the complete graph.
    pub n: u32,
    /// Ramsey parameters (s, t).
    pub s: u32,
    pub t: u32,
    /// Red groups: at-most-k constraints on red edges (K_s avoidance).
    pub red_groups: Vec<BiclGroup>,
    /// Blue groups: at-most-k constraints on blue edges (K_t avoidance).
    /// Blue edge e being "true" means the original variable e is false.
    pub blue_groups: Vec<BiclGroup>,
    /// Total number of edge variables.
    pub n_edges: u32,
}

/// Decompose Ramsey R(s,t) ban clauses on K_n into biclique groups.
///
/// For each vertex v (1..=n), for each color:
///   - Red: the star edges from v to all other vertices form a group
///     with threshold = R(s-1, t) - 2 (max red degree at v).
///   - Blue: the star edges form a group with threshold = R(s, t-1) - 2.
///
/// This is the simplest decomposition: one group per vertex per color.
/// Each group is a star (all edges incident to v), and the threshold
/// comes from the Ramsey degree bound.
pub fn decompose(n: u32, s: u32, t: u32) -> BiclDecomp {
    let n_edges = n * (n - 1) / 2;

    // Degree bounds from Ramsey recursion
    let red_bound = if s >= 2 {
        cardinality::ramsey_lookup(s - 1, t)
    } else {
        0
    };
    let blue_bound = if t >= 2 {
        cardinality::ramsey_lookup(s, t - 1)
    } else {
        0
    };

    // Red threshold: at most (red_bound - 2) red edges at each vertex
    // (red_bound - 1 neighbors = red_bound - 1 edges, but threshold is
    //  the max allowed, so threshold = red_bound - 2)
    let red_threshold = if red_bound >= 2 { red_bound - 2 } else { n - 1 };
    let blue_threshold = if blue_bound >= 2 { blue_bound - 2 } else { n - 1 };

    let mut red_groups = Vec::with_capacity(n as usize);
    let mut blue_groups = Vec::with_capacity(n as usize);

    for v in 1..=n {
        let mut star_edges = Vec::with_capacity((n - 1) as usize);
        for w in 1..=n {
            if w == v {
                continue;
            }
            let (a, b) = if v < w { (v, w) } else { (w, v) };
            let e = cardinality::ev(a, b, n).raw() as u32;
            star_edges.push(e);
        }

        red_groups.push(BiclGroup {
            edges: star_edges.clone(),
            threshold: red_threshold,
        });

        blue_groups.push(BiclGroup {
            edges: star_edges,
            threshold: blue_threshold,
        });
    }

    BiclDecomp {
        n,
        s,
        t,
        red_groups,
        blue_groups,
        n_edges,
    }
}

/// Decompose directly from ban clauses in the CNF.
///
/// Each ban clause (width C(s,2) or C(t,2)) becomes a group:
///   - Positive-literal ban (red K_s): all lits positive → threshold = width-1
///   - Negative-literal ban (blue K_t): all lits negative → threshold = width-1
///
/// The reason clauses ARE the ban clauses, so they're trivially RUP.
pub fn decompose_from_cnf(cnf: &Cnf, n: u32, s: u32, t: u32) -> BiclDecomp {
    let n_edges = n * (n - 1) / 2;
    let red_width = s * (s - 1) / 2;   // C(s,2)
    let blue_width = t * (t - 1) / 2;  // C(t,2)

    let mut red_groups = Vec::new();
    let mut blue_groups = Vec::new();

    for clause in cnf.clauses.iter() {
        let lits = clause.lits();
        let width = lits.len() as u32;

        // Identify ban clauses by their width and polarity pattern
        if width == red_width && lits.iter().all(|l| l.is_negative()) {
            // Red K_s ban: (¬e1 ∨ ¬e2 ∨ ... ∨ ¬e_{C(s,2)})
            // = "not all edges red" = at most C(s,2)-1 can be true
            let edges: Vec<u32> = lits.iter().map(|l| l.var().0).collect();
            red_groups.push(BiclGroup {
                edges,
                threshold: width - 1,
            });
        } else if width == blue_width && lits.iter().all(|l| l.is_positive()) {
            // Blue K_t ban: (e1 ∨ e2 ∨ ... ∨ e_{C(t,2)})
            // = "not all edges blue" = at most C(t,2)-1 can be false
            let edges: Vec<u32> = lits.iter().map(|l| l.var().0).collect();
            blue_groups.push(BiclGroup {
                edges,
                threshold: width - 1,
            });
        }
    }

    BiclDecomp {
        n,
        s,
        t,
        red_groups,
        blue_groups,
        n_edges,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn decompose_r33() {
        // R(3,3)=6, K_6: each vertex has 5 neighbors
        // R(2,3)=3, so red threshold = 3-2 = 1 (at most 1 red edge per vertex)
        // R(3,2)=3, so blue threshold = 3-2 = 1
        let d = decompose(6, 3, 3);
        assert_eq!(d.red_groups.len(), 6);
        assert_eq!(d.red_groups[0].edges.len(), 5);
        assert_eq!(d.red_groups[0].threshold, 1);
        assert_eq!(d.blue_groups[0].threshold, 1);
    }

    #[test]
    fn decompose_r44() {
        // R(4,4)=18, K_18: each vertex has 17 neighbors
        // R(3,4)=9, so red threshold = 9-2 = 7
        // R(4,3)=9, so blue threshold = 9-2 = 7
        let d = decompose(18, 4, 4);
        assert_eq!(d.red_groups.len(), 18);
        assert_eq!(d.red_groups[0].edges.len(), 17);
        assert_eq!(d.red_groups[0].threshold, 7);
    }

    #[test]
    fn decompose_r45() {
        // R(4,5)=25, K_25: each vertex has 24 neighbors
        // R(3,5)=14, so red threshold = 14-2 = 12
        // R(4,4)=18, so blue threshold = 18-2 = 16
        let d = decompose(25, 4, 5);
        assert_eq!(d.red_groups.len(), 25);
        assert_eq!(d.red_groups[0].edges.len(), 24);
        assert_eq!(d.red_groups[0].threshold, 12);
        assert_eq!(d.blue_groups[0].threshold, 16);
    }

    #[test]
    fn decompose_r46() {
        // R(4,6) — K_36: each vertex has 35 neighbors
        // R(3,6)=18, so red threshold = 18-2 = 16
        // R(4,5)=25, so blue threshold = 25-2 = 23
        let d = decompose(36, 4, 6);
        assert_eq!(d.red_groups.len(), 36);
        assert_eq!(d.red_groups[0].edges.len(), 35);
        assert_eq!(d.red_groups[0].threshold, 16);
        assert_eq!(d.blue_groups[0].threshold, 23);
    }
}
