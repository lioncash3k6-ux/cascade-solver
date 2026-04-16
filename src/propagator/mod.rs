//! Propagator module — homes for every IPASIR-UP external propagator.
//!
//! v0.5 shipped a single `BicliquePropagator`. v0.6 introduces
//! `CompositePropagator` so that multiple sub-propagators (biclique,
//! online symmetry, future algebraic/hierarchical engines) can share the
//! one external-propagator slot CaDiCaL exposes.
//!
//! # Re-exports
//! The public surface is unchanged from v0.5: `BicliquePropagator` is
//! still reachable as `cascade::propagator::BicliquePropagator`.

pub mod biclique;
pub mod composite;

pub use biclique::BicliquePropagator;
pub use composite::CompositePropagator;
