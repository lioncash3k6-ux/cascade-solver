//! Rust FFI bindings to CaDiCaL 2.2.1 with IPASIR-UP external propagator.
//!
//! Uses a thin C++ wrapper (`cadical_ffi.cpp`) that bridges Rust function
//! pointers to CaDiCaL's C++ virtual method dispatch.

use std::ffi::CString;
use std::os::raw::{c_char, c_int, c_void};
use std::path::Path;

// Raw FFI declarations matching cadical_ffi.h
#[repr(C)]
struct FFIPropagatorVtable {
    state: *mut c_void,
    notify_assignment: Option<unsafe extern "C" fn(*mut c_void, *const c_int, usize)>,
    notify_new_decision_level: Option<unsafe extern "C" fn(*mut c_void)>,
    notify_backtrack: Option<unsafe extern "C" fn(*mut c_void, usize)>,
    cb_propagate: Option<unsafe extern "C" fn(*mut c_void) -> c_int>,
    cb_add_reason_clause_lit: Option<unsafe extern "C" fn(*mut c_void, c_int) -> c_int>,
    cb_check_found_model: Option<unsafe extern "C" fn(*mut c_void, *const c_int, usize) -> c_int>,
    cb_has_external_clause: Option<unsafe extern "C" fn(*mut c_void, *mut c_int) -> c_int>,
    cb_add_external_clause_lit: Option<unsafe extern "C" fn(*mut c_void) -> c_int>,
    cb_decide: Option<unsafe extern "C" fn(*mut c_void) -> c_int>,
    reasons_forgettable: c_int,
    cb_learning: Option<unsafe extern "C" fn(*mut c_void, c_int) -> c_int>,
    cb_learn: Option<unsafe extern "C" fn(*mut c_void, c_int)>,
}

#[repr(C)]
struct CaDiCaLSolverOpaque {
    _private: [u8; 0],
}

extern "C" {
    fn cadical_ffi_new() -> *mut CaDiCaLSolverOpaque;
    fn cadical_ffi_delete(s: *mut CaDiCaLSolverOpaque);
    fn cadical_ffi_add(s: *mut CaDiCaLSolverOpaque, lit: c_int);
    fn cadical_ffi_solve(s: *mut CaDiCaLSolverOpaque) -> c_int;
    fn cadical_ffi_val(s: *mut CaDiCaLSolverOpaque, lit: c_int) -> c_int;
    fn cadical_ffi_set(s: *mut CaDiCaLSolverOpaque, name: *const c_char, val: c_int);
    fn cadical_ffi_connect_propagator(
        s: *mut CaDiCaLSolverOpaque,
        vt: *mut FFIPropagatorVtable,
    );
    fn cadical_ffi_disconnect_propagator(s: *mut CaDiCaLSolverOpaque);
    fn cadical_ffi_add_observed_var(s: *mut CaDiCaLSolverOpaque, var: c_int);
    fn cadical_ffi_trace_proof(s: *mut CaDiCaLSolverOpaque, path: *const c_char) -> c_int;
    fn cadical_ffi_flush_proof(s: *mut CaDiCaLSolverOpaque);
    fn cadical_ffi_close_proof(s: *mut CaDiCaLSolverOpaque);
    fn cadical_ffi_conflicts(s: *mut CaDiCaLSolverOpaque) -> i64;
    fn cadical_ffi_vars(s: *mut CaDiCaLSolverOpaque) -> c_int;
    fn cadical_ffi_connect_timeout(s: *mut CaDiCaLSolverOpaque, secs: f64);
    fn cadical_ffi_disconnect_timeout(s: *mut CaDiCaLSolverOpaque);
}

/// Result of a CaDiCaL solve call.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SolveResult {
    Sat,
    Unsat,
    Unknown,
}

/// Trait for implementing an IPASIR-UP external propagator.
pub trait ExternalPropagator {
    /// Called when observed variables are assigned.
    fn notify_assignment(&mut self, lits: &[i32]);
    /// Called when a new decision level is created.
    fn notify_new_decision_level(&mut self);
    /// Called on backtrack — all assignments above `new_level` are undone.
    fn notify_backtrack(&mut self, new_level: usize);
    /// Return a literal to propagate, or 0 if none.
    fn propagate(&mut self) -> i32;
    /// Return the next literal in the reason clause for `propagated_lit`, or 0 to end.
    fn add_reason_clause_lit(&mut self, propagated_lit: i32) -> i32;
    /// Check if the found model is valid. Return true to accept.
    fn check_found_model(&mut self, model: &[i32]) -> bool;

    /// Learner callback: called for each CDCL-learned clause. Return true
    /// to receive the clause lits via `learn_clause_lit`.
    fn learning(&mut self, _size: i32) -> bool { false }
    /// Receive one literal of a learned clause (0-terminated).
    fn learn_clause_lit(&mut self, _lit: i32) {}

    /// Does the propagator have an external clause to add? If yes, set
    /// `is_forgettable` and return true.
    fn has_external_clause(&mut self, _is_forgettable: &mut bool) -> bool { false }
    /// Stream one literal of the external clause; return 0 to end.
    fn add_external_clause_lit(&mut self) -> i32 { 0 }

    /// Called before each CaDiCaL decision. Return a literal to decide
    /// on (variable + polarity), or 0 to let CaDiCaL decide. The
    /// literal must be an observed, currently-unassigned variable.
    fn decide(&mut self) -> i32 { 0 }
}

/// In-process CaDiCaL solver with IPASIR-UP support.
pub struct Solver {
    ptr: *mut CaDiCaLSolverOpaque,
    _vtable: Option<Box<FFIPropagatorVtable>>,
    /// Raw pointer to Box<dyn ExternalPropagator> on the heap. Freed in Drop.
    _prop_raw: *mut Box<dyn ExternalPropagator>,
}

// Trampoline functions that dispatch from C callbacks to Rust trait methods
unsafe extern "C" fn trampoline_notify_assignment(
    state: *mut c_void,
    lits: *const c_int,
    n: usize,
) {
    let prop = &mut *(state as *mut Box<dyn ExternalPropagator>);
    let slice = std::slice::from_raw_parts(lits, n);
    prop.notify_assignment(slice);
}

unsafe extern "C" fn trampoline_notify_new_decision_level(state: *mut c_void) {
    let prop = &mut *(state as *mut Box<dyn ExternalPropagator>);
    prop.notify_new_decision_level();
}

unsafe extern "C" fn trampoline_notify_backtrack(state: *mut c_void, new_level: usize) {
    let prop = &mut *(state as *mut Box<dyn ExternalPropagator>);
    prop.notify_backtrack(new_level);
}

unsafe extern "C" fn trampoline_cb_propagate(state: *mut c_void) -> c_int {
    let prop = &mut *(state as *mut Box<dyn ExternalPropagator>);
    prop.propagate()
}

unsafe extern "C" fn trampoline_cb_add_reason_clause_lit(
    state: *mut c_void,
    propagated_lit: c_int,
) -> c_int {
    let prop = &mut *(state as *mut Box<dyn ExternalPropagator>);
    prop.add_reason_clause_lit(propagated_lit)
}

unsafe extern "C" fn trampoline_cb_check_found_model(
    state: *mut c_void,
    model: *const c_int,
    n: usize,
) -> c_int {
    let prop = &mut *(state as *mut Box<dyn ExternalPropagator>);
    let slice = std::slice::from_raw_parts(model, n);
    if prop.check_found_model(slice) { 1 } else { 0 }
}

unsafe extern "C" fn trampoline_cb_decide(state: *mut c_void) -> c_int {
    let prop = &mut *(state as *mut Box<dyn ExternalPropagator>);
    prop.decide()
}

unsafe extern "C" fn trampoline_cb_has_external_clause(
    state: *mut c_void,
    is_forgettable: *mut c_int,
) -> c_int {
    let prop = &mut *(state as *mut Box<dyn ExternalPropagator>);
    let mut forgettable = false;
    let has = prop.has_external_clause(&mut forgettable);
    if !is_forgettable.is_null() {
        *is_forgettable = if forgettable { 1 } else { 0 };
    }
    if has { 1 } else { 0 }
}

unsafe extern "C" fn trampoline_cb_add_external_clause_lit(state: *mut c_void) -> c_int {
    let prop = &mut *(state as *mut Box<dyn ExternalPropagator>);
    prop.add_external_clause_lit()
}

unsafe extern "C" fn trampoline_cb_learning(state: *mut c_void, size: c_int) -> c_int {
    let prop = &mut *(state as *mut Box<dyn ExternalPropagator>);
    if prop.learning(size) { 1 } else { 0 }
}

unsafe extern "C" fn trampoline_cb_learn(state: *mut c_void, lit: c_int) {
    let prop = &mut *(state as *mut Box<dyn ExternalPropagator>);
    prop.learn_clause_lit(lit);
}

impl Solver {
    /// Create a new in-process CaDiCaL solver.
    pub fn new() -> Self {
        let ptr = unsafe { cadical_ffi_new() };
        assert!(!ptr.is_null());
        Self {
            ptr,
            _vtable: None,
            _prop_raw: std::ptr::null_mut(),
        }
    }

    /// Add a clause literal-by-literal. Call with 0 to terminate the clause.
    pub fn add(&mut self, lit: i32) {
        unsafe { cadical_ffi_add(self.ptr, lit) }
    }

    /// Add a full clause from a slice.
    pub fn add_clause(&mut self, lits: &[i32]) {
        for &lit in lits {
            self.add(lit);
        }
        self.add(0);
    }

    /// Solve the formula. Returns SAT/UNSAT/Unknown.
    pub fn solve(&mut self) -> SolveResult {
        match unsafe { cadical_ffi_solve(self.ptr) } {
            10 => SolveResult::Sat,
            20 => SolveResult::Unsat,
            _ => SolveResult::Unknown,
        }
    }

    /// Get the value of a literal in the model (after SAT).
    pub fn val(&self, lit: i32) -> i32 {
        unsafe { cadical_ffi_val(self.ptr, lit) }
    }

    /// Set a solver option.
    pub fn set(&mut self, name: &str, val: i32) {
        let cname = CString::new(name).unwrap();
        unsafe { cadical_ffi_set(self.ptr, cname.as_ptr(), val) }
    }

    /// Connect a wall-clock timeout: CaDiCaL terminates after `secs` seconds.
    pub fn connect_timeout(&mut self, secs: f64) {
        unsafe { cadical_ffi_connect_timeout(self.ptr, secs) }
    }

    /// Disconnect the wall-clock timeout (also called automatically on drop).
    pub fn disconnect_timeout(&mut self) {
        unsafe { cadical_ffi_disconnect_timeout(self.ptr) }
    }

    /// Enable DRAT proof tracing to a file.
    pub fn trace_proof(&mut self, path: &Path) -> bool {
        let cpath = CString::new(path.to_str().unwrap()).unwrap();
        unsafe { cadical_ffi_trace_proof(self.ptr, cpath.as_ptr()) != 0 }
    }

    /// Flush the proof trace.
    pub fn flush_proof(&mut self) {
        unsafe { cadical_ffi_flush_proof(self.ptr) }
    }

    /// Close the proof trace.
    pub fn close_proof(&mut self) {
        unsafe { cadical_ffi_close_proof(self.ptr) }
    }

    /// Get number of conflicts.
    pub fn conflicts(&self) -> i64 {
        unsafe { cadical_ffi_conflicts(self.ptr) }
    }

    /// Get number of variables.
    pub fn vars(&self) -> i32 {
        unsafe { cadical_ffi_vars(self.ptr) }
    }

    /// Connect an external propagator and observe the given variables.
    pub fn connect_propagator(
        &mut self,
        propagator: Box<dyn ExternalPropagator>,
        observed_vars: &[i32],
    ) {
        // Leak the propagator into a raw pointer for stable address.
        // We'll reconstruct the Box in drop/disconnect to free it.
        let prop_raw = Box::into_raw(Box::new(propagator));

        let mut vtable = Box::new(FFIPropagatorVtable {
            state: prop_raw as *mut c_void,
            notify_assignment: Some(trampoline_notify_assignment),
            notify_new_decision_level: Some(trampoline_notify_new_decision_level),
            notify_backtrack: Some(trampoline_notify_backtrack),
            cb_propagate: Some(trampoline_cb_propagate),
            cb_add_reason_clause_lit: Some(trampoline_cb_add_reason_clause_lit),
            cb_check_found_model: Some(trampoline_cb_check_found_model),
            cb_has_external_clause: Some(trampoline_cb_has_external_clause),
            cb_add_external_clause_lit: Some(trampoline_cb_add_external_clause_lit),
            cb_decide: Some(trampoline_cb_decide),
            reasons_forgettable: 0, // Non-forgettable = proof-safe
            cb_learning: Some(trampoline_cb_learning),
            cb_learn: Some(trampoline_cb_learn),
        });

        unsafe {
            cadical_ffi_connect_propagator(self.ptr, &mut *vtable);
            for &var in observed_vars {
                cadical_ffi_add_observed_var(self.ptr, var);
            }
        }

        // Keep vtable alive; propagator raw pointer freed in Drop
        self._vtable = Some(vtable);
        self._prop_raw = prop_raw;
    }

    /// Disconnect the external propagator.
    pub fn disconnect_propagator(&mut self) {
        unsafe { cadical_ffi_disconnect_propagator(self.ptr) }
        self._vtable = None;
        if !self._prop_raw.is_null() {
            unsafe { drop(Box::from_raw(self._prop_raw)) };
            self._prop_raw = std::ptr::null_mut();
        }
    }
}

impl Drop for Solver {
    fn drop(&mut self) {
        unsafe { cadical_ffi_delete(self.ptr) }
        if !self._prop_raw.is_null() {
            unsafe { drop(Box::from_raw(self._prop_raw)) };
            self._prop_raw = std::ptr::null_mut();
        }
    }
}

// Safety: CaDiCaL solver is single-threaded, but we only use it from one thread
unsafe impl Send for Solver {}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn basic_sat() {
        let mut s = Solver::new();
        // x1 ∨ x2
        s.add_clause(&[1, 2]);
        // ¬x1 ∨ x2
        s.add_clause(&[-1, 2]);
        assert_eq!(s.solve(), SolveResult::Sat);
        // x2 must be true
        assert!(s.val(2) > 0);
    }

    #[test]
    fn basic_unsat() {
        let mut s = Solver::new();
        s.add_clause(&[1]);
        s.add_clause(&[-1]);
        assert_eq!(s.solve(), SolveResult::Unsat);
    }

    #[test]
    fn proof_trace() {
        let mut s = Solver::new();
        let proof_path = std::path::Path::new("/tmp/test_cadical_ffi.drat");
        s.trace_proof(proof_path);
        s.add_clause(&[1]);
        s.add_clause(&[-1]);
        assert_eq!(s.solve(), SolveResult::Unsat);
        s.close_proof();
        assert!(proof_path.exists());
        let _ = std::fs::remove_file(proof_path);
    }
}
