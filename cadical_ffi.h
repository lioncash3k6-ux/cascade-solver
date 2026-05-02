/* C wrapper for CaDiCaL 2.2.1 IPASIR-UP external propagator API.
 * Bridges Rust function pointers to C++ virtual method dispatch. */

#ifndef CADICAL_FFI_H
#define CADICAL_FFI_H

#include <stdint.h>
#include <stddef.h>

#ifdef __cplusplus
extern "C" {
#endif

/* Opaque solver handle */
typedef struct CaDiCaLSolver CaDiCaLSolver;

/* Propagator callbacks — Rust implements these */
typedef void (*ffi_notify_assignment)(void *state, const int *lits, size_t n);
typedef void (*ffi_notify_new_decision_level)(void *state);
typedef void (*ffi_notify_backtrack)(void *state, size_t new_level);
typedef int  (*ffi_cb_propagate)(void *state);
typedef int  (*ffi_cb_add_reason_clause_lit)(void *state, int propagated_lit);
typedef int  (*ffi_cb_check_found_model)(void *state, const int *model, size_t n);
typedef int  (*ffi_cb_has_external_clause)(void *state, int *is_forgettable);
typedef int  (*ffi_cb_add_external_clause_lit)(void *state);
typedef int  (*ffi_cb_decide)(void *state);

/* Propagator vtable — all callbacks + opaque state pointer */
typedef struct {
    void *state;
    ffi_notify_assignment        notify_assignment;
    ffi_notify_new_decision_level notify_new_decision_level;
    ffi_notify_backtrack         notify_backtrack;
    ffi_cb_propagate             cb_propagate;
    ffi_cb_add_reason_clause_lit cb_add_reason_clause_lit;
    ffi_cb_check_found_model     cb_check_found_model;
    ffi_cb_has_external_clause   cb_has_external_clause;
    ffi_cb_add_external_clause_lit cb_add_external_clause_lit;
    ffi_cb_decide                cb_decide;
    int reasons_forgettable;     /* 0 = non-forgettable (proof-safe) */

    /* Learner callback: notified for every CDCL-learned clause.
     * cb_learning(state, size) → 1 if interested, 0 to skip.
     * cb_learn(state, lit) streams lits; 0-terminated. */
    int  (*cb_learning)(void *state, int size);
    void (*cb_learn)(void *state, int lit);
} FFIPropagatorVtable;

/* Solver lifecycle */
CaDiCaLSolver *cadical_ffi_new(void);
void cadical_ffi_delete(CaDiCaLSolver *s);

/* Add clause literal-by-literal, 0-terminated */
void cadical_ffi_add(CaDiCaLSolver *s, int lit);

/* Solve. Returns 10=SAT, 20=UNSAT, 0=UNKNOWN */
int cadical_ffi_solve(CaDiCaLSolver *s);

/* Get value of variable in model. Returns lit or -lit */
int cadical_ffi_val(CaDiCaLSolver *s, int lit);

/* Set option (e.g., "chrono", "0") */
void cadical_ffi_set(CaDiCaLSolver *s, const char *name, int val);

/* Connect external propagator */
void cadical_ffi_connect_propagator(CaDiCaLSolver *s, FFIPropagatorVtable *vt);

/* Disconnect external propagator */
void cadical_ffi_disconnect_propagator(CaDiCaLSolver *s);

/* Add/remove observed variables */
void cadical_ffi_add_observed_var(CaDiCaLSolver *s, int var);
void cadical_ffi_remove_observed_var(CaDiCaLSolver *s, int var);
void cadical_ffi_reset_observed_vars(CaDiCaLSolver *s);

/* Proof tracing — write DRAT proof to file */
int cadical_ffi_trace_proof(CaDiCaLSolver *s, const char *path);
void cadical_ffi_flush_proof(CaDiCaLSolver *s);
void cadical_ffi_close_proof(CaDiCaLSolver *s);

/* Statistics */
int64_t cadical_ffi_conflicts(CaDiCaLSolver *s);
int64_t cadical_ffi_decisions(CaDiCaLSolver *s);
int64_t cadical_ffi_propagations(CaDiCaLSolver *s);

/* Number of variables */
int cadical_ffi_vars(CaDiCaLSolver *s);

/* Wall-clock timeout: connect a Terminator that fires after `secs` seconds.
 * Must be called before cadical_ffi_solve(). Automatically disconnected and
 * freed when the solver is deleted or cadical_ffi_disconnect_timeout is called. */
void cadical_ffi_connect_timeout(CaDiCaLSolver *s, double secs);
void cadical_ffi_disconnect_timeout(CaDiCaLSolver *s);

#ifdef __cplusplus
}
#endif

#endif /* CADICAL_FFI_H */
