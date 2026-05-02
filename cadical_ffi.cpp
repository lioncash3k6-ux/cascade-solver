/* C++ implementation of the C wrapper for CaDiCaL IPASIR-UP.
 * Bridges FFIPropagatorVtable (C function pointers) to
 * CaDiCaL's ExternalPropagator (C++ virtual methods). */

#include "cadical_ffi.h"
#include "cadical.hpp"
#include <vector>
#include <cstring>
#include <chrono>

/* Bridge class: dispatches C++ virtual calls to C function pointers */
class FFIPropagator : public CaDiCaL::ExternalPropagator {
    FFIPropagatorVtable *vt;

public:
    FFIPropagator(FFIPropagatorVtable *vt) : vt(vt) {
        this->are_reasons_forgettable = (vt->reasons_forgettable != 0);
    }

    void notify_assignment(const std::vector<int> &lits) override {
        if (vt->notify_assignment)
            vt->notify_assignment(vt->state, lits.data(), lits.size());
    }

    void notify_new_decision_level() override {
        if (vt->notify_new_decision_level)
            vt->notify_new_decision_level(vt->state);
    }

    void notify_backtrack(size_t new_level) override {
        if (vt->notify_backtrack)
            vt->notify_backtrack(vt->state, new_level);
    }

    int cb_propagate() override {
        if (vt->cb_propagate)
            return vt->cb_propagate(vt->state);
        return 0;
    }

    int cb_add_reason_clause_lit(int propagated_lit) override {
        if (vt->cb_add_reason_clause_lit)
            return vt->cb_add_reason_clause_lit(vt->state, propagated_lit);
        return 0;
    }

    bool cb_check_found_model(const std::vector<int> &model) override {
        if (vt->cb_check_found_model)
            return vt->cb_check_found_model(vt->state, model.data(), model.size()) != 0;
        return true;
    }

    bool cb_has_external_clause(bool &is_forgettable) override {
        if (vt->cb_has_external_clause) {
            int forgettable = 0;
            int has = vt->cb_has_external_clause(vt->state, &forgettable);
            is_forgettable = (forgettable != 0);
            return has != 0;
        }
        return false;
    }

    int cb_add_external_clause_lit() override {
        if (vt->cb_add_external_clause_lit)
            return vt->cb_add_external_clause_lit(vt->state);
        return 0;
    }

    int cb_decide() override {
        if (vt->cb_decide)
            return vt->cb_decide(vt->state);
        return 0;
    }
};

/* Bridge class: dispatches learned-clause notifications to Rust */
class FFILearner : public CaDiCaL::Learner {
    FFIPropagatorVtable *vt;

public:
    FFILearner(FFIPropagatorVtable *vt) : vt(vt) {}

    bool learning(int size) override {
        if (vt->cb_learning)
            return vt->cb_learning(vt->state, size) != 0;
        return false;
    }

    void learn(int lit) override {
        if (vt->cb_learn)
            vt->cb_learn(vt->state, lit);
    }
};

/* Wall-clock terminator: fires once the deadline is passed. */
class TimeTerminator : public CaDiCaL::Terminator {
    std::chrono::steady_clock::time_point deadline;
public:
    TimeTerminator(double secs) {
        auto ns = std::chrono::duration_cast<std::chrono::nanoseconds>(
            std::chrono::duration<double>(secs));
        deadline = std::chrono::steady_clock::now() + ns;
    }
    bool terminate() override {
        return std::chrono::steady_clock::now() >= deadline;
    }
};

/* Opaque handle wraps solver + propagator + learner + optional terminator */
struct CaDiCaLSolver {
    CaDiCaL::Solver *solver;
    FFIPropagator *propagator;
    FFILearner *learner;
    TimeTerminator *terminator;
};

extern "C" {

CaDiCaLSolver *cadical_ffi_new(void) {
    auto *s = new CaDiCaLSolver;
    s->solver = new CaDiCaL::Solver;
    s->propagator = nullptr;
    s->learner = nullptr;
    s->terminator = nullptr;
    return s;
}

void cadical_ffi_delete(CaDiCaLSolver *s) {
    if (!s) return;
    if (s->terminator) {
        s->solver->disconnect_terminator();
        delete s->terminator;
    }
    if (s->learner) {
        s->solver->disconnect_learner();
        delete s->learner;
    }
    if (s->propagator) {
        s->solver->disconnect_external_propagator();
        delete s->propagator;
    }
    delete s->solver;
    delete s;
}

void cadical_ffi_add(CaDiCaLSolver *s, int lit) {
    s->solver->add(lit);
}

int cadical_ffi_solve(CaDiCaLSolver *s) {
    return s->solver->solve();
}

int cadical_ffi_val(CaDiCaLSolver *s, int lit) {
    return s->solver->val(lit);
}

void cadical_ffi_set(CaDiCaLSolver *s, const char *name, int val) {
    s->solver->set(name, val);
}

void cadical_ffi_connect_propagator(CaDiCaLSolver *s, FFIPropagatorVtable *vt) {
    if (s->propagator) {
        s->solver->disconnect_external_propagator();
        delete s->propagator;
    }
    s->propagator = new FFIPropagator(vt);
    s->solver->connect_external_propagator(s->propagator);

    /* Also connect a learner if the vtable has cb_learning set */
    if (vt->cb_learning) {
        if (s->learner) {
            s->solver->disconnect_learner();
            delete s->learner;
        }
        s->learner = new FFILearner(vt);
        s->solver->connect_learner(s->learner);
    }
}

void cadical_ffi_disconnect_propagator(CaDiCaLSolver *s) {
    if (s->propagator) {
        s->solver->disconnect_external_propagator();
        delete s->propagator;
        s->propagator = nullptr;
    }
}

void cadical_ffi_add_observed_var(CaDiCaLSolver *s, int var) {
    s->solver->add_observed_var(var);
}

void cadical_ffi_remove_observed_var(CaDiCaLSolver *s, int var) {
    s->solver->remove_observed_var(var);
}

void cadical_ffi_reset_observed_vars(CaDiCaLSolver *s) {
    s->solver->reset_observed_vars();
}

int cadical_ffi_trace_proof(CaDiCaLSolver *s, const char *path) {
    return s->solver->trace_proof(path) ? 1 : 0;
}

void cadical_ffi_flush_proof(CaDiCaLSolver *s) {
    s->solver->flush_proof_trace();
}

void cadical_ffi_close_proof(CaDiCaLSolver *s) {
    s->solver->close_proof_trace();
}

int64_t cadical_ffi_conflicts(CaDiCaLSolver *s) {
    return s->solver->get_statistic_value("conflicts");
}

int64_t cadical_ffi_decisions(CaDiCaLSolver *s) {
    return s->solver->get_statistic_value("decisions");
}

int64_t cadical_ffi_propagations(CaDiCaLSolver *s) {
    return s->solver->get_statistic_value("propagations");
}

int cadical_ffi_vars(CaDiCaLSolver *s) {
    return s->solver->vars();
}

void cadical_ffi_connect_timeout(CaDiCaLSolver *s, double secs) {
    if (s->terminator) {
        s->solver->disconnect_terminator();
        delete s->terminator;
    }
    s->terminator = new TimeTerminator(secs);
    s->solver->connect_terminator(s->terminator);
}

void cadical_ffi_disconnect_timeout(CaDiCaLSolver *s) {
    if (s->terminator) {
        s->solver->disconnect_terminator();
        delete s->terminator;
        s->terminator = nullptr;
    }
}

} /* extern "C" */
