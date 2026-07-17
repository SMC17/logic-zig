/**
 * IPASIR — Incremental SAT solver API (logic-zig)
 * Compatible with the standard IPASIR interface used by SAT competitions.
 */
#ifndef IPASIR_H_INCLUDED
#define IPASIR_H_INCLUDED

#ifdef __cplusplus
extern "C" {
#endif

const char * ipasir_signature(void);
void * ipasir_init(void);
void ipasir_release(void * solver);
void ipasir_add(void * solver, int lit_or_zero);
void ipasir_assume(void * solver, int lit);
int ipasir_solve(void * solver);
int ipasir_val(void * solver, int lit);
int ipasir_failed(void * solver, int lit);
void ipasir_set_terminate(void * solver, void * state, int (*terminate)(void * state));
void ipasir_set_learn(void * solver, void * state, int max_length, void (*learn)(void * state, int * clause));

#ifdef __cplusplus
}
#endif
#endif
