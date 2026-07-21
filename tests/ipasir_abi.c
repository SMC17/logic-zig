#include "ipasir.h"
#include <assert.h>
#include <stddef.h>

struct callback_state {
    int terminate_calls;
    int learned_calls;
    int last_learned_len;
};

static int terminate_now(void *opaque) {
    struct callback_state *state = opaque;
    state->terminate_calls++;
    return 1;
}

static void record_learned(void *opaque, int *clause) {
    struct callback_state *state = opaque;
    int len = 0;
    while (clause[len] != 0) len++;
    state->learned_calls++;
    state->last_learned_len = len;
}

int main(void) {
    assert(ipasir_signature() != NULL);

    void *empty = ipasir_init();
    assert(empty != NULL);
    ipasir_add(empty, 0);
    assert(ipasir_solve(empty) == 20);
    ipasir_release(empty);

    struct callback_state terminated = {0};
    void *interruptible = ipasir_init();
    assert(interruptible != NULL);
    ipasir_add(interruptible, 1);
    ipasir_add(interruptible, 0);
    ipasir_set_terminate(interruptible, &terminated, terminate_now);
    assert(ipasir_solve(interruptible) == 0);
    assert(terminated.terminate_calls > 0);
    ipasir_release(interruptible);

    struct callback_state learned = {0};
    void *solver = ipasir_init();
    assert(solver != NULL);
    const int clauses[4][2] = {{1, 2}, {1, -2}, {-1, 2}, {-1, -2}};
    for (int i = 0; i < 4; i++) {
        ipasir_add(solver, clauses[i][0]);
        ipasir_add(solver, clauses[i][1]);
        ipasir_add(solver, 0);
    }
    ipasir_set_learn(solver, &learned, 8, record_learned);
    assert(ipasir_solve(solver) == 20);
    assert(learned.learned_calls > 0);
    assert(learned.last_learned_len > 0 && learned.last_learned_len <= 8);
    ipasir_release(solver);
    return 0;
}
