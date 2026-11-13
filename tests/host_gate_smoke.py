"""Exercise public CLI trust failures with deliberately unusable external tools.

These fixtures test refusal, not independent correctness. Real checkers remain
required by the separate trust-report and DRAT verification CI steps.
"""
from pathlib import Path
import os
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
LOGIC = ROOT / 'zig-out/bin/logic-zig'
SAT = ROOT / 'zig-out/bin/logic-sat'
CNF = ROOT / 'corpus/bench/sat/simple_unsat.cnf'


def expect(command, status, marker, *, cwd, env):
    result = subprocess.run(command, cwd=cwd, env=env, text=True,
                            capture_output=True, timeout=30)
    output = result.stdout + result.stderr
    if result.returncode != status or marker not in output:
        raise AssertionError((command, result.returncode, output))


with tempfile.TemporaryDirectory(prefix='logic-host-gates-') as directory:
    cwd = Path(directory)
    env = os.environ.copy()
    env.pop('LOGIC_ZIG_DRAT_TRIM', None)
    expect([SAT, 'check-drat', CNF], 1, 'external_drat=unavailable',
           cwd=cwd, env=env)
    for code in (0, 1):
        tool = cwd / f'not-a-checker-{code}'
        tool.write_text(f'#!/bin/sh\nexit {code}\n')
        tool.chmod(0o700)
        env['LOGIC_ZIG_DRAT_TRIM'] = str(tool)
        expect([SAT, 'check-drat', CNF], 1, 'external_drat=failed',
               cwd=cwd, env=env)
        env['LOGIC_ZIG_EXTERNAL_SOLVER'] = str(tool)
        expect([LOGIC, 'diff-external', '--iters', '1'], 1,
               'EXTERNAL_DIFF_FAIL', cwd=cwd, env=env)
print('CLI gates reject missing, failed, and inconclusive independent checks.')
