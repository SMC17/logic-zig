"""Exercise public CLI trust failures with deliberately unusable external tools.

These fixtures test refusal, not independent correctness. Real checkers remain
required by the separate trust-report and DRAT verification CI steps.
"""
from pathlib import Path
import json
import os
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]
LOGIC = ROOT / 'zig-out/bin/logic-zig'
SAT = ROOT / 'zig-out/bin/logic-sat'
CERT = ROOT / 'zig-out/bin/logic-cert'
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
    expect([CERT, 'check-drat', CNF], 1, 'external_drat=unavailable',
           cwd=cwd, env=env)
    expect([LOGIC, 'sat', '--file', CNF, '--check-drat'], 1,
           'external_drat=unavailable', cwd=cwd, env=env)
    expect([LOGIC, 'sat', '(a & !a)', '--check-drat'], 2,
           '--check-drat requires --file', cwd=cwd, env=env)
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
    # Exercise the public process boundary, not just the output parser in isolation.
    for number, (message, code) in enumerate([
        ('s NOT VERIFIED', 0), ('s NOT VERIFIED', 1),
        ('c VERIFIED derivation', 0), ('s VERIFIED later', 0),
        ('s VERIFIED', 1), ('s VERIFIED\ns NOT VERIFIED', 0),
    ]):
        tool = cwd / f'misleading-checker-{number}'
        tool.write_text("#!/bin/sh\ncat <<'CHECKER_OUTPUT'\n" + message
                        + f'\nCHECKER_OUTPUT\nexit {code}\n')
        tool.chmod(0o700)
        env['LOGIC_ZIG_DRAT_TRIM'] = str(tool)
        expect([SAT, 'check-drat', CNF], 1, 'external_drat=failed',
               cwd=cwd, env=env)
        expect([LOGIC, 'sat', '--file', CNF, '--check-drat'], 1,
               'external_drat=failed', cwd=cwd, env=env)
    # The intentionally inconclusive solver cannot produce a successful report.
    report = subprocess.run([LOGIC, 'trust-report', '--json'], cwd=cwd,
                            env=env, capture_output=True, text=True, timeout=300)
    evidence = json.loads(report.stdout)
    assert report.returncode == 1, (report.returncode, report.stdout, report.stderr)
    assert evidence['schema_version'] == 1
    assert evidence['status'] == 'TRUST_FAIL' and evidence['passed'] is False
    assert evidence['checks']['drat']['failed'] > 0
    assert evidence['checks']['cadical']['mismatches'] > 0
    expect([LOGIC, 'trust-report', '--jsno'], 2,
           'trust-report accepts only --json', cwd=cwd, env=env)
    # A receipt must fail if the checker is missing or merely parrots success.
    # In particular, accepting the original proof is insufficient: changed input
    # must also be rejected by the same checker.
    missing = cwd / 'absent-checker'
    parrot = cwd / 'parrot-checker'
    parrot.write_text("#!/bin/sh\nprintf 's VERIFIED\\n'\nexit 0\n")
    parrot.chmod(0o700)
    for index, checker in enumerate((missing, parrot)):
        destination = cwd / f'failed-policy-{index}'
        demo = subprocess.run([sys.executable, ROOT / 'tools/policy_demo.py',
                               '--checker', checker, '--out', destination],
                              env=env, capture_output=True, text=True, timeout=30)
        receipt = json.loads((destination / 'receipt.json').read_text())
        assert demo.returncode == 1 and receipt['status'] == 'FAIL', demo.stdout
        if checker == parrot:
            assert receipt['steps'][-1]['name'] == 'reject-changed-input'
            assert receipt['steps'][-1]['passed'] is False
print('CLI gates reject missing, negative, conflicting, failed, and inconclusive evidence; JSON reports refusal.')
