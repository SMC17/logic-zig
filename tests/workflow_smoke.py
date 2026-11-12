"""Check public workflow errors, examples, saved certificates and receipt integrity."""
import copy
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]
AGENT = ROOT / 'zig-out/bin/logic-agent'
CERT = ROOT / 'zig-out/bin/logic-cert'


def run(argv, status, cwd):
    result = subprocess.run([str(arg) for arg in argv], cwd=cwd, text=True,
                            capture_output=True, timeout=180)
    if result.returncode != status:
        raise AssertionError((argv, result.returncode, result.stdout, result.stderr))
    return result


with tempfile.TemporaryDirectory(prefix='logic-workflows-') as directory:
    cwd = Path(directory)
    base = {'schema_version': 1, 'variables': ['a'], 'clauses': [],
            'queries': [{'id': 'q', 'assumptions': ['a']}]}
    cases = []
    for field, value in [('schema_version', 2), ('variables', ['a', 'a']),
                         ('clauses', [['missing']]), ('queries', [])]:
        invalid = copy.deepcopy(base)
        invalid[field] = value
        cases.append(invalid)
    misspelled = copy.deepcopy(base)
    misspelled['queries'][0]['assumptons'] = []
    cases.append(misspelled)
    for number, payload in enumerate(cases):
        path = cwd / f'invalid-{number}.json'
        path.write_text(json.dumps(payload))
        error = json.loads(run([AGENT, 'run', path], 2, cwd).stdout)
        assert error['status'] == 'WORKFLOW_ERROR' and error['error_code']
    malformed = cwd / 'malformed.json'
    malformed.write_text('{')
    run([AGENT, 'run', malformed], 2, cwd)
    run([AGENT, 'run'], 2, cwd)
    run([AGENT, 'run', malformed, 'extra'], 2, cwd)

    gate = [sys.executable, ROOT / 'examples/deployment_gate.py']
    for flags, status, decision in [
        ([], 1, 'DENY'),
        (['--approved', '--tests-passed', '--rollback-ready'], 0, 'ALLOW'),
        (['--approved', '--tests-passed', '--rollback-ready', '--max-conflicts', '0'], 3, 'UNRESOLVED'),
        (['--logic-agent', cwd / 'missing-agent'], 3, 'UNRESOLVED'),
    ]:
        assert json.loads(run(gate + flags, status, cwd).stdout)['decision'] == decision
    malformed_agent = cwd / 'malformed-agent'
    malformed_agent.write_text("#!/bin/sh\nprintf '[]\\n'\n")
    malformed_agent.chmod(0o700)
    assert json.loads(run(gate + ['--logic-agent', malformed_agent], 3, cwd).stdout)['decision'] == 'UNRESOLVED'

    evidence = cwd / 'evidence'
    outcome = run([sys.executable, ROOT / 'tools/workflow_demo.py', '--out', evidence], 0, cwd)
    assert json.loads(outcome.stdout)['status'] == 'PASS'
    receipt = json.loads((evidence / 'receipt.json').read_text())
    assert receipt['status'] == 'PASS' and len(receipt['steps']) == 7
    assert all(step['passed'] for step in receipt['steps'])
    for line in (evidence / 'SHA256SUMS').read_text().splitlines():
        digest, name = line.split('  ', 1)
        assert hashlib.sha256((evidence / name).read_bytes()).hexdigest() == digest

    # Requesting external checking must not silently downgrade to local success.
    external = cwd / 'missing-external'
    failed = run([sys.executable, ROOT / 'tools/workflow_demo.py', '--out', external,
                  '--aigtoaig', cwd / 'missing-aigtoaig', '--abc', cwd / 'missing-abc'], 1, cwd)
    assert json.loads(failed.stdout)['status'] == 'FAIL'
    silent = cwd / 'silent-tool'
    silent.write_text('#!/bin/sh\nexit 0\n')
    silent.chmod(0o700)
    inconclusive = cwd / 'inconclusive-external'
    failed = run([sys.executable, ROOT / 'tools/workflow_demo.py', '--out', inconclusive,
                  '--aigtoaig', silent, '--abc', silent], 1, cwd)
    assert json.loads(failed.stdout)['status'] == 'FAIL'
    external_receipt = json.loads((inconclusive / 'receipt.json').read_text())
    assert external_receipt['steps'][-1]['name'] == 'external-safe'
    assert external_receipt['steps'][-1]['passed'] is False

    certificate = evidence / 'protocol/safe.invariant.txt'
    changed = cwd / 'wrong-property.txt'
    text = certificate.read_text()
    changed.write_text('\n'.join('bad=999999' if line.startswith('bad=') else line
                                for line in text.splitlines()) + '\n')
    refused = json.loads(run([CERT, 'verify-invariant', evidence / 'protocol/safe.aag', changed], 1, cwd).stdout)
    assert refused['verified'] is False and refused['property_matches'] is False
    changed.write_text(text + '0\n')
    run([CERT, 'verify-invariant', evidence / 'protocol/safe.aag', changed], 1, cwd)
print('WORKFLOWS_OK: 13 queries, independent Boolean checks, temporal trace, saved certificate replay and malformed-input refusal.')
