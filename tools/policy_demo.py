#!/usr/bin/env python3
"""Produce a replayable policy proof and a receipt using real local binaries."""
import argparse
import datetime as dt
import hashlib
import json
import os
from pathlib import Path
import platform
import shutil
import subprocess

ROOT = Path(__file__).resolve().parents[1]


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def verified(result):
    statuses = [line.strip() for line in (result.stdout + '\n' + result.stderr).splitlines()
                if line.strip().startswith('s ')]
    return result.returncode == 0 and bool(statuses) and all(
        line == 's VERIFIED' for line in statuses)


def run_demo(output, checker):
    output = output.resolve()
    if output == ROOT or ROOT in output.parents:
        raise ValueError('choose an output directory outside the repository')
    output.mkdir(parents=True, exist_ok=False)
    receipt = {
        'schema_version': 1, 'status': 'FAIL',
        'measured_at': dt.datetime.now(dt.timezone.utc).isoformat(),
        'platform': {'system': platform.system(), 'machine': platform.machine()},
        'scope': 'two explicit propositional encodings; no action authorization or general agent-safety claim',
        'source_commit': None, 'source_dirty': None,
        'steps': [],
    }
    logic = ROOT / 'zig-out/bin/logic-zig'
    sat = ROOT / 'zig-out/bin/logic-sat'

    def run(name, argv, accept):
        result = subprocess.run([str(arg) for arg in argv], cwd=output,
                                capture_output=True, text=True, timeout=60)
        log = (result.stdout + result.stderr).replace(str(output), '{evidence}').replace(
            str(ROOT), '{source}').replace(str(checker), '{checker}')
        filename = name + '.log'
        (output / filename).write_text(log)
        passed = bool(accept(result))
        receipt['steps'].append({'name': name, 'exit': result.returncode,
                                 'passed': passed, 'log': filename})
        if not passed:
            raise ValueError('unexpected result at ' + name + '; read ' + filename)
        return result

    try:
        # Source packs intentionally omit Git metadata. Keep its absence explicit
        # rather than inventing a revision or preventing proof replay from a pack.
        if (ROOT / '.git').exists():
            receipt['source_commit'] = subprocess.check_output(
                ['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip()
            receipt['source_dirty'] = bool(subprocess.check_output(
                ['git', 'status', '--porcelain'], cwd=ROOT, text=True).strip())
        receipt['tools'] = {name: {'sha256': sha256(path)} for name, path in (
            ('logic-zig', logic), ('logic-sat', sat), ('drat-trim', checker))}
        receipt['runner_sha256'] = sha256(Path(__file__))
        for name in ('blocked.cnf', 'weakened.cnf'):
            shutil.copyfile(ROOT / 'examples/policy' / name, output / name)

        # Export the artifact without trusting its self-reported verification text.
        run('export-proof', [logic, 'sat', '--file', 'blocked.cnf', '--proof',
                             '--dump-proof', 'blocked.drat'],
            lambda r: r.returncode == 0 and any(
                line == 'UNSAT' for line in r.stderr.splitlines()))
        run('independent-proof', [checker, 'blocked.cnf', 'blocked.drat'], verified)
        run('weakened-policy', [sat, 'solve', 'weakened.cnf'],
            lambda r: r.returncode == 10 and 's SATISFIABLE' in r.stderr)
        # The original proof cannot establish UNSAT after the policy is weakened.
        run('reject-changed-input', [checker, 'weakened.cnf', 'blocked.drat'],
            lambda r: r.returncode != 0 and 's NOT VERIFIED' in r.stdout.splitlines())
        receipt['status'] = 'PASS'
    except (OSError, ValueError, subprocess.SubprocessError) as error:
        message = str(error).replace(str(output), '{evidence}').replace(
            str(ROOT), '{source}').replace(str(checker), '{checker}')
        receipt['error'] = message
    finally:
        # These hashes bind the receipt to the exact inputs, proof and recorded logs.
        receipt['files'] = {p.name: sha256(p) for p in sorted(output.iterdir()) if p.is_file()}
        (output / 'receipt.json').write_text(json.dumps(receipt, indent=2) + '\n')
        files = sorted(p for p in output.iterdir() if p.is_file())
        (output / 'SHA256SUMS').write_text(''.join(
            sha256(p) + '  ' + p.name + '\n' for p in files))
    return receipt


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--out', required=True, type=Path)
    parser.add_argument('--checker', type=Path, default=Path(os.environ.get(
        'LOGIC_ZIG_DRAT_TRIM', str(ROOT / 'third_party/drat-trim/drat-trim'))))
    args = parser.parse_args()
    try:
        receipt = run_demo(args.out, args.checker.resolve())
    except (OSError, ValueError) as error:
        parser.exit(2, str(error) + '\n')
    print(json.dumps({'status': receipt['status'], 'steps': len(receipt['steps'])}))
    return 0 if receipt['status'] == 'PASS' else 1


if __name__ == '__main__':
    raise SystemExit(main())
