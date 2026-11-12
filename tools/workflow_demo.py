#!/usr/bin/env python3
"""Run the worked reasoning examples and retain checked outputs and receipts."""
import argparse
import datetime as dt
import hashlib
import itertools
import json
from pathlib import Path
import platform
import re
import shutil
import subprocess

ROOT = Path(__file__).resolve().parents[1]
EXPECTED = {
    'deployment': ['unsat', 'sat', 'unsat', 'sat'],
    'configuration': ['unsat', 'unsat', 'sat', 'unsat'],
    'scheduling': ['sat', 'unsat', 'sat', 'unsat'],
    'budget-exhausted': ['unknown'],
}


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def literal(text, model):
    return not model[text[1:]] if text.startswith('!') else model[text]


def satisfies(workflow, assumptions, model):
    return all(any(literal(value, model) for value in clause)
               for clause in workflow['clauses']) and all(
                   literal(value, model) for value in assumptions)


def possible(workflow, assumptions):
    # This oracle enumerates only the committed small examples, not arbitrary
    # large user workloads. It shares no SAT-solving implementation with Zig.
    return any(satisfies(workflow, assumptions, dict(zip(workflow['variables'], bits)))
               for bits in itertools.product((False, True), repeat=len(workflow['variables'])))


def validate(workflow, report, expected):
    if report['schema_version'] != 1 or len(report['results']) != len(workflow['queries']):
        raise ValueError('invalid workflow report envelope')
    for query, answer, status in zip(workflow['queries'], report['results'], expected):
        if answer['id'] != query['id'] or answer['status'] != status:
            raise ValueError('unexpected answer to ' + query['id'])
        assumptions = query.get('assumptions', [])
        if status == 'sat':
            model = {item['variable']: item['value'] for item in answer['model']}
            if (set(model) != set(workflow['variables']) or
                    not all(type(value) is bool for value in model.values()) or
                    not satisfies(workflow, assumptions, model) or not answer['model_verified']):
                raise ValueError('invalid model for ' + query['id'])
        elif status == 'unsat':
            core = answer['core']
            if (possible(workflow, assumptions) or not set(core).issubset(assumptions)
                    or possible(workflow, core) or not answer['core_verified']
                    or not answer['core_deletion_minimal']):
                raise ValueError('invalid conflict core for ' + query['id'])
            if not all(possible(workflow, core[:i] + core[i+1:]) for i in range(len(core))):
                raise ValueError('core is not deletion-minimal for ' + query['id'])
        elif answer['model'] is not None or answer['core'] is not None:
            raise ValueError('unknown query fabricated evidence')


def check_protocol_model(path, expect_safe, trace=None):
    """Exhaustively explore the actual saved classic ASCII two-latch model."""
    lines = iter(path.read_text().splitlines())
    header = next(lines).split()
    if header[0] != 'aag' or len(header) != 6:
        raise ValueError('protocol fixture must export classic ASCII AIGER')
    maximum, inputs, latches, outputs, gates = map(int, header[1:])
    if (inputs, latches, outputs) != (2, 2, 1):
        raise ValueError('oracle expects the worked two-input, two-state-bit fixture')
    input_literals = [int(next(lines)) for _ in range(inputs)]
    latch_rows = [list(map(int, next(lines).split())) for _ in range(latches)]
    if any(len(row) != 3 or row[2] not in (0, 1) for row in latch_rows):
        raise ValueError('protocol latches need explicit current, next and Boolean init')
    output_literals = [int(next(lines)) for _ in range(outputs)]
    and_rows = [list(map(int, next(lines).split())) for _ in range(gates)]
    initial = tuple(bool(row[2]) for row in latch_rows)

    def evaluate(state, stimulus):
        values = {0: False}
        values.update((dimension // 2, bit) for dimension, bit in zip(input_literals, stimulus))
        values.update((row[0] // 2, bit) for row, bit in zip(latch_rows, state))

        def bit(dimension):
            if not 0 <= dimension <= maximum * 2 + 1:
                raise ValueError('literal outside the saved model')
            return values[dimension // 2] != bool(dimension & 1)

        for lhs, left, right in and_rows:
            values[lhs // 2] = bit(left) and bit(right)
        return any(bit(dimension) for dimension in output_literals), tuple(
            bit(row[1]) for row in latch_rows)

    reached, pending, violation = {initial}, [initial], False
    while pending:
        state = pending.pop()
        for stimulus in itertools.product((False, True), repeat=inputs):
            bad, following = evaluate(state, stimulus)
            violation = violation or bad
            if following not in reached:
                reached.add(following)
                pending.append(following)
    if violation == expect_safe:
        raise ValueError('saved model disagrees with the exhaustive reachability oracle')
    if trace:
        if (trace[0]['approved'], trace[0]['deployed']) != initial:
            raise ValueError('trace has the wrong saved-model initial state')
        for i, frame in enumerate(trace):
            bad, following = evaluate((frame['approved'], frame['deployed']),
                                      (frame['approve_request'], frame['deploy_request']))
            if bad != frame['bad'] or (i+1 < len(trace) and following != (
                    trace[i+1]['approved'], trace[i+1]['deployed'])):
                raise ValueError('trace fails replay against the saved AIGER model')
    return {'reachable_states': len(reached), 'bad_reachable': violation}


def run_demo(output, aigtoaig=None, abc=None):
    output = output.resolve()
    if output == ROOT or ROOT in output.parents:
        raise ValueError('choose an output directory outside the repository')
    output.mkdir(parents=True, exist_ok=False)
    receipt = {
        'schema_version': 1, 'status': 'FAIL',
        'measured_at': dt.datetime.now(dt.timezone.utc).isoformat(),
        'platform': {'system': platform.system(), 'machine': platform.machine()},
        'source_commit': None, 'source_dirty': None,
        'scope': 'small encoded examples; exhaustive Boolean oracle, internal certificate checking and transition replay',
        'steps': [],
    }

    def command(name, argv, expected_exit):
        result = subprocess.run([str(arg) for arg in argv], cwd=output,
                                capture_output=True, text=True, timeout=120)
        stdout = result.stdout.replace(str(output), '{evidence}').replace(str(ROOT), '{source}')
        stderr = result.stderr.replace(str(output), '{evidence}').replace(str(ROOT), '{source}')
        (output / (name + '.json')).write_text(stdout)
        (output / (name + '.log')).write_text(stderr)
        receipt['steps'].append({'name': name, 'exit': result.returncode,
                                 'passed': result.returncode == expected_exit})
        if result.returncode != expected_exit:
            raise ValueError('unexpected exit at ' + name)
        return json.loads(stdout)

    try:
        if (ROOT / '.git').exists():
            receipt['source_commit'] = subprocess.check_output(
                ['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip()
            receipt['source_dirty'] = bool(subprocess.check_output(
                ['git', 'status', '--porcelain'], cwd=ROOT, text=True).strip())
        binaries = {name: ROOT / 'zig-out/bin' / name for name in ('logic-agent', 'logic-cert', 'protocol-demo')}
        receipt['binary_sha256'] = {name: sha256(path) for name, path in binaries.items()}
        receipt['runner_sha256'] = sha256(Path(__file__))
        for name, expected in EXPECTED.items():
            fixture = output / (name + '-input.json')
            shutil.copyfile(ROOT / 'examples/workflows' / (name + '.json'), fixture)
            workflow = json.loads(fixture.read_text())
            report = command(name, [binaries['logic-agent'], 'run', fixture], 1 if 'unknown' in expected else 0)
            if report['input_sha256'] != sha256(fixture):
                raise ValueError('workflow report is bound to a different input')
            if report['complete'] != ('unknown' not in expected):
                raise ValueError('incomplete workflow reported success')
            if report['status'] != ('WORKFLOW_INCOMPLETE' if 'unknown' in expected else 'WORKFLOW_OK'):
                raise ValueError('workflow status disagrees with its completion evidence')
            validate(workflow, report, expected)
            receipt['steps'][-1]['oracle_verified'] = True

        protocol = command('release-protocol', [binaries['protocol-demo'], '--out', output / 'protocol'], 0)
        if (protocol['status'] != 'PROTOCOL_DEMO_OK' or not protocol['safe']['invariant_verified']
                or not protocol['unsafe']['trace_verified'] or not protocol['changed_model_rejected']
                or not protocol['empty_invariant_rejected']):
            raise ValueError('release protocol evidence is incomplete')
        frames = protocol['unsafe']['trace']
        if not frames or frames[0]['approved'] or frames[0]['deployed'] or not frames[-1]['bad']:
            raise ValueError('invalid counterexample endpoints')
        for index, frame in enumerate(frames):
            if frame['step'] != index or frame['bad'] != (frame['deployed'] and not frame['approved']):
                raise ValueError('counterexample property does not replay')
            if index:
                previous = frames[index-1]
                if (frame['approved'] != (previous['approved'] or previous['approve_request'])
                        or frame['deployed'] != previous['deploy_request']):
                    raise ValueError('counterexample transition does not replay')
        receipt['steps'][-1]['oracle_verified'] = True
        receipt['model_oracle'] = {
            'safe': check_protocol_model(output / 'protocol/safe.aag', True),
            'unsafe': check_protocol_model(output / 'protocol/unsafe.aag', False, frames),
        }
        # Replay the persisted certificate in another process against both files.
        for name, expected_exit in (('safe', 0), ('unsafe', 1)):
            report = command('replay-' + name, [binaries['logic-cert'], 'verify-invariant',
                             output / 'protocol' / (name + '.aag'),
                             output / 'protocol/safe.invariant.txt'], expected_exit)
            if report['verified'] != (name == 'safe') or not report['property_matches']:
                raise ValueError('certificate replay did not check the same property')
        if aigtoaig is not None and abc is not None:
            receipt['external_binary_sha256'] = {'aigtoaig': sha256(aigtoaig), 'abc': sha256(abc)}
            receipt['external_results'] = {}
            for name in ('safe', 'unsafe'):
                converted = subprocess.run([str(aigtoaig), name + '.aag', name + '.aig'],
                                           cwd=output / 'protocol', capture_output=True, text=True, timeout=60)
                (output / ('aiger-' + name + '.log')).write_text(converted.stdout + converted.stderr)
                if converted.returncode != 0:
                    raise ValueError('upstream AIGER reader refused ' + name)
                # Only fixed artifact basenames occur in ABC's command language;
                # user-provided paths remain subprocess arguments or the cwd.
                baseline = subprocess.run([str(abc), '-c', 'read_aiger ' + name + '.aig; pdr'],
                                          cwd=output / 'protocol', capture_output=True, text=True, timeout=120)
                log = baseline.stdout + baseline.stderr
                (output / ('abc-' + name + '.log')).write_text(log)
                proved = 'Property proved.' in log
                violated = re.search(r'Output 0 .* was asserted in frame [0-9]+', log) is not None
                matches = baseline.returncode == 0 and (proved and not violated if name == 'safe' else violated and not proved)
                receipt['steps'].append({'name': 'external-' + name, 'exit': baseline.returncode, 'passed': matches})
                if not matches:
                    raise ValueError('ABC did not establish the expected result for ' + name)
                receipt['external_results'][name] = 'proved' if proved else 'violated'
        receipt['status'] = 'PASS'
    except (OSError, ValueError, KeyError, TypeError, subprocess.SubprocessError) as error:
        receipt['error'] = str(error).replace(str(output), '{evidence}').replace(str(ROOT), '{source}')
    finally:
        receipt['files'] = {p.relative_to(output).as_posix(): sha256(p)
                            for p in sorted(output.rglob('*')) if p.is_file()}
        (output / 'receipt.json').write_text(json.dumps(receipt, indent=2) + '\n')
        (output / 'SHA256SUMS').write_text(''.join(
            sha256(p) + '  ' + p.relative_to(output).as_posix() + '\n'
            for p in sorted(output.rglob('*')) if p.is_file()))
    return receipt


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--out', type=Path, required=True)
    parser.add_argument('--aigtoaig', type=Path)
    parser.add_argument('--abc', type=Path)
    args = parser.parse_args()
    if bool(args.aigtoaig) != bool(args.abc):
        parser.error('--aigtoaig and --abc must be supplied together')
    try:
        receipt = run_demo(args.out, args.aigtoaig.resolve() if args.aigtoaig else None,
                          args.abc.resolve() if args.abc else None)
    except (OSError, ValueError) as error:
        parser.exit(2, str(error) + '\n')
    print(json.dumps({'status': receipt['status'], 'steps': len(receipt['steps'])}))
    return 0 if receipt['status'] == 'PASS' else 1


if __name__ == '__main__':
    raise SystemExit(main())
