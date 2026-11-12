#!/usr/bin/env python3
"""Demonstrate a fail-closed application decision over explicit supplied facts."""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]


def decide(agent, approved, tests_passed, rollback_ready, max_conflicts):
    workflow = json.loads((ROOT / 'examples/workflows/deployment.json').read_text())
    facts = {'deploy': True, 'approved': approved, 'tests_passed': tests_passed,
             'rollback_ready': rollback_ready}
    workflow['queries'] = [{'id': 'proposed_deploy', 'assumptions': [
        name if value else '!' + name for name, value in facts.items()]}]
    workflow['max_conflicts'] = max_conflicts
    encoded = (json.dumps(workflow) + '\n').encode()
    response = {'schema_version': 1, 'decision': 'UNRESOLVED',
                'facts': facts, 'scope': 'local decision example over supplied Boolean facts; no deployment is executed'}
    try:
        with tempfile.TemporaryDirectory(prefix='logic-deploy-request-') as directory:
            path = Path(directory) / 'request.json'
            path.write_bytes(encoded)
            result = subprocess.run([str(agent), 'run', str(path)], capture_output=True,
                                    text=True, timeout=60)
        report = json.loads(result.stdout)
        if not isinstance(report, dict):
            response['reason'] = 'Malformed workflow report'
            return response
        if (result.returncode != 0 or report.get('schema_version') != 1
                or report.get('status') != 'WORKFLOW_OK' or report.get('complete') is not True
                or report.get('input_sha256') != hashlib.sha256(encoded).hexdigest()
                or len(report.get('results', [])) != 1):
            response['reason'] = 'No completed, input-bound answer'
            return response
        answer = report['results'][0]
        if answer['id'] != 'proposed_deploy':
            response['reason'] = 'Answer is for a different request'
            return response
        response['answer'] = answer
        if answer['status'] == 'unsat' and answer['core_verified'] is True:
            response['decision'] = 'DENY'
        elif answer['status'] == 'sat' and answer['model_verified'] is True:
            model = {item['variable']: item['value'] for item in answer['model']}
            # Bind the reported assignment to every supplied observed fact. A
            # solver-chosen approval value cannot substitute for a supplied fact.
            if (len(answer['model']) == len(facts) and model == facts
                    and all(type(value) is bool for value in model.values())
                    and all(any(not model[text[1:]] if text.startswith('!') else model[text]
                                for text in clause) for clause in workflow['clauses'])):
                response['decision'] = 'ALLOW'
    except (OSError, ValueError, KeyError, TypeError, subprocess.SubprocessError) as error:
        response['reason'] = type(error).__name__
    return response


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--approved', action='store_true')
    parser.add_argument('--tests-passed', action='store_true')
    parser.add_argument('--rollback-ready', action='store_true')
    parser.add_argument('--max-conflicts', type=int, default=200_000)
    parser.add_argument('--logic-agent', type=Path, default=ROOT / 'zig-out/bin/logic-agent')
    args = parser.parse_args()
    if not 0 <= args.max_conflicts <= 2**64 - 1:
        parser.error('--max-conflicts must be an unsigned 64-bit integer')
    decision = decide(args.logic_agent, args.approved, args.tests_passed,
                      args.rollback_ready, args.max_conflicts)
    print(json.dumps(decision, indent=2))
    return {'ALLOW': 0, 'DENY': 1, 'UNRESOLVED': 3}[decision['decision']]


if __name__ == '__main__':
    raise SystemExit(main())
