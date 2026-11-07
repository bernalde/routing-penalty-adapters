#!/usr/bin/env python3
"""Check a package with the selected Lean toolchain and real bundled kernels."""
from pathlib import Path
import argparse
import datetime
import hashlib
import json
import re
import shutil
import subprocess
import time

ROOT = Path(__file__).resolve().parents[1]


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--evidence-dir', type=Path, required=True)
    args = parser.parse_args()
    out = args.evidence_dir.resolve()
    out.mkdir(parents=True, exist_ok=False)
    for name in ['lake', 'lean', 'bwrap']:
        assert shutil.which(name), 'Missing '+name
    prefix = Path(subprocess.check_output(['lean', '--print-prefix'], cwd=ROOT, text=True).strip())
    config = json.loads((ROOT/'comparator.json').read_text())
    assert 'external_kernels' not in config
    for executable in ['nanoda_bin', 'con-ron']:
        assert (prefix/'bin'/executable).is_file(), executable
    config['external_kernels'] = {'nanoda': [str(prefix/'bin/nanoda_bin')], 'con-ron': [str(prefix/'bin/con-ron')]}
    local = out/'comparator-local.json'
    local.write_text(json.dumps(config, indent=2)+'\n')
    inputs = {}
    for path in ROOT.rglob('*'):
        if not path.is_file() or any(s in path.relative_to(ROOT).parts for s in ['.lake', '.git']):
            continue
        if path.suffix == '.lean' or path.name in ['lean-toolchain', 'lakefile.toml', 'lake-manifest.json', 'comparator.json']:
            inputs[path.relative_to(ROOT).as_posix()] = hashlib.sha256(path.read_bytes()).hexdigest()
    report = {'state': 'RUNNING', 'toolchain': (ROOT/'lean-toolchain').read_text().strip(),
              'lean_version': subprocess.check_output(['lean', '--version'], cwd=ROOT, text=True).strip(),
              'input_sha256': inputs, 'steps': [], 'no_service_submission': True,
              'upstream_cache': 'Matching pinned Mathlib/dependency objects may be reused; package sources build independently.'}
    try:
        commands = [('source-format', ['python3', 'scripts/check-lean-sources.py']),
                    ('build', ['lake', 'build']),
                    ('axioms', ['lake', 'env', 'lean', 'AxiomAudit.lean']),
                    ('comparator', ['lake', 'comparator', '--config', str(local)])]
        for name, argv in commands:
            started = datetime.datetime.now(datetime.timezone.utc).isoformat()
            tick = time.monotonic()
            stdout, stderr = out/(name+'.stdout.txt'), out/(name+'.stderr.txt')
            with stdout.open('xb') as a, stderr.open('xb') as b:
                result = subprocess.run(argv, cwd=ROOT, stdout=a, stderr=b)
            step = {'name': name, 'argv': argv, 'started_utc': started, 'elapsed_seconds': time.monotonic()-tick,
                    'exit_code': result.returncode, 'stdout_sha256': hashlib.sha256(stdout.read_bytes()).hexdigest(),
                    'stderr_sha256': hashlib.sha256(stderr.read_bytes()).hexdigest()}
            report['steps'].append(step)
            if result.returncode:
                raise RuntimeError(name+' failed; retained logs in '+str(out))
            if name == 'axioms':
                rows = re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]", stdout.read_text())
                observed = {}
                for target, values in rows:
                    if target not in config['theorem_names']:
                        continue
                    axioms = sorted(s.strip() for s in values.split(',') if s.strip())
                    assert set(axioms) <= {'propext', 'Classical.choice', 'Quot.sound'}, (target, axioms)
                    observed[target] = axioms
                assert set(observed) == set(config['theorem_names']), observed
                report['solution_axioms'] = observed
        for name, digest in inputs.items():
            assert hashlib.sha256((ROOT/name).read_bytes()).hexdigest() == digest, name
        report['state'] = 'PASS_ACTUAL_BUILD_AXIOMS_SANDBOXED_COMPARATOR_BUNDLED_KERNELS'
    except Exception as error:
        report['state'] = 'FAILED'
        report['error'] = str(error)
        raise
    finally:
        (out/'result.json').write_text(json.dumps(report, indent=2)+'\n')
    print(report['state'])


if __name__ == '__main__':
    main()
