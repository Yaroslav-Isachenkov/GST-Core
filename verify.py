#!/usr/bin/env python3
"""Check release files and saved evidence; optionally rebuild with pinned Mathlib."""
import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
MODULES = [f'GSTStage{i:02d}' for i in range(1, 192) if i != 3]
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}


def require(ok, message):
    if not ok:
        raise RuntimeError(message)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read_json(path):
    return json.loads(path.read_text(encoding='utf-8'))


def axioms(text, expected):
    require(not re.search(r'\b(?:warning|error|sorryAx)\b', text),
            'Log contains warning, error or sorryAx')
    pairs = re.findall(r"'([^']+)'\s+depends on axioms:\s*\[([^\]]*)\]", text, re.S)
    actual = {name: set(a.strip() for a in values.split(',') if a.strip())
              for name, values in pairs}
    expected = {name: set(values) for name, values in expected.items()}
    require(len(pairs) == len(expected) and actual == expected,
            'Axiom inventory differs from the archived inventory')
    require(all(values <= ALLOWED for values in actual.values()), 'Unexpected axiom')
    return {name: sorted(values) for name, values in actual.items()}


def check_release():
    release = read_json(ROOT / 'MANIFEST.json')
    for name, info in release['files'].items():
        path = ROOT / name
        require(path.is_file(), 'Missing release file: ' + name)
        require(sha(path) == info['sha256'] and path.stat().st_size == info['size_bytes'],
                'Release file changed: ' + name)
    original = read_json(ROOT / 'evidence/original_MANIFEST.json')
    closure_path = ROOT / 'evidence/full_core_document_coverage.json'
    require(sha(closure_path) == original['closure_sha256'], 'Coverage hash mismatch')
    closure = read_json(closure_path)
    require({p.name for p in (ROOT / 'src').iterdir()} == {n + '.lean' for n in MODULES},
            'src/ must contain exactly the 190 release source files')
    for module in MODULES:
        number = module.removeprefix('GSTStage')
        old_path = f'stage{number}/{module}.lean'
        require(sha(ROOT / 'src' / (module + '.lean')) == original['files'][old_path]['sha256'],
                'Original source mismatch: ' + module)
    report = read_json(ROOT / 'evidence/rebuild_20261123/report.json')
    require(report['status'] == 'complete', 'Saved rebuild incomplete')
    require([m['module'] for m in report['modules']] == MODULES, 'Saved module list mismatch')
    require(report['lean_version'] == original['lean_version'] and
            report['mathlib_commit'] == original['mathlib_commit'], 'Saved environment mismatch')
    for item in report['modules']:
        module = item['module']
        require(item['passed'] and item['exit_code'] == 0, 'Saved failure: ' + module)
        require(sha(ROOT / 'src' / (module + '.lean')) == item['source_sha256'],
                'Saved source hash mismatch: ' + module)
        log = ROOT / 'evidence/rebuild_20261123/logs' / (module + '.log')
        require(sha(log) == item['log_sha256'], 'Saved log hash mismatch: ' + module)
        actual = axioms(log.read_text(encoding='utf-8'), closure['module_evidence'][module]['axioms'])
        require(actual == {k: sorted(v) for k, v in item['axioms'].items()},
                'Saved report/log mismatch: ' + module)
    print('PASS: release files, 190 original sources and saved rebuild evidence verified.', flush=True)
    return original, closure


def environment(args, original):
    require(args.mathlib is not None, '--mathlib is required for environment checks/rebuilds')
    work = args.mathlib.resolve()
    require(work.is_dir(), 'Mathlib directory does not exist')
    lake_arg = args.lake or shutil.which('lake')
    require(lake_arg is not None, 'Provide --lake /absolute/path/to/lake')
    # Do not resolve the executable symlink: elan proxies use the invoked name.
    lake = Path(os.path.abspath(os.path.expanduser(str(lake_arg))))
    require(lake.is_file(), 'Lake executable not found')
    env = os.environ.copy()
    if args.elan_home:
        env['ELAN_HOME'] = str(args.elan_home.resolve())
    env['PATH'] = str(lake.parent) + os.pathsep + env.get('PATH', '')
    env['GIT_OPTIONAL_LOCKS'] = '0'
    env.pop('LEAN_PATH', None)
    env.pop('LEAN_SRC_PATH', None)

    def capture(command):
        result = subprocess.run(command, cwd=work, env=env, capture_output=True, timeout=120)
        require(result.returncode == 0, result.stdout.decode(errors='replace') +
                result.stderr.decode(errors='replace'))
        return result.stdout

    for name in ('lean-toolchain', 'lake-manifest.json'):
        require(sha(work / name) == original['files']['environment/' + name]['sha256'],
                'Mathlib environment mismatch: ' + name)
    require(capture(['git', 'rev-parse', 'HEAD']).decode().strip() == original['mathlib_commit'],
            'Mathlib commit mismatch')
    require(hashlib.sha256(capture(['git', 'diff', '--binary', 'HEAD'])).hexdigest() ==
            original['files']['environment/mathlib-tracked-changes.patch']['sha256'],
            'Mathlib tracked changes mismatch')
    require(capture([str(lake), 'env', 'lean', '--version']).decode().strip() == original['lean_version'],
            'Lean version mismatch (this release targets the recorded Linux x86_64 toolchain)')
    print('PASS: pinned Lean and Mathlib environment verified.', flush=True)
    return work, lake, env


def rebuild(args, original, closure, work, lake, env):
    stamp = datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%S%fZ')
    run = ROOT / 'verification' / stamp
    build = run / 'build'
    build.mkdir(parents=True, exist_ok=False)
    env['LEAN_PATH'] = str(build)
    report = {'status': 'running', 'started_at_utc': stamp,
              'lean_version': original['lean_version'], 'mathlib_commit': original['mathlib_commit'],
              'verifier_sha256': sha(Path(__file__)), 'modules': []}
    def save():
        temp = run / 'report.json.tmp'
        temp.write_text(json.dumps(report, indent=2) + '\n', encoding='utf-8')
        temp.replace(run / 'report.json')
    save()
    print('New rebuild directory:', run, flush=True)
    try:
        for index, module in enumerate(MODULES, 1):
            source = ROOT / 'src' / (module + '.lean')
            snapshot = build / source.name
            snapshot.write_bytes(source.read_bytes())
            original_hash = original['files'][f'stage{module[8:]}/{module}.lean']['sha256']
            require(sha(snapshot) == original_hash, 'Source changed before compilation: ' + module)
            target = build / (module + '.olean')
            log = run / (module + '.log')
            print(f'[{index}/190] {module} ...', flush=True)
            with log.open('w', encoding='utf-8') as output:
                result = subprocess.run(
                    [str(lake), 'env', 'lean', '--root=' + str(build), '-o', str(target), str(snapshot)],
                    cwd=work, env=env, stdout=output, stderr=subprocess.STDOUT)
            require(result.returncode == 0 and target.is_file(), 'Compilation failed; see ' + str(log))
            actual = axioms(log.read_text(encoding='utf-8'), closure['module_evidence'][module]['axioms'])
            require(sha(source) == original_hash, 'Source changed during compilation: ' + module)
            report['modules'].append({'module': module, 'passed': True, 'exit_code': result.returncode,
                                      'source_sha256': sha(snapshot), 'log_sha256': sha(log),
                                      'olean_sha256': sha(target), 'axioms': actual})
            save()
            print('PASS:', module, flush=True)
        # Recheck all release files after the run, including previously compiled sources.
        check_release()
        report['status'] = 'complete'
        report['finished_at_utc'] = datetime.now(timezone.utc).isoformat()
        save()
    except BaseException as exc:
        report['status'] = 'interrupted' if isinstance(exc, KeyboardInterrupt) else 'failed'
        report['failure'] = str(exc)
        save()
        raise
    print('PASS: fresh rebuild of all 190 modules completed. Report:', run / 'report.json')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check-env', action='store_true', help='also check installed Lean/Mathlib; do not compile')
    parser.add_argument('--rebuild', action='store_true', help='check environment and freshly compile all 190 modules')
    parser.add_argument('--mathlib', type=Path, help='existing Mathlib checkout at the pinned commit')
    parser.add_argument('--lake', help='absolute path to the Lake executable (defaults to PATH)')
    parser.add_argument('--elan-home', type=Path, help='optional custom ELAN_HOME')
    args = parser.parse_args()
    original, closure = check_release()
    if args.check_env or args.rebuild:
        work, lake, env = environment(args, original)
        if args.rebuild:
            rebuild(args, original, closure, work, lake, env)
        else:
            print('No fresh Lean compilation was performed.')
    else:
        print('Integrity and saved-evidence check only; Lean was not run.')


if __name__ == '__main__':
    try:
        main()
    except (RuntimeError, OSError, ValueError, KeyError, subprocess.TimeoutExpired) as exc:
        print('STOP:', exc, file=sys.stderr)
        sys.exit(1)
    except KeyboardInterrupt:
        print('STOP: interrupted by user.', file=sys.stderr)
        sys.exit(130)
