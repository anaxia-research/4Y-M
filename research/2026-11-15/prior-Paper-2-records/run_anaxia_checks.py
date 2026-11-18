"""Replay the available Anaxia checks without promoting finite tests to a Clay proof."""
from pathlib import Path
from fractions import Fraction
import contextlib
import hashlib
import importlib
import io
import json
import runpy
import subprocess
import sys
import unittest

sys.dont_write_bytecode = True
sys.stdout.reconfigure(encoding='utf-8')
HERE = Path(__file__).resolve().parent
ENGINE = Path(r'C:\CLAUDE PAPERS\eBLLM')
OPENGLUON = Path(r'C:\CLAUDE PAPERS\OpenGluon')
sys.path.insert(0, str(ENGINE / 'src'))

from ebllm.cli import main
from ebllm.research.certificates import certify_psd, verify_psd
from ebllm.obligations import ObligationGraph

def cli_record(arguments, name):
    buffer = io.StringIO()
    with contextlib.redirect_stdout(buffer), contextlib.redirect_stderr(buffer):
        code = main(arguments)
    text = buffer.getvalue()
    (HERE / name).write_text(text, encoding='utf-8')
    assert code == 0, (arguments, code)
    return {'arguments': arguments, 'exit_code': code, 'file': name}

runs = [
    cli_record(['routes', 'Yang-Mills', '-k', '20'], 'anaxia-routes.json'),
    cli_record(['superstring', '--target', 'yang-mills', '--json'], 'anaxia-attack-records.json'),
]
for name in ('check_yang_mills_one_scale.py', 'check_thermal_gap_identifiability.py'):
    script = OPENGLUON / 'scripts' / name
    buffer = io.StringIO()
    with contextlib.redirect_stdout(buffer):
        runpy.run_path(str(script), run_name='__main__')
    log_name = name.removesuffix('.py') + '.txt'
    (HERE / log_name).write_text(buffer.getvalue(), encoding='utf-8')
    runs.append({'script': str(script), 'sha256': hashlib.sha256(script.read_bytes()).hexdigest(), 'file': log_name})

suite = unittest.defaultTestLoader.discover(str(ENGINE / 'tests'), pattern='test_ym_blocks.py')
buffer = io.StringIO()
test_result = unittest.TextTestRunner(stream=buffer, verbosity=2).run(suite)
(HERE / 'anaxia-ym-block-tests.txt').write_text(buffer.getvalue(), encoding='utf-8')
assert test_result.wasSuccessful()

matrices = {
    'rank-two-kernel': [['2/3', '1/3'], ['1/3', '2/3']],
    'vacuum-complement': [['1/2', '-1/2'], ['-1/2', '1/2']],
    'excited-ratio-at-most-one-half': [['1/12', '-1/12'], ['-1/12', '1/12']],
    'positive-pressure-margin': [['32359519/3376414720000']],
}
certificates = {}
for name, values in matrices.items():
    certificate = certify_psd(values)
    assert verify_psd(values, certificate)
    certificates[name] = {'matrix': values, 'certificate': certificate}
(HERE / 'anaxia-finite-certificates.json').write_text(json.dumps(certificates, indent=2)+'\n', encoding='utf-8')

campaign_path = OPENGLUON / 'data' / 'campaign' / 'latest' / 'yang-mills.json'
campaign = json.loads(campaign_path.read_text(encoding='utf-8'))
campaign_summary = {key: campaign.get(key) for key in (
    'sequence', 'attempted_at_utc', 'provider', 'model', 'max_tokens',
    'status', 'global_status', 'scope', 'outcome')}

graph = ObligationGraph()
graph.add('finite_certificate', status='PASS', verifier='Anaxia exact LDL reconstruction')
graph.add('uniform_Wilson_pressure_seed', status='UNK')
graph.add('continuum_family_and_field_axioms', status='COND')
graph.add('mass_gap_transfer', status='COND')
graph.add('Clay_mass_gap', status='UNK')
graph.bridge(['finite_certificate', 'uniform_Wilson_pressure_seed',
              'continuum_family_and_field_axioms', 'mass_gap_transfer'], 'Clay_mass_gap')
assert not graph.releasable('Clay_mass_gap')
commit = subprocess.run(['git', '-C', str(ENGINE), 'rev-parse', 'HEAD'],
                        capture_output=True, text=True, check=True).stdout.strip()
result = {
    'engine_commit': commit,
    'runs': runs,
    'ym_tests_passed': test_result.testsRun,
    'ym_test_skips': len(test_result.skipped),
    'finite_psd_certificates_verified': len(certificates),
    'existing_campaign_record': campaign_summary,
    'closure_certified': graph.releasable('Clay_mass_gap'),
    'missing_obligations': graph.blockers('Clay_mass_gap'),
    'scope': 'Stored route records, finite arithmetic, and sampled block tests only. No uniform weak-coupling Wilson bound or continuum mass-gap proof is certified.',
}
(HERE / 'anaxia-run-summary.json').write_text(json.dumps(result, indent=2)+'\n', encoding='utf-8')
print(json.dumps(result, indent=2))
