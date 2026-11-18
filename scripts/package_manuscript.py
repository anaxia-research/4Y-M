"""Rebuild the current submission source ZIP; optionally compile its PDF."""
from pathlib import Path
import argparse
import shutil
import subprocess
import zipfile

root = Path(__file__).resolve().parents[1]
source = root / 'Paper-2/source'
parser = argparse.ArgumentParser()
parser.add_argument('--compile', action='store_true')
args = parser.parse_args()
if args.compile:
    for _ in range(3):
        subprocess.run(['pdflatex', '-no-shell-escape', '-interaction=nonstopmode',
                        '-halt-on-error', 'YangMills.tex'], cwd=source, check=True)
    log = (source / 'YangMills.log').read_text(errors='replace')
    for error in ('LaTeX Warning: Reference', 'LaTeX Warning: Citation',
                  'Overfull', 'Float too large', 'multiply defined', 'Rerun to get'):
        if error in log:
            raise RuntimeError('Unresolved compilation diagnostic: ' + error)
    shutil.copyfile(source / 'YangMills.pdf', root / 'Paper-2/YangMills.pdf')
with zipfile.ZipFile(root / 'Paper-2/ymmdpitex.zip', 'w', zipfile.ZIP_DEFLATED) as archive:
    for p in sorted(source.rglob('*')):
        if p.is_file() and p.suffix in {'.tex', '.png', '.py', '.jl', '.md', '.json'} and '__pycache__' not in p.parts:
            archive.write(p, p.relative_to(source).as_posix())
print('Current source ZIP prepared. No release or DOI operation is performed.')
