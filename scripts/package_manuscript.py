"""Package the submission as main.tex and its PNG figures, optionally compiling the ZIP."""
import argparse
from pathlib import Path
import re
import shutil
import subprocess
import tempfile
from zipfile import ZIP_DEFLATED, ZipFile, ZipInfo

paper = Path(__file__).resolve().parents[1] / "Paper-2"
source = paper / "source"
input_line = re.compile(r"^\\input\{([^{}]+)\}\s*(?:%[^\n]*)?$", re.MULTILINE)
image_use = re.compile(r"\\includegraphics(?:\[[^\]]*\])?\{(figures/[^{}]+\.png)\}")


def expand(path, ancestors=()):
    path = path.resolve()
    if not path.is_relative_to(source.resolve()) or path in ancestors:
        raise ValueError(f"Unexpected manuscript input {path}")
    body = path.read_text(encoding="utf-8")

    def include(match):
        target = Path(match[1]).with_suffix(".tex")
        return expand(source / target, (*ancestors, path)).rstrip() + "\n"

    return input_line.sub(include, body)


def build():
    body = expand(source / "YangMills.tex")
    if re.search(r"\\(?:input|include|bibliography)\s*\{", body):
        raise ValueError("Unexpanded document input")
    files = {"main.tex": body.encode("utf-8")}
    for name in sorted(set(image_use.findall(body))):
        files[name] = (source / name).read_bytes()
    if body.count(r"\includegraphics") != len(image_use.findall(body)):
        raise ValueError("Unrecognized figure reference")
    output = paper / "texmdpi.zip"
    with ZipFile(output.with_suffix(".tmp"), "w") as archive:
        for name, data in files.items():
            info = ZipInfo(name, (1980, 1, 1, 0, 0, 0))
            info.compress_type = ZIP_DEFLATED
            archive.writestr(info, data)
    output.with_suffix(".tmp").replace(output)
    return output


def compile_archive(output):
    with tempfile.TemporaryDirectory() as directory:
        stage = Path(directory)
        with ZipFile(output) as archive:
            if archive.testzip() is not None:
                raise ValueError("Damaged source archive")
            archive.extractall(stage)
        for _ in range(3):
            subprocess.run(["pdflatex", "-no-shell-escape", "-interaction=nonstopmode",
                            "-halt-on-error", "main.tex"], cwd=stage, check=True,
                           stdout=subprocess.PIPE)
        log = (stage / "main.log").read_text(errors="replace")
        for diagnostic in ("undefined", "Rerun to get", "Overfull", "Float too large",
                           "multiply defined", "LaTeX Error:"):
            if diagnostic in log:
                raise RuntimeError(f"Unresolved TeX diagnostic: {diagnostic}")
        shutil.copyfile(stage / "main.pdf", paper / "YangMills.pdf")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--compile", action="store_true")
    args = parser.parse_args()
    archive = build()
    if args.compile:
        compile_archive(archive)
    print(archive)
