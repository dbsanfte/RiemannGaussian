#!/usr/bin/env python3
"""Check the shorter principal proof against Alpöge's pinned compiled archive."""

import argparse
import hashlib
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
from tempfile import TemporaryDirectory


ROOT = Path(__file__).resolve().parents[1]
ENDPOINT = "CheckAlpogePrincipalArchivedGeometryRH"
TOOLCHAIN = "leanprover/lean4:v4.33.1"
LAKE_MANIFEST = "fee57ee9ed399d0a638ca955e5ad40a37a36eeb9b6dfd9f5964114fa7bbe4774"
SOURCE_MANIFEST = "773ca5dd8e2f9f27a81c2449a0c5559a04aa7dafd0c2197789662bc32e7dfacf"
IMPORT = re.compile(r"^[ \t]*(?:(?:public|private|meta)[ \t]+)*import[ \t]+([^\r\n]+)", re.M)


def module_path(module, suffix):
    return Path(*module.split(".")).with_suffix(suffix)


def proof_closure(archive):
    """Return the pinned archive modules and local sources in import order."""
    archive_hashes = {}
    local_sources = {}
    visited = set()

    def visit(module):
        if module in visited:
            return
        visited.add(module)
        relative = module_path(module, ".lean")
        archived = archive / "src" / relative
        if archived.is_file():
            data = archived.read_bytes()
            archive_hashes[module] = hashlib.sha256(data).hexdigest()
            source = None
        else:
            source = next((p for p in (ROOT / "scripts" / relative, ROOT / relative) if p.is_file()), None)
            if source is None:
                # Lean and Lake packages are loaded through the pinned toolchain and Lake manifest.
                return
            data = source.read_bytes()
        for line in IMPORT.findall(data.decode()):
            for dep in line.partition("--")[0].split():
                visit(dep)
        if source is not None:
            local_sources[module] = source

    visit(ENDPOINT)
    manifest = "".join(f"{module} {archive_hashes[module]}\n" for module in sorted(archive_hashes))
    if hashlib.sha256(manifest.encode()).hexdigest() != SOURCE_MANIFEST:
        raise ValueError("The proof's archive source closure differs from the pinned manifest")
    return archive_hashes, local_sources


def link_objects(modules, compiled, selected):
    for module in modules:
        relative = module_path(module, ".olean")
        source = compiled / relative
        if not source.is_file():
            raise FileNotFoundError(f"Missing pinned compiled archive object: {source}")
        target = selected / relative
        target.parent.mkdir(parents=True, exist_ok=True)
        target.symlink_to(source)


def run_check(archive, compiled, sandbox):
    if (archive / "lean-toolchain").read_text().strip() != TOOLCHAIN:
        raise ValueError(f"Expected {TOOLCHAIN}")
    if hashlib.sha256((archive / "lake-manifest.json").read_bytes()).hexdigest() != LAKE_MANIFEST:
        raise ValueError("Unexpected archive Lake dependency manifest")
    modules, local_sources = proof_closure(archive)
    lake = os.environ.get("LAKE") or shutil.which("lake") or Path.home() / ".elan/bin/lake"
    lean = Path(subprocess.check_output([lake, "env", "which", "lean"], cwd=archive, text=True).strip())
    lean_path = subprocess.check_output([lake, "env", "printenv", "LEAN_PATH"], cwd=archive, text=True).strip()
    archive_build = (archive / ".lake/build/lib/lean").resolve()
    dependencies = [(archive / path).resolve() for path in lean_path.split(os.pathsep) if path]
    dependencies = [str(path) for path in dependencies if path != archive_build]
    env = os.environ.copy()
    env.setdefault("LEAN_NUM_THREADS", "1")
    env["PATH"] = os.pathsep.join([str(lean.parent), env["PATH"]])

    with TemporaryDirectory(prefix="alpoge-archive-rh-") as tmp:
        workspace = Path(tmp)
        selected = workspace / "archive"
        output = workspace / "local"
        selected.mkdir()
        output.mkdir()
        link_objects(modules, compiled, selected)
        print(f"Selected {len(modules):,} compiled archive modules and {len(local_sources)} local modules.", flush=True)
        env["LEAN_PATH"] = os.pathsep.join([str(output), str(selected), *dependencies])
        command = []
        if sandbox:
            command.extend([
                "bwrap", "--die-with-parent", "--new-session", "--unshare-all",
                "--ro-bind", "/", "/", "--dev", "/dev", "--proc", "/proc",
                "--ro-bind", str(compiled), str(compiled),
                "--ro-bind", str(workspace), str(workspace), "--bind", str(output), str(output), "--",
            ])
        command.extend([sys.executable, str(ROOT / "scripts/alpoge_lean_heap_loader.py")])
        for module, source in local_sources.items():
            print(f"Checking {module}", flush=True)
            target = output / module_path(module, ".olean")
            target.parent.mkdir(parents=True, exist_ok=True)
            source_root = ROOT / "scripts" if source.is_relative_to(ROOT / "scripts") else ROOT
            subprocess.run(
                [*command, lean, "--trust=0", "-DwarningAsError=true", f"--root={source_root}", "-o", target, source],
                env=env, cwd=archive, check=True,
            )
        subprocess.run([*command, lean.with_name("leanchecker"), "-v", ENDPOINT], env=env, cwd=output, check=True)
    print("All local modules passed strict elaboration and the final theorem passed standalone kernel replay.")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("archive", type=Path, help="Extracted archive with its pinned toolchain and Lake dependencies")
    parser.add_argument("compiled_objects", type=Path, help="Directory containing the public archive .olean files")
    parser.add_argument("--sandbox", action="store_true", help="Run Lean offline with read-only imports using bubblewrap")
    args = parser.parse_args()
    run_check(args.archive.resolve(), args.compiled_objects.resolve(), args.sandbox)


if __name__ == "__main__":
    main()
