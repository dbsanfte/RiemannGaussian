#!/usr/bin/env python3
"""Build the optional certificate in bounded batches, then audit its full closure.

Copyright (c) 2026 David Sanftenberg. Released under Apache 2.0.
Lake validates every restored trace. This script schedules genuine Lean
checks; it cannot turn a failed check into an accepted mathematical result.
"""
from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
import shutil
import signal
import subprocess
import time

from numerical_certificate import ROOT, closure, config, fingerprint, partition

MANIFEST = ROOT / "RiemannGaussian/CertificateData/MontgomeryTaylorCover/manifest.json"


def resource_snapshot():
    """Record runner headroom alongside progress, without changing proof inputs."""
    result = {"diskFreeBytes": shutil.disk_usage(ROOT).free}
    try:
        values = dict(line.split(":", 1) for line in Path("/proc/meminfo").read_text().splitlines())
        for key in ("MemAvailable", "SwapFree"):
            result[key + "KiB"] = int(values[key].split()[0])
    except (OSError, KeyError, ValueError):
        pass
    return result


def stop_process(process):
    """Stop the isolated Lake process group before recording an interruption."""
    try:
        os.killpg(process.pid, signal.SIGTERM)
    except ProcessLookupError:
        return
    try:
        process.wait(timeout=10)
    except subprocess.TimeoutExpired:
        try:
            os.killpg(process.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass
        process.wait(timeout=10)


def terminate_signal(number, _frame):
    """Let the ordinary failed-run cleanup handle a runner termination."""
    raise SystemExit(128 + number)


def select_groups(groups, shard_index, shard_count):
    """Disjoint, exhaustive round-robin partition of the declared proof groups."""
    if shard_count < 1 or not 0 <= shard_index < shard_count:
        raise ValueError("Require a positive shard count and 0 <= shard index < shard count")
    return groups[shard_index::shard_count]


def prerequisite_batches(optional, groups, jobs):
    """Schedule generated data before its dependents, with the same process cap.

    A cold group build otherwise starts all imported data modules at once.
    Transitive dependencies matter: a reusable module can mediate an import.
    The complete cover and modules depending on it are excluded from this stage.
    """
    if jobs < 1:
        raise ValueError("jobs must be positive")
    cover_names = {g["module"] for g in groups}
    cover_prefixes = {name.rsplit(".", 1)[0] for name in cover_names}
    heavy_prefix = config()["heavyModulePrefix"]
    candidates = {
        name for name in optional
        if name.startswith(heavy_prefix)
        and not any(name == prefix or name.startswith(prefix + ".")
                    for prefix in cover_prefixes)
    }
    imports = {name: set(closure(name)) for name in candidates}
    pending = {name for name in candidates if not imports[name].intersection(cover_names)}
    dependencies = {name: (imports[name] & pending) - {name} for name in pending}
    result = []
    while pending:
        ready = sorted(name for name in pending if not dependencies[name].intersection(pending))
        if not ready:
            raise ValueError(f"Generated data imports contain a cycle: {sorted(pending)}")
        batch = ready[:jobs]
        result.append(batch)
        pending.difference_update(batch)
    return result


def lake_command():
    lake = shutil.which("lake")
    if lake:
        return [lake], os.environ.copy()
    elan = ROOT.parent / ".lean/elan"
    lake = elan / "bin/lake"
    if not lake.is_file():
        raise RuntimeError("Install the pinned Lean toolchain before verifying")
    env = os.environ.copy()
    env["ELAN_HOME"] = str(elan)
    return [str(lake)], env


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--jobs", type=int, default=4, help="Maximum simultaneous cover modules")
    parser.add_argument("--output", type=Path, default=ROOT / ".lake/numerical-certificate")
    parser.add_argument("--groups-only", action="store_true", help="Check pieces; defer assembly and audit")
    parser.add_argument("--data-only", action="store_true", help="Check only the generated prerequisite data")
    parser.add_argument("--shard-index", type=int, default=0, help="Zero-based CI shard index")
    parser.add_argument("--shard-count", type=int, default=1, help="Number of disjoint CI shards")
    args = parser.parse_args()
    if args.jobs < 1:
        parser.error("--jobs must be positive")
    if args.shard_count < 1 or not 0 <= args.shard_index < args.shard_count:
        parser.error("Require --shard-count > 0 and 0 <= --shard-index < --shard-count")
    if args.data_only and args.groups_only:
        parser.error("Choose either --data-only or --groups-only")
    if args.shard_count != 1 and (not args.groups_only or args.data_only):
        parser.error("Shards require --groups-only; only the complete target may enter the final audit")
    _, optional = partition()
    manifest = json.loads(MANIFEST.read_text())
    all_groups = manifest["groups"]
    if not all_groups:
        raise RuntimeError("The manifest must declare the complete cover's proof groups")
    groups = select_groups(all_groups, args.shard_index, args.shard_count)
    data_batches = prerequisite_batches(optional, all_groups, args.jobs)
    commands, env = lake_command()
    args.output.mkdir(parents=True, exist_ok=True)
    raw_audit = ROOT / ".lake/numerical-certificate/audit.json"
    result_markers = {args.output / "input-sha256.txt", args.output / "audit.json"}
    if not args.groups_only and not args.data_only:
        result_markers.add(raw_audit)
    for path in result_markers:
        path.unlink(missing_ok=True)
    digest = fingerprint()
    start = time.monotonic()
    state = {"state": "running", "inputSha256": digest, "totalGroups": len(all_groups),
             "selectedGroups": 0 if args.data_only else len(groups),
             "shardIndex": args.shard_index, "shardCount": args.shard_count,
             "totalDataModules": sum(map(len, data_batches)), "verifiedDataModules": 0,
             "verifiedGroups": 0, "verifiedNodesInPieces": 0, "verifiedAnchorLeaves": 0,
             "activeModules": [], "stage": "prerequisite-data", "controllerPid": os.getpid()}

    def save():
        state["elapsedSeconds"] = round(time.monotonic() - start, 1)
        state["resources"] = resource_snapshot()
        tmp = args.output / "progress.json.tmp"
        tmp.write_text(json.dumps(state, indent=2) + "\n")
        tmp.replace(args.output / "progress.json")

    def run(args_, name):
        log = args.output / name
        with log.open("w") as stream:
            process = subprocess.Popen(commands + args_, cwd=ROOT, env=env,
                                       stdout=stream, stderr=subprocess.STDOUT,
                                       start_new_session=True)
            state["processPid"] = process.pid
            save()
            try:
                while True:
                    try:
                        code = process.wait(timeout=30)
                        break
                    except subprocess.TimeoutExpired:
                        save()
                        print(json.dumps(state), flush=True)
            except BaseException:
                stop_process(process)
                state.pop("processPid", None)
                raise
            state.pop("processPid", None)
        if code:
            state.update(state="failed", exitCode=code, failureLog=str(log))
            save()
            raise RuntimeError(f"Lean verification failed; see {log}")

    previous_handler = signal.signal(signal.SIGTERM, terminate_signal)
    try:
        for index, batch in enumerate(data_batches):
            state.update(activeModules=batch, batch=index)
            save()
            run(["build", *batch, "--wfail"], f"data-{index:03d}.log")
            state["verifiedDataModules"] += len(batch)
            save()
            print(json.dumps(state), flush=True)
        if args.data_only:
            if fingerprint() != digest:
                raise RuntimeError("Certificate inputs changed during data verification")
            state.update(state="passed", stage="data-only", activeModules=[])
            save()
            (args.output / "input-sha256.txt").write_text(digest + "\n")
            print(json.dumps(state), flush=True)
            return
        state["stage"] = "pieces"
        for start_index in range(0, len(groups), args.jobs):
            batch = groups[start_index:start_index + args.jobs]
            state["activeModules"] = [g["module"] for g in batch]
            state["batch"] = start_index // args.jobs
            save()
            run(["build", *state["activeModules"], "--wfail"], f"batch-{state['batch']:03d}.log")
            state["verifiedGroups"] += len(batch)
            state["verifiedNodesInPieces"] += sum(g["nodes"] for g in batch)
            state["verifiedAnchorLeaves"] += sum(g["anchorLeaves"] for g in batch)
            save()
            print(json.dumps(state), flush=True)
        if fingerprint() != digest:
            raise RuntimeError("Certificate inputs changed during verification; revalidate the changed inputs")
        if not args.groups_only:
            state.update(stage="assembly", activeModules=["NumericalCertificate"])
            run(["build", "NumericalCertificate", "--wfail"], "build.log")
            state.update(stage="axiom-audit", activeModules=[])
            run(["env", "lean", "-DwarningAsError=true", "scripts/AuditNumericalCertificate.lean"], "audit.log")
            if fingerprint() != digest:
                raise RuntimeError("Certificate inputs changed during the final build")
            if not raw_audit.is_file():
                raise RuntimeError("Axiom audit completed without its report")
            report = json.loads(raw_audit.read_text())
            report["inputSha256"] = digest
            report_tmp = args.output / "audit.json.tmp"
            report_tmp.write_text(json.dumps(report, indent=2) + "\n")
            report_tmp.replace(args.output / "audit.json")
        state.update(state="passed", stage="pieces-only" if args.groups_only else "complete-selected-target",
                     activeModules=[])
        save()
        (args.output / "input-sha256.txt").write_text(digest + "\n")
        print(json.dumps(state), flush=True)
    except BaseException:
        for path in result_markers:
            path.unlink(missing_ok=True)
        if state["state"] == "running":
            state["state"] = "interrupted-or-failed"
            save()
        print(json.dumps(state), flush=True)
        raise
    finally:
        signal.signal(signal.SIGTERM, previous_handler)


if __name__ == "__main__":
    main()
