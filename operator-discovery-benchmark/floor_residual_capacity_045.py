"""Explicit support capacity for the unchanged 045 candidates and 044 formulas.

Load isolated instances of the frozen backends. Only the list-length resource
limit changes; arithmetic, certificates, bit/index limits and old modules stay
unchanged. This is a recovery configuration, not a new mathematical provider.
"""
import importlib.util
from pathlib import Path
import resource
import time

ROOT = Path(__file__).resolve().parent
SUPPORT_LIMIT = 3072


def isolated(filename, name):
    spec = importlib.util.spec_from_file_location(name, ROOT / filename)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


INTERVAL = isolated('floor_residual_interval_044.py', 'floor_capacity_interval_045')
CHECK = isolated('check_floor_residual_arguments_044.py', 'floor_capacity_checker_045')
for backend in (INTERVAL, CHECK):
    if backend.MAX_SUPPORT != 2048 or backend.MAX_INDEX != 4096:
        raise ValueError('expected frozen backend resource limits')
    backend.MAX_SUPPORT = SUPPORT_LIMIT
RUN = isolated('run_floor_residual_045.py', 'floor_capacity_runner_045')
RUN.CHECK = CHECK


def compile_batch(search, parents):
    return RUN.compile_batch(search, parents)


def memory_preflight(programs):
    reserves = []
    for program in programs:
        meter = INTERVAL.Meter()
        lattice = INTERVAL.integer_lattice(program, meter)
        support = len(program['coefficients']) + len(program['steps'])
        K = program['coefficients'][-1]['n'] if program['coefficients'] else 1
        extra = (K + 1) * (384 + (lattice['early_bound_num'].bit_length() + 7) // 8)
        meter.reserve(RUN.S.FINAL_H, lattice['event_abs'].bit_length(), support, extra)
        reserves.append(meter.counts()['peak_bytes_estimate'])
    aggregate = 2 * max(reserves, default=0) + 2 * 1024**3
    if aggregate > 16 * 1024**3:
        raise MemoryError('aggregate two-worker memory preflight')
    return aggregate


_worker_kernel = None


def audit_one(task):
    global _worker_kernel
    if _worker_kernel is None:
        _worker_kernel = INTERVAL.JordanKernel()
    program, H = task['program'], task['H']
    started = time.monotonic()
    meter = INTERVAL.Meter(cap=1_000_000_000, seconds=3600)
    certificate = INTERVAL.certify(program, H=H, precision=192, meter=meter, kernel=_worker_kernel)
    proof_meter = CHECK.Meter(cap=3_000_000_000)
    checked = CHECK.verify_norm(program, certificate, meter=proof_meter)
    if not checked['verified'] or not checked['all_domain_included'] or checked['convergence_proved']:
        raise ValueError('whole-domain admission failed')
    return dict(id=program['id'], certificate=certificate, verification=checked,
                producer_counts=meter.counts(), checker_operations=proof_meter.operations,
                elapsed_seconds=time.monotonic()-started,
                worker_peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss)
