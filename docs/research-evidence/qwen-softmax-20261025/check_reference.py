"""Synthetic operation/bit checks, not a GPU benchmark or a proof of libm."""
import json
import math
import random
import struct
from pathlib import Path


def f32(x):
    return struct.unpack('<f', struct.pack('<f', x))[0]


def bits32(x):
    return struct.unpack('<I', struct.pack('<f', x))[0]


def bf16(x):
    bits = bits32(f32(x))
    bits = (bits + 0x7fff + ((bits >> 16) & 1)) & 0xffff0000
    return struct.unpack('<f', struct.pack('<I', bits))[0]


def fp16(x):
    return struct.unpack('<e', struct.pack('<e', x))[0]


def tree_sum(values):
    values = list(values)
    while len(values) > 1:
        values = [f32(values[i] + values[i + 1])
                  if i + 1 < len(values) else values[i]
                  for i in range(0, len(values), 2)]
    return values[0]


def softmax_model(logits, memo=False, exp_round=f32):
    m = max(logits)
    cache = {}
    weights = []
    calls = 0
    for z in logits:
        arg = f32(z - m)
        key = bits32(arg)
        if not memo or key not in cache:
            value = exp_round(math.exp(arg))
            calls += 1
            if memo:
                cache[key] = value
        else:
            value = cache[key]
        weights.append(value)
    denominator = tree_sum(weights)
    reciprocal = f32(1 / denominator)
    if memo:
        normalized = {key: f32(w * reciprocal) for key, w in cache.items()}
        output = [normalized[bits32(f32(z - m))] for z in logits]
    else:
        output = [f32(w * reciprocal) for w in weights]
    return output, calls, denominator


def main():
    rng = random.Random(20261025)
    cases = []
    for n in [10, 128, 2048, 248320]:
        for sigma in [1, 4, 16]:
            for origin in ['bf16', 'fp32']:
                quantize = bf16 if origin == 'bf16' else f32
                logits = [quantize(rng.gauss(0, sigma)) for _ in range(n)]
                # A row-wide temperature preserves equality between logits.
                logits = [f32(z / 0.7) for z in logits]
                reference, full_calls, denominator = softmax_model(logits)
                memoized, calls, memo_denominator = softmax_model(logits, memo=True)
                mismatches = sum(bits32(x) != bits32(y)
                                 for x, y in zip(reference, memoized))
                assert mismatches == 0 and denominator == memo_denominator
                m = max(logits)
                keys = [bits32(f32(z - m)) for z in logits]
                tile_calls = {str(size): sum(len(set(keys[i:i + size]))
                                            for i in range(0, n, size))
                              for size in [32, 128, 1024]}
                cases.append(dict(n=n, sigma=sigma, origin=origin,
                                  exp_calls=full_calls, memo_exp_calls=calls,
                                  normalization_muls=full_calls, memo_normalization_muls=calls,
                                  tiled_memo_exp_calls=tile_calls,
                                  fp32_bit_mismatches=mismatches))
    lower_precision = []
    for n in [2, 10, 128, 2048]:
        logits = [f32(rng.gauss(0, 2)) for _ in range(n)]
        reference, _, _ = softmax_model(logits)
        for name, q in [('fp16', fp16), ('bf16', bf16)]:
            approximate, _, _ = softmax_model(logits, exp_round=q)
            lower_precision.append(dict(
                n=n, exp_storage=name,
                fp32_mismatches=sum(bits32(x) != bits32(y)
                                    for x, y in zip(reference, approximate)),
                bf16_output_mismatches=sum(bf16(x) != bf16(y)
                                           for x, y in zip(reference, approximate))))
    logits = [f32(256), f32(256.5)]
    original, _, _ = softmax_model(logits)
    rounded, _, _ = softmax_model([bf16(z) for z in logits])
    tiny = 2 ** -24
    sequential = f32(f32(1 + tiny) + tiny)
    regrouped = f32(1 + f32(2 * tiny))
    assert sequential != regrouped
    result = dict(
        scope='Synthetic Python CPU floating model; math.exp narrowed to FP32, '
              'fixed pairwise FP32 reduction, one FP32 reciprocal then FP32 products. '
              'No Qwen traces or GPU timing. Memoization preserves the same leaves '
              'and reduction tree; grouped reduction is deliberately not used.',
        memoization=cases, lower_precision_without_certificate=lower_precision,
        casting_counterexample=dict(logits=logits, bf16_logits=list(map(bf16, logits)),
                                    original=original, after_cast=rounded),
        regrouping_counterexample=dict(weights=[1, tiny, tiny],
                                      sequential=sequential, regrouped=regrouped))
    destination = Path(__file__).with_name('reference-results.json')
    destination.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(dict(cases=len(cases),
                         memoized_bits_matched=sum(c['n'] for c in cases),
                         example=[c for c in cases if c['n'] == 248320 and c['sigma'] == 1],
                         lower_precision=lower_precision,
                         casting=result['casting_counterexample'],
                         regrouping=result['regrouping_counterexample']), indent=2))


if __name__ == '__main__':
    main()
