# Public unique-cover constructor: structural replay

26 October 2026. Standard-library Python, scratch only. No factor-field simulation, group/order acquisition, factor search or factoring-success benchmark.

Artifacts: [check_unique_cover.py](check_unique_cover.py), full [unique-cover-check.json](unique-cover-check.json), and one constructor-only [single-fixture output](unique-cover-single-check.json).

Default replay from the formal repository root (18 fixtures, exhaustive validator enabled; output outside the frozen packet):

```sh
python3 docs/research-evidence/semiprime-unique-weighted-20261026/check_unique_cover.py --output /tmp/semiprime-unique-cover-replay.json
```

Single public input, constructor only:

```sh
python3 docs/research-evidence/semiprime-unique-weighted-20261026/check_unique_cover.py --K 54 --N 24794911295 --B 131072 --no-validate --output /tmp/semiprime-unique-cover-single-replay.json
```

`--help` documents all CLI options; `--K`, `--N`, `--B` must be supplied together. Omitting them chooses K=54,162,486; N=K^6-1 and K^6-5 (both coprime to 6); and B=1, the lower dyadic bin near sqrt N, and B=N. These fixtures are not asserted semiprime. They test the PUBLIC combinatorial/number-theoretic construction only.

## Constructor versus validator

The constructor enumerates a bounding rectangle with integer floor caps sqrt(floor(4KN/B²)) and sqrt(floor(4KB²/N)); their product is at most 4K. It applies the exact squared ellipse test, and only adds primitive +/-K axes that pass the same test. Conic colours use at most two unit Hensel roots modulo K/g and O(g) parity-filtered lifts, not a scan of K colours for each pair. Canonical phases use public inverses modulo H. Maximum-3-content integer directions, actual phase groups, and singleton fallbacks then construct the selected cover. No direct f(r) scan is used by acquisition.

The output includes each selected ACTUAL row, its full public support class, selection kind, normalized pi/barpi exponent ledger and the unchanged original M0,h,q-exponent. Operation counters separate bounding candidates, Hensel candidates, colour lifts, phase rows, direction keys and support marks from validation operations. The polynomial identity/field-order proof is not inferred from measured runtime.

The separate exhaustive validator computes f_j(r) modulo H for EVERY catalogue row and EVERY unit r for these small inputs, checks exact equality with its canonical-phase class, and independently checks each selected support. This validation is intentionally O(K²) and is not charged to the nearlinear constructor theorem. It also checks J<23K, J_selected<=phi(K), the support partition, own-colour availability, filtered-axis legality, stationarity/conic congruences, and unchanged clock metadata. For native-scale inputs N<=K^6 it asserts h<16H. No native element or order certificate is simulated.

## Results

All 18 fixtures passed in approximately 0.28 seconds in this environment. Direct catalogue support checks: 442080. Independent selected-support checks: 167544.

|K|six-fixture bounding candidates|acquired phase rows|colour-lift candidates|exhaustive catalogue tests|selected tests|
|---:|---:|---:|---:|---:|---:|
|54|1632|248|144|4464|1872|
|162|5000|856|616|46224|15984|
|486|15000|2416|1648|391392|149688|

Balanced-bin selected row counts were respectively 16,40,138, versus phi(K)=18,54,162. The thin fixtures selected exactly phi(K) singleton-axis supports. These counts are structural examples, not a uniform power saving. The whole-query acquisition bound remains unchanged.

Machine-readable metadata records all selected supports and independent operation counts. This replay validates the implemented public selection on those fixtures; universal all-semiprime coverage, mixed-ring guards, good-field uniqueness and soft-K setup still rest on the reviewed mathematical proof. It supplies no evidence of factor success or faster selected-residue acquisition.
