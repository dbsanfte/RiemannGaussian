# Every cofactor type in the retained owner window is now paid jointly

`ZetaRieszAllTagNativeFloor` applies the checked complete signed tag
estimate to **every prime through `N^3`**, including tags at or below
`N^2`. The previous native instantiation retained only tags above `N^2`.
The underlying counting theorem already allowed the larger tag set; the
native window/count support theorem proves every original physical and
deletion mask without that extra restriction. The original full
`boundedShare` allocation, phase and native count crop are retained.

`budget_eq_previous` proves the error budget does not increase. The
independent `eventually_packet_bound` and `tendsto_packet` cover the entire
small-prime union, regardless of how many additional small primes divide
the cofactor. `addedPacket_eq`, `eventually_addedPacket_bound` and
`tendsto_addedPacket` isolate just the newly covered labels, excluding all
old paid small-tag labels. Their signed real contribution is bounded by
twice the old source-small budget and tends to zero without any zero or
unproved arithmetic cancellation hypothesis.

`owner_rows_complete` proves the exact disjoint union of these rows and
the previous completely rough rows is **every squarefree composite
cofactor** in the original `1.95N < log(p*a) <= 2.03N` core window with
the literal native count cutoff. There is no remaining small-prime,
roughness or least-tag condition in this union. The owner range stays
`51N/50 <= log(p) <= 5N/4`; this theorem does not cover its exterior.

The terminal independent arithmetic estimate is

```text
abs(fullPacket_j + nativeHead(N_j)) <= combinedBudget_j, eventually,
combinedBudget_j -> 0.
```

It holds for `1/2 < u <= 10001/20000` and fixed `abs(y) >= 54` and uses no
zero, exposure or unproved cancellation premise. `fullPacket` is the
literal **full allocation** on that entire native owner population.
Only real signed decay is claimed; the packet or prime head separately
need not decay. The budget is exactly the previous combined budget.

`eventually_sum_fullPaidIncrement` and
`eventually_joined_floor_pruned` spend this whole population once inside
the original native cutoff ledger. The signed prime head is joined with
the remaining main before complete-period clipping using the exact
physical increment from `ZetaRieszPrimeHeadPeriods`. Every outside-owner
label and whole free null/tangent correction remains. Older valid floors
are kept as alternatives, not stacked overlapping credits.

**The cofinal numerical price bound `<=399/5000` remains open.**
`false_of_cofinal_price` is a conditional simple-exposed-zero endpoint,
not a zero exclusion. The outstanding arithmetic quantity is the signed
prime head together with the outside-owner native remainder; this slice
does not give a percentage of the whole floor deficit. The multiplicity
ceiling and RH remain open as well.

Validation is strict local Lean, targeted leaf builds, compiled ordinary
root plus explicit-leaf lint, and a transitive axiom audit of every compiled
declaration, including private/generated helpers. Only the three standard
logical axioms are allowed. See
[the frozen focused report](riesz-all-tag-native-floor-audit.json).
No root registration, public endpoint update, wider gates, commit or push
is part of this local slice.
