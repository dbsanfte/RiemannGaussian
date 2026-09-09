# A finite floor is enough for the Suzuki contradiction

Lean now proves that **any eventual uniform lower bound** for the original
cumulative signed prime work implies Mathlib's `RiemannHypothesis`:

```text
there exists a finite B such that, for all sufficiently large j,
  -B <= sum_{n<j} suzukiFirstTailTransportLinearWork(n).
```

The terminal theorem is
`riemannHypothesis_of_suzuki_signed_work_eventually_bounded_below` in
`SuzukiBoundedWork.lean`. The independent arithmetic bound is still open.
No new unconditional zero bound is claimed.

The exact identity remains `G_j = G_0 + sum I_n - sum C_n`. Since the actual
nonnegative costs have finite total, a work floor gives a gap floor. Adding
that finite constant to the frozen base value transfers the floor to the
literal Suzuki function without altering its curvature, event locations,
weights or canonical centers. The prime-free initial interval is handled
by its exact formula.

For the arithmetic Laplace signal, adding a constant `C` makes a positive
measure and adds exactly `C/z` to the genuine safe-half-plane transform.
The checked Landau argument applies to this measure. Subtracting `C/z`
then supplies a holomorphic continuation of the original response on
`Re z > 0`; no right-half-zero residue can be removed by that correction.
A finite initial prefix of work is absorbed into the arbitrary floor.

The converse consequence for a hypothetical right-half zero is now stronger
than a single failed prefix:
`suzuki_signed_work_frequently_below_of_right_half_zero` proves that the
cumulative work falls below **every** prescribed finite floor at arbitrarily
large cutoffs. Thus exact gap positivity and a preselected positive margin
are unnecessary for the contradiction.

This changes the estimate worth seeking: preserve cancellation across the
negative individual events and negative doubling blocks, and try to prove
a finite floor for the cumulative work. Bounding the separate absolute
contributions need not produce such a floor. The existing Möbius prefix
estimate retains its natural cutoff power times an exponential saving on
a cubic logarithmic scale; that estimate alone is not a bound for this
nonlinear signed prime work.

This is a strengthened reduction and source consequence, not a proof of
the independent arithmetic estimate. The local slice is uncommitted.
