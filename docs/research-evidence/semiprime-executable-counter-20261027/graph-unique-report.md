# Actual macro graph uniqueness

New sole-owned module `RiemannGaussian/SemiprimeMacroGraphUnique.lean` strict-compiles. Its root-import scoped audit passes all 15 linters and examines every generated declaration: 9 declarations/theorems, standard axioms only.

Main API:

```
accepted_unique (p : Config) (a b : BitSignal p.r p.t p.digits → Bool)
  (ha : OriginalAccepted p a) (hb : OriginalAccepted p b)
  (hin : ∀ side (i : Fin p.digits),
    wordNat p a (.input side casti) = wordNat p b (.input side casti)) : a = b
```

Here `casti` is the actual `Fin (p.r*p.t)` active input index licensed by `p.cap`. The proof uses the literal accepted source tables to zero inactive inputs, derives equality of every forward/twiddle/second-stage canonical integer word, derives equality of point products and inverse stages, and uses the actual integer carry equations from the fixed zero initial carry. Source flags then agree by their actual digit tables; the new FlagExtension uniqueness theorem fixes all OR wires. Injectivity of actual Boolean-word decoding finally yields equality of every physical bit.

There is no assumed global transform correctness, guessed flags, accepted-extension oracle, or counting/runtime theorem. The result proves at most one original accepted extension for fixed active source digits. The companion construction establishes existence separately; equality-subdivision/operand-level bijection adapters remain distinct steps.

Logs: `graph-unique-build.log`, `graph-unique-audit.log`. Replay uses absolute lake path and strict autoImplicit/warning settings as in the other scoped reports. No pre-existing source was changed.
