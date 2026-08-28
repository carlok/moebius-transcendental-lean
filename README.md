# moebius-transcendental-lean

A Lean 4 + Mathlib formalization of the conjugation degree on the transcendental
locus, following the companion paper `p19.tex`.

The setting is the action of

    Γ^± = ⟨PGL(2, Q̄), J⟩,   J(z) = conj z

on `𝒯 = ℂ ∖ Q̄`, organised by the **conjugation degree**

    δ(z) = [Q̄(z, conj z) : Q̄(z)].

`δ(z) = 1` says exactly that complex conjugation is already determined by the
field structure on `Q̄(z)` rather than being independent data. That stratum is
formalized separately in [`carlok/diaz-modulus-lean`](https://github.com/carlok/diaz-modulus-lean),
where it is machine-checked and verified by two independent kernels.

## Status

Early. Five declarations proved and `sorry`-free; two definitions with no
results yet attached. [`tex/ground-up.tex`](tex/ground-up.tex) states every
result with its status — proved, stated only, or out of reach — and
[`BACKLOG.md`](BACKLOG.md) has the increments.

This is a **blueprint-style** formalization. Results are either proved
outright, or — once increment 3 lands — proved *conditionally* on results cited
from the literature and collected in a single `Axioms.lean`. Nothing is left as
`sorry`; anything not yet formalized is stated in `tex/ground-up.tex` and marked
as such rather than stubbed in Lean.

Two consequences of that design, stated plainly:

- A theorem depending on an imported result is a genuine theorem *about that
  dependency*. Run `#print axioms` on any declaration to see exactly what it
  leans on.
- Some of the paper is not reachable in Lean today. Bézout's theorem for plane
  curves, normalization of a projective curve, and Borel reducibility are absent
  from Mathlib and from Tau Ceti alike. Where the paper needs them, the
  formalization assumes them and says so.

## Build

```bash
lake exe cache get
lake build
```

Pinned to `leanprover/lean4:v4.32.0` with Mathlib at the same tag. The pin is
deliberate and documented in `BACKLOG.md`.

## What formalization has already found

Formalizing the reflection lemma of the companion paper turned up a
transcription error in its printed formula — the map did not fix its own zero
locus. The slip was confirmed by counterexample, symbolically, numerically and
then formally, and the paper was corrected. The corrected reflection is proved
in [`carlok/inversive-geometry-lean`](https://github.com/carlok/inversive-geometry-lean).

## Licence

Apache-2.0.

## AI assistance

The mathematics, the formalization and the companion paper were developed with
substantial assistance from large language models, directed and accepted by the
author, who is responsible for the content. Every proof here is machine-checked
by Lean at the pinned toolchain; no claim rests on an assertion by a model.
