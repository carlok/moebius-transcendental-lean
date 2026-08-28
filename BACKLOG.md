# Backlog

Formalization of `p19.tex` — the conjugation degree on the transcendental locus.
Blueprint-first, Mathlib-style, Palomar as a view. Increments are ordered so
each one ends somewhere publishable.

Source paper: `~/Documents/varie/hacks/t/transcendental/p19.tex`

---

## Decisions already made — do not re-litigate

| | |
|---|---|
| Toolchain | `leanprover/lean4:v4.32.0`. Not v4.32.1/.2 — `lean4export` has no such revision, and that blocks Comparator. Oleans already cached. |
| Mathlib | pinned v4.32.0, rev `81a5d257c8e410db227a6665ed08f64fea08e997`. Manifest copied from `diaz-modulus-lean`, so no resolve needed. |
| `δ` typing | `ℕ∞` via `minpoly … natDegree`, **not** `Module.finrank`. Dodges `IntermediateField` tower instances; `⊤` is a real value, not `finrank`'s junk `0`. Settled and compiled. |
| Cited literature | one documented `Axioms.lean`, as in `diaz-modulus-lean`. **Not** `sorry` (proves nothing) and **not** threaded hypotheses (unreadable at this scale). |
| Style | Mathlib conventions throughout — copyright header, module docstring, docstring per declaration, `#lint`-clean. Keeps small upstream PRs possible at PR cost, not rewrite cost. |
| Palomar | **REVISED 2026-08-28 — see "Correction" below.** Still a view, not a driver. But the gate is *positioning*, not novelty, and conditional-on-cited-literature entries are registered routinely. |
| Remote | not created. Local only until you decide. |

---

## Increment 0 — skeleton ✅ done

Lakefile, toolchain, manifest, LICENSE (Apache-2.0), `.gitignore`,
`Multiplicity.lean`, `Basic.lean`. Both modules were compiled during the round-2
and round-3 studies before being ported here.

**DoD:** `lake build` green.

---

## Correction — the Palomar model was wrong

Read `https://data.palomar-registry.org/recent.json`. The 37 registered entries
say something the policy documents do not.

**Pure formalization of classical theorems is registrable.** Descartes's Rule of
Signs (1637), Hall's Marriage Theorem (1935), Erdős–Ko–Rado, Sylvester–Gallai,
Bollobás, Bondy, Graham–Pollak — all registered, several described as
"formalization only". The gate is not novelty.

**Conditional entries are registered routinely.** `Vulkin-prog/paper-c-lean` is
conditional on "exactly six fully stated ordinary source propositions" —
registered twice. `AviKndr/universal-words` keeps its main theorem on the three
standard axioms with the axiom-assuming version in "a quarantined module" that
is not compared. `teal-sea/zeta-lab` leaves its eight-point instance conditional
and discloses a step "checked numerically only".

That quarantine architecture is exactly the `Axioms.lean` plan in increment 3.
It is not a workaround; it is the registered norm.

**Why the two 2026-08-27/28 refusals happened.** Both claimed *original results*
about *self-defined objects* — `OffsetAdmissible`, the conjugation rigidity.
Registered entries are formalizations of *named* theorems, refutations of
*named* conjectures, or solutions to *named* problems, and they under-claim
heavily. Several say outright "not claimed as new".

### Consequences for this backlog

1. **Increment 4 is no longer blocked.** `thm:circular-degree` conditional on
   Bézout, normalization and morphism degree — each a fully stated hypothesis —
   follows the Vulkin-prog pattern directly. Round 2's NO-GO rested on the false
   premise that conditionality disqualifies.
2. **The ground-up TeX matters more than expected.** Registered abstracts devote
   a large fraction of their length to what is *not* proved. `ground_up_2.tex`
   is already in that register; p19 needs the same treatment.
3. **`diaz-modulus-lean` may be registrable unchanged**, repositioned as a
   formalization of the rigidity underlying Diaz's 2004 question rather than as
   a new obstruction. Same Lean, different framing. Worth revisiting before
   building anything new.
4. **`parsimagma` too.** `BrandonMYates` has several registered *refutations* of
   named conjectures, explicitly "not claimed as new". The ETP counterexamples
   have that shape.

### The abstract template

An LLM extracted the accepted profile into a drafting prompt with eight
sections: what is proved (matching the compared statement exactly) · conditionality
(N fully stated propositions, hypotheses not axioms, each source named) · what is
NOT proved (a dedicated paragraph, enumerated) · audience (named papers and
researchers, not a category) · novelty as a dated *procedure*, never a claim ·
contribution recorded as the formalization itself · axiom hygiene with
`#print axioms` output pasted · automation with every model named.

Keep that prompt. It is the most useful artefact produced this week.

---

## Increment 1 — blueprint scaffolding and the statement inventory

The spine. Everything after this hangs off it.

- `leanblueprint` and `plastex` are already installed in
  `~/Documents/varie/hacks/t/transcendental/p19-lean/venv/bin/`.
- Build the inventory in the style of
  `t/transcendental/p19-lean/PHASE0.md` — one row per numbered statement of
  `p19.tex`: informal statement, kind, Mathlib support, verdict
  `FORMALIZE` / `ASSUME`.
- Wire `\lean{}` and `\leanok` so the graph renders.

**DoD:** the blueprint site builds and shows a dependency graph with every
`p19.tex` statement present as a node, colour-coded. Most will be blue. That is
the honest starting picture and the point of doing this first.

---

## Increment 2 — Tier A, fully proved

Reachable now, no assumptions. From round 1's coverage check, every dependency
exists.

- `lem:no-holo-stab` — fixed points of a non-identity `g ∈ Γ` are algebraic
- `thm:preservation-transcendence` and `-anti`
- `thm:maximal-transfer` — three-point rigidity
- `lem:dense-affine-orbits` — density of `ℚ(i)`
- `conjDegree` invariance under `Γ^±`
- `conjDegree z = 1 ↔ conj z ∈ gen z`

**DoD:** all green in the blueprint, `#print axioms` clean on each, `#lint`
passes.

**Note:** these are elementary. That is fine here — they are the paper's
foundations, and the blueprint is not a submission.

---

## Increment 3 — `Axioms.lean`

One file, every imported result visible in one place, each with a full citation
and a docstring saying why it is assumed rather than proved.

Expected contents: Bézout for plane curves; normalization of a projective curve;
degree of a morphism as a function-field extension degree. Possibly
Hermite–Lindemann, if the δ = 1 material is ported from `diaz-modulus-lean`.

**DoD:** each axiom carries source, page, and a one-line statement of what would
discharge it. Follow `diaz-modulus-lean/Diaz/Axioms.lean`, which does this well.

---

## Increment 4 — `thm:circular-degree`, conditionally

The paper's strongest result. Unreachable unconditionally — Bézout and
normalization are absent from Mathlib and Tau Ceti both — but a proved
conditional theorem is a real artefact.

- extend `mult` to a projective point (chart at `I± = [1:±i:0]`)
- define `cdeg` as `d − m`
- prove `δ(z) = d − m` **from** the increment-3 axioms

**DoD:** the theorem compiles; `#print axioms` shows exactly which imported
results it leans on; the blueprint node is marked as conditional.

---

## Increment 5 — Zenodo release

Publishable as soon as increments 1–2 are done. Does not wait for 4.

- GitHub–Zenodo integration, DOI per tagged release
- new version of `10.5281/zenodo.18048181` (currently p16) with the p19 PDF
- PDF points at the repo and its DOI; repo points back
- AI disclosure, JOSS-style: tools and models, scope of assistance,
  confirmation of human review
- include `t/transcendental/p19-lean/DiazSample1/NOTE_discrepancy.md` — a
  formalization catching a real paper error, checked symbolically, numerically
  and formally. It is the concrete answer to "what is the Lean for".

**DoD:** DOI minted, both directions of the link resolve.

---

## Increment 6 — the dimension road *(large, optional)*

`dimH (Z(P)) ≤ 1` for `0 ≠ P ∈ ℝ[X,Y]`, unlocking the stratum dimension
results. Months, not weeks.

Route: `Res_Y(P, ∂P/∂Y) ≠ 0` for squarefree `P` via `resultant_eq_zero_iff`
(`Mathlib/RingTheory/Polynomial/Resultant/Basic.lean`, 1025 lines — better
supported than first thought) → singular locus finite → implicit function
theorem at regular points → `dimH_iUnion` + `ContDiff.dimH_range_le`.

**Know before starting:** round 3 found the resulting theorem is δ-**insensitive**
— `dimH (U ∩ 𝒯ₙ) = 1` for *every* finite `n`, so it cannot separate the strata
it stratifies. Worth doing as mathematics and as a Mathlib gap. Not worth doing
to impress a reviewer.

---

## Increment 7 — descriptive set theory *(largest, optional)*

`cor:E0-embeds` and `thm:orbit-complexity-circle`. Nothing exists: no Borel
reducibility, no `E₀`, no hyperfiniteness, no amenability, in Mathlib or Tau
Ceti.

**Definitions cannot be assumed** — unlike theorems. `E₀`, Borel reducibility
and hyperfiniteness must be *defined* first (each short), and only then can
Mycielski and the ergodicity inputs be assumed.

---

## Increment 8 — Palomar view *(opportunistic)*

Whenever an axiom-free subset exists that says something worth saying, add
`Challenge.lean`, `Solution.lean`, `comparator.json`, `formalization.yaml`. The
plumbing is a few hours and `diaz-modulus-lean` is the working template.

Traps, all paid for already:

1. `import Mathlib` in **both** Challenge and Solution — narrow imports made the
   `Fintype (Fin 2)` instance resolve to `SimplexCategory.…` in one and
   `Fin.fintype 2` in the other, and Comparator rejected the pair.
2. A pretty-printed `#check` diff is **not** a match test. Use
   `set_option pp.all true`.
3. Licence at repository root. Permitted axioms only `propext`,
   `Classical.choice`, `Quot.sound`.
4. `verify-comparator.sh` cannot run on macOS — Landrun needs Linux Landlock.

**Do not** let this increment choose what increments 2–7 formalize.

---

## Open questions

1. **Does the `lem:R_H` slip propagate?** `NOTE_discrepancy.md` flags this as
   unchecked. A grep found only one use of the explicit formula, matching its
   guess, but that is a grep and not an audit. Worth settling before the Zenodo
   version goes out.
2. **Is `p19.tex` itself audited?** `STATUS.md` records a known defect in
   `p19_diaz.tex` — a different document. Nobody has confirmed p19 is
   unaffected. Statements were read closely during the rounds; proofs were not.
3. **Would a δ-sensitive metric statement exist?** Increment 6's theorem is not
   one. If the paper can say something where the answer depends on `n`, that is
   the interesting version and it is not currently written down.

---

## Reference material

| Path | What |
|---|---|
| `t/transcendental/p19.tex` | the source paper |
| `t/transcendental/p19-lean/PHASE0.md` | the inventory method, already designed |
| `t/transcendental/p19-lean/DiazSample1/` | worked sample + `NOTE_discrepancy.md` |
| `t/transcendental/lean-inversive-geometry/` | `lem:R_H` already proved, 118 lines |
| `t/transcendental/p19-round{1,2,3}-*-result-*.md` | the three feasibility studies |
| `lean4/diaz-modulus-lean/` | δ = 1 stratum, Palomar template, `Axioms.lean` pattern |
