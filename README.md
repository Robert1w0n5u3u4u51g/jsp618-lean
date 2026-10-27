# Independent Lean 4 formalization of Alon's theorem (Erdős #618)

An independent formalization, from Noga Alon's paper *Triangle-free
graphs of diameter 2* (Princeton note, `remark1901.pdf`), of the
theorem that settles the Erdős–Gyárfás `h₂` question (Erdős Problem
#618) in a strong asymptotic form.

This formalization was developed independently from Alon's paper. It
does not use any existing formalization of this result.

## What is proved

- **`Jsp618.theorem_1_2`** (in `Jsp618/Basic.lean`, proved from
  `theorem_1_2_aux` in `Jsp618/Theorem12.lean`): for every
  `0 < ε < 1 / 8` there is `n₀` such that every triangle-free graph on
  `n ≥ n₀` vertices with maximum degree at most `n ^ (1 / 2 - ε)` can
  be turned into a triangle-free graph of diameter two by adding
  fewer than `3 * n ^ (2 - ε)` edges.

  The range is `1 / 8`, not the `1 / 6` in Alon's abstract, honestly:
  this formalization uses the crude union bound over at most `2 ^ n`
  independent sets, and with that bound the union-bound exponent is
  `3 / 2 - 4 * ε`, which beats `n` only for `ε < 1 / 8`. Alon's `1 / 6`
  would need the sharper entropy bound
  `(n choose 5cn) ≤ 2 ^ (H(5c) n)`. The statement here is therefore a
  weakening of Alon's `1 / 6` form, not a claim about it.

- **`Jsp618.erdos_618`** (in `Jsp618/Main618.lean`): for every family
  of triangle-free graphs `G n` on `n` vertices with maximum degree
  `Δ (G n) = o(√n)`, one has `h2 (G n) = o(n²)`.

  Note: `erdos_618` is not deduced from `theorem_1_2` at a fixed `ε`
  (that argument is invalid: e.g. `Δ = √n / log n` is `o(√n)` but
  violates `Δ ≤ n ^ (1 / 2 - ε)` for every fixed `ε > 0`). It is
  proved from the general degree-bound lemma below with the varying
  bound `b n = max (Δ (G n)) (n ^ (7 / 16))`.

## Structure

- `Jsp618/Defs.lean` — definitions: `maxDeg`, `DiamLETwo`, `h2`
  (the least number of edges whose addition produces a triangle-free
  supergraph of diameter at most two).
- `Jsp618/Deterministic.lean` — the deterministic half: maximal
  triangle-free extensions, diameter at most two for maximal graphs,
  `Δ ≤ α`, and the reduction `2 * h₂ ≤ n * B` when all independent
  sets have size at most `B`.
- `Jsp618/Counting.lean` — counting lemmas: `k`-subsets bounded by
  `2 ^ n`, pairs sharing a common neighbour bounded by
  `n * C(maxDeg, 2)`.
- `Jsp618/Process.lean` — the random process: ordered eligible pairs,
  the process invariants, and `process_claim` (with high probability
  over the choice sequences, the process output has no independent
  set of size `K`).
- `Jsp618/Theorem12.lean` — the assembly: the general degree-bound
  lemma `h2_bound_of_degree_bound` (`h2 G ≤ (111 / 40) * b * n * √n`
  whenever `20 ≤ b ≤ √n` and `2 * n * √n ≤ b ^ 4`) and
  `theorem_1_2_aux`.
- `Jsp618/Basic.lean` — the statement of `theorem_1_2`.
- `Jsp618/Main618.lean` — the statement and proof of `erdos_618`.

## Building

Lean 4.24.0 (`leanprover/lean4:v4.24.0`, see `lean-toolchain`) with
mathlib v4.24.0 (pinned in `lake-manifest.json`).

```bash
lake build Jsp618
```

## Verification

The project builds with no `sorry`, `admit`, or placeholders, and:

```
#print axioms Jsp618.theorem_1_2
-- 'Jsp618.theorem_1_2' depends on axioms: [propext, Classical.choice, Quot.sound]

#print axioms Jsp618.erdos_618
-- 'Jsp618.erdos_618' depends on axioms: [propext, Classical.choice, Quot.sound]
```

No `sorryAx`. Only Lean's standard axioms.

## Attribution

The mathematical results are Alon's; no claim is made to the
underlying discoveries. The Lean formalization was directed and
commissioned by Yang Liu, partly assisted by AI.
