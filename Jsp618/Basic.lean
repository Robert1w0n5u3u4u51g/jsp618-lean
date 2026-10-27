-- Erdős Problem #618 (Erdős–Gyárfás): triangle-free graphs of diameter 2.
--
-- Independent Lean 4 formalization of Noga Alon's theorem
-- *Triangle-free graphs of diameter 2* (Princeton note, `remark1901.pdf`),
-- which settles Erdős Problem #618 in a strong form.
--
-- The basic definitions live in `Defs.lean` (moved there so this file
-- can state the target theorem proved in `Theorem12.lean` without an
-- import cycle). The proof of the theorem below is the auxiliary
-- theorem `theorem_1_2_aux` in `Theorem12.lean`.
--
-- Authorship: formalization directed and commissioned by Yang Liu (Pondy),
-- partly assisted by AI. The mathematical results are Alon's; no claim is
-- made to the underlying discoveries.

import Jsp618.Theorem12

open scoped Classical
open Finset SimpleGraph Asymptotics Filter

namespace Jsp618

/-- **Alon's Theorem 1.2, restated for `0 < ε < 1 / 8`** (the abstract
of the note states it for `ε < 1 / 6`): for every `0 < ε < 1 / 8`
there is `n₀` such that every triangle-free graph on `n ≥ n₀`
vertices with maximum degree at most `n ^ (1 / 2 − ε)` can be turned
into a triangle-free graph of diameter two by adding fewer than
`3 * n ^ (2 − ε)` edges.

The range is `1 / 8`, not `1 / 6`, honestly: this formalization uses
the crude union bound over at most `2 ^ n` independent sets (see
`Counting.lean`), and with that bound the union-bound exponent is
`3 / 2 − 4 * ε`, which beats `n` only for `ε < 1 / 8`. Alon's
`1 / 6` would need the sharper entropy bound
`(n choose 5cn) ≤ 2 ^ (H(5c) n)`. The statement here is therefore
a weakening of Alon's `1 / 6` form, not a claim about it, and
`erdos_618` is not weakened at all: it is proved in `Main618.lean`
from the same general degree-bound lemma, with a varying bound
`b n = max (Δ (G n)) (n ^ (7 / 16))`, not from this theorem at a
fixed `ε` (a fixed `ε` does not suffice: e.g. `Δ = √n / log n`
satisfies `Δ = o(√n)` but violates `Δ ≤ n ^ (1 / 2 - ε)` for every
fixed `ε > 0`). -/
theorem theorem_1_2 (ε : ℝ) (hε : 0 < ε) (hε8 : ε < 1 / 8) :
    ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n → ∀ G : SimpleGraph (Fin n),
      G.CliqueFree 3 →
      (maxDeg G : ℝ) ≤ (n : ℝ) ^ (1 / 2 - ε) →
      (h2 G : ℝ) < 3 * (n : ℝ) ^ (2 - ε) :=
  theorem_1_2_aux ε hε hε8

end Jsp618
