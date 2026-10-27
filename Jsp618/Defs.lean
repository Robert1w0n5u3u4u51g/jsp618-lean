-- Erdős Problem #618 (Erdős–Gyárfás): triangle-free graphs of diameter 2.
--
-- Independent Lean 4 formalization of Noga Alon's theorem
-- *Triangle-free graphs of diameter 2* (Princeton note, `remark1901.pdf`),
-- which settles Erdős Problem #618 in a strong form.
--
-- This file fixes the basic definitions. The target statements are
-- proved in the companion files; see `ROADMAP.md`.
--
-- Authorship: formalization directed and commissioned by Yang Liu (Pondy),
-- partly assisted by AI. The mathematical results are Alon's; no claim is
-- made to the underlying discoveries.
--
-- Note on file layout: the definitions were originally in `Basic.lean`.
-- They were moved here so that `Basic.lean` can state (and prove, from
-- `Theorem12.lean`) the restated `theorem_1_2` without creating an
-- import cycle: `Defs → Deterministic → Counting → Process →
-- Theorem12 → Basic`, and `Theorem12 → Main618`.

import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Sqrt

open scoped Classical
open Finset SimpleGraph Asymptotics Filter

namespace Jsp618

/-- The maximum degree of a graph on `Fin n`. -/
noncomputable def maxDeg {n : ℕ} (G : SimpleGraph (Fin n)) : ℕ :=
  Finset.univ.sup (fun v : Fin n => G.degree v)

/-- `G` has diameter at most two: any two distinct vertices are adjacent
or have a common neighbour. -/
def DiamLETwo {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∀ x y : Fin n, x ≠ y → G.Adj x y ∨ ∃ z, G.Adj x z ∧ G.Adj z y

/-- `h2 G` is the least number of edges whose addition to `G` produces a
triangle-free supergraph of diameter at most two. That such a supergraph
always exists (extend greedily to a maximal triangle-free graph) is part
of what the development proves; the `sInf` is over the set of attainable
counts. -/
noncomputable def h2 {n : ℕ} (G : SimpleGraph (Fin n)) : ℕ :=
  sInf {k : ℕ | ∃ H : SimpleGraph (Fin n),
    G ≤ H ∧ H.CliqueFree 3 ∧ DiamLETwo H ∧
    (H.edgeFinset \ G.edgeFinset).card = k}

end Jsp618
