-- Counting estimates for the random-process half of Alon's proof
-- of Theorem 1.2 (Erdős #618).
--
-- Contents:
-- * the number of `k`-subsets of an `n`-vertex set is at most `2 ^ n`
--   (the union bound over independent sets `U` in `Process.lean`),
-- * twice the number of unordered pairs in a `k`-set is at most `k ^ 2`,
-- * the number of unordered pairs inside a set `U` that share a common
--   neighbour in a graph `H` is at most `n * (maxDeg H).choose 2`
--   (each common neighbour `w` contributes only pairs inside its
--   neighbourhood, and neighbourhoods have at most `maxDeg H` vertices).
--
-- These are the pure counting inputs to the eligible-pair lower bound:
-- the pairs inside `U` number `U.card.choose 2`, of which at most the
-- third bound are "blocked" by a common neighbour.

import Jsp618.Deterministic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Sum

open scoped Classical
open Finset SimpleGraph

namespace Jsp618

/-- The number of `k`-subsets of an `n`-vertex set is at most `2 ^ n`. -/
theorem card_powersetCard_univ_le_two_pow {n k : ℕ} :
    (Finset.univ.powersetCard k (α := Fin n)).card ≤ 2 ^ n := by
  rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  exact Nat.choose_le_two_pow n k

/-- Twice the number of unordered pairs in a `k`-set is at most `k ^ 2`. -/
theorem two_mul_choose_two_le_sq (k : ℕ) : 2 * Nat.choose k 2 ≤ k ^ 2 := by
  rw [Nat.choose_two_right]
  have h1 : 2 * (k * (k - 1) / 2) ≤ k * (k - 1) := by
    rw [Nat.mul_comm 2]
    exact Nat.div_mul_le_self _ _
  have h2 : k * (k - 1) ≤ k ^ 2 := by
    rw [pow_two]
    exact Nat.mul_le_mul_left k (Nat.sub_le k 1)
  exact h1.trans h2

/-- Pairs inside `U` sharing a common neighbour: at most
`n * (maxDeg H).choose 2`. -/
theorem card_pairs_with_common_neighbor_le {n : ℕ} (H : SimpleGraph (Fin n))
    (U : Finset (Fin n)) :
    ((U.powersetCard 2).filter (fun P => ∃ w, P ⊆ H.neighborFinset w)).card ≤
      n * Nat.choose (maxDeg H) 2 := by
  classical
  -- Every such pair lies in the neighbourhood-powerset of its witness.
  have hsub : (U.powersetCard 2).filter (fun P => ∃ w, P ⊆ H.neighborFinset w) ⊆
      Finset.univ.biUnion (fun w => (H.neighborFinset w).powersetCard 2) := by
    intro P hP
    rw [Finset.mem_filter] at hP
    obtain ⟨hPcard, w, hw⟩ := hP
    rw [Finset.mem_biUnion]
    refine ⟨w, Finset.mem_univ w, ?_⟩
    rw [Finset.mem_powersetCard]
    exact ⟨hw, (Finset.mem_powersetCard.mp hPcard).2⟩
  calc ((U.powersetCard 2).filter (fun P => ∃ w, P ⊆ H.neighborFinset w)).card
      ≤ (Finset.univ.biUnion (fun w => (H.neighborFinset w).powersetCard 2)).card :=
        Finset.card_le_card hsub
    _ ≤ ∑ w : Fin n, ((H.neighborFinset w).powersetCard 2).card :=
        Finset.card_biUnion_le
    _ = ∑ w : Fin n, Nat.choose (H.degree w) 2 := by
        apply Finset.sum_congr rfl
        intro w _
        rw [Finset.card_powersetCard, SimpleGraph.card_neighborFinset_eq_degree]
    _ ≤ ∑ _w : Fin n, Nat.choose (maxDeg H) 2 := by
        apply Finset.sum_le_sum
        intro w _
        apply Nat.choose_le_choose
        show H.degree w ≤ Finset.univ.sup (fun v => H.degree v)
        exact Finset.le_sup (f := fun v => H.degree v) (Finset.mem_univ w)
    _ = n * Nat.choose (maxDeg H) 2 := by simp

end Jsp618
