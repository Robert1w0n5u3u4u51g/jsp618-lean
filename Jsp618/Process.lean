-- The random-process half of Alon's proof of Theorem 1.2 (Erdős #618).
--
-- Alon's process: starting from a triangle-free graph `G` with maximum
-- degree at most `d`, repeatedly add an eligible pair — two distinct
-- vertices, nonadjacent, with no common neighbour, both of degree below
-- the cap `D = 2d`. Every intermediate graph stays triangle-free, and
-- degrees never exceed `D`.
--
-- This file contains the deterministic infrastructure of the process:
-- * the eligible pairs inside a surviving independent set `U`, counted
--   from below (the key inequality of Alon's Claim),
-- * the bound on the number of vertices that ever reach the degree cap,
-- * the process itself (as a fold over a list of ordered choices) and
--   its invariants.
--
-- The remaining analytic step — the counting/union-bound argument that
-- some choice sequence kills every large independent set — is stated as
-- `process_claim` below with its proof strategy; it is the only open
-- piece of this file. The counting lemma behind it is the next step.
--
-- Design note: choices are ORDERED pairs (including the diagonal, which
-- is always a no-op). This avoids all `Sym2`-vs-finset friction, keeps
-- the total number of choices exactly `n ^ 2`, and only costs a factor
-- of 2 in the constants, which Alon's argument has to spare.

import Jsp618.Counting

open scoped Classical
open Finset SimpleGraph

namespace Jsp618

/-- Ordered eligible pairs inside `U`: distinct vertices of `U`,
nonadjacent, with no common neighbour, both of degree below the cap. -/
noncomputable def eligibleOrdered {n : ℕ} (H : SimpleGraph (Fin n)) (D : ℕ)
    (U : Finset (Fin n)) : Finset (Fin n × Fin n) :=
  (U ×ˢ U).filter (fun p =>
    p.1 ≠ p.2 ∧ ¬ H.Adj p.1 p.2 ∧ (∀ w, ¬ (H.Adj p.1 w ∧ H.Adj w p.2)) ∧
      H.degree p.1 < D ∧ H.degree p.2 < D)

/-- Degrees only grow when passing to a supergraph. -/
theorem degree_le_of_le {n : ℕ} {G H : SimpleGraph (Fin n)} (hle : G ≤ H)
    (v : Fin n) : G.degree v ≤ H.degree v := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree,
    ← SimpleGraph.card_neighborFinset_eq_degree]
  apply Finset.card_le_card
  intro w hw
  rw [SimpleGraph.mem_neighborFinset] at hw ⊢
  exact hle hw

/-- Vertices at the cap: `(D - d)` times their number is at most twice
the number of added edges. -/
theorem mul_card_capped_le {n : ℕ} {G H : SimpleGraph (Fin n)} (hle : G ≤ H)
    {d D : ℕ} (hd : ∀ v, G.degree v ≤ d) :
    (D - d) * (Finset.univ.filter (fun v => D ≤ H.degree v)).card ≤
      2 * (H.edgeFinset \ G.edgeFinset).card := by
  classical
  have hdeg : ∀ v, G.degree v ≤ H.degree v := fun v => degree_le_of_le hle v
  have hsum : ∑ v, (H.degree v - G.degree v) = 2 * (H.edgeFinset \ G.edgeFinset).card := by
    rw [Finset.sum_tsub_distrib Finset.univ (fun v _ => hdeg v),
      SimpleGraph.sum_degrees_eq_twice_card_edges,
      SimpleGraph.sum_degrees_eq_twice_card_edges,
      ← Nat.mul_sub_left_distrib, Finset.card_sdiff_of_subset
        (SimpleGraph.edgeFinset_subset_edgeFinset.mpr hle)]
  have hcap : (Finset.univ.filter (fun v => D ≤ H.degree v)).card * (D - d) ≤
      ∑ v ∈ Finset.univ.filter (fun v => D ≤ H.degree v), (H.degree v - G.degree v) := by
    calc (Finset.univ.filter (fun v => D ≤ H.degree v)).card * (D - d)
        = ∑ _v ∈ Finset.univ.filter (fun v => D ≤ H.degree v), (D - d) := by
          rw [Finset.sum_const, smul_eq_mul]
      _ ≤ ∑ v ∈ Finset.univ.filter (fun v => D ≤ H.degree v),
            (H.degree v - G.degree v) := by
          apply Finset.sum_le_sum
          intro v hv
          rw [Finset.mem_filter] at hv
          have hdv := hd v
          omega
  have hle_sum : ∑ v ∈ Finset.univ.filter (fun v => D ≤ H.degree v),
        (H.degree v - G.degree v) ≤ ∑ v, (H.degree v - G.degree v) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun v _ _ => Nat.zero_le _)
  rw [mul_comm (D - d)]
  exact le_trans hcap (le_trans hle_sum (le_of_eq hsum))

/-- Off-diagonal pairs inside `U` number `K * (K - 1)`. -/
theorem card_offDiag {n : ℕ} (U : Finset (Fin n)) :
    ((U ×ˢ U).filter (fun p => p.1 ≠ p.2)).card = U.card * (U.card - 1) := by
  have hpart : ((U ×ˢ U).filter (fun p => p.1 ≠ p.2)).card +
      ((U ×ˢ U).filter (fun p => p.1 = p.2)).card = U.card * U.card := by
    have h := Finset.filter_card_add_filter_neg_card_eq_card (s := U ×ˢ U)
      (fun p => p.1 ≠ p.2)
    rw [Finset.card_product] at h
    have heq : (U ×ˢ U).filter (fun p => ¬ p.1 ≠ p.2) =
        (U ×ˢ U).filter (fun p => p.1 = p.2) := by
      ext ⟨a, b⟩
      simp only [Finset.mem_filter, Finset.mem_product, not_ne_iff]
    rw [heq] at h
    exact h
  have hdiag : ((U ×ˢ U).filter (fun p => p.1 = p.2)).card = U.card := by
    have himg : (U ×ˢ U).filter (fun p => p.1 = p.2) = U.image (fun v => (v, v)) := by
      ext ⟨a, b⟩
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_image]
      constructor
      · rintro ⟨⟨ha, hb⟩, hab⟩
        exact ⟨a, ha, by simp [hab]⟩
      · rintro ⟨v, hv, h⟩
        obtain ⟨rfl, rfl⟩ := Prod.mk_inj.mp h
        exact ⟨⟨hv, hv⟩, rfl⟩
    rw [himg, Finset.card_image_of_injective _
      (fun a b h => (Prod.mk_inj.mp h).1)]
  have hsub : U.card * U.card - U.card = U.card * (U.card - 1) := by
    rw [mul_tsub, mul_one]
  omega

/-- **Eligible pairs inside a surviving independent set, from below.**
Every off-diagonal pair inside `U` is either eligible, shares a common
neighbour, or has a capped endpoint; the last two classes are bounded
by `n * D ^ 2` and `2 * C₀ * K` respectively. -/
theorem card_eligibleOrdered_add_le {n : ℕ} {H : SimpleGraph (Fin n)}
    (hH : H.CliqueFree 3) {D : ℕ} (hD : maxDeg H ≤ D)
    {U : Finset (Fin n)} (hUindep : IsIndep H U)
    {C₀ : ℕ} (hcap : (Finset.univ.filter (fun v => D ≤ H.degree v)).card ≤ C₀) :
    U.card * (U.card - 1) ≤ (eligibleOrdered H D U).card +
      (n * D ^ 2 + 2 * C₀ * U.card) := by
  classical
  -- The off-diagonal pairs split into eligible / blocked.
  have hsplit : (U ×ˢ U).filter (fun p => p.1 ≠ p.2) ⊆
      eligibleOrdered H D U ∪
        ((U ×ˢ U).filter (fun p => p.1 ≠ p.2 ∧
          ∃ w, H.Adj p.1 w ∧ H.Adj w p.2)) ∪
        ((U ×ˢ U).filter (fun p => p.1 ≠ p.2 ∧
          (D ≤ H.degree p.1 ∨ D ≤ H.degree p.2))) := by
    intro p hp
    rw [Finset.mem_filter] at hp
    obtain ⟨hpU, hpne⟩ := hp
    rw [Finset.mem_product] at hpU
    obtain ⟨hp1, hp2⟩ := hpU
    by_cases hadj : H.Adj p.1 p.2
    · exact absurd hadj (hUindep p.1 hp1 p.2 hp2 hpne)
    by_cases hcommon : ∃ w, H.Adj p.1 w ∧ H.Adj w p.2
    · have hmem : p ∈ (U ×ˢ U).filter (fun p => p.1 ≠ p.2 ∧
          ∃ w, H.Adj p.1 w ∧ H.Adj w p.2) :=
        Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hp1, hp2⟩, hpne, hcommon⟩
      exact Finset.mem_union_left _ (Finset.mem_union_right _ hmem)
    by_cases hcap1 : D ≤ H.degree p.1
    · have hmem : p ∈ (U ×ˢ U).filter (fun p => p.1 ≠ p.2 ∧
          (D ≤ H.degree p.1 ∨ D ≤ H.degree p.2)) :=
        Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hp1, hp2⟩, hpne, Or.inl hcap1⟩
      exact Finset.mem_union_right _ hmem
    by_cases hcap2 : D ≤ H.degree p.2
    · have hmem : p ∈ (U ×ˢ U).filter (fun p => p.1 ≠ p.2 ∧
          (D ≤ H.degree p.1 ∨ D ≤ H.degree p.2)) :=
        Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hp1, hp2⟩, hpne, Or.inr hcap2⟩
      exact Finset.mem_union_right _ hmem
    · have hcommon' : ∀ w, ¬ (H.Adj p.1 w ∧ H.Adj w p.2) :=
        fun w hw => hcommon ⟨w, hw⟩
      have helig : p ∈ eligibleOrdered H D U :=
        Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hp1, hp2⟩, hpne, hadj, hcommon',
          Nat.lt_of_not_le hcap1, Nat.lt_of_not_le hcap2⟩
      exact Finset.mem_union_left _ (Finset.mem_union_left _ helig)
  -- Common-neighbour pairs: at most `n * D ^ 2`.
  have hcommon_le : ((U ×ˢ U).filter (fun p => p.1 ≠ p.2 ∧
      ∃ w, H.Adj p.1 w ∧ H.Adj w p.2)).card ≤ n * D ^ 2 := by
    have hsub : (U ×ˢ U).filter (fun p => p.1 ≠ p.2 ∧
        ∃ w, H.Adj p.1 w ∧ H.Adj w p.2) ⊆
        Finset.univ.biUnion (fun w =>
          (H.neighborFinset w ∩ U) ×ˢ (H.neighborFinset w ∩ U)) := by
      intro p hp
      rw [Finset.mem_filter] at hp
      obtain ⟨hpU, -, w, hw1, hw2⟩ := hp
      rw [Finset.mem_product] at hpU
      rw [Finset.mem_biUnion]
      refine ⟨w, Finset.mem_univ w, Finset.mem_product.mpr ⟨?_, ?_⟩⟩
      · exact Finset.mem_inter.mpr ⟨by rw [SimpleGraph.mem_neighborFinset]; exact hw1.symm, hpU.1⟩
      · exact Finset.mem_inter.mpr ⟨by rw [SimpleGraph.mem_neighborFinset]; exact hw2, hpU.2⟩
    calc ((U ×ˢ U).filter (fun p => p.1 ≠ p.2 ∧
          ∃ w, H.Adj p.1 w ∧ H.Adj w p.2)).card
        ≤ (Finset.univ.biUnion (fun w =>
            (H.neighborFinset w ∩ U) ×ˢ (H.neighborFinset w ∩ U))).card :=
          Finset.card_le_card hsub
      _ ≤ ∑ w : Fin n, ((H.neighborFinset w ∩ U) ×ˢ
            (H.neighborFinset w ∩ U)).card := Finset.card_biUnion_le
      _ ≤ ∑ _w : Fin n, D ^ 2 := by
          apply Finset.sum_le_sum
          intro w _
          rw [Finset.card_product]
          have hw1 : (H.neighborFinset w ∩ U).card ≤ D := by
            calc (H.neighborFinset w ∩ U).card ≤ (H.neighborFinset w).card :=
                  Finset.card_le_card Finset.inter_subset_left
              _ = H.degree w := by rw [SimpleGraph.card_neighborFinset_eq_degree]
              _ ≤ maxDeg H := by
                  show H.degree w ≤ Finset.univ.sup (fun v => H.degree v)
                  exact Finset.le_sup (f := fun v => H.degree v) (Finset.mem_univ w)
              _ ≤ D := hD
          have hw2 := hw1
          calc (H.neighborFinset w ∩ U).card * (H.neighborFinset w ∩ U).card
              ≤ D * D := Nat.mul_le_mul hw1 hw2
            _ = D ^ 2 := by rw [pow_two]
      _ = n * D ^ 2 := by simp
  -- Capped-endpoint pairs: at most `2 * C₀ * K`.
  have hcapped_le : ((U ×ˢ U).filter (fun p => p.1 ≠ p.2 ∧
      (D ≤ H.degree p.1 ∨ D ≤ H.degree p.2))).card ≤ 2 * C₀ * U.card := by
    have hsub : (U ×ˢ U).filter (fun p => p.1 ≠ p.2 ∧
        (D ≤ H.degree p.1 ∨ D ≤ H.degree p.2)) ⊆
        ((Finset.univ.filter (fun v => D ≤ H.degree v)) ×ˢ U) ∪
          (U ×ˢ (Finset.univ.filter (fun v => D ≤ H.degree v))) := by
      intro p hp
      rw [Finset.mem_filter] at hp
      obtain ⟨hpU, -, hor⟩ := hp
      rw [Finset.mem_product] at hpU
      rcases hor with hor | hor
      · exact Finset.mem_union_left _
          (Finset.mem_product.mpr ⟨Finset.mem_filter.mpr
            ⟨Finset.mem_univ _, hor⟩, hpU.2⟩)
      · exact Finset.mem_union_right _
          (Finset.mem_product.mpr ⟨hpU.1, Finset.mem_filter.mpr
            ⟨Finset.mem_univ _, hor⟩⟩)
    calc ((U ×ˢ U).filter (fun p => p.1 ≠ p.2 ∧
          (D ≤ H.degree p.1 ∨ D ≤ H.degree p.2))).card
        ≤ (((Finset.univ.filter (fun v => D ≤ H.degree v)) ×ˢ U) ∪
            (U ×ˢ (Finset.univ.filter (fun v => D ≤ H.degree v)))).card :=
          Finset.card_le_card hsub
      _ ≤ ((Finset.univ.filter (fun v => D ≤ H.degree v)) ×ˢ U).card +
            (U ×ˢ (Finset.univ.filter (fun v => D ≤ H.degree v))).card :=
          Finset.card_union_le _ _
      _ ≤ C₀ * U.card + U.card * C₀ := by
          apply Nat.add_le_add
          · rw [Finset.card_product]
            exact Nat.mul_le_mul_right _ hcap
          · rw [Finset.card_product]
            exact Nat.mul_le_mul_left _ hcap
      _ = 2 * C₀ * U.card := by ring
  calc U.card * (U.card - 1)
      = ((U ×ˢ U).filter (fun p => p.1 ≠ p.2)).card := (card_offDiag U).symm
    _ ≤ (eligibleOrdered H D U ∪
          ((U ×ˢ U).filter (fun p => p.1 ≠ p.2 ∧
            ∃ w, H.Adj p.1 w ∧ H.Adj w p.2)) ∪
          ((U ×ˢ U).filter (fun p => p.1 ≠ p.2 ∧
            (D ≤ H.degree p.1 ∨ D ≤ H.degree p.2)))).card :=
        Finset.card_le_card hsplit
    _ ≤ (eligibleOrdered H D U).card +
          (((U ×ˢ U).filter (fun p => p.1 ≠ p.2 ∧
            ∃ w, H.Adj p.1 w ∧ H.Adj w p.2)).card +
          ((U ×ˢ U).filter (fun p => p.1 ≠ p.2 ∧
            (D ≤ H.degree p.1 ∨ D ≤ H.degree p.2))).card) := by
        have h1 := Finset.card_union_le (eligibleOrdered H D U ∪
          ((U ×ˢ U).filter (fun p => p.1 ≠ p.2 ∧
            ∃ w, H.Adj p.1 w ∧ H.Adj w p.2)))
          ((U ×ˢ U).filter (fun p => p.1 ≠ p.2 ∧
            (D ≤ H.degree p.1 ∨ D ≤ H.degree p.2)))
        have h2 := Finset.card_union_le (eligibleOrdered H D U)
          ((U ×ˢ U).filter (fun p => p.1 ≠ p.2 ∧
            ∃ w, H.Adj p.1 w ∧ H.Adj w p.2))
        omega
    _ ≤ (eligibleOrdered H D U).card + (n * D ^ 2 + 2 * C₀ * U.card) :=
        Nat.add_le_add_left (Nat.add_le_add hcommon_le hcapped_le) _

/-- One step of the process: add the ordered pair if it is eligible in
the current graph, otherwise do nothing. -/
noncomputable def step {n : ℕ} (H : SimpleGraph (Fin n)) (D : ℕ)
    (p : Fin n × Fin n) : SimpleGraph (Fin n) :=
  if h : p.1 ≠ p.2 ∧ ¬ H.Adj p.1 p.2 ∧ (∀ w, ¬ (H.Adj p.1 w ∧ H.Adj w p.2)) ∧
      H.degree p.1 < D ∧ H.degree p.2 < D
  then addEdge H p.1 p.2 h.1
  else H

/-- Run the process over a list of ordered choices. -/
noncomputable def run {n : ℕ} (G : SimpleGraph (Fin n)) (D : ℕ) :
    List (Fin n × Fin n) → SimpleGraph (Fin n)
  | [] => G
  | p :: ps => run (step G D p) D ps

/-- The step equation in the eligible case. -/
theorem step_eq_addEdge {n : ℕ} {H : SimpleGraph (Fin n)} {D : ℕ}
    {p : Fin n × Fin n}
    (hc : p.1 ≠ p.2 ∧ ¬ H.Adj p.1 p.2 ∧ (∀ w, ¬ (H.Adj p.1 w ∧ H.Adj w p.2)) ∧
      H.degree p.1 < D ∧ H.degree p.2 < D) :
    step H D p = addEdge H p.1 p.2 hc.1 := by
  unfold step
  rw [dif_pos hc]

/-- The step equation in the ineligible case. -/
theorem step_eq_self {n : ℕ} {H : SimpleGraph (Fin n)} {D : ℕ}
    {p : Fin n × Fin n}
    (hc : ¬ (p.1 ≠ p.2 ∧ ¬ H.Adj p.1 p.2 ∧ (∀ w, ¬ (H.Adj p.1 w ∧ H.Adj w p.2)) ∧
      H.degree p.1 < D ∧ H.degree p.2 < D)) :
    step H D p = H := by
  unfold step
  rw [dif_neg hc]

/-- A step never removes edges. -/
theorem le_step {n : ℕ} {H : SimpleGraph (Fin n)} {D : ℕ}
    (p : Fin n × Fin n) : H ≤ step H D p := by
  by_cases hc : p.1 ≠ p.2 ∧ ¬ H.Adj p.1 p.2 ∧ (∀ w, ¬ (H.Adj p.1 w ∧ H.Adj w p.2)) ∧
      H.degree p.1 < D ∧ H.degree p.2 < D
  · rw [step_eq_addEdge hc]
    exact le_addEdge hc.1
  · rw [step_eq_self hc]

/-- The process never removes edges. -/
theorem le_run {n : ℕ} {G : SimpleGraph (Fin n)} {D : ℕ}
    (ps : List (Fin n × Fin n)) : G ≤ run G D ps := by
  induction ps generalizing G with
  | nil => exact le_rfl
  | cons p ps ih => exact le_trans (le_step p) (ih)

/-- A step preserves triangle-freeness: the only new edge is eligible,
and an eligible edge cannot close a triangle. -/
theorem cliqueFree_step {n : ℕ} {H : SimpleGraph (Fin n)} {D : ℕ}
    (hH : H.CliqueFree 3) (p : Fin n × Fin n) :
    (step H D p).CliqueFree 3 := by
  by_cases hc : p.1 ≠ p.2 ∧ ¬ H.Adj p.1 p.2 ∧ (∀ w, ¬ (H.Adj p.1 w ∧ H.Adj w p.2)) ∧
      H.degree p.1 < D ∧ H.degree p.2 < D
  · rw [step_eq_addEdge hc]
    by_contra hcon
    obtain ⟨z, hz1, hz2⟩ :=
      exists_common_neighbor_of_not_cliqueFree_addEdge hH hc.1 hcon
    exact hc.2.2.1 z ⟨hz1, hz2⟩
  · rw [step_eq_self hc]
    exact hH

/-- The process preserves triangle-freeness. -/
theorem cliqueFree_run {n : ℕ} {G : SimpleGraph (Fin n)} {D : ℕ}
    (hG : G.CliqueFree 3) (ps : List (Fin n × Fin n)) :
    (run G D ps).CliqueFree 3 := by
  induction ps generalizing G with
  | nil => exact hG
  | cons p ps ih => exact ih (cliqueFree_step hG p)

/-- Neighbours added by one edge: at the first endpoint, only the second
endpoint can be new. -/
theorem neighborFinset_addEdge_left_subset {n : ℕ} {H : SimpleGraph (Fin n)}
    {x y : Fin n} (hxy : x ≠ y) :
    (addEdge H x y hxy).neighborFinset x ⊆ insert y (H.neighborFinset x) := by
  intro w hw
  rw [SimpleGraph.mem_neighborFinset, adj_addEdge_iff hxy] at hw
  rcases hw with hw | ⟨-, rfl⟩ | ⟨h1, -⟩
  · exact Finset.mem_insert_of_mem (by rw [SimpleGraph.mem_neighborFinset]; exact hw)
  · exact Finset.mem_insert_self _ _
  · exact absurd h1 hxy

/-- Same, at the second endpoint. -/
theorem neighborFinset_addEdge_right_subset {n : ℕ} {H : SimpleGraph (Fin n)}
    {x y : Fin n} (hxy : x ≠ y) :
    (addEdge H x y hxy).neighborFinset y ⊆ insert x (H.neighborFinset y) := by
  intro w hw
  rw [SimpleGraph.mem_neighborFinset, adj_addEdge_iff hxy] at hw
  rcases hw with hw | ⟨h1, -⟩ | ⟨-, rfl⟩
  · exact Finset.mem_insert_of_mem (by rw [SimpleGraph.mem_neighborFinset]; exact hw)
  · exact absurd h1 hxy.symm
  · exact Finset.mem_insert_self _ _

/-- Away from the new edge, neighbourhoods do not change. -/
theorem neighborFinset_addEdge_of_ne {n : ℕ} {H : SimpleGraph (Fin n)}
    {x y v : Fin n} (hxy : x ≠ y) (hv1 : v ≠ x) (hv2 : v ≠ y) :
    (addEdge H x y hxy).neighborFinset v ⊆ H.neighborFinset v := by
  intro w hw
  rw [SimpleGraph.mem_neighborFinset, adj_addEdge_iff hxy] at hw
  rw [SimpleGraph.mem_neighborFinset]
  rcases hw with hw | ⟨h1, -⟩ | ⟨h1, -⟩
  · exact hw
  · exact absurd h1 hv1
  · exact absurd h1 hv2

/-- A step keeps all degrees at most the cap. -/
theorem degree_step_le {n : ℕ} {H : SimpleGraph (Fin n)} {D : ℕ}
    (hD : ∀ v, H.degree v ≤ D) (p : Fin n × Fin n) :
    ∀ v, (step H D p).degree v ≤ D := by
  intro v
  by_cases hc : p.1 ≠ p.2 ∧ ¬ H.Adj p.1 p.2 ∧ (∀ w, ¬ (H.Adj p.1 w ∧ H.Adj w p.2)) ∧
      H.degree p.1 < D ∧ H.degree p.2 < D
  · have hdx : H.degree p.1 < D := hc.2.2.2.1
    have hdy : H.degree p.2 < D := hc.2.2.2.2
    rw [step_eq_addEdge hc]
    by_cases hvx : v = p.1
    · subst hvx
      rw [← SimpleGraph.card_neighborFinset_eq_degree]
      calc ((addEdge H p.1 p.2 hc.1).neighborFinset p.1).card
          ≤ (insert p.2 (H.neighborFinset p.1)).card :=
            Finset.card_le_card (neighborFinset_addEdge_left_subset hc.1)
        _ ≤ (H.neighborFinset p.1).card + 1 := Finset.card_insert_le _ _
        _ = H.degree p.1 + 1 := by rw [SimpleGraph.card_neighborFinset_eq_degree]
        _ ≤ D := by omega
    · by_cases hvy : v = p.2
      · subst hvy
        rw [← SimpleGraph.card_neighborFinset_eq_degree]
        calc ((addEdge H p.1 p.2 hc.1).neighborFinset p.2).card
            ≤ (insert p.1 (H.neighborFinset p.2)).card :=
              Finset.card_le_card (neighborFinset_addEdge_right_subset hc.1)
          _ ≤ (H.neighborFinset p.2).card + 1 := Finset.card_insert_le _ _
          _ = H.degree p.2 + 1 := by rw [SimpleGraph.card_neighborFinset_eq_degree]
          _ ≤ D := by omega
      · rw [← SimpleGraph.card_neighborFinset_eq_degree]
        exact le_trans (Finset.card_le_card
          (neighborFinset_addEdge_of_ne hc.1 hvx hvy))
          (by rw [SimpleGraph.card_neighborFinset_eq_degree]; exact hD v)
  · rw [step_eq_self hc]
    exact hD v

/-- The process keeps all degrees at most the cap. -/
theorem degree_run_le {n : ℕ} {G : SimpleGraph (Fin n)} {D : ℕ}
    (hD : ∀ v, G.degree v ≤ D) (ps : List (Fin n × Fin n)) :
    ∀ v, (run G D ps).degree v ≤ D := by
  induction ps generalizing G with
  | nil => exact hD
  | cons p ps ih => exact ih (degree_step_le hD p)

/-- A step adds at most one new edge. -/
theorem card_edgeFinset_step_le {n : ℕ} {H : SimpleGraph (Fin n)} {D : ℕ}
    (p : Fin n × Fin n) :
    ((step H D p).edgeFinset \ H.edgeFinset).card ≤ 1 := by
  by_cases hc : p.1 ≠ p.2 ∧ ¬ H.Adj p.1 p.2 ∧ (∀ w, ¬ (H.Adj p.1 w ∧ H.Adj w p.2)) ∧
      H.degree p.1 < D ∧ H.degree p.2 < D
  · rw [step_eq_addEdge hc]
    -- Pointwise degree bound.
    have hpoint : ∀ v, (addEdge H p.1 p.2 hc.1).degree v ≤ H.degree v +
        (if v = p.1 then 1 else 0) + (if v = p.2 then 1 else 0) := by
      intro v
      by_cases hvx : v = p.1
      · subst hvx
        have h1 : (addEdge H p.1 p.2 hc.1).degree p.1 ≤ H.degree p.1 + 1 :=
          le_trans (Finset.card_le_card (neighborFinset_addEdge_left_subset hc.1))
            (Finset.card_insert_le _ _)
        rw [if_pos rfl, if_neg hc.1]
        omega
      · by_cases hvy : v = p.2
        · subst hvy
          have h2 : (addEdge H p.1 p.2 hc.1).degree p.2 ≤ H.degree p.2 + 1 :=
            le_trans (Finset.card_le_card (neighborFinset_addEdge_right_subset hc.1))
              (Finset.card_insert_le _ _)
          rw [if_neg (Ne.symm hc.1), if_pos rfl]
          omega
        · have h3 : (addEdge H p.1 p.2 hc.1).degree v ≤ H.degree v :=
            Finset.card_le_card (neighborFinset_addEdge_of_ne hc.1 hvx hvy)
          rw [if_neg hvx, if_neg hvy]
          omega
    have hsum : ∑ v, (addEdge H p.1 p.2 hc.1).degree v ≤ ∑ v, H.degree v + 2 := by
      calc ∑ v, (addEdge H p.1 p.2 hc.1).degree v
          ≤ ∑ v, (H.degree v + (if v = p.1 then 1 else 0) + (if v = p.2 then 1 else 0)) :=
            Finset.sum_le_sum (fun v _ => hpoint v)
        _ = ∑ v, H.degree v + 2 := by
            rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
              Finset.sum_ite_eq', Finset.sum_ite_eq']
            simp
    have hcard : (addEdge H p.1 p.2 hc.1).edgeFinset.card ≤ H.edgeFinset.card + 1 := by
      have h1 := SimpleGraph.sum_degrees_eq_twice_card_edges (G := addEdge H p.1 p.2 hc.1)
      have h2 := SimpleGraph.sum_degrees_eq_twice_card_edges (G := H)
      omega
    have hsdiff : ((addEdge H p.1 p.2 hc.1).edgeFinset \ H.edgeFinset).card =
        (addEdge H p.1 p.2 hc.1).edgeFinset.card - H.edgeFinset.card :=
      Finset.card_sdiff_of_subset (SimpleGraph.edgeFinset_subset_edgeFinset.mpr (le_addEdge hc.1))
    omega
  · rw [step_eq_self hc]
    simp

/-- The process adds at most one edge per choice. -/
theorem card_edgeFinset_run_le {n : ℕ} {G : SimpleGraph (Fin n)} {D : ℕ}
    (ps : List (Fin n × Fin n)) :
    ((run G D ps).edgeFinset \ G.edgeFinset).card ≤ ps.length := by
  induction ps generalizing G with
  | nil =>
    have hrun : run G D [] = G := rfl
    rw [hrun]
    simp
  | cons p ps ih =>
    have h1 : ((run (step G D p) D ps).edgeFinset \ G.edgeFinset).card ≤
        ((run (step G D p) D ps).edgeFinset \ (step G D p).edgeFinset).card +
          ((step G D p).edgeFinset \ G.edgeFinset).card := by
      have hsub : (run (step G D p) D ps).edgeFinset \ G.edgeFinset ⊆
          ((run (step G D p) D ps).edgeFinset \ (step G D p).edgeFinset) ∪
            ((step G D p).edgeFinset \ G.edgeFinset) := by
        intro e he
        rw [Finset.mem_sdiff] at he
        by_cases he' : e ∈ (step G D p).edgeFinset
        · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨he', he.2⟩)
        · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨he.1, he'⟩)
      exact le_trans (Finset.card_le_card hsub) (Finset.card_union_le _ _)
    calc ((run (step G D p) D ps).edgeFinset \ G.edgeFinset).card
        ≤ ps.length + 1 := le_trans h1 (Nat.add_le_add (ih) (card_edgeFinset_step_le p))
      _ = (p :: ps).length := by simp

/-- A vertex's degree is at most the maximum degree. -/
theorem degree_le_maxDeg {n : ℕ} {H : SimpleGraph (Fin n)} (v : Fin n) :
    H.degree v ≤ maxDeg H := by
  show H.degree v ≤ Finset.univ.sup (fun v => H.degree v)
  exact Finset.le_sup (f := fun w => H.degree w) (Finset.mem_univ v)

/-- If the first choice is eligible inside `U`, the resulting graph
is no longer independent on `U`: the chosen edge itself lies in `U`. -/
theorem not_isIndep_step_of_mem_eligible {n : ℕ} {H : SimpleGraph (Fin n)}
    {D : ℕ} {U : Finset (Fin n)} {p : Fin n × Fin n}
    (hp : p ∈ eligibleOrdered H D U) : ¬ IsIndep (step H D p) U := by
  have hp' : p ∈ (U ×ˢ U).filter (fun q =>
      q.1 ≠ q.2 ∧ ¬ H.Adj q.1 q.2 ∧ (∀ w, ¬ (H.Adj q.1 w ∧ H.Adj w q.2)) ∧
        H.degree q.1 < D ∧ H.degree q.2 < D) := hp
  rw [Finset.mem_filter, Finset.mem_product] at hp'
  obtain ⟨⟨hp1, hp2⟩, hpne, hadj, hcommon, hd1, hd2⟩ := hp'
  intro hindep
  have hstep : step H D p = addEdge H p.1 p.2 hpne :=
    step_eq_addEdge ⟨hpne, hadj, hcommon, hd1, hd2⟩
  have hadj' : (step H D p).Adj p.1 p.2 := by
    rw [hstep]
    exact Or.inr (Or.inl ⟨rfl, rfl⟩)
  exact hindep p.1 hp1 p.2 hp2 hpne hadj'

/-- One step adds at most one edge to the edge-set difference from `G`. -/
theorem card_edgeFinset_step_sdiff_le {n : ℕ} {G H : SimpleGraph (Fin n)}
    (hle : G ≤ H) {D : ℕ} (p : Fin n × Fin n) :
    ((step H D p).edgeFinset \ G.edgeFinset).card ≤
      (H.edgeFinset \ G.edgeFinset).card + 1 := by
  have hsub : (step H D p).edgeFinset \ G.edgeFinset ⊆
      ((step H D p).edgeFinset \ H.edgeFinset) ∪ (H.edgeFinset \ G.edgeFinset) := by
    intro e he
    rw [Finset.mem_sdiff] at he
    by_cases he' : e ∈ H.edgeFinset
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨he', he.2⟩)
    · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨he.1, he'⟩)
  calc ((step H D p).edgeFinset \ G.edgeFinset).card
      ≤ (((step H D p).edgeFinset \ H.edgeFinset) ∪
          (H.edgeFinset \ G.edgeFinset)).card := Finset.card_le_card hsub
    _ ≤ ((step H D p).edgeFinset \ H.edgeFinset).card +
          (H.edgeFinset \ G.edgeFinset).card := Finset.card_union_le _ _
    _ ≤ 1 + (H.edgeFinset \ G.edgeFinset).card :=
        Nat.add_le_add_right (card_edgeFinset_step_le p) _
    _ = (H.edgeFinset \ G.edgeFinset).card + 1 := by rw [Nat.add_comm]

/-- A step keeps the maximum degree at most the cap. -/
theorem maxDeg_step_le {n : ℕ} {H : SimpleGraph (Fin n)} {D : ℕ}
    (hD : maxDeg H ≤ D) (p : Fin n × Fin n) : maxDeg (step H D p) ≤ D := by
  show Finset.univ.sup (fun v => (step H D p).degree v) ≤ D
  apply Finset.sup_le
  intro v _
  exact degree_step_le (fun v => (degree_le_maxDeg v).trans hD) p v

/-- The embedding of tail sequences under a fixed first choice. -/
noncomputable def consEmb {n r : ℕ} (p : Fin n × Fin n) :
    (Fin r → Fin n × Fin n) ↪ (Fin (r + 1) → Fin n × Fin n) where
  toFun g := Fin.cons (α := fun _ : Fin (r + 1) => Fin n × Fin n) p g
  inj' := by
    intro a b h
    have h2 := congrArg (Fin.tail (α := fun _ : Fin (r + 1) => Fin n × Fin n)) h
    simpa [Fin.tail_cons] using h2

/-- Consing the head and tail of a sequence recovers the sequence. -/
theorem consEmb_tail {n r : ℕ} (f : Fin (r + 1) → Fin n × Fin n) :
    consEmb (f 0) (Fin.tail f) = f := by
  show Fin.cons (α := fun _ : Fin (r + 1) => Fin n × Fin n) (f 0) (Fin.tail f) = f
  exact Fin.cons_self_tail f

/-- **Counting lemma for the process claim.** Fix a `K`-set `U`.
If every stage `H` (a triangle-free supergraph of `G` with maximum
degree at most `2d` and at most `m0` added edges) has at least `L`
eligible ordered pairs inside every surviving `K`-set, then the number
of `r`-choice sequences that keep `U` alive is at most `(n ^ 2 - L) ^ r`.
Proof: induct on `r`, splitting by the first choice. A first choice
eligible inside `U` kills `U` outright (the chosen edge lands in `U`);
every other first choice leaves at most `(n ^ 2 - L) ^ r` tails by the
induction hypothesis, and there are at most `n ^ 2 - L` such choices
(the eligible ones, at least `L` of them, are excluded). -/
theorem surviving_card_le {n : ℕ} {G : SimpleGraph (Fin n)} (hG : G.CliqueFree 3)
    {d K L m0 : ℕ}
    (hL : ∀ H : SimpleGraph (Fin n), G ≤ H → H.CliqueFree 3 → maxDeg H ≤ 2 * d →
      (H.edgeFinset \ G.edgeFinset).card ≤ m0 →
      ∀ U : Finset (Fin n), U.card = K → IsIndep H U →
        L ≤ (eligibleOrdered H (2 * d) U).card) :
    ∀ (r : ℕ) (H : SimpleGraph (Fin n)), G ≤ H → H.CliqueFree 3 → maxDeg H ≤ 2 * d →
      (H.edgeFinset \ G.edgeFinset).card + r ≤ m0 →
      ∀ U : Finset (Fin n), U.card = K →
        (Finset.univ.filter (fun f : Fin r → Fin n × Fin n =>
          IsIndep (run H (2 * d) (List.ofFn f)) U)).card ≤ (n * n - L) ^ r := by
  intro r
  induction r with
  | zero =>
    intro H _ _ _ _ U _
    calc (Finset.univ.filter (fun f : Fin 0 → Fin n × Fin n =>
            IsIndep (run H (2 * d) (List.ofFn f)) U)).card
        ≤ Finset.univ.card := Finset.card_filter_le _ _
      _ = 1 := by simp
      _ = (n * n - L) ^ 0 := by simp
  | succ r ih =>
    intro H hGH hH hmax hedge U hUK
    by_cases hU : IsIndep H U
    · have hedge0 : (H.edgeFinset \ G.edgeFinset).card ≤ m0 := by omega
      have hLelig : L ≤ (eligibleOrdered H (2 * d) U).card :=
        hL H hGH hH hmax hedge0 U hUK hU
      have hsub : Finset.univ.filter (fun f : Fin (r + 1) → Fin n × Fin n =>
          IsIndep (run H (2 * d) (List.ofFn f)) U) ⊆
          Finset.univ.biUnion (fun p : Fin n × Fin n =>
            (Finset.univ.filter (fun g : Fin r → Fin n × Fin n =>
              IsIndep (run (step H (2 * d) p) (2 * d) (List.ofFn g)) U)).map
              (consEmb p)) := by
        intro f hf
        rw [Finset.mem_filter] at hf
        rw [Finset.mem_biUnion]
        refine ⟨f 0, Finset.mem_univ _,
          Finset.mem_map.mpr ⟨Fin.tail f, ?_, consEmb_tail f⟩⟩
        rw [Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_⟩
        have hrun : run H (2 * d) (List.ofFn f) =
            run (step H (2 * d) (f 0)) (2 * d) (List.ofFn (Fin.tail f)) := by
          have h1 : List.ofFn f = List.ofFn (Fin.cons (f 0) (Fin.tail f)) := by
            rw [Fin.cons_self_tail]
          rw [h1, List.ofFn_cons]
          simp [run]
        rw [hrun] at hf
        exact hf.2
      have hcard : (Finset.univ.filter (fun f : Fin (r + 1) → Fin n × Fin n =>
          IsIndep (run H (2 * d) (List.ofFn f)) U)).card ≤
          ∑ p : Fin n × Fin n, (Finset.univ.filter (fun g : Fin r → Fin n × Fin n =>
            IsIndep (run (step H (2 * d) p) (2 * d) (List.ofFn g)) U)).card := by
        calc (Finset.univ.filter (fun f : Fin (r + 1) → Fin n × Fin n =>
              IsIndep (run H (2 * d) (List.ofFn f)) U)).card
            ≤ (Finset.univ.biUnion (fun p : Fin n × Fin n =>
                (Finset.univ.filter (fun g : Fin r → Fin n × Fin n =>
                  IsIndep (run (step H (2 * d) p) (2 * d) (List.ofFn g)) U)).map
                  (consEmb p))).card :=
              Finset.card_le_card hsub
          _ ≤ ∑ p ∈ Finset.univ, ((Finset.univ.filter (fun g : Fin r → Fin n × Fin n =>
                IsIndep (run (step H (2 * d) p) (2 * d) (List.ofFn g)) U)).map
                (consEmb p)).card :=
              Finset.card_biUnion_le
          _ = ∑ p : Fin n × Fin n, (Finset.univ.filter (fun g : Fin r → Fin n × Fin n =>
                IsIndep (run (step H (2 * d) p) (2 * d) (List.ofFn g)) U)).card := by
              apply Finset.sum_congr rfl
              intro p _
              rw [Finset.card_map]
      have htail : ∀ p : Fin n × Fin n,
          (Finset.univ.filter (fun g : Fin r → Fin n × Fin n =>
            IsIndep (run (step H (2 * d) p) (2 * d) (List.ofFn g)) U)).card ≤
            (if p ∈ eligibleOrdered H (2 * d) U then 0 else (n * n - L) ^ r) := by
        intro p
        by_cases hp : p ∈ eligibleOrdered H (2 * d) U
        · rw [if_pos hp]
          have hfilter : Finset.univ.filter (fun g : Fin r → Fin n × Fin n =>
              IsIndep (run (step H (2 * d) p) (2 * d) (List.ofFn g)) U) = ∅ := by
            rw [Finset.eq_empty_iff_forall_notMem]
            intro g hg
            rw [Finset.mem_filter] at hg
            exact not_isIndep_step_of_mem_eligible hp
              (isIndep_of_le (le_run (List.ofFn g)) hg.2)
          rw [hfilter]
          simp
        · rw [if_neg hp]
          apply ih (step H (2 * d) p)
          · exact le_trans hGH (le_step p)
          · exact cliqueFree_step hH p
          · exact maxDeg_step_le hmax p
          · have h1 := card_edgeFinset_step_sdiff_le hGH (D := 2 * d) p
            omega
          · exact hUK
      have hsum : (∑ p : Fin n × Fin n, (Finset.univ.filter (fun g : Fin r → Fin n × Fin n =>
          IsIndep (run (step H (2 * d) p) (2 * d) (List.ofFn g)) U)).card) ≤
          (n * n - L) * (n * n - L) ^ r := by
        calc (∑ p : Fin n × Fin n, (Finset.univ.filter (fun g : Fin r → Fin n × Fin n =>
              IsIndep (run (step H (2 * d) p) (2 * d) (List.ofFn g)) U)).card)
            ≤ ∑ p : Fin n × Fin n,
                (if p ∈ eligibleOrdered H (2 * d) U then 0 else (n * n - L) ^ r) :=
              Finset.sum_le_sum (fun p _ => htail p)
          _ = (Finset.univ.filter (fun p => p ∉ eligibleOrdered H (2 * d) U)).card *
                (n * n - L) ^ r := by
              calc (∑ p : Fin n × Fin n,
                    (if p ∈ eligibleOrdered H (2 * d) U then 0 else (n * n - L) ^ r))
                  = ∑ p : Fin n × Fin n,
                      (if p ∉ eligibleOrdered H (2 * d) U then (n * n - L) ^ r else 0) := by
                    apply Finset.sum_congr rfl
                    intro p _
                    by_cases hp : p ∈ eligibleOrdered H (2 * d) U <;> simp [hp]
                _ = ∑ p ∈ Finset.univ.filter (fun p => p ∉ eligibleOrdered H (2 * d) U),
                      (n * n - L) ^ r := (Finset.sum_filter (fun p => p ∉ eligibleOrdered H (2 * d) U) (fun _ => (n * n - L) ^ r)).symm
                _ = (Finset.univ.filter (fun p => p ∉ eligibleOrdered H (2 * d) U)).card *
                      (n * n - L) ^ r := by
                    rw [Finset.sum_const, smul_eq_mul]
          _ ≤ (n * n - L) * (n * n - L) ^ r := by
              apply Nat.mul_le_mul_right
              have hcardU : (Finset.univ : Finset (Fin n × Fin n)).card = n * n := by simp
              have hset : Finset.univ.filter (fun p => p ∉ eligibleOrdered H (2 * d) U) =
                  Finset.univ \ eligibleOrdered H (2 * d) U := by
                ext p
                simp
              rw [hset, Finset.card_sdiff_of_subset (Finset.subset_univ _), hcardU]
              exact Nat.sub_le_sub_left hLelig _
      calc (Finset.univ.filter (fun f : Fin (r + 1) → Fin n × Fin n =>
            IsIndep (run H (2 * d) (List.ofFn f)) U)).card
          ≤ (n * n - L) * (n * n - L) ^ r := le_trans hcard hsum
        _ = (n * n - L) ^ (r + 1) := by rw [pow_succ, Nat.mul_comm]
    · have hfilter : Finset.univ.filter (fun f : Fin (r + 1) → Fin n × Fin n =>
          IsIndep (run H (2 * d) (List.ofFn f)) U) = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro f hf
        rw [Finset.mem_filter] at hf
        exact hU (isIndep_of_le (le_run (List.ofFn f)) hf.2)
      rw [hfilter]
      simp

/-- **Process claim.** If every surviving `K`-set has at least `L`
eligible ordered pairs at every stage, and the crude union bound
`2 ^ n * ((n ^ 2 - L) / n ^ 2) ^ m < 1` holds, then some `m`-choice
sequence leaves no independent `K`-set alive.
The proof counts choice sequences: for a fixed `U`, at most
`(n ^ 2 - L) ^ m` sequences keep `U` alive (the counting lemma above),
and there are at most `2 ^ n` sets `U` of size `K` (Counting.lean), so
the number of sequences where some `K`-set survives is at most
`2 ^ n * (n ^ 2 - L) ^ m`, strictly less than the total `(n ^ 2) ^ m`
exactly when the stated inequality holds. The surviving run is the
required `H`.
Note: the hypothesis `0 < n` excludes the degenerate corner `n = 0`,
`K = 0`, where the claim as stated is false (the empty set is always
independent, yet the inequality can hold vacuously); the intended
application has `n` large, so this costs nothing. -/
theorem process_claim {n : ℕ} {G : SimpleGraph (Fin n)} (hG : G.CliqueFree 3)
    {d K m L : ℕ} (hd : maxDeg G ≤ d)
    (hL : ∀ H : SimpleGraph (Fin n), G ≤ H → H.CliqueFree 3 → maxDeg H ≤ 2 * d →
      (H.edgeFinset \ G.edgeFinset).card ≤ m →
      ∀ U : Finset (Fin n), U.card = K → IsIndep H U →
        L ≤ (eligibleOrdered H (2 * d) U).card)
    (hLP : L ≤ n * n)
    (hineq : (2 : ℝ) ^ n * (((n * n - L : ℕ) : ℝ) / (n * n : ℝ)) ^ m < 1)
    (hn : 0 < n) :
    ∃ H : SimpleGraph (Fin n), G ≤ H ∧ H.CliqueFree 3 ∧
      ∀ U : Finset (Fin n), IsIndep H U → U.card < K := by
  classical
  have hNpos : (0 : ℝ) < (n : ℝ) * (n : ℝ) := by
    have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    exact mul_pos hnR hnR
  have hNat : 2 ^ n * (n * n - L) ^ m < (n * n) ^ m := by
    have hcast : (((n * n - L : ℕ) : ℝ)) = (n : ℝ) * (n : ℝ) - (L : ℝ) := by
      rw [Nat.cast_sub hLP, Nat.cast_mul]
    have hkey : (2 : ℝ) ^ n * (((n * n - L : ℕ) : ℝ) / ((n : ℝ) * (n : ℝ))) ^ m *
        ((n : ℝ) * (n : ℝ)) ^ m < 1 * ((n : ℝ) * (n : ℝ)) ^ m :=
      mul_lt_mul_of_pos_right hineq (pow_pos hNpos m)
    rw [mul_assoc] at hkey
    have hdiv : (((n * n - L : ℕ) : ℝ) / ((n : ℝ) * (n : ℝ))) ^ m *
        ((n : ℝ) * (n : ℝ)) ^ m =
        ((n * n - L : ℕ) : ℝ) ^ m := by
      rw [div_pow, div_mul_cancel₀ _ (pow_ne_zero m (ne_of_gt hNpos))]
    rw [hdiv] at hkey
    have hkey2 : (((2 ^ n * (n * n - L) ^ m : ℕ) : ℝ) < ((n * n) ^ m : ℕ)) := by
      push_cast
      simpa using hkey
    exact_mod_cast hkey2
  have hBadcard : (Finset.univ.filter (fun f : Fin m → Fin n × Fin n =>
      ∃ U : Finset (Fin n), U.card = K ∧
        IsIndep (run G (2 * d) (List.ofFn f)) U)).card ≤
      2 ^ n * (n * n - L) ^ m := by
    have hsub : Finset.univ.filter (fun f : Fin m → Fin n × Fin n =>
        ∃ U : Finset (Fin n), U.card = K ∧
          IsIndep (run G (2 * d) (List.ofFn f)) U) ⊆
        (Finset.univ.powersetCard K).biUnion (fun U =>
          Finset.univ.filter (fun f : Fin m → Fin n × Fin n =>
            IsIndep (run G (2 * d) (List.ofFn f)) U)) := by
      intro f hf
      rw [Finset.mem_filter] at hf
      obtain ⟨_, U, hUK, hUindep⟩ := hf
      rw [Finset.mem_biUnion]
      refine ⟨U, ?_, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hUindep⟩⟩
      rw [Finset.mem_powersetCard]
      exact ⟨Finset.subset_univ U, hUK⟩
    calc (Finset.univ.filter (fun f : Fin m → Fin n × Fin n =>
            ∃ U : Finset (Fin n), U.card = K ∧
              IsIndep (run G (2 * d) (List.ofFn f)) U)).card
        ≤ ((Finset.univ.powersetCard K).biUnion (fun U =>
            Finset.univ.filter (fun f : Fin m → Fin n × Fin n =>
              IsIndep (run G (2 * d) (List.ofFn f)) U))).card :=
          Finset.card_le_card hsub
      _ ≤ ∑ U ∈ Finset.univ.powersetCard K, (Finset.univ.filter (fun f : Fin m → Fin n × Fin n =>
            IsIndep (run G (2 * d) (List.ofFn f)) U)).card := Finset.card_biUnion_le
      _ ≤ ∑ U ∈ Finset.univ.powersetCard K, (n * n - L) ^ m := by
          apply Finset.sum_le_sum
          intro U hUmem
          have hUcard : U.card = K := (Finset.mem_powersetCard.mp hUmem).2
          exact surviving_card_le hG hL m G le_rfl hG (le_trans hd (by omega)) (by simp) U hUcard
      _ = (Finset.univ.powersetCard K).card * (n * n - L) ^ m := by
          rw [Finset.sum_const, smul_eq_mul]
      _ ≤ 2 ^ n * (n * n - L) ^ m := by
          apply Nat.mul_le_mul_right
          exact card_powersetCard_univ_le_two_pow
  have htotal : (Finset.univ : Finset (Fin m → Fin n × Fin n)).card = (n * n) ^ m := by
    rw [Finset.card_univ]
    simp [Fintype.card_fin, Fintype.card_prod]
  have hBadlt : (Finset.univ.filter (fun f : Fin m → Fin n × Fin n =>
      ∃ U : Finset (Fin n), U.card = K ∧
        IsIndep (run G (2 * d) (List.ofFn f)) U)).card <
      (Finset.univ : Finset (Fin m → Fin n × Fin n)).card := by
    rw [htotal]
    exact lt_of_le_of_lt hBadcard hNat
  obtain ⟨f, hf⟩ : ∃ f, f ∉ Finset.univ.filter (fun f : Fin m → Fin n × Fin n =>
      ∃ U : Finset (Fin n), U.card = K ∧
        IsIndep (run G (2 * d) (List.ofFn f)) U) := by
    by_contra hcon
    push_neg at hcon
    have hEq : Finset.univ.filter (fun f : Fin m → Fin n × Fin n =>
        ∃ U : Finset (Fin n), U.card = K ∧
          IsIndep (run G (2 * d) (List.ofFn f)) U) = Finset.univ :=
      Finset.eq_univ_of_forall hcon
    rw [hEq] at hBadlt
    exact lt_irrefl _ hBadlt
  refine ⟨run G (2 * d) (List.ofFn f), le_run _, cliqueFree_run hG _, ?_⟩
  intro U hUindep
  by_contra hnot
  push_neg at hnot
  obtain ⟨U', hU'sub, hU'card⟩ := Finset.exists_subset_card_eq hnot
  have hU'indep : IsIndep (run G (2 * d) (List.ofFn f)) U' := by
    intro x hx y hy hxy hadj
    exact hUindep x (hU'sub hx) y (hU'sub hy) hxy hadj
  apply hf
  rw [Finset.mem_filter]
  exact ⟨Finset.mem_univ _, U', hU'card, hU'indep⟩

end Jsp618
