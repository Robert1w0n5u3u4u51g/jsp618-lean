-- Deterministic half of Alon's proof of Theorem 1.2 (Erdős #618).
--
-- Contents:
-- * neighbourhoods are independent sets in a triangle-free graph,
-- * a triangle-free graph extends to a maximal triangle-free graph,
--   which has diameter at most two,
-- * hence, if every independent set has at most `B` elements, the
--   extension has maximum degree at most `B`, at most `n * B / 2` edges,
--   and so `2 * h2 G ≤ n * B`.
--
-- This is the deterministic finish of Alon's proof; the probabilistic
-- claim (that a graph with no large independent set can be produced)
-- is the remaining ingredient, handled in `Process.lean`.

import Jsp618.Defs
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

open scoped Classical
open Finset SimpleGraph

namespace Jsp618

/-- A finset `U` is independent in `G` if no two of its elements are adjacent. -/
def IsIndep {n : ℕ} (G : SimpleGraph (Fin n)) (U : Finset (Fin n)) : Prop :=
  ∀ x ∈ U, ∀ y ∈ U, x ≠ y → ¬ G.Adj x y

/-- A set of three pairwise adjacent vertices is a clique. -/
theorem isClique_triple {n : ℕ} {G : SimpleGraph (Fin n)} {a b c : Fin n}
    (hab : G.Adj a b) (hac : G.Adj a c) (hbc : G.Adj b c) :
    G.IsClique {a, b, c} := by
  intro p hp q hq hpq
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp hq
  rcases hp with rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl <;>
    first
      | exact hab
      | exact hac
      | exact hbc
      | exact hab.symm
      | exact hac.symm
      | exact hbc.symm
      | exact absurd rfl hpq

/-- Same, as a finset coerced to a set (the form `IsNClique` uses). -/
theorem isClique_triple_finset {n : ℕ} {G : SimpleGraph (Fin n)} {a b c : Fin n}
    (hab : G.Adj a b) (hac : G.Adj a c) (hbc : G.Adj b c) :
    G.IsClique (↑({a, b, c} : Finset (Fin n))) := by
  simpa using isClique_triple hab hac hbc

/-- A three-element finset has card 3. -/
theorem card_triple {n : ℕ} {a b c : Fin n} (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) : ({a, b, c} : Finset (Fin n)).card = 3 := by
  rw [Finset.card_insert_of_notMem (by simp [hab, hac]),
    Finset.card_insert_of_notMem (by simp [hbc]), Finset.card_singleton]

/-- In a triangle-free graph, the neighbourhood of any vertex is independent. -/
theorem isIndep_neighborFinset {n : ℕ} {G : SimpleGraph (Fin n)}
    (hG : G.CliqueFree 3) (v : Fin n) : IsIndep G (G.neighborFinset v) := by
  intro x hx y hy hxy hxy_adj
  rw [SimpleGraph.mem_neighborFinset] at hx hy
  have hvx : v ≠ x := by
    rintro rfl
    exact G.loopless _ hx
  have hvy : v ≠ y := by
    rintro rfl
    exact G.loopless _ hy
  exact hG _ ((SimpleGraph.isNClique_iff G).mpr
    ⟨isClique_triple_finset hx hy hxy_adj, card_triple hvx hvy hxy⟩)

/-- Independence is preserved when passing to a subgraph. -/
theorem isIndep_of_le {n : ℕ} {G H : SimpleGraph (Fin n)} (hle : G ≤ H)
    {U : Finset (Fin n)} (hU : IsIndep H U) : IsIndep G U :=
  fun x hx y hy hxy hg => hU x hx y hy hxy (hle hg)

/-- The graph obtained from `G` by adding the single edge `x—y`. -/
def addEdge {n : ℕ} (G : SimpleGraph (Fin n)) (x y : Fin n) (hxy : x ≠ y) :
    SimpleGraph (Fin n) where
  Adj a b := G.Adj a b ∨ (a = x ∧ b = y) ∨ (a = y ∧ b = x)
  symm := by
    intro a b h
    rcases h with h | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl h.symm
    · exact Or.inr (Or.inr ⟨rfl, rfl⟩)
    · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
  loopless := by
    intro a h
    rcases h with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact G.loopless a h
    · exact hxy (h1.symm.trans h2)
    · exact hxy (h2.symm.trans h1)

/-- Adjacency in the graph with one extra edge, unfolded. -/
theorem adj_addEdge_iff {n : ℕ} {G : SimpleGraph (Fin n)} {x y : Fin n}
    (hxy : x ≠ y) {a b : Fin n} :
    (addEdge G x y hxy).Adj a b ↔
      G.Adj a b ∨ (a = x ∧ b = y) ∨ (a = y ∧ b = x) :=
  Iff.rfl

/-- `G` is a subgraph of `G` with one extra edge. -/
theorem le_addEdge {n : ℕ} {G : SimpleGraph (Fin n)} {x y : Fin n}
    (hxy : x ≠ y) : G ≤ addEdge G x y hxy := by
  intro a b hab
  exact Or.inl hab

/-- The new edge strictly increases the edge count. -/
theorem edgeFinset_ssubset_addEdge {n : ℕ} {H : SimpleGraph (Fin n)}
    {x y : Fin n} (hxy : x ≠ y) (h : ¬ H.Adj x y) :
    H.edgeFinset ⊂ (addEdge H x y hxy).edgeFinset := by
  refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
  · exact SimpleGraph.edgeFinset_subset_edgeFinset.mpr (le_addEdge hxy)
  · intro hEq
    have h1 : s(x, y) ∈ (addEdge H x y hxy).edgeFinset := by
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, adj_addEdge_iff hxy]
      exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    rw [← hEq] at h1
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at h1
    exact h h1

/-- If adding the edge `x—y` to a triangle-free graph creates a triangle,
then `x` and `y` already have a common neighbour. -/
theorem exists_common_neighbor_of_not_cliqueFree_addEdge {n : ℕ}
    {H : SimpleGraph (Fin n)} (hH : H.CliqueFree 3) {x y : Fin n} (hxy : x ≠ y)
    (h : ¬ (addEdge H x y hxy).CliqueFree 3) :
    ∃ z, H.Adj x z ∧ H.Adj z y := by
  classical
  obtain ⟨t, ht⟩ : ∃ t, (addEdge H x y hxy).IsNClique 3 t := by
    by_contra hcon
    push_neg at hcon
    exact h hcon
  rw [SimpleGraph.isNClique_iff] at ht
  obtain ⟨hcl, hcard⟩ := ht
  rw [Finset.card_eq_three] at hcard
  obtain ⟨a, b, c, hab_ne, hac_ne, hbc_ne, rfl⟩ := hcard
  have hab : (addEdge H x y hxy).Adj a b :=
    hcl (by simp) (by simp) hab_ne
  have hac : (addEdge H x y hxy).Adj a c :=
    hcl (by simp) (by simp) hac_ne
  have hbc : (addEdge H x y hxy).Adj b c :=
    hcl (by simp) (by simp) hbc_ne
  rw [adj_addEdge_iff hxy] at hab hac hbc
  -- Case split on which of the three pairs is the new edge. The nested
  -- structure (rather than a flat `rcases` chain) keeps the equation
  -- handling robust: after each split we rewrite with the equations,
  -- which never fails on reflexive equations the way `subst` does.
  rcases hab with hab | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rcases hac with hac | ⟨h3, h4⟩ | ⟨h3, h4⟩
    · rcases hbc with hbc | ⟨h5, h6⟩ | ⟨h5, h6⟩
      · exfalso
        exact hH _ ((SimpleGraph.isNClique_iff H).mpr
          ⟨isClique_triple_finset hab hac hbc, card_triple hab_ne hac_ne hbc_ne⟩)
      · simp only [h5, h6] at *
        exact ⟨a, hab.symm, hac⟩
      · simp only [h5, h6] at *
        exact ⟨a, hac.symm, hab⟩
    · simp only [h3, h4] at *
      rcases hbc with hbc | ⟨h5, h6⟩ | ⟨h5, h6⟩
      · exact ⟨b, hab, hbc⟩
      · simp only [h5, h6] at *
        contradiction
      · simp only [h5, h6] at *
        contradiction
    · simp only [h3, h4] at *
      rcases hbc with hbc | ⟨h5, h6⟩ | ⟨h5, h6⟩
      · exact ⟨b, hbc.symm, hab.symm⟩
      · simp only [h5, h6] at *
        contradiction
      · simp only [h5, h6] at *
        contradiction
  · simp only [h1, h2] at *
    rcases hac with hac | ⟨h3, h4⟩ | ⟨h3, h4⟩
    · rcases hbc with hbc | ⟨h5, h6⟩ | ⟨h5, h6⟩
      · exact ⟨c, hac, hbc.symm⟩
      · simp only [h5, h6] at *
        contradiction
      · simp only [h5, h6] at *
        contradiction
    · simp only [h3, h4] at *
      contradiction
    · simp only [h3, h4] at *
      contradiction
  · simp only [h1, h2] at *
    rcases hac with hac | ⟨h3, h4⟩ | ⟨h3, h4⟩
    · rcases hbc with hbc | ⟨h5, h6⟩ | ⟨h5, h6⟩
      · exact ⟨c, hbc, hac.symm⟩
      · simp only [h5, h6] at *
        contradiction
      · simp only [h5, h6] at *
        contradiction
    · simp only [h3, h4] at *
      contradiction
    · simp only [h3, h4] at *
      contradiction

/-- Every triangle-free graph extends to a maximal triangle-free graph,
which has diameter at most two. -/
theorem exists_maximal_triangle_free_extension {n : ℕ} {G : SimpleGraph (Fin n)}
    (hG : G.CliqueFree 3) :
    ∃ H : SimpleGraph (Fin n), G ≤ H ∧ H.CliqueFree 3 ∧ DiamLETwo H := by
  classical
  obtain ⟨H, hH, hmax⟩ := Finset.exists_max_image
    (Finset.univ.filter (fun H : SimpleGraph (Fin n) => G ≤ H ∧ H.CliqueFree 3))
    (fun H => H.edgeFinset.card)
    ⟨G, Finset.mem_filter.mpr ⟨Finset.mem_univ G, le_rfl, hG⟩⟩
  rw [Finset.mem_filter] at hH
  obtain ⟨_, hGH, hHfree⟩ := hH
  refine ⟨H, hGH, hHfree, ?_⟩
  intro x y hxy
  by_cases hadj : H.Adj x y
  · exact Or.inl hadj
  · right
    by_cases h' : (addEdge H x y hxy).CliqueFree 3
    · exfalso
      have h'mem : addEdge H x y hxy ∈
          Finset.univ.filter (fun H : SimpleGraph (Fin n) => G ≤ H ∧ H.CliqueFree 3) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_trans hGH (le_addEdge hxy), h'⟩
      have hle : (addEdge H x y hxy).edgeFinset.card ≤ H.edgeFinset.card :=
        hmax _ h'mem
      have hlt : H.edgeFinset.card < (addEdge H x y hxy).edgeFinset.card :=
        Finset.card_lt_card (edgeFinset_ssubset_addEdge hxy hadj)
      omega
    · exact exists_common_neighbor_of_not_cliqueFree_addEdge hHfree hxy h'

/-- In a triangle-free graph, the degree of a vertex is at most the size
of the largest independent set. -/
theorem degree_le_of_forall_isIndep {n : ℕ} {H : SimpleGraph (Fin n)}
    (hH : H.CliqueFree 3) {B : ℕ}
    (hα : ∀ U : Finset (Fin n), IsIndep H U → U.card ≤ B) (v : Fin n) :
    H.degree v ≤ B := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  exact hα _ (isIndep_neighborFinset hH v)

/-- Same, for the maximum degree. -/
theorem maxDeg_le_of_forall_isIndep {n : ℕ} {H : SimpleGraph (Fin n)}
    (hH : H.CliqueFree 3) {B : ℕ}
    (hα : ∀ U : Finset (Fin n), IsIndep H U → U.card ≤ B) :
    maxDeg H ≤ B := by
  show Finset.univ.sup (fun v => H.degree v) ≤ B
  apply Finset.sup_le
  intro v _
  exact degree_le_of_forall_isIndep hH hα v

/-- Twice the number of edges is at most `n` times the maximum degree. -/
theorem two_mul_card_edgeFinset_le {n : ℕ} (H : SimpleGraph (Fin n)) :
    2 * H.edgeFinset.card ≤ n * maxDeg H := by
  classical
  rw [← SimpleGraph.sum_degrees_eq_twice_card_edges]
  calc ∑ v, H.degree v ≤ ∑ _v : Fin n, maxDeg H :=
        Finset.sum_le_sum (fun v _ => by
          show H.degree v ≤ Finset.univ.sup (fun v => H.degree v)
          exact Finset.le_sup (f := fun w => H.degree w) (Finset.mem_univ v))
    _ = n * maxDeg H := by simp

/-- `h2 G` is at most the number of edges of any suitable extension. -/
theorem h2_le_of_extension {n : ℕ} {G H : SimpleGraph (Fin n)} (hle : G ≤ H)
    (hH : H.CliqueFree 3) (hd : DiamLETwo H) :
    h2 G ≤ H.edgeFinset.card := by
  classical
  have hmem : (H.edgeFinset \ G.edgeFinset).card ∈
      {k : ℕ | ∃ H' : SimpleGraph (Fin n),
        G ≤ H' ∧ H'.CliqueFree 3 ∧ DiamLETwo H' ∧
        (H'.edgeFinset \ G.edgeFinset).card = k} :=
    ⟨H, hle, hH, hd, rfl⟩
  unfold h2
  exact le_trans (Nat.sInf_le hmem) (Finset.card_le_card Finset.sdiff_subset)

/-- **Deterministic reduction.** If every independent set of `G` has at
most `B` elements, then `G` extends to a triangle-free diameter-two graph
with maximum degree at most `B`, and `2 * h2 G ≤ n * B`. -/
theorem deterministic_reduction {n : ℕ} {G : SimpleGraph (Fin n)}
    (hG : G.CliqueFree 3) {B : ℕ}
    (hα : ∀ U : Finset (Fin n), IsIndep G U → U.card ≤ B) :
    ∃ H : SimpleGraph (Fin n),
      G ≤ H ∧ H.CliqueFree 3 ∧ DiamLETwo H ∧ maxDeg H ≤ B ∧ 2 * h2 G ≤ n * B := by
  obtain ⟨H, hle, hH, hdiam⟩ := exists_maximal_triangle_free_extension hG
  have hαH : ∀ U : Finset (Fin n), IsIndep H U → U.card ≤ B :=
    fun U hU => hα U (isIndep_of_le hle hU)
  have hmax : maxDeg H ≤ B := maxDeg_le_of_forall_isIndep hH hαH
  refine ⟨H, hle, hH, hdiam, hmax, ?_⟩
  calc 2 * h2 G ≤ 2 * H.edgeFinset.card :=
        Nat.mul_le_mul_left 2 (h2_le_of_extension hle hH hdiam)
    _ ≤ n * maxDeg H := two_mul_card_edgeFinset_le H
    _ ≤ n * B := Nat.mul_le_mul_left n hmax

end Jsp618
