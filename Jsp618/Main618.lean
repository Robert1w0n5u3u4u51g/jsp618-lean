-- Erdős Problem #618, from Theorem 1.2 (restated for `ε < 1 / 8`).
--
-- This file is an independent formalization of Alon's argument, from
-- the paper itself; it does not use the existing Alexeev formalization.
--
-- Why the proof does not apply `theorem_1_2` with a fixed `ε`:
-- from `Δ = o(√n)` alone one cannot conclude `Δ ≤ n ^ (1 / 2 - ε)`
-- eventually for any fixed `ε` (e.g. `Δ = √n / log n` violates every
-- such bound). Instead the general degree-bound lemma
-- `h2_bound_of_degree_bound` is applied directly, with the degree
-- bound `b n = max (Δ (G n)) (n ^ (7 / 16))`:
-- * `b n / √n = max (Δ (G n) / √n) (n ^ (-1 / 16)) → 0`, since both
--   terms tend to `0`;
-- * `b n ≥ n ^ (7 / 16)`, so `b n ^ 4 ≥ n ^ (7 / 4) ≥ 2 * n * √n`
--   eventually, which is exactly the union-bound condition the
--   general lemma needs.
-- Hence `h2 (G n) / n ^ 2 ≤ (111 / 40) * (b n / √n) → 0`.

import Jsp618.Theorem12
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

open scoped Classical Topology
open Finset SimpleGraph Asymptotics Filter

namespace Jsp618

set_option maxHeartbeats 1200000 in
/-- **Erdős Problem #618** (Erdős–Gyárfás `h₂` question), affirmative
asymptotic answer: for every family of triangle-free graphs `G n` on `n`
vertices with maximum degree `Δ(G n) = o(√n)`, one has `h2 (G n) = o(n²)`. -/
theorem erdos_618
    (G : ∀ n : ℕ, SimpleGraph (Fin n))
    (hTF : ∀ n : ℕ, (G n).CliqueFree 3)
    (hΔ : (fun n : ℕ => (maxDeg (G n) : ℝ) / Real.sqrt n)
        =o[atTop] (fun _ => (1 : ℝ))) :
    (fun n : ℕ => (h2 (G n) : ℝ) / (n : ℝ) ^ 2)
        =o[atTop] (fun _ => (1 : ℝ)) := by
  classical
  rw [Asymptotics.isLittleO_one_iff ℝ]
  have hc_tendsto : Filter.Tendsto
      (fun n : ℕ => (maxDeg (G n) : ℝ) / Real.sqrt n) Filter.atTop (𝓝 0) :=
    (Asymptotics.isLittleO_one_iff ℝ).mp hΔ
  have hr_tendsto : Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ (-(1 / 16) : ℝ))
      Filter.atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 16)).comp
      tendsto_natCast_atTop_atTop
  have hmax_tendsto : Filter.Tendsto
      (fun n : ℕ => max ((maxDeg (G n) : ℝ) / Real.sqrt n)
        ((n : ℝ) ^ (-(1 / 16) : ℝ))) Filter.atTop (𝓝 0) := by
    simpa using hc_tendsto.max hr_tendsto
  -- `b n / √n → 0`, by squeezing against the max above.
  have hb_tendsto : Filter.Tendsto
      (fun n : ℕ => (max (maxDeg (G n) : ℝ) ((n : ℝ) ^ (7 / 16 : ℝ))) /
        Real.sqrt n) Filter.atTop (𝓝 0) := by
    apply Filter.Tendsto.squeeze' tendsto_const_nhds hmax_tendsto
    · filter_upwards with n
      exact div_nonneg (le_max_of_le_left (Nat.cast_nonneg _))
        (Real.sqrt_nonneg _)
    · filter_upwards [Filter.eventually_gt_atTop 0] with n hn0
      have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn0
      have hsqrt_pos : 0 < Real.sqrt n := Real.sqrt_pos.mpr hnR
      have hRdiv : ((n : ℝ) ^ (7 / 16 : ℝ)) / Real.sqrt n =
          (n : ℝ) ^ (-(1 / 16) : ℝ) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_sub hnR]
        congr 1
        norm_num
      rcases le_total (maxDeg (G n) : ℝ) ((n : ℝ) ^ (7 / 16 : ℝ)) with hle | hle
      · rw [max_eq_right hle, hRdiv]
        exact le_max_right _ _
      · rw [max_eq_left hle]
        exact le_max_left _ _
  have hupper_tendsto : Filter.Tendsto
      (fun n : ℕ => (111 / 40) * ((max (maxDeg (G n) : ℝ)
        ((n : ℝ) ^ (7 / 16 : ℝ))) / Real.sqrt n)) Filter.atTop (𝓝 0) := by
    simpa using hb_tendsto.const_mul (111 / 40)
  -- Main squeeze: `0 ≤ h2 / n ^ 2 ≤ (111 / 40) * (b n / √n)` eventually.
  apply Filter.Tendsto.squeeze' tendsto_const_nhds hupper_tendsto
  · filter_upwards with n
    exact div_nonneg (Nat.cast_nonneg _)
      (pow_nonneg (Nat.cast_nonneg _) 2)
  · have ht20 : Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ (7 / 16 : ℝ))
        Filter.atTop Filter.atTop :=
      (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 7 / 16)).comp
        tendsto_natCast_atTop_atTop
    have ht14 : Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ (1 / 4 : ℝ))
        Filter.atTop Filter.atTop :=
      (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)).comp
        tendsto_natCast_atTop_atTop
    have ev20 : ∀ᶠ n : ℕ in Filter.atTop, (20 : ℝ) ≤ (n : ℝ) ^ (7 / 16 : ℝ) :=
      ht20.eventually_ge_atTop 20
    have ev14 : ∀ᶠ n : ℕ in Filter.atTop, (2 : ℝ) ≤ (n : ℝ) ^ (1 / 4 : ℝ) :=
      ht14.eventually_ge_atTop 2
    have evc : ∀ᶠ n : ℕ in Filter.atTop,
        (maxDeg (G n) : ℝ) / Real.sqrt n < 1 :=
      hc_tendsto.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
    filter_upwards [ev20, ev14, evc, Filter.eventually_ge_atTop 1] with n
      h20 hquarter hc1 hn1
    have hn_pos : 0 < n := by omega
    have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn_pos
    have hnR1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
    have hsqrt_pos : 0 < Real.sqrt n := Real.sqrt_pos.mpr hnR
    have hsqrt_ne : Real.sqrt n ≠ 0 := ne_of_gt hsqrt_pos
    set b := max (maxDeg (G n) : ℝ) ((n : ℝ) ^ (7 / 16 : ℝ)) with hb_def
    have hb0 : 0 ≤ b := by
      rw [hb_def]; exact le_max_of_le_left (Nat.cast_nonneg _)
    have hb20 : 20 ≤ b := by
      rw [hb_def]; exact le_max_of_le_right h20
    have hb_le : b ≤ Real.sqrt n := by
      rw [hb_def]
      apply max_le
      · rw [div_lt_iff₀ hsqrt_pos] at hc1
        linarith
      · rw [Real.sqrt_eq_rpow]
        exact Real.rpow_le_rpow_of_exponent_le hnR1 (by norm_num)
    have hmax_b : (maxDeg (G n) : ℝ) ≤ b := by
      rw [hb_def]; exact le_max_left _ _
    have hunion : 2 * (n : ℝ) * Real.sqrt n ≤ b ^ 4 := by
      have hb4ge : ((n : ℝ) ^ (7 / 16 : ℝ)) ^ 4 ≤ b ^ 4 :=
        pow_le_pow_left₀ (Real.rpow_nonneg hnR.le _) (by rw [hb_def]; exact le_max_right _ _) 4
      have hb4eq : ((n : ℝ) ^ (7 / 16 : ℝ)) ^ 4 = (n : ℝ) ^ (7 / 4 : ℝ) := by
        rw [← Real.rpow_natCast _ 4, ← Real.rpow_mul hnR.le]
        congr 1
        norm_num
      have hsplit : (n : ℝ) ^ (7 / 4 : ℝ) =
          (n : ℝ) ^ (3 / 2 : ℝ) * (n : ℝ) ^ (1 / 4 : ℝ) := by
        rw [← Real.rpow_add hnR]
        congr 1
        norm_num
      have hnsqrt : (n : ℝ) * Real.sqrt n = (n : ℝ) ^ (3 / 2 : ℝ) := by
        calc (n : ℝ) * Real.sqrt n
            = ((n : ℝ) ^ (1 : ℝ)) * ((n : ℝ) ^ (1 / 2 : ℝ)) := by
              rw [Real.sqrt_eq_rpow, Real.rpow_one]
          _ = (n : ℝ) ^ (3 / 2 : ℝ) := by
              rw [← Real.rpow_add hnR]
              congr 1
              ring
      calc 2 * (n : ℝ) * Real.sqrt n
          = 2 * ((n : ℝ) ^ (3 / 2 : ℝ)) := by rw [← hnsqrt]; ring
        _ ≤ (n : ℝ) ^ (3 / 2 : ℝ) * (n : ℝ) ^ (1 / 4 : ℝ) := by
            rw [mul_comm ((n : ℝ) ^ (3 / 2 : ℝ)) ((n : ℝ) ^ (1 / 4 : ℝ))]
            exact mul_le_mul_of_nonneg_right hquarter
              (Real.rpow_nonneg hnR.le _)
        _ = (n : ℝ) ^ (7 / 4 : ℝ) := hsplit.symm
        _ = ((n : ℝ) ^ (7 / 16 : ℝ)) ^ 4 := hb4eq.symm
        _ ≤ b ^ 4 := hb4ge
    have hgen := h2_bound_of_degree_bound (hTF n) b hb0 hb20 hb_le hmax_b
      hunion hn_pos
    have hdiv : (h2 (G n) : ℝ) / (n : ℝ) ^ 2 ≤ (111 / 40) * (b / Real.sqrt n) := by
      rw [div_le_iff₀ (pow_pos hnR 2)]
      have heq : (111 / 40) * (b / Real.sqrt n) * ((n : ℝ) ^ 2) =
          (111 / 40) * b * (n : ℝ) * Real.sqrt n := by
        have h1 : (n : ℝ) ^ 2 / Real.sqrt n = (n : ℝ) * Real.sqrt n := by
          rw [div_eq_iff hsqrt_ne, pow_two, mul_assoc,
            Real.mul_self_sqrt hnR.le]
        calc (111 / 40) * (b / Real.sqrt n) * ((n : ℝ) ^ 2)
            = (111 / 40) * b * (((n : ℝ) ^ 2) / Real.sqrt n) := by ring
          _ = (111 / 40) * b * ((n : ℝ) * Real.sqrt n) := by rw [h1]
          _ = (111 / 40) * b * (n : ℝ) * Real.sqrt n := by ring
      rw [heq]
      exact hgen
    -- The goal's upper bound is stated with `max ...`, i.e. with `b`.
    exact hdiv

end Jsp618
