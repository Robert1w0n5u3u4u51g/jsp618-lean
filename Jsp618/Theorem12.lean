-- Assembly of Alon's Theorem 1.2 (Erdős #618) from the process claim
-- (`Process.lean`) and the deterministic finish (`Deterministic.lean`).
--
-- This file is an independent formalization of Alon's proof, from the
-- paper itself; it does not use the existing Alexeev formalization.
--
-- Structure, following `Theorem12-plan.md`:
-- * a general degree-bound lemma `h2_bound_of_degree_bound`: for a
--   triangle-free graph whose maximum degree is at most a real bound
--   `b` (with `20 ≤ b ≤ √n` and the union-bound condition
--   `2 * n * √n ≤ b ^ 4`), one has
--   `h2 G ≤ (111 / 40) * b * n * √n`;
-- * `theorem_1_2_aux`: the restated Theorem 1.2 for `0 < ε < 1 / 8`,
--   obtained from the general lemma with `b = n ^ (1 / 2 - ε)`.
--
-- Parameters (with `s = √n`, `d = ⌈b⌉₊`, cap `2 * d`):
-- * `K = ⌈(11 / 2) * b * s⌉₊` — the independent-set size to kill.
--   The constant `11 / 2 = 5.5` is used instead of the plan's `5`:
--   it is still `< 6` (so the deterministic finish gives
--   `h2 < 3 * n ^ (2 - ε)`), but it gives much more slack in the
--   eligible-pair estimate: `5.5 ^ 2 - 4 - 4 * 5.5 = 4.25 > 0`,
--   against `5 ^ 2 - 4 - 20 = 1` for `5`. The extra slack absorbs
--   all ceiling losses with room to spare.
-- * `m = ⌈b ^ 2 * s⌉₊` — the number of process steps;
-- * `L = ⌈b ^ 2 * n⌉₊` — the eligible-pair lower bound;
-- * `C0 = 2 * m / d` — the capped-vertex bound, from
--   `mul_card_capped_le` (with the degree bound `d`, not the actual
--   maximum degree: this is why `d` is `⌈b⌉₊`, the ceiling of the
--   *bound*, rather than `maxDeg G` itself).

import Jsp618.Process
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

open scoped Classical
open Finset SimpleGraph

namespace Jsp618

set_option maxHeartbeats 1200000 in
/-- General degree-bound lemma: the assembly of the process claim and
the deterministic finish, for an arbitrary real degree bound `b`.
The hypotheses are exactly the ones the two halves need: `b` is
large enough that all ceiling losses are at most `5 %` of the main
terms, `b ≤ √n` (so `L ≤ n ^ 2`), and the union-bound condition
`2 * n * √n ≤ b ^ 4` (so `m * L / n ^ 2 ≥ 2 * n`). -/
theorem h2_bound_of_degree_bound {n : ℕ} {G : SimpleGraph (Fin n)}
    (hG : G.CliqueFree 3) (b : ℝ) (hb0 : 0 ≤ b) (hb20 : 20 ≤ b)
    (hb_le : b ≤ Real.sqrt n) (hmax : (maxDeg G : ℝ) ≤ b)
    (hunion : 2 * (n : ℝ) * Real.sqrt n ≤ b ^ 4) (hn : 0 < n) :
    (h2 G : ℝ) ≤ (111 / 40) * b * (n : ℝ) * Real.sqrt n := by
  classical
  set s := Real.sqrt n with hs_def
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hnR1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hs_pos : 0 < s := by
    rw [hs_def]; exact Real.sqrt_pos.mpr hnR
  have hs1 : 1 ≤ s := by
    have h := Real.sqrt_le_sqrt hnR1
    rw [hs_def]
    simpa using h
  have hs2 : s ^ 2 = (n : ℝ) := by
    rw [hs_def]; exact Real.sq_sqrt hnR.le
  have hbs : 20 ≤ b * s := by
    calc (20 : ℝ) = 20 * 1 := by ring
      _ ≤ b * s := mul_le_mul hb20 hs1 (by norm_num) (by linarith)
  have hb2s : (400 : ℝ) ≤ b ^ 2 * s := by
    have h1 : (20 : ℝ) ^ 2 ≤ b ^ 2 := by
      apply pow_le_pow_left₀ (by norm_num) hb20
    calc (400 : ℝ) = (20 : ℝ) ^ 2 * 1 := by norm_num
      _ ≤ b ^ 2 * s := mul_le_mul h1 hs1 (by norm_num) (by positivity)
  have hb2n : (400 : ℝ) ≤ b ^ 2 * (n : ℝ) := by
    have h1 : (20 : ℝ) ^ 2 ≤ b ^ 2 := by
      apply pow_le_pow_left₀ (by norm_num) hb20
    calc (400 : ℝ) = (20 : ℝ) ^ 2 * 1 := by norm_num
      _ ≤ b ^ 2 * (n : ℝ) := mul_le_mul h1 hnR1 (by norm_num) (by positivity)
  -- Parameters.
  set d := ⌈b⌉₊ with hd_def
  set K := ⌈(11 / 2) * b * s⌉₊ with hK_def
  set m := ⌈b ^ 2 * s⌉₊ with hm_def
  set L := ⌈b ^ 2 * (n : ℝ)⌉₊ with hL_def
  set C0 := 2 * m / d with hC0_def
  -- Ceiling bounds.
  have hd_ge : b ≤ (d : ℝ) := by rw [hd_def]; exact Nat.le_ceil b
  have hd_lt : (d : ℝ) < b + 1 := by rw [hd_def]; exact Nat.ceil_lt_add_one hb0
  have hd_le : (d : ℝ) ≤ (21 / 20) * b := by
    have h1 : b + 1 ≤ (21 / 20) * b := by linarith
    linarith
  have hd_pos : 0 < d := by
    by_contra hcon
    push_neg at hcon
    interval_cases d
    simp at hd_ge
    linarith
  have hmax_nat : maxDeg G ≤ d := by
    have h : (maxDeg G : ℝ) ≤ (d : ℝ) := le_trans hmax hd_ge
    exact_mod_cast h
  have hdeg_le : ∀ v, G.degree v ≤ d :=
    fun v => (degree_le_maxDeg v).trans hmax_nat
  have hK_ge : (11 / 2) * b * s ≤ (K : ℝ) := by
    rw [hK_def]; exact Nat.le_ceil _
  have hK_lt : (K : ℝ) < (11 / 2) * b * s + 1 := by
    rw [hK_def]
    exact Nat.ceil_lt_add_one (by positivity)
  have hK_le : (K : ℝ) ≤ (111 / 20) * b * s := by
    have h1 : (1 : ℝ) ≤ (b * s) / 20 := by linarith
    linarith
  have hm_ge : b ^ 2 * s ≤ (m : ℝ) := by
    rw [hm_def]; exact Nat.le_ceil _
  have hm_lt : (m : ℝ) < b ^ 2 * s + 1 := by
    rw [hm_def]
    exact Nat.ceil_lt_add_one (by positivity)
  have hm_le : (m : ℝ) ≤ (21 / 20) * (b ^ 2 * s) := by
    have h1 : (1 : ℝ) ≤ (b ^ 2 * s) / 20 := by linarith
    linarith
  have hL_ge : b ^ 2 * (n : ℝ) ≤ (L : ℝ) := by
    rw [hL_def]; exact Nat.le_ceil _
  have hL_lt : (L : ℝ) < b ^ 2 * (n : ℝ) + 1 := by
    rw [hL_def]
    exact Nat.ceil_lt_add_one (by positivity)
  have hL_le : (L : ℝ) ≤ (21 / 20) * (b ^ 2 * (n : ℝ)) := by
    have h1 : (1 : ℝ) ≤ (b ^ 2 * (n : ℝ)) / 20 := by linarith
    linarith
  have hL_nat : L ≤ n * n := by
    rw [hL_def]
    apply Nat.ceil_le.mpr
    have hb2 : b ^ 2 ≤ (n : ℝ) := by
      calc b ^ 2 ≤ s ^ 2 := by
            apply pow_le_pow_left₀ hb0 hb_le
        _ = (n : ℝ) := hs2
    calc b ^ 2 * (n : ℝ) ≤ (n : ℝ) * (n : ℝ) :=
          mul_le_mul_of_nonneg_right hb2 hnR.le
      _ = ((n * n : ℕ) : ℝ) := by push_cast; ring
  have hC0_real : (C0 : ℝ) ≤ (21 / 10) * b * s := by
    have hdiv : (C0 : ℝ) ≤ (2 * (m : ℝ)) / (d : ℝ) := by
      calc (C0 : ℝ) = ((2 * m / d : ℕ) : ℝ) := by rw [hC0_def]
        _ ≤ ((2 * m : ℕ) : ℝ) / ((d : ℕ) : ℝ) := Nat.cast_div_le
        _ = (2 * (m : ℝ)) / (d : ℝ) := by push_cast; ring
    have hd_posR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd_pos
    have h1 : (2 * (m : ℝ)) / (d : ℝ) ≤ (2 * (m : ℝ)) / b := by
      have hb_pos : (0 : ℝ) < b := by linarith
      exact div_le_div_of_nonneg_left
        (mul_nonneg (by norm_num) (Nat.cast_nonneg m)) hb_pos hd_ge
    have h2 : (2 * (m : ℝ)) / b ≤ (21 / 10) * b * s := by
      have hb_pos : (0 : ℝ) < b := by linarith
      rw [div_le_iff₀ hb_pos]
      have hm' : (m : ℝ) ≤ (21 / 20) * (b ^ 2 * s) := hm_le
      nlinarith [hm', hb_pos, hs_pos]
    exact le_trans hdiv (le_trans h1 h2)
  -- The eligible-pair lower bound required by `process_claim`.
  have hL : ∀ H : SimpleGraph (Fin n), G ≤ H → H.CliqueFree 3 → maxDeg H ≤ 2 * d →
      (H.edgeFinset \ G.edgeFinset).card ≤ m →
      ∀ U : Finset (Fin n), U.card = K → IsIndep H U →
        L ≤ (eligibleOrdered H (2 * d) U).card := by
    intro H hGH hH hmaxH hadd U hUK hUindep
    -- Capped vertices.
    have hcap_mul : d * (Finset.univ.filter (fun v => 2 * d ≤ H.degree v)).card ≤
        2 * m := by
      have h := mul_card_capped_le (G := G) (H := H) hGH (d := d) (D := 2 * d) hdeg_le
      rw [show 2 * d - d = d by omega] at h
      exact le_trans h (Nat.mul_le_mul_left 2 hadd)
    have hcap : (Finset.univ.filter (fun v => 2 * d ≤ H.degree v)).card ≤ C0 := by
      rw [hC0_def]
      exact (Nat.le_div_iff_mul_le hd_pos).mpr (by rw [mul_comm]; exact hcap_mul)
    have hcard := card_eligibleOrdered_add_le (H := H) hH (D := 2 * d) hmaxH
      hUindep hcap
    rw [hUK] at hcard
    -- Real version of the eligible bound.
    have hcardR : ((K * (K - 1) : ℕ) : ℝ) ≤
        ((eligibleOrdered H (2 * d) U).card : ℝ) +
          ((n * (2 * d) ^ 2 + 2 * C0 * K : ℕ) : ℝ) := by
      exact_mod_cast hcard
    push_cast at hcardR
    have hK1 : (1 : ℕ) ≤ K := by
      have h : (1 : ℝ) ≤ (K : ℝ) := by linarith [hK_ge, hbs]
      exact_mod_cast h
    have hKsub : ((K - 1 : ℕ) : ℝ) = (K : ℝ) - 1 := by
      rw [Nat.cast_sub hK1]; simp
    rw [hKsub] at hcardR
    -- Lower bound for `K * (K - 1)`.
    have hKminus : (109 / 20) * b * s ≤ (K : ℝ) - 1 := by
      have h1 : (1 : ℝ) ≤ (b * s) / 20 := by linarith
      linarith
    have hprod_low : (1199 / 40) * ((n : ℝ) * b ^ 2) ≤ (K : ℝ) * ((K : ℝ) - 1) := by
      have hB_nonneg : (0 : ℝ) ≤ (109 / 20) * b * s := by positivity
      have hK_nonneg : (0 : ℝ) ≤ (K : ℝ) := Nat.cast_nonneg K
      have hmul := mul_le_mul hK_ge hKminus hB_nonneg hK_nonneg
      have hsq : (b * s) ^ 2 = (n : ℝ) * b ^ 2 := by
        rw [mul_pow, hs2]; ring
      have heq : ((11 / 2) * b * s) * ((109 / 20) * b * s) =
          (1199 / 40) * ((n : ℝ) * b ^ 2) := by
        have h2 : ((11 / 2) * b * s) * ((109 / 20) * b * s) =
            ((11 / 2) * (109 / 20)) * (b * s) ^ 2 := by ring
        rw [h2, hsq]; norm_num
      rw [← heq]; exact hmul
    -- Upper bounds for the blocked terms.
    have hblock1 : (n : ℝ) * ((2 * (d : ℝ)) ^ 2) ≤ (441 / 100) * ((n : ℝ) * b ^ 2) := by
      have h2d : (2 * (d : ℝ)) ≤ (21 / 10) * b := by linarith
      have hsq : ((2 * (d : ℝ)) ^ 2) ≤ ((21 / 10) * b) ^ 2 :=
        pow_le_pow_left₀ (by positivity) h2d 2
      calc (n : ℝ) * ((2 * (d : ℝ)) ^ 2)
          ≤ (n : ℝ) * (((21 / 10) * b) ^ 2) :=
            mul_le_mul_of_nonneg_left hsq hnR.le
        _ = (441 / 100) * ((n : ℝ) * b ^ 2) := by ring
    have hblock2 : (2 : ℝ) * (C0 : ℝ) * (K : ℝ) ≤
        (2331 / 100) * ((n : ℝ) * b ^ 2) := by
      have hK_nonneg : (0 : ℝ) ≤ (K : ℝ) := Nat.cast_nonneg K
      have hbound_nonneg : (0 : ℝ) ≤ (21 / 10) * b * s := by positivity
      have hmul := mul_le_mul hC0_real hK_le hK_nonneg hbound_nonneg
      have hbsq : (b * s) ^ 2 = (n : ℝ) * b ^ 2 := by
        rw [mul_pow, hs2]; ring
      have hsq : ((21 / 10) * b * s) * ((111 / 20) * b * s) =
          (2331 / 200) * ((n : ℝ) * b ^ 2) := by
        have h2 : ((21 / 10) * b * s) * ((111 / 20) * b * s) =
            ((21 / 10) * (111 / 20)) * (b * s) ^ 2 := by ring
        rw [h2, hbsq]; ring
      have hmul2 : (2 : ℝ) * (((21 / 10) * b * s) * ((111 / 20) * b * s)) =
          (2331 / 100) * ((n : ℝ) * b ^ 2) := by
        rw [hsq]; ring
      calc (2 : ℝ) * (C0 : ℝ) * (K : ℝ)
          = 2 * ((C0 : ℝ) * (K : ℝ)) := by ring
        _ ≤ 2 * (((21 / 10) * b * s) * ((111 / 20) * b * s)) :=
            mul_le_mul_of_nonneg_left hmul (by norm_num)
        _ = (2331 / 100) * ((n : ℝ) * b ^ 2) := hmul2
    have heligR : (L : ℝ) ≤ ((eligibleOrdered H (2 * d) U).card : ℝ) := by
      have hpos : (0 : ℝ) < (n : ℝ) * b ^ 2 :=
        mul_pos hnR (pow_pos (by linarith : (0 : ℝ) < b) 2)
      linarith [hcardR, hprod_low, hblock1, hblock2, hL_le, hpos]
    exact_mod_cast heligR
  -- The union-bound inequality required by `process_claim`.
  have hineq : (2 : ℝ) ^ n * ((((n * n - L : ℕ) : ℝ) / (n * n : ℝ)) ^ m) < 1 := by
    have hN2pos : (0 : ℝ) < (n : ℝ) * (n : ℝ) := mul_pos hnR hnR
    have hN2cast : ((n * n : ℕ) : ℝ) = (n : ℝ) * (n : ℝ) := by push_cast; ring
    have hsubcast : ((n * n - L : ℕ) : ℝ) = (n : ℝ) * (n : ℝ) - (L : ℝ) := by
      rw [Nat.cast_sub hL_nat]; push_cast; ring
    set r := (((n * n - L : ℕ) : ℝ) / (n * n : ℝ)) with hr_def
    have hr_eq : r = 1 - (L : ℝ) / ((n : ℝ) * (n : ℝ)) := by
      rw [hr_def, hsubcast, sub_div, div_self (ne_of_gt hN2pos)]
    have hr_nonneg : 0 ≤ r := by
      rw [hr_eq]
      have hLle : (L : ℝ) ≤ (n : ℝ) * (n : ℝ) := by
        have h : (L : ℝ) ≤ ((n * n : ℕ) : ℝ) := by exact_mod_cast hL_nat
        rw [hN2cast] at h; exact h
      have h : (L : ℝ) / ((n : ℝ) * (n : ℝ)) ≤ 1 := by
        rw [div_le_one hN2pos]; exact hLle
      linarith
    -- `m * L / n ^ 2 > n`.
    have hML : (n : ℝ) < (m : ℝ) * (L : ℝ) / ((n : ℝ) * (n : ℝ)) := by
      have hnum : (b ^ 2 * s) * (b ^ 2 * (n : ℝ)) ≤ (m : ℝ) * (L : ℝ) :=
        mul_le_mul hm_ge hL_ge (by positivity) (by positivity)
      have hdiv : (b ^ 2 * s) * (b ^ 2 * (n : ℝ)) / ((n : ℝ) * (n : ℝ)) =
          b ^ 4 * s / (n : ℝ) := by
        field_simp
      have hge : (2 : ℝ) * (n : ℝ) ≤ b ^ 4 * s / (n : ℝ) := by
        rw [le_div_iff₀ hnR]
        have h1 : (2 * (n : ℝ) * s) * s ≤ b ^ 4 * s := by
          have h := mul_le_mul_of_nonneg_right hunion hs_pos.le
          -- `hunion : 2 * n * s ≤ b ^ 4`; multiply by `s`.
          have h2 : (2 * (n : ℝ) * s) * s = (2 * (n : ℝ) * Real.sqrt n) * s := by
            rw [hs_def]
          rw [h2] at h
          exact h
        calc (2 : ℝ) * (n : ℝ) * (n : ℝ) = (2 * (n : ℝ) * s) * s := by
              rw [← hs2]; ring
          _ ≤ b ^ 4 * s := h1
      have hdiv2 : (b ^ 2 * s) * (b ^ 2 * (n : ℝ)) / ((n : ℝ) * (n : ℝ)) ≥
          (2 : ℝ) * (n : ℝ) := by rw [hdiv]; exact hge
      have hle : (b ^ 2 * s) * (b ^ 2 * (n : ℝ)) / ((n : ℝ) * (n : ℝ)) ≤
          (m : ℝ) * (L : ℝ) / ((n : ℝ) * (n : ℝ)) :=
        div_le_div_of_nonneg_right hnum hN2pos.le
      linarith
    -- Exponential bound for the ratio.
    have hexp : r ^ m ≤ Real.exp (-((m : ℝ) * (L : ℝ) / ((n : ℝ) * (n : ℝ)))) := by
      have h1 : r ≤ Real.exp (-((L : ℝ) / ((n : ℝ) * (n : ℝ)))) := by
        have h := Real.add_one_le_exp (-((L : ℝ) / ((n : ℝ) * (n : ℝ))))
        rw [hr_eq]
        linarith
      have h2 : (Real.exp (-((L : ℝ) / ((n : ℝ) * (n : ℝ))))) ^ m =
          Real.exp (-((m : ℝ) * (L : ℝ) / ((n : ℝ) * (n : ℝ)))) := by
        rw [← Real.exp_nat_mul]
        congr 1
        field_simp
      calc r ^ m ≤ (Real.exp (-((L : ℝ) / ((n : ℝ) * (n : ℝ))))) ^ m :=
            pow_le_pow_left₀ hr_nonneg h1 m
        _ = Real.exp (-((m : ℝ) * (L : ℝ) / ((n : ℝ) * (n : ℝ)))) := h2
    have h2n : (2 : ℝ) ^ n ≤ Real.exp (n : ℝ) := by
      have h1 : (2 : ℝ) ≤ Real.exp 1 := by
        have h := Real.add_one_le_exp (1 : ℝ)
        norm_num at h
        exact h
      calc (2 : ℝ) ^ n ≤ (Real.exp 1) ^ n := pow_le_pow_left₀ (by norm_num) h1 n
        _ = Real.exp (n : ℝ) := by rw [← Real.exp_nat_mul]; simp
    have hprod : (2 : ℝ) ^ n * r ^ m ≤
        Real.exp ((n : ℝ) - (m : ℝ) * (L : ℝ) / ((n : ℝ) * (n : ℝ))) := by
      calc (2 : ℝ) ^ n * r ^ m
          ≤ Real.exp (n : ℝ) * Real.exp (-((m : ℝ) * (L : ℝ) / ((n : ℝ) * (n : ℝ)))) :=
            mul_le_mul h2n hexp (by positivity) (Real.exp_nonneg _)
        _ = Real.exp ((n : ℝ) - (m : ℝ) * (L : ℝ) / ((n : ℝ) * (n : ℝ))) := by
            rw [← Real.exp_add, sub_eq_add_neg]
    have hexp_lt : Real.exp ((n : ℝ) - (m : ℝ) * (L : ℝ) / ((n : ℝ) * (n : ℝ))) < 1 := by
      have hneg : (n : ℝ) - (m : ℝ) * (L : ℝ) / ((n : ℝ) * (n : ℝ)) < 0 := by linarith
      calc Real.exp ((n : ℝ) - (m : ℝ) * (L : ℝ) / ((n : ℝ) * (n : ℝ)))
          < Real.exp 0 := Real.exp_strictMono hneg
        _ = 1 := Real.exp_zero
    exact lt_of_le_of_lt hprod hexp_lt
  -- Apply the process claim.
  obtain ⟨H, hGH, hH, hHsmall⟩ := process_claim hG (d := d) (K := K) (m := m)
    (L := L) hmax_nat hL hL_nat hineq hn
  -- Deterministic finish, replayed from `H` (not from `G`).
  obtain ⟨H', hHH', hH'free, hH'diam⟩ := exists_maximal_triangle_free_extension hH
  have hαH' : ∀ U : Finset (Fin n), IsIndep H' U → U.card ≤ K - 1 := by
    intro U hU
    have hUH : IsIndep H U := isIndep_of_le hHH' hU
    have hlt := hHsmall U hUH
    omega
  have hmaxH' : maxDeg H' ≤ K - 1 := maxDeg_le_of_forall_isIndep hH'free hαH'
  have hh2 : h2 G ≤ H'.edgeFinset.card :=
    h2_le_of_extension (le_trans hGH hHH') hH'free hH'diam
  have htwo : 2 * H'.edgeFinset.card ≤ n * maxDeg H' := two_mul_card_edgeFinset_le H'
  have hnat : 2 * h2 G ≤ n * (K - 1) := by
    calc 2 * h2 G ≤ 2 * H'.edgeFinset.card := Nat.mul_le_mul_left 2 hh2
      _ ≤ n * maxDeg H' := htwo
      _ ≤ n * (K - 1) := Nat.mul_le_mul_left n hmaxH'
  have hnatR : (2 : ℝ) * (h2 G : ℝ) ≤ (n : ℝ) * ((K - 1 : ℕ) : ℝ) := by
    exact_mod_cast hnat
  have hK1R : ((K - 1 : ℕ) : ℝ) ≤ (K : ℝ) := by
    have h : K - 1 ≤ K := Nat.sub_le K 1
    exact_mod_cast h
  have hfinal : (2 : ℝ) * (h2 G : ℝ) ≤ (111 / 20) * b * (n : ℝ) * s := by
    calc (2 : ℝ) * (h2 G : ℝ)
        ≤ (n : ℝ) * (K : ℝ) := by
          apply le_trans hnatR
          exact mul_le_mul_of_nonneg_left hK1R hnR.le
      _ ≤ (n : ℝ) * ((111 / 20) * b * s) :=
          mul_le_mul_of_nonneg_left hK_le hnR.le
      _ = (111 / 20) * b * (n : ℝ) * s := by ring
  rw [hs_def] at hfinal
  linarith

/-- **Alon's Theorem 1.2, restated for `0 < ε < 1 / 8`.**
The crude `2 ^ n` union bound caps the range at `1 / 8`: the
exponent in the union-bound estimate is `3 / 2 - 4 * ε`, which beats
`n` only for `ε < 1 / 8`. Alon's `1 / 6` would need the sharper
entropy bound `(n choose 5cn) ≤ 2 ^ (H(5c) n)`. `erdos_618` itself
is proved in `Main618.lean` from the general lemma above with a
varying bound, not from this theorem at a fixed `ε`. This is the
auxiliary form proved here; `Basic.lean` states it as
`theorem_1_2`. -/
theorem theorem_1_2_aux (ε : ℝ) (hε : 0 < ε) (hε8 : ε < 1 / 8) :
    ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n → ∀ G : SimpleGraph (Fin n),
      G.CliqueFree 3 →
      (maxDeg G : ℝ) ≤ (n : ℝ) ^ (1 / 2 - ε) →
      (h2 G : ℝ) < 3 * (n : ℝ) ^ (2 - ε) := by
  classical
  have ha1 : (0 : ℝ) < 1 / 2 - ε := by linarith
  have ha2 : (0 : ℝ) < 1 / 2 - 4 * ε := by linarith
  have ht1 : Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ (1 / 2 - ε)) Filter.atTop
      Filter.atTop :=
    (tendsto_rpow_atTop ha1).comp tendsto_natCast_atTop_atTop
  have ht2 : Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ (1 / 2 - 4 * ε)) Filter.atTop
      Filter.atTop :=
    (tendsto_rpow_atTop ha2).comp tendsto_natCast_atTop_atTop
  have ev1 : ∀ᶠ n : ℕ in Filter.atTop, (20 : ℝ) ≤ (n : ℝ) ^ (1 / 2 - ε) :=
    ht1.eventually_ge_atTop 20
  have ev2 : ∀ᶠ n : ℕ in Filter.atTop, (2 : ℝ) ≤ (n : ℝ) ^ (1 / 2 - 4 * ε) :=
    ht2.eventually_ge_atTop 2
  have ev : ∀ᶠ n : ℕ in Filter.atTop, (20 : ℝ) ≤ (n : ℝ) ^ (1 / 2 - ε) ∧
      (2 : ℝ) ≤ (n : ℝ) ^ (1 / 2 - 4 * ε) ∧ 1 ≤ n := by
    filter_upwards [ev1, ev2, Filter.eventually_ge_atTop 1] with n h1 h2 h3
    exact ⟨h1, h2, h3⟩
  obtain ⟨n0, hn0⟩ := Filter.eventually_atTop.mp ev
  refine ⟨n0, ?_⟩
  intro n hn G hG hmax
  have hn_ge : 1 ≤ n := (hn0 n hn).2.2
  have hn_pos : 0 < n := by omega
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn_pos
  have hnR1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn_ge
  -- Real-power identities.
  have hprod : (n : ℝ) ^ (1 / 2 - ε) * (n : ℝ) * Real.sqrt n =
      (n : ℝ) ^ (2 - ε) := by
    calc (n : ℝ) ^ (1 / 2 - ε) * (n : ℝ) * Real.sqrt n
        = (n : ℝ) ^ (1 / 2 - ε) * ((n : ℝ) ^ (1 : ℝ)) *
            ((n : ℝ) ^ (1 / 2 : ℝ)) := by
          rw [Real.sqrt_eq_rpow, Real.rpow_one]
      _ = (n : ℝ) ^ (2 - ε) := by
          rw [← Real.rpow_add hnR, ← Real.rpow_add hnR]
          congr 1
          ring
  have hnsqrt : (n : ℝ) * Real.sqrt n = (n : ℝ) ^ (3 / 2 : ℝ) := by
    calc (n : ℝ) * Real.sqrt n
        = ((n : ℝ) ^ (1 : ℝ)) * ((n : ℝ) ^ (1 / 2 : ℝ)) := by
          rw [Real.sqrt_eq_rpow, Real.rpow_one]
      _ = (n : ℝ) ^ (3 / 2 : ℝ) := by
          rw [← Real.rpow_add hnR]
          congr 1
          ring
  have hb4 : ((n : ℝ) ^ (1 / 2 - ε)) ^ 4 = (n : ℝ) ^ (2 - 4 * ε) := by
    rw [← Real.rpow_natCast _ 4, ← Real.rpow_mul hnR.le]
    congr 1
    ring
  have hb_le : (n : ℝ) ^ (1 / 2 - ε) ≤ Real.sqrt n := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hnR1 (by linarith)
  have hunion : 2 * (n : ℝ) * Real.sqrt n ≤
      ((n : ℝ) ^ (1 / 2 - ε)) ^ 4 := by
    have hsplit : (n : ℝ) ^ (2 - 4 * ε) =
        (n : ℝ) ^ (3 / 2 : ℝ) * (n : ℝ) ^ (1 / 2 - 4 * ε) := by
      rw [← Real.rpow_add hnR]
      congr 1
      ring
    have h2le : (2 : ℝ) ≤ (n : ℝ) ^ (1 / 2 - 4 * ε) := (hn0 n hn).2.1
    have hX : (0 : ℝ) ≤ (n : ℝ) ^ (3 / 2 : ℝ) := Real.rpow_nonneg hnR.le _
    calc 2 * (n : ℝ) * Real.sqrt n
        = 2 * ((n : ℝ) ^ (3 / 2 : ℝ)) := by rw [← hnsqrt]; ring
      _ ≤ (n : ℝ) ^ (3 / 2 : ℝ) * (n : ℝ) ^ (1 / 2 - 4 * ε) := by
          rw [mul_comm ((n : ℝ) ^ (3 / 2 : ℝ)) ((n : ℝ) ^ (1 / 2 - 4 * ε))]
          exact mul_le_mul_of_nonneg_right h2le hX
      _ = (n : ℝ) ^ (2 - 4 * ε) := hsplit.symm
      _ = ((n : ℝ) ^ (1 / 2 - ε)) ^ 4 := hb4.symm
  have hgen := h2_bound_of_degree_bound hG ((n : ℝ) ^ (1 / 2 - ε))
    (Real.rpow_nonneg hnR.le _) (hn0 n hn).1 hb_le hmax hunion hn_pos
  have hXpos : (0 : ℝ) < (n : ℝ) ^ (2 - ε) := Real.rpow_pos_of_pos hnR _
  calc (h2 G : ℝ)
      ≤ (111 / 40) * (n : ℝ) ^ (1 / 2 - ε) * (n : ℝ) * Real.sqrt n := hgen
    _ = (111 / 40) * (n : ℝ) ^ (2 - ε) := by rw [← hprod]; ring
    _ < 3 * (n : ℝ) ^ (2 - ε) :=
        mul_lt_mul_of_pos_right (by norm_num) hXpos

end Jsp618
