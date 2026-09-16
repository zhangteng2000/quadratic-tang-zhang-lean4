import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! # Exact numerical comparisons used in the analytic tail

Bounds involving `exp` and `log` below are real inequalities, proved using
mathlib's certified exponential bounds. No external numerical oracle is used.
-/

namespace QuadraticTangZhang

theorem exp_one_bounds : (27 : ℝ) / 10 < Real.exp 1 ∧ Real.exp 1 < 11 / 4 := by
  constructor
  · linarith [Real.exp_one_gt_d9]
  · linarith [Real.exp_one_lt_d9]

theorem sqrt_exp_one_lt : Real.sqrt (Real.exp 1) < (5 : ℝ) / 3 := by
  rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < 5 / 3)]
  linarith [exp_one_bounds.2]

theorem log_million_bounds : (13 : ℝ) < Real.log 1000000 ∧ Real.log 1000000 < 14 := by
  constructor
  · apply (Real.lt_log_iff_exp_lt (by norm_num)).mpr
    have h := pow_lt_pow_left₀ exp_one_bounds.2 (Real.exp_pos 1).le (by norm_num : (13 : ℕ) ≠ 0)
    rw [Real.exp_one_pow] at h
    norm_num at h ⊢
    linarith
  · apply (Real.log_lt_iff_lt_exp (by norm_num)).mpr
    have h := pow_lt_pow_left₀ exp_one_bounds.1 (by norm_num : (0 : ℝ) ≤ 27 / 10)
      (by norm_num : (14 : ℕ) ≠ 0)
    rw [Real.exp_one_pow] at h
    norm_num at h ⊢
    linarith

theorem log_three_eighths_million : (12 : ℝ) < Real.log 375000 := by
  apply (Real.lt_log_iff_exp_lt (by norm_num)).mpr
  have h := pow_lt_pow_left₀ exp_one_bounds.2 (Real.exp_pos 1).le (by norm_num : (12 : ℕ) ≠ 0)
  rw [Real.exp_one_pow] at h
  norm_num at h ⊢
  linarith

theorem log_fifty_thousand : (4 : ℝ) < Real.log 50000 := by
  apply (Real.lt_log_iff_exp_lt (by norm_num)).mpr
  have h := pow_lt_pow_left₀ exp_one_bounds.2 (Real.exp_pos 1).le (by norm_num : (4 : ℕ) ≠ 0)
  rw [Real.exp_one_pow] at h
  norm_num at h ⊢
  linarith

theorem near_coefficient_base :
    (2048 * (5 / 3) / 81 : ℝ) * (10 / 9) ^ 3 *
      (1000000 ^ 2 * (1000000 + 1) / (1000000 - 1) ^ 3) < 60 := by norm_num

theorem decreasing_coefficient_base :
    (20 / 3 : ℝ) * (1000000 / (1000000 - 1)) ^ 2 < 7 := by norm_num

theorem near_endpoint_coefficient_base :
    4 * (5 / 3 : ℝ) * (1000000 / (1000000 - 1)) ^ 2 < 7 := by norm_num

theorem near_total_base :
    (60 / 1000000 : ℝ) + 7 / 1000000 ^ 2 < 61 / 1000000 ∧
      (61 / 1000000 : ℝ) < 9 / 20 := by norm_num

theorem near_exponent_base :
    (1000 / 6 : ℝ) > 56 ∧ (9 * 1000000 / 160 : ℝ) > 56 := by norm_num

theorem polar_log_exponent_base : (10 : ℝ) * (1 - 3 / 1000000) > 9 := by norm_num

theorem small_alpha_base :
    (16 * 16 ^ 2 : ℕ) < 2 ^ 17 ∧ (17 / 16 : ℝ) ^ 2 < 2 := by norm_num

theorem large_alpha_base : (1 / (2 * 1000000 ^ 3) : ℝ) < 1 / 4 := by norm_num

theorem sigma_base : ((1000000 - 1) / (1000000 + 2) : ℝ) > 99999 / 100000 := by norm_num

theorem degree_correction_base :
    (1 / (1 - 56 / (1000000 + 2)) : ℝ) < 1001 / 1000 := by norm_num

theorem small_a_power_base : (8 / 3 : ℝ) ^ 4 < 4 ^ 3 := by norm_num

theorem small_a_increasing_coefficient :
    (4 * (5 / 3) * (1001 / 1000) / (27 / 10) : ℝ) < 5 / 2 := by norm_num

theorem small_a_decreasing_coefficient :
    (7 * (1000000 + 2) / (24 * 1000000) : ℝ) < 292 / 1000 := by norm_num

theorem small_a_total : (292 / 1000 : ℝ) + 5 / 26 + 1 / 10000 < 1 / 2 := by norm_num

theorem cube_root_base : (72 : ℕ) ^ 3 < 375000 := by norm_num

theorem large_a_correction_base : (1 / (1 - 14 / 75000) : ℝ) < 1001 / 1000 := by norm_num

theorem large_a_increasing_coefficient :
    (5 / 12 : ℝ) * (1 / 27) * (1001 / 1000) < 16 / 1000 := by norm_num

theorem large_a_total :
    (112 / 1000000 : ℝ) + 8 / (3 * 1000000) + 16 / 1000 < 17 / 1000 ∧
      (17 / 1000 : ℝ) < 1 / 20 := by norm_num

theorem boundary_gap_base : (19 / 20 : ℝ) ^ 2 > 9 / 10 := by norm_num

end QuadraticTangZhang
