import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

/-! # The strict integral bound for degrees two through five -/

namespace QuadraticTangZhang

noncomputable def smallIntegral (a : ℝ) (k : ℕ) : ℝ :=
  ∫ t in (0 : ℝ)..1, (a + (1 - a ^ 2) * t) ^ k

theorem smallIntegral_mul (a : ℝ) (k : ℕ) :
    (1 - a ^ 2) * smallIntegral a k =
      ((a + (1 - a ^ 2)) ^ (k + 1) - a ^ (k + 1)) / (k + 1) := by
  have h := intervalIntegral.mul_integral_comp_add_mul (f := fun t : ℝ => t ^ k)
    (a := 0) (b := 1) (1 - a ^ 2) a
  simpa [smallIntegral, integral_pow] using h

theorem smallIntegral_one (a : ℝ) (ha : a ^ 2 ≠ 1) :
    1 - smallIntegral a 1 = (1 - a) ^ 2 / 2 := by
  have h := smallIntegral_mul a 1
  have hne : 1 - a ^ 2 ≠ 0 := sub_ne_zero.mpr (Ne.symm ha)
  apply (mul_left_cancel₀ hne)
  rw [mul_sub, h]
  norm_num
  ring

theorem smallIntegral_two (a : ℝ) (ha : a ^ 2 ≠ 1) :
    1 - smallIntegral a 2 = (2 - a) * (1 - a) ^ 2 * (a + 1) / 3 := by
  have h := smallIntegral_mul a 2
  have hne : 1 - a ^ 2 ≠ 0 := sub_ne_zero.mpr (Ne.symm ha)
  apply (mul_left_cancel₀ hne)
  rw [mul_sub, h]
  norm_num
  ring

theorem smallIntegral_three (a : ℝ) (ha : a ^ 2 ≠ 1) :
    1 - smallIntegral a 3 =
      (1 - a) ^ 2 * (a ^ 4 - 2 * a ^ 3 - 2 * a ^ 2 + 2 * a + 3) / 4 := by
  have h := smallIntegral_mul a 3
  have hne : 1 - a ^ 2 ≠ 0 := sub_ne_zero.mpr (Ne.symm ha)
  apply (mul_left_cancel₀ hne)
  rw [mul_sub, h]
  norm_num
  ring

theorem smallIntegral_four (a : ℝ) (ha : a ^ 2 ≠ 1) :
    1 - smallIntegral a 4 =
      (1 - a) ^ 3 * (1 + a) / 5 * (a ^ 4 - 3 * a ^ 3 + 3 * a + 4) := by
  have h := smallIntegral_mul a 4
  have hne : 1 - a ^ 2 ≠ 0 := sub_ne_zero.mpr (Ne.symm ha)
  apply (mul_left_cancel₀ hne)
  rw [mul_sub, h]
  norm_num
  ring

/-- Strict bound for each of the four integer powers, avoiding a power-mean black box. -/
theorem smallIntegral_lt_one {a : ℝ} (ha : 0 < a) (ha1 : a < 1)
    {k : ℕ} (hk : 1 ≤ k) (hk4 : k ≤ 4) : smallIntegral a k < 1 := by
  have hasq : a ^ 2 < 1 := by nlinarith
  have hapos : 0 < 1 - a := sub_pos.mpr ha1
  have hq3 : 0 < a ^ 4 - 2 * a ^ 3 - 2 * a ^ 2 + 2 * a + 3 := by
    have h := mul_pos ha (sub_pos.mpr hasq)
    nlinarith [sq_nonneg (a ^ 2)]
  have hq4 : 0 < a ^ 4 - 3 * a ^ 3 + 3 * a + 4 := by
    have h := mul_pos ha (sub_pos.mpr hasq)
    nlinarith [sq_nonneg (a ^ 2)]
  have h2 : 0 < 2 - a := by linarith
  interval_cases k
  · have h := smallIntegral_one a (ne_of_lt hasq)
    have : 0 < (1 - a) ^ 2 / 2 := by positivity
    linarith
  · have h := smallIntegral_two a (ne_of_lt hasq)
    have : 0 < (2 - a) * (1 - a) ^ 2 * (a + 1) / 3 := by positivity
    linarith
  · have h := smallIntegral_three a (ne_of_lt hasq)
    have : 0 < (1 - a) ^ 2 * (a ^ 4 - 2 * a ^ 3 - 2 * a ^ 2 + 2 * a + 3) / 4 := by positivity
    linarith
  · have h := smallIntegral_four a (ne_of_lt hasq)
    have : 0 < (1 - a) ^ 3 * (1 + a) / 5 * (a ^ 4 - 3 * a ^ 3 + 3 * a + 4) := by positivity
    linarith

end QuadraticTangZhang
