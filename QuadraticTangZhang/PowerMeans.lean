import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Tactic

/-! # Transfer of the quadratic bound to every real exponent at least two -/

namespace QuadraticTangZhang
open scoped BigOperators

theorem quadratic_mean_power_le {m : ℕ} (hm : 0 < m) (t : Fin m → ℝ)
    (ht : ∀ i, 0 ≤ t i) {p : ℝ} (hp : 2 ≤ p) :
    ((∑ i, t i ^ 2) / m) ^ (p / 2) ≤ (∑ i, (t i) ^ p) / m := by
  have hm0 : (m : ℝ) ≠ 0 := by positivity
  have h := Real.rpow_arith_mean_le_arith_mean_rpow Finset.univ
    (fun _ : Fin m => (1 : ℝ) / m) (fun i => t i ^ 2)
    (fun _ _ => by positivity)
    (by simp [hm0]) (fun _ _ => sq_nonneg _) (show 1 ≤ p / 2 by linarith)
  have hpow (i : Fin m) : (t i ^ 2 : ℝ) ^ (p / 2) = (t i) ^ p := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (ht i)]
    congr 1
    norm_num
    ring
  simp_rw [hpow, ← Finset.mul_sum, one_div_mul_eq_div] at h
  exact h

theorem power_sum_ge_card {m : ℕ} (hm : 0 < m) (t : Fin m → ℝ)
    (ht : ∀ i, 0 ≤ t i) {p : ℝ} (hp : 2 ≤ p)
    (hs : (m : ℝ) ≤ ∑ i, t i ^ 2) : (m : ℝ) ≤ ∑ i, (t i) ^ p := by
  have hmpos : (0 : ℝ) < m := by positivity
  have havg : (1 : ℝ) ≤ (∑ i, t i ^ 2) / m := (le_div_iff₀ hmpos).mpr (by simpa)
  have hpow := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1) havg
    (show 0 ≤ p / 2 by linarith)
  rw [Real.one_rpow] at hpow
  have h := hpow.trans (quadratic_mean_power_le hm t ht hp)
  exact (le_div_iff₀ hmpos).mp h |>.trans' (by simp)

theorem quadratic_equality_of_power_equality {m : ℕ} (hm : 0 < m) (t : Fin m → ℝ)
    (ht : ∀ i, 0 ≤ t i) {p : ℝ} (hp : 2 ≤ p)
    (hs : (m : ℝ) ≤ ∑ i, t i ^ 2)
    (heq : (∑ i, (t i) ^ p) = m) : (∑ i, t i ^ 2) = m := by
  have hmpos : (0 : ℝ) < m := by positivity
  apply le_antisymm _ hs
  by_contra hle
  have hgt : (m : ℝ) < ∑ i, t i ^ 2 := lt_of_not_ge hle
  have havg : (1 : ℝ) < (∑ i, t i ^ 2) / m := (lt_div_iff₀ hmpos).mpr (by simpa)
  have hpow := Real.rpow_lt_rpow (by norm_num : (0 : ℝ) ≤ 1) havg
    (show 0 < p / 2 by linarith)
  rw [Real.one_rpow] at hpow
  have h := quadratic_mean_power_le hm t ht hp
  rw [heq, div_self (ne_of_gt hmpos)] at h
  exact (not_lt_of_ge h) hpow

end QuadraticTangZhang
