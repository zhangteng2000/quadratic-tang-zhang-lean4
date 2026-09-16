import QuadraticTangZhang.Polar
import QuadraticTangZhang.Reciprocal

/-! # Strict quadratic Tang--Zhang inequality at real interior roots, degrees 2--5 -/

namespace QuadraticTangZhang
open Polynomial MeasureTheory

theorem low_degree_interior (p : ℂ[X]) (hdeg : 2 ≤ p.natDegree) (hdeg5 : p.natDegree ≤ 5)
    (hroots : RootsInClosedDisk p) {a : ℝ} (ha : 0 < a) (ha1 : a < 1)
    (hpa : p.eval (a : ℂ) = 0) : (p.natDegree - 1 : ℕ) < criticalEnergy p (a : ℂ) := by
  have hp0 : p ≠ 0 := by intro h; simp [h] at hdeg
  have hd0 : p.derivative ≠ 0 := derivative_ne_zero.mpr (by omega)
  by_cases hsimple : p.derivative.eval (a : ℂ) ≠ 0
  · by_contra hlt
    have henergy : criticalEnergy p (a : ℂ) ≤ (p.natDegree - 1 : ℕ) := le_of_not_gt hlt
    let q := criticalReciprocals p (a : ℂ)
    have hqcard : q.card = p.natDegree - 1 := criticalReciprocals_card _ _
    have hqpos : 0 < q.card := by omega
    have hqrpos : (0 : ℝ) < q.card := by exact_mod_cast hqpos
    have hq0 : ∀ v ∈ q, v ≠ 0 := criticalReciprocals_ne_zero p _ hsimple
    have hqsum : (q.map fun v => ‖v‖ ^ 2).sum ≤ (q.card : ℝ) := by
      rw [hqcard]
      exact reciprocal_sum_le_of_energy_le p _ hsimple henergy
    let x := (q.map Complex.re).sum / q.card
    let s := (q.map fun v => ‖v‖ ^ 2).sum / q.card
    have hx : (q.map Complex.re).sum = (q.card : ℝ) * x := by dsimp [x]; field_simp
    have hs : (q.map fun v => ‖v‖ ^ 2).sum = (q.card : ℝ) * s := by dsimp [s]; field_simp
    have hs1 : s ≤ 1 := (div_le_one hqrpos).mpr hqsum
    have hxs : x ^ 2 ≤ s := multiset_mean_sq_le hqpos hx hs
    have hx1 : x ≤ 1 := by nlinarith [sq_nonneg (x - 1)]
    obtain ⟨z, hzcard, hzroots, hpz⟩ := Sendov.exists_root_multiset (by omega : 1 ≤ p.natDegree)
      rfl hroots hpa
    have hpq := criticalReciprocals_factorization p (a : ℂ)
    have hc0 := leadingCoeff_ne_zero.mpr hp0
    have ha0 : (a : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt ha
    have ha2 : (a : ℂ) ^ 2 ≠ 1 := by
      have h : a ^ 2 ≠ 1 := by nlinarith
      exact_mod_cast h
    have hpol := Sendov.polar_identity hc0 ha0 ha2 hzcard hqcard hq0 hpa hpz hpq
    have hden := Sendov.prod_sub_mul_prod hc0 hq0 hpz hpq
    have habs : |a| ≤ 1 := by rw [abs_of_pos ha]; exact ha1.le
    have hstar := Sendov.one_le_integral_prod_norm hdeg habs hzroots hpol hden
    have hraw := exact_polar_inequality hqpos hx hs hstar
    exact small_degree_polar_contradiction ha ha1 hx1 hxs hs1 (by omega) (by omega) hraw
  · have hmem : (a : ℂ) ∈ p.derivative.roots := (mem_roots hd0).mpr (not_ne_iff.mp hsimple)
    exact main_at_common_zero hmem

end QuadraticTangZhang
