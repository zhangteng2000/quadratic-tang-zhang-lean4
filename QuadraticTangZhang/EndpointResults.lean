import QuadraticTangZhang.Reciprocal
import QuadraticTangZhang.Boundary
import Sendov.Analytic.PolarBase

/-! # Quadratic Tang--Zhang inequality at the normalized endpoints -/

namespace QuadraticTangZhang
open Polynomial

theorem origin_strict (p : ℂ[X]) (hdeg : 2 ≤ p.natDegree)
    (hroots : RootsInClosedDisk p) (hpzero : p.eval 0 = 0) :
    (p.natDegree - 1 : ℕ) < criticalEnergy p 0 := by
  have hp0 : p ≠ 0 := by intro h; simp [h] at hdeg
  have hd0 : p.derivative ≠ 0 := derivative_ne_zero.mpr (by omega)
  by_cases hsimple : p.derivative.eval 0 ≠ 0
  · by_contra hlt
    let q := criticalReciprocals p 0
    have hqcard : q.card = p.natDegree - 1 := criticalReciprocals_card _ _
    have hqpos : 0 < q.card := by omega
    have hqrpos : (0 : ℝ) < q.card := by exact_mod_cast hqpos
    have hq0 := criticalReciprocals_ne_zero p 0 hsimple
    have hqsum : (q.map fun v => ‖v‖ ^ 2).sum ≤ (q.card : ℝ) := by
      rw [hqcard]
      exact reciprocal_sum_le_of_energy_le p 0 hsimple (le_of_not_gt hlt)
    have havg : (q.map fun v => ‖v‖ ^ 2).sum / q.card ≤ 1 := (div_le_one hqrpos).mpr hqsum
    have hnonneg : ∀ y ∈ q.map (fun v => ‖v‖ ^ 2), (0 : ℝ) ≤ y := by
      intro y hy
      obtain ⟨v, hv, rfl⟩ := Multiset.mem_map.mp hy
      exact sq_nonneg _
    have hpow := pow_le_one₀ (n := q.card) (div_nonneg (Multiset.sum_nonneg hnonneg) hqrpos.le) havg
    have hamgm := Sendov.Multiset.prod_le_mean_pow (q.map fun v => ‖v‖ ^ 2) hnonneg
    rw [Multiset.card_map, Sendov.prod_map_sq] at hamgm
    have hqnorm : ‖q.prod‖ ≤ 1 := by
      rw [Sendov.norm_multiset_prod]
      nlinarith [hamgm.trans hpow, Sendov.prod_map_norm_nonneg q id]
    obtain ⟨z, hzcard, hzroots, hpz⟩ := Sendov.exists_root_multiset (by omega : 1 ≤ p.natDegree)
      rfl hroots hpzero
    have hpq := criticalReciprocals_factorization p 0
    have hden := Sendov.prod_sub_mul_prod (leadingCoeff_ne_zero.mpr hp0) hq0 hpz hpq
    have hdenNorm := congrArg (fun w : ℂ => ‖w‖) hden
    simp only [norm_mul, Sendov.norm_prod_map, zero_sub, norm_neg, Complex.norm_natCast] at hdenNorm
    have hzprod : (z.map fun w => ‖w‖).prod ≤ 1 := by
      have h := Sendov.prod_map_le_of_le (s := z) (f := id) (g := fun _ => (1 : ℂ)) (by
        intro w hw
        simpa using hzroots w hw)
      simpa using h
    have hprod : ‖q.prod‖ * (z.map fun w => ‖w‖).prod ≤ 1 := by
      calc
        _ ≤ ‖q.prod‖ * 1 := mul_le_mul_of_nonneg_left hzprod (norm_nonneg _)
        _ ≤ 1 := by simpa using hqnorm
    have hn : (2 : ℝ) ≤ p.natDegree := by exact_mod_cast hdeg
    change ‖q.prod‖ * (z.map fun w => ‖w‖).prod = _ at hdenNorm
    linarith
  · exact main_at_common_zero ((mem_roots hd0).mpr (not_ne_iff.mp hsimple))

theorem boundary_inequality (p : ℂ[X]) (hdeg : 2 ≤ p.natDegree)
    (hroots : RootsInClosedDisk p) (hpone : p.eval 1 = 0) :
    (p.natDegree - 1 : ℕ) ≤ criticalEnergy p 1 := by
  have hp0 : p ≠ 0 := by intro h; simp [h] at hdeg
  have hd0 : p.derivative ≠ 0 := derivative_ne_zero.mpr (by omega)
  by_cases hsimple : p.derivative.eval 1 ≠ 0
  · obtain ⟨P, hP⟩ : (X - C (1 : ℂ)) ∣ p := dvd_iff_isRoot.mpr hpone
    have hP1 : P.eval 1 ≠ 0 := by simpa [hP, derivative_mul] using hsimple
    have hP0 : P ≠ 0 := by intro h; simp [h] at hP1
    have hPr : ∀ z ∈ P.roots, ‖z‖ ≤ 1 := by
      intro z hz
      apply hroots z ((mem_roots hp0).mpr _)
      have hzval : P.eval z = 0 := isRoot_of_mem_roots hz
      simp [hP, hzval]
    have hdegP : P.natDegree = p.natDegree - 1 := by
      rw [hP, natDegree_mul (X_sub_C_ne_zero 1) hP0, natDegree_X_sub_C]
      omega
    have hS := boundary_secondMoment_factored P hP1 hPr
    rw [criticalEnergy_eq_ofReal p 1 hsimple]
    have hS' : ((p.natDegree - 1 : ℕ) : ℝ) ≤
        ((criticalReciprocals p 1).map Complex.normSq).sum := by
      simpa only [criticalReciprocals, hP, Multiset.map_map, Function.comp_def,
        one_div, hdegP] using hS
    have h := ENNReal.ofReal_le_ofReal hS'
    simpa only [ENNReal.ofReal_natCast] using h
  · exact (main_at_common_zero ((mem_roots hd0).mpr (not_ne_iff.mp hsimple))).le

end QuadraticTangZhang
