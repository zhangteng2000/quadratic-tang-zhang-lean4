import QuadraticTangZhang.BoundaryEquality

/-! # Complete equality classification in degrees 2 through 5 -/

namespace QuadraticTangZhang
open Polynomial

theorem low_degree_strict_interior (p : ℂ[X]) (hdeg : 2 ≤ p.natDegree)
    (hdeg5 : p.natDegree ≤ 5) (hroots : RootsInClosedDisk p) {a : ℂ}
    (hpa : p.eval a = 0) (ha : ‖a‖ < 1) :
    (p.natDegree - 1 : ℕ) < criticalEnergy p a := by
  have hp0 : p ≠ 0 := by intro h; simp [h] at hdeg
  by_cases ha0 : a = 0
  · subst a
    exact origin_strict p hdeg hroots hpa
  have hrpos : 0 < ‖a‖ := norm_pos_iff.mpr ha0
  let ω := a / ((‖a‖ : ℝ) : ℂ)
  have hrC : ((‖a‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hrpos
  have hω0 : ω ≠ 0 := div_ne_zero ha0 hrC
  have hω : ‖ω‖ = 1 := by
    dsimp [ω]
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hrpos, div_self (ne_of_gt hrpos)]
  have hωr : ω * ((‖a‖ : ℝ) : ℂ) = a := div_mul_cancel₀ _ hrC
  have hroot : (rotatePolynomial ω p).eval ((‖a‖ : ℝ) : ℂ) = 0 := by
    rw [eval_rotatePolynomial, hωr, hpa]
  have hd := natDegree_rotatePolynomial hω0 p
  have h := low_degree_interior (rotatePolynomial ω p) (by simpa [hd] using hdeg)
    (by simpa [hd] using hdeg5) (roots_rotatePolynomial hω hp0 hroots) hrpos ha hroot
  rwa [hd, criticalEnergy_rotation hω p _, hωr] at h

theorem low_degree_equality_iff (p : ℂ[X]) (hdeg : 2 ≤ p.natDegree)
    (hdeg5 : p.natDegree ≤ 5) (hroots : RootsInClosedDisk p) {a : ℂ}
    (hpa : p.eval a = 0) : criticalEnergy p a = (p.natDegree - 1 : ℕ) ↔ Extremal p := by
  refine ⟨fun heq => ?_, energy_of_extremal p hdeg hpa⟩
  have hp0 : p ≠ 0 := by intro h; simp [h] at hdeg
  have hrle : ‖a‖ ≤ 1 := hroots a ((mem_roots hp0).mpr hpa)
  have ha : ‖a‖ = 1 := by
    by_contra hne
    have h := low_degree_strict_interior p hdeg hdeg5 hroots hpa (lt_of_le_of_ne hrle hne)
    rw [heq] at h
    exact lt_irrefl _ h
  exact extremal_of_unit_circle_equality p hdeg hroots hpa ha heq

/-- The manuscript's theorem, including the iff statement, fully checked for degrees 2--5. -/
theorem main_degrees_two_to_five (p : ℂ[X]) (hdeg : 2 ≤ p.natDegree)
    (hdeg5 : p.natDegree ≤ 5) (hroots : RootsInClosedDisk p) (a : ℂ) (ha : a ∈ p.roots) :
    (p.natDegree - 1 : ℕ) ≤ criticalEnergy p a ∧
      (criticalEnergy p a = (p.natDegree - 1 : ℕ) ↔ Extremal p) :=
  ⟨low_degree_inequality p hdeg hdeg5 hroots (isRoot_of_mem_roots ha),
    low_degree_equality_iff p hdeg hdeg5 hroots (isRoot_of_mem_roots ha)⟩

end QuadraticTangZhang
