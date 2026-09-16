import QuadraticTangZhang.EndpointResults
import QuadraticTangZhang.LowDegreeResult

/-! # Rotation covariance, preserving multiplicities and reciprocal energies -/

namespace QuadraticTangZhang
open Polynomial

noncomputable def rotatePolynomial (ω : ℂ) (p : ℂ[X]) : ℂ[X] := p.comp (C ω * X)

@[simp] theorem eval_rotatePolynomial (ω : ℂ) (p : ℂ[X]) (z : ℂ) :
    (rotatePolynomial ω p).eval z = p.eval (ω * z) := by
  simp [rotatePolynomial, eval_comp]

theorem natDegree_rotatePolynomial {ω : ℂ} (hω : ω ≠ 0) (p : ℂ[X]) :
    (rotatePolynomial ω p).natDegree = p.natDegree := by
  rw [rotatePolynomial, natDegree_comp, natDegree_C_mul hω, natDegree_X, mul_one]

theorem derivative_rotatePolynomial (ω : ℂ) (p : ℂ[X]) :
    (rotatePolynomial ω p).derivative = C ω * rotatePolynomial ω p.derivative := by
  simp only [rotatePolynomial, derivative_comp, derivative_mul, derivative_C,
    derivative_X, zero_mul, mul_one, zero_add]

theorem roots_rotatePolynomial {ω : ℂ} (hω : ‖ω‖ = 1) {p : ℂ[X]} (hp : p ≠ 0)
    (hroots : RootsInClosedDisk p) : RootsInClosedDisk (rotatePolynomial ω p) := by
  intro z hz
  have hzval : p.eval (ω * z) = 0 := by
    simpa using (isRoot_of_mem_roots hz : (rotatePolynomial ω p).eval z = 0)
  have h := hroots (ω * z) ((mem_roots hp).mpr hzval)
  simpa only [norm_mul, hω, one_mul] using h

theorem critical_roots_rotation {ω : ℂ} (hω : ω ≠ 0) (p : ℂ[X]) :
    ((rotatePolynomial ω p).derivative.roots.map (fun z => ω * z)) = p.derivative.roots := by
  rw [derivative_rotatePolynomial, roots_C_mul _ hω]
  have h := p.derivative.map_roots_comp_C_mul_X_add_C ω 0 (isUnit_iff_ne_zero.mpr hω)
  simpa only [map_zero, add_zero, rotatePolynomial] using h

theorem criticalEnergy_rotation {ω : ℂ} (hω : ‖ω‖ = 1) (p : ℂ[X]) (a : ℂ) :
    criticalEnergy (rotatePolynomial ω p) a = criticalEnergy p (ω * a) := by
  have hω0 : ω ≠ 0 := by intro h; simp [h] at hω
  unfold criticalEnergy
  rw [← critical_roots_rotation hω0 p, Multiset.map_map]
  apply congrArg Multiset.sum
  apply Multiset.map_congr rfl
  intro z hz
  simp only [Function.comp_def, reciprocalEnergy, ← mul_sub, norm_mul, hω, one_mul]

theorem unit_circle_inequality (p : ℂ[X]) (hdeg : 2 ≤ p.natDegree)
    (hroots : RootsInClosedDisk p) {a : ℂ} (hpa : p.eval a = 0) (ha : ‖a‖ = 1) :
    (p.natDegree - 1 : ℕ) ≤ criticalEnergy p a := by
  have hp0 : p ≠ 0 := by intro h; simp [h] at hdeg
  have ha0 : a ≠ 0 := by intro h; simp [h] at ha
  have hr := roots_rotatePolynomial ha hp0 hroots
  have hd := natDegree_rotatePolynomial ha0 p
  have hroot : (rotatePolynomial a p).eval 1 = 0 := by simpa using hpa
  have h := boundary_inequality (rotatePolynomial a p) (by simpa [hd] using hdeg) hr hroot
  rw [hd, criticalEnergy_rotation ha p 1, mul_one] at h
  exact h

/-- The full inequality for every complex zero, with arbitrary multiplicities, in degrees 2--5. -/
theorem low_degree_inequality (p : ℂ[X]) (hdeg : 2 ≤ p.natDegree) (hdeg5 : p.natDegree ≤ 5)
    (hroots : RootsInClosedDisk p) {a : ℂ} (hpa : p.eval a = 0) :
    (p.natDegree - 1 : ℕ) ≤ criticalEnergy p a := by
  have hp0 : p ≠ 0 := by intro h; simp [h] at hdeg
  by_cases ha0 : a = 0
  · subst a
    exact (origin_strict p hdeg hroots hpa).le
  have hrpos : 0 < ‖a‖ := norm_pos_iff.mpr ha0
  have hrle : ‖a‖ ≤ 1 := hroots a ((mem_roots hp0).mpr hpa)
  by_cases hr1 : ‖a‖ = 1
  · exact unit_circle_inequality p hdeg hroots hpa hr1
  have hrlt : ‖a‖ < 1 := lt_of_le_of_ne hrle hr1
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
    (by simpa [hd] using hdeg5) (roots_rotatePolynomial hω hp0 hroots) hrpos hrlt hroot
  rw [hd, criticalEnergy_rotation hω p _, hωr] at h
  exact h.le

end QuadraticTangZhang
