import QuadraticTangZhang.Statement
import Mathlib.Tactic

/-! # The equality family c (X^n - omega): all critical points and exact energy -/

namespace QuadraticTangZhang
open Polynomial

noncomputable def extremalPolynomial (c ω : ℂ) (n : ℕ) : ℂ[X] := C c * (X ^ n - C ω)

theorem extremal_derivative (c ω : ℂ) (n : ℕ) :
    (extremalPolynomial c ω n).derivative = C (c * n) * X ^ (n - 1) := by
  simp [extremalPolynomial, derivative_mul, derivative_X_pow, map_mul, mul_assoc]

theorem extremal_critical_roots {c ω : ℂ} (hc : c ≠ 0) {n : ℕ} (hn : 0 < n) :
    (extremalPolynomial c ω n).derivative.roots = (n - 1) • ({0} : Multiset ℂ) := by
  rw [extremal_derivative, roots_C_mul _ (mul_ne_zero hc (by exact_mod_cast ne_of_gt hn)), roots_X_pow]

theorem extremal_root_norm {c ω a : ℂ} (hc : c ≠ 0) (hω : ‖ω‖ = 1)
    {n : ℕ} (hn : 0 < n) (ha : (extremalPolynomial c ω n).eval a = 0) : ‖a‖ = 1 := by
  have hp : a ^ n = ω := by
    simpa [extremalPolynomial, hc, sub_eq_zero] using ha
  have hnorm : ‖a‖ ^ n = 1 := by
    rw [← norm_pow, hp, hω]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg a) (ne_of_gt hn)).mp hnorm

theorem extremal_energy {c ω a : ℂ} (hc : c ≠ 0) (hω : ‖ω‖ = 1)
    {n : ℕ} (hn : 0 < n) (ha : (extremalPolynomial c ω n).eval a = 0) :
    criticalEnergy (extremalPolynomial c ω n) a = (n - 1 : ℕ) := by
  have hnorm := extremal_root_norm hc hω hn ha
  have hterm : reciprocalEnergy a 0 = 1 := by simp [reciprocalEnergy, hnorm]
  unfold criticalEnergy
  rw [extremal_critical_roots hc hn]
  simp only [Multiset.map_nsmul, Multiset.map_singleton, Multiset.sum_nsmul,
    Multiset.sum_singleton, hterm, nsmul_eq_mul, mul_one]

end QuadraticTangZhang
