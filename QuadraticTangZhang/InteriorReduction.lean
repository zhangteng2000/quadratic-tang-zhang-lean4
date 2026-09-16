import QuadraticTangZhang.PowerCorollary

/-!
# Reduction to the normalized interior statement

This assembly layer proves that the unrestricted theorem and its equality
classification follow from `RemainingInteriorStatement`. The finite and
infinite degree arguments are connected in `FinalAssembly.lean`; the final
certificate is supplied in `MainTheorem.lean`.
-/

namespace QuadraticTangZhang
open Polynomial

/-- Strict inequality at a normalized interior zero in degrees at least 6. -/
def RemainingInteriorStatement : Prop :=
  ∀ (p : ℂ[X]), 6 ≤ p.natDegree → RootsInClosedDisk p →
    ∀ a : ℝ, 0 < a → a < 1 → p.eval (a : ℂ) = 0 →
      (p.natDegree - 1 : ℕ) < criticalEnergy p (a : ℂ)

theorem complex_interior_of_remaining (H : RemainingInteriorStatement)
    (p : ℂ[X]) (hdeg : 2 ≤ p.natDegree) (hroots : RootsInClosedDisk p)
    {a : ℂ} (hpa : p.eval a = 0) (ha : ‖a‖ < 1) :
    (p.natDegree - 1 : ℕ) < criticalEnergy p a := by
  by_cases hd5 : p.natDegree ≤ 5
  · exact low_degree_strict_interior p hdeg hd5 hroots hpa ha
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
  have h := H (rotatePolynomial ω p) (by rw [hd]; omega)
    (roots_rotatePolynomial hω hp0 hroots) ‖a‖ hrpos ha hroot
  rwa [hd, criticalEnergy_rotation hω p _, hωr] at h

/-- Assembly from an explicit proof of the normalized interior statement. -/
theorem main_and_equality_of_remaining (H : RemainingInteriorStatement) :
    MainStatement ∧ EqualityStatement := by
  constructor
  · intro p hd hr a hamem
    have ha := isRoot_of_mem_roots hamem
    have har := hr a hamem
    rcases eq_or_lt_of_le har with he | hl
    · exact unit_circle_inequality p hd hr ha he
    · exact (complex_interior_of_remaining H p hd hr ha hl).le
  · intro p hd hr a hamem
    have ha := isRoot_of_mem_roots hamem
    refine ⟨fun heq => ?_, energy_of_extremal p hd ha⟩
    have har := hr a hamem
    rcases eq_or_lt_of_le har with he | hl
    · exact extremal_of_unit_circle_equality p hd hr ha he heq
    · have h := complex_interior_of_remaining H p hd hr ha hl
      rw [heq] at h
      exact False.elim (lt_irrefl _ h)

end QuadraticTangZhang
