import QuadraticTangZhang.FinalAssembly
import QuadraticTangZhang.Certificate.Verified

namespace QuadraticTangZhang
open Polynomial

/-- K. Every degree from 6 through 1,000,000. -/
theorem finite_degree_interior (p : ℂ[X]) (hdeg : 6 ≤ p.natDegree)
    (hdeg1 : p.natDegree ≤ 1000000) (hroots : RootsInClosedDisk p)
    {a : ℝ} (ha : 0<a) (ha1 : a<1) (hpa : p.eval (a:ℂ)=0) :
    (p.natDegree-1:ℕ) < criticalEnergy p (a:ℂ) :=
  finite_degree_interior_of_certificate CertificateData.full_certificate_checked
    p hdeg hdeg1 hroots ha ha1 hpa

/-- M. The remaining interior statement is now a theorem with no unproved input. -/
theorem remainingInterior : RemainingInteriorStatement :=
  remaining_interior_of_certificate CertificateData.full_certificate_checked

/-- N. The quadratic Tang–Zhang inequality, in every degree n ≥ 2. -/
theorem mainStatement : MainStatement :=
  (main_and_equality_of_remaining remainingInterior).1

/-- The complete equality classification, in every degree n ≥ 2. -/
theorem equalityStatement : EqualityStatement :=
  (main_and_equality_of_remaining remainingInterior).2

theorem strict_interior (p : ℂ[X]) (hdeg : 2 ≤ p.natDegree)
    (hroots : RootsInClosedDisk p) {a : ℂ} (hpa : p.eval a=0) (ha : ‖a‖<1) :
    (p.natDegree-1:ℕ) < criticalEnergy p a :=
  complex_interior_of_remaining remainingInterior p hdeg hroots hpa ha

/-- The manuscript's main theorem with the inequality and equality case together. -/
theorem main_theorem (p : ℂ[X]) (hdeg : 2 ≤ p.natDegree)
    (hroots : RootsInClosedDisk p) {a : ℂ} (hpa : p.eval a=0) :
    (p.natDegree-1:ℕ) ≤ criticalEnergy p a ∧
      (criticalEnergy p a=(p.natDegree-1:ℕ) ↔ Extremal p) := by
  have hp0 : p ≠ 0 := by intro h; simp [h] at hdeg
  have hamem : a ∈ p.roots := (mem_roots hp0).mpr hpa
  exact ⟨mainStatement p hdeg hroots a hamem, equalityStatement p hdeg hroots a hamem⟩

/-- The manuscript's corollary for every real exponent λ ≥ 2, including equality. -/
theorem powers_ge_two (p : ℂ[X]) (hdeg : 2 ≤ p.natDegree)
    (hroots : RootsInClosedDisk p) {a : ℂ} (hpa : p.eval a=0)
    {ell : ℝ} (hell : 2 ≤ ell) :
    (p.natDegree-1:ℕ) ≤ criticalPowerEnergy p a ell ∧
      (criticalPowerEnergy p a ell=(p.natDegree-1:ℕ) ↔ Extremal p) := by
  have hmain := main_theorem p hdeg hroots hpa
  have hpower := power_corollary_of_quadratic p hdeg a hell hmain.1
  exact ⟨hpower.1, ⟨fun h => hmain.2.mp (hpower.2 h),
    fun h => power_energy_of_extremal p hdeg hpa h ell⟩⟩

#print axioms remainingInterior
#print axioms mainStatement
#print axioms equalityStatement
#print axioms powers_ge_two

end QuadraticTangZhang
