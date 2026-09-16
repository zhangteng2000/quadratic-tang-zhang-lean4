import QuadraticTangZhang.LargeDegreeResult
import QuadraticTangZhang.Certificate.Assembly
import QuadraticTangZhang.InteriorReduction

namespace QuadraticTangZhang
open Polynomial

/-- K follows from the finite certificate, using the polynomial-to-scalar bridge. -/
theorem finite_degree_interior_of_certificate (hchecks : CertificateData.allBlocksAccepted=true)
    (p : ℂ[X]) (hdeg : 6 ≤ p.natDegree) (hdeg1 : p.natDegree ≤ 1000000)
    (hroots : RootsInClosedDisk p) {a : ℝ} (ha : 0<a) (ha1 : a<1)
    (hpa : p.eval (a:ℂ)=0) : (p.natDegree-1:ℕ) < criticalEnergy p (a:ℂ) := by
  apply interior_of_scalar_exclusion p hdeg hroots ha ha1 hpa
  intro x s r hw
  exact CertificateData.finite_scalar_exclusion_of_checks hchecks (by omega) (by omega) hw

/-- M combines the finite range and the entire infinite range. -/
theorem remaining_interior_of_certificate (hchecks : CertificateData.allBlocksAccepted=true) :
    RemainingInteriorStatement := by
  intro p hdeg hroots a ha ha1 hpa
  by_cases hn : p.natDegree ≤ 1000000
  · exact finite_degree_interior_of_certificate hchecks p hdeg hn hroots ha ha1 hpa
  · exact large_degree_interior p (by omega) hroots ha ha1 hpa

/-- The only computational input is the explicitly stated finite Boolean assertion. -/
theorem main_and_equality_of_certificate (hchecks : CertificateData.allBlocksAccepted=true) :
    MainStatement ∧ EqualityStatement :=
  main_and_equality_of_remaining (remaining_interior_of_certificate hchecks)

end QuadraticTangZhang
