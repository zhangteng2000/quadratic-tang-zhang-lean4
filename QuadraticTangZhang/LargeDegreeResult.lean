import QuadraticTangZhang.LargeNear
import QuadraticTangZhang.LargeAway
import QuadraticTangZhang.ScalarBridge

namespace QuadraticTangZhang
open Polynomial

/-- L, scalar form, on the entire infinite degree range. -/
theorem large_degree_scalar_exclusion {m : ℕ} (hm : 1000000 ≤ m)
    {a x s r : ℝ} (hw : ScalarConditions m a x s r) : False := by
  rcases le_total (1-a^2) (1/10:ℝ) with hnear | haway
  · exact large_near_scalar_exclusion hw hm hnear
  · exact large_away_scalar_exclusion hw hm haway

/-- L, the strict polynomial inequality for n ≥ 1,000,001 at real interior roots. -/
theorem large_degree_interior (p : ℂ[X]) (hdeg : 1000001 ≤ p.natDegree)
    (hroots : RootsInClosedDisk p) {a : ℝ} (ha : 0<a) (ha1 : a<1) (hpa : p.eval (a:ℂ)=0) :
    (p.natDegree-1:ℕ) < criticalEnergy p (a:ℂ) := by
  apply interior_of_scalar_exclusion p (by omega) hroots ha ha1 hpa
  intro x s r hw
  exact large_degree_scalar_exclusion (by omega) hw

#print axioms large_degree_interior

end QuadraticTangZhang
