import QuadraticTangZhang.RectangleExclusion
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-! # E. Convexity and weighted chord quadrature -/

namespace QuadraticTangZhang
open MeasureTheory

def boxEnvelope (A h t : ℝ) : ℝ := 1-h*t-A^2*t*(1-t)

theorem boxEnvelope_nonneg {A h t : ℝ} (hA : A^2 ≤ 1) (hh : h ≤ 1)
    (ht : t ∈ Set.Icc (0:ℝ) 1) : 0 ≤ boxEnvelope A h t := by
  have h1 := mul_nonneg (sub_nonneg.mpr hh) ht.1
  have h2 := mul_nonneg (mul_nonneg (sub_nonneg.mpr hA) ht.1) (sub_nonneg.mpr ht.2)
  unfold boxEnvelope
  nlinarith [sq_nonneg (1-t)]

theorem boxEnvelope_le_one {A h t : ℝ} (hh : 0 ≤ h) (ht : t ∈ Set.Icc (0:ℝ) 1) :
    boxEnvelope A h t ≤ 1 := by
  have h1 := mul_nonneg hh ht.1
  have h2 := mul_nonneg (mul_nonneg (sq_nonneg A) ht.1) (sub_nonneg.mpr ht.2)
  unfold boxEnvelope
  linarith

theorem boxEnvelope_convex (A h : ℝ) : ConvexOn ℝ (Set.Icc (0:ℝ) 1) (boxEnvelope A h) := by
  refine ⟨convex_Icc _ _, ?_⟩
  intro x hx y hy u v hu hv huv
  simp only [smul_eq_mul]
  have hid : u*boxEnvelope A h x + v*boxEnvelope A h y - boxEnvelope A h (u*x+v*y) =
      A^2*u*v*(x-y)^2 := by
    have hvv : v=1-u := by linarith
    rw [hvv]
    unfold boxEnvelope
    ring
  have hnn : 0 ≤ A^2*u*v*(x-y)^2 := by positivity
  linarith

theorem boxEnvelope_rpow_convex {A h r : ℝ} (hA : A^2 ≤ 1) (hh : h ≤ 1) (hr : 1 ≤ r) :
    ConvexOn ℝ (Set.Icc (0:ℝ) 1) (fun t => boxEnvelope A h t ^ r) := by
  refine ⟨convex_Icc _ _, ?_⟩
  intro x hx y hy u v hu hv huv
  have hxy := (convex_Icc (0:ℝ) 1) hx hy hu hv huv
  have hb := (boxEnvelope_convex A h).2 hx hy hu hv huv
  have hp := Real.rpow_le_rpow (boxEnvelope_nonneg hA hh hxy) hb (by linarith : 0 ≤ r)
  have hj := (convexOn_rpow hr).2 (boxEnvelope_nonneg hA hh hx)
    (boxEnvelope_nonneg hA hh hy) hu hv huv
  exact hp.trans hj

theorem weighted_sq_div {u v x y d e : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hd : 0 < d) (he : 0 < e) (hden : 0 < u*d+v*e) :
    (u*x+v*y)^2/(u*d+v*e) ≤ u*x^2/d+v*y^2/e := by
  apply (div_le_iff₀ hden).mpr
  apply (mul_le_mul_iff_right₀ (mul_pos hd he)).mp
  have hnn := mul_nonneg (mul_nonneg hu hv) (sq_nonneg (e*x-d*y))
  have hid : (u*x^2/d+v*y^2/e)*(u*d+v*e)*(d*e) - (u*x+v*y)^2*(d*e) =
      u*v*(e*x-d*y)^2 := by field_simp; ring
  nlinarith

theorem convexOn_sq_div_affine {f : ℝ → ℝ} (hf : ConvexOn ℝ (Set.Icc (0:ℝ) 1) f)
    (hf0 : ∀ t ∈ Set.Icc (0:ℝ) 1, 0 ≤ f t) {d : ℝ} (hd : d < 1) :
    ConvexOn ℝ (Set.Icc (0:ℝ) 1) (fun t => (f t)^2/(1-d*t)) := by
  have hD (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) 1) : 0 < 1-d*t := by
    by_cases hd0 : 0 ≤ d
    · nlinarith [mul_nonneg hd0 (sub_nonneg.mpr ht.2)]
    · have h := mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hd0) ht.1
      linarith
  refine ⟨convex_Icc _ _, ?_⟩
  intro x hx y hy u v hu hv huv
  have hxy := (convex_Icc (0:ℝ) 1) hx hy hu hv huv
  have hconv := hf.2 hx hy hu hv huv
  simp only [smul_eq_mul] at *
  have hden : 1-d*(u*x+v*y) = u*(1-d*x)+v*(1-d*y) := by nlinarith [huv]
  have hsq := pow_le_pow_left₀ (hf0 _ hxy) hconv 2
  have hdiv := div_le_div_of_nonneg_right hsq (hD _ hxy).le
  have hweighted := weighted_sq_div (x := f x) (y := f y) hu hv (hD x hx) (hD y hy)
    (by rw [← hden]; exact hD _ hxy)
  rw [← hden] at hweighted
  exact hdiv.trans (by simpa only [mul_div_assoc] using hweighted)

theorem boxEnvelope_rpow_div_convex {A h r d : ℝ} (hA : A^2 ≤ 1) (hh : h ≤ 1)
    (hr : 2 ≤ r) (hd : d < 1) :
    ConvexOn ℝ (Set.Icc (0:ℝ) 1) (fun t => boxEnvelope A h t ^ r/(1-d*t)) := by
  have hf := boxEnvelope_rpow_convex hA hh (by linarith : 1 ≤ r/2)
  have hs := convexOn_sq_div_affine hf
    (fun t ht => Real.rpow_nonneg (boxEnvelope_nonneg hA hh ht) _) hd
  apply hs.congr
  intro t ht
  change (boxEnvelope A h t ^ (r/2))^2/(1-d*t) = boxEnvelope A h t^r/(1-d*t)
  congr 1
  rw [← Real.rpow_natCast, ← Real.rpow_mul (boxEnvelope_nonneg hA hh ht)]
  congr 1
  norm_num

theorem convex_chord_bound {f : ℝ → ℝ} {l z t : ℝ} (hz : 0 < z)
    (hf : ConvexOn ℝ (Set.Icc l (l+z)) f) (ht : t ∈ Set.Icc l (l+z)) :
    f t ≤ (l+z-t)/z*f l + (t-l)/z*f (l+z) := by
  have hu : 0 ≤ (l+z-t)/z := div_nonneg (by linarith [ht.2]) hz.le
  have hv : 0 ≤ (t-l)/z := div_nonneg (by linarith [ht.1]) hz.le
  have huv : (l+z-t)/z+(t-l)/z=1 := by field_simp; ring
  have h := hf.2 (show l ∈ Set.Icc l (l+z) by constructor <;> linarith)
    (show l+z ∈ Set.Icc l (l+z) by constructor <;> linarith) hu hv huv
  simp only [smul_eq_mul] at h
  have htform : (l+z-t)/z*l+(t-l)/z*(l+z)=t := by field_simp; ring
  rwa [htform] at h

theorem weighted_chord_integral (k : ℕ) (l z u v : ℝ) :
    (∫ t in l..(l+z), t^k*((l+z-t)/z*u+(t-l)/z*v)) =
      ((l+z)*u-l*v)/z * (((l+z)^(k+1)-l^(k+1))/(k+1)) +
        (v-u)/z * (((l+z)^(k+2)-l^(k+2))/(k+2)) := by
  have heq : (fun t : ℝ => t^k*((l+z-t)/z*u+(t-l)/z*v)) =
      (fun t : ℝ => ((l+z)*u-l*v)/z*t^k+(v-u)/z*t^(k+1)) := by
    funext t
    rw [pow_succ]
    ring
  rw [heq, intervalIntegral.integral_add
    ((by fun_prop : Continuous (fun t : ℝ => ((l+z)*u-l*v)/z*t^k)).intervalIntegrable _ _)
    ((by fun_prop : Continuous (fun t : ℝ => (v-u)/z*t^(k+1))).intervalIntegrable _ _),
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul,integral_pow,integral_pow]
  norm_num [Nat.add_assoc, add_assoc]

theorem weighted_convex_integral_le_chord (k : ℕ) {f : ℝ → ℝ} {l z : ℝ}
    (hl : 0 ≤ l) (hz : 0 < z) (hf : ConvexOn ℝ (Set.Icc l (l+z)) f)
    (hc : ContinuousOn f (Set.Icc l (l+z))) :
    (∫ t in l..(l+z), t^k*f t) ≤ ∫ t in l..(l+z), t^k*((l+z-t)/z*f l+(t-l)/z*f (l+z)) := by
  have hab : l ≤ l+z := by linarith
  have hcont : ContinuousOn (fun t : ℝ => t^k*f t) (Set.Icc l (l+z)) :=
    (continuous_id.pow k).continuousOn.mul hc
  apply intervalIntegral.integral_mono_on hab (hcont.intervalIntegrable_of_Icc hab)
    ((by fun_prop : Continuous (fun t : ℝ => t^k*((l+z-t)/z*f l+(t-l)/z*f (l+z)))).intervalIntegrable _ _)
  intro t ht
  exact mul_le_mul_of_nonneg_left (convex_chord_bound hz hf ht) (pow_nonneg (hl.trans ht.1) k)

theorem convex_quadrature_weight_one {f : ℝ → ℝ} {l z : ℝ}
    (hl : 0 ≤ l) (hz : 0 < z) (hf : ConvexOn ℝ (Set.Icc l (l+z)) f)
    (hc : ContinuousOn f (Set.Icc l (l+z))) :
    (∫ t in l..(l+z), t*f t) ≤ z*(l/2+z/6)*f l+z*(l/2+z/3)*f (l+z) := by
  have h := weighted_convex_integral_le_chord 1 hl hz hf hc
  rw [weighted_chord_integral] at h
  simp only [pow_one] at h
  convert h using 1 <;> first | rfl | (norm_num; field_simp; ring)

theorem convex_quadrature_weight_two {f : ℝ → ℝ} {l z : ℝ}
    (hl : 0 ≤ l) (hz : 0 < z) (hf : ConvexOn ℝ (Set.Icc l (l+z)) f)
    (hc : ContinuousOn f (Set.Icc l (l+z))) :
    (∫ t in l..(l+z), t^2*f t) ≤
      z*(l^2/2+l*z/3+z^2/12)*f l+z*(l^2/2+2*l*z/3+z^2/4)*f (l+z) := by
  have h := weighted_convex_integral_le_chord 2 hl hz hf hc
  rw [weighted_chord_integral] at h
  convert h using 1 <;> first | rfl | (norm_num; field_simp; ring)

end QuadraticTangZhang
