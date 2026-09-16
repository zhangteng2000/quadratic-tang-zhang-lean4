import QuadraticTangZhang.CenteredRemainder

/-! # B. From the centered remainder to the centered scalar inequality -/

namespace QuadraticTangZhang
open Polynomial MeasureTheory
open scoped BigOperators

noncomputable def originProduct {m : ℕ} (q : Fin m → ℂ) (a t : ℝ) : ℂ :=
  ∏ j, ((1:ℂ)-(a:ℂ)*(t:ℂ)*q j)

noncomputable def centerFactor {m : ℕ} (q : Fin m → ℂ) (a t : ℝ) : ℂ :=
  1-(a:ℂ)*(t:ℂ)*meanComplex q

noncomputable def centerIntegral (m : ℕ) (a x : ℝ) : ℝ :=
  ∫ t in (0:ℝ)..1, t^2 * beta a x t ^ (((m-1:ℕ):ℝ)/2) / (1-a*x*t)

/-- This is C_n(a,x) in the manuscript, with n=m+1. -/
noncomputable def centerCoefficient (m : ℕ) (a x : ℝ) : ℝ :=
  5*a^3*(m+1)*m/6 * centerIntegral m a x

theorem origin_gap_pos {a x t : ℝ} (ha : 0 ≤ a) (ha1 : a < 1) (hx : x ≤ 1)
    (ht : 0 ≤ t) (ht1 : t ≤ 1) : 0 < 1-a*x*t := by
  have h1 := mul_nonneg (mul_nonneg ha ht) (sub_nonneg.mpr hx)
  have h2 := mul_nonneg ha (sub_nonneg.mpr ht1)
  nlinarith

theorem beta_pos_on_unit {a x t : ℝ} (ha : 0 ≤ a) (ha1 : a < 1) (hx : x ≤ 1)
    (ht : 0 ≤ t) (ht1 : t ≤ 1) : 0 < beta a x t := by
  have hat : a*t < 1 := lt_of_le_of_lt (by nlinarith) ha1
  have h := mul_nonneg (show 0 ≤ 2*a*t by positivity) (sub_nonneg.mpr hx)
  have hsq := sq_pos_of_pos (sub_pos.mpr hat)
  unfold beta
  nlinarith

theorem centerFactor_norm_lower {m : ℕ} (q : Fin m → ℂ) (a t : ℝ) :
    1-a*meanRe q*t ≤ ‖centerFactor q a t‖ := by
  have h := Complex.re_le_norm (centerFactor q a t)
  convert h using 1 <;> simp only [centerFactor, meanComplex, Complex.sub_re, Complex.one_re,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im] <;> ring

theorem centerIntegral_integrable {a x : ℝ} (ha : 0 ≤ a) (ha1 : a < 1) (hx : x ≤ 1) (m : ℕ) :
    IntervalIntegrable (fun t : ℝ => t^2 * beta a x t ^ (((m-1:ℕ):ℝ)/2) / (1-a*x*t))
      volume 0 1 := by
  have hc : Continuous fun t : ℝ => beta a x t := by unfold beta; fun_prop
  have hp := (Real.continuous_rpow_const (show (0:ℝ) ≤ ((m-1:ℕ):ℝ)/2 by positivity)).comp hc
  have hnum : Continuous fun t : ℝ => t^2 * beta a x t ^ (((m-1:ℕ):ℝ)/2) :=
    (continuous_id.pow 2).mul hp
  have hden : Continuous fun t : ℝ => 1-a*x*t := by fun_prop
  exact (hnum.continuousOn.div hden.continuousOn
    (fun t ht => ne_of_gt (origin_gap_pos ha ha1 hx ht.1 ht.2))).intervalIntegrable_of_Icc (by norm_num)

theorem centerIntegral_nonneg {a x : ℝ} (ha : 0 ≤ a) (ha1 : a < 1) (hx : x ≤ 1) (m : ℕ) :
    0 ≤ centerIntegral m a x := by
  apply intervalIntegral.integral_nonneg (by norm_num)
  intro t ht
  exact div_nonneg (mul_nonneg (sq_nonneg t)
    (Real.rpow_nonneg (beta_pos_on_unit ha ha1 hx ht.1 ht.2).le _))
    (origin_gap_pos ha ha1 hx ht.1 ht.2).le

theorem centerCoefficient_nonneg {a x : ℝ} (ha : 0 ≤ a) (ha1 : a < 1) (hx : x ≤ 1) (m : ℕ) :
    0 ≤ centerCoefficient m a x := by
  have hi := centerIntegral_nonneg ha ha1 hx m
  unfold centerCoefficient
  positivity

theorem centerFactor_integral (m : ℕ) (b : ℂ) :
    b*(m+1 : ℕ)*(∫ t in (0:ℝ)..1, ((1:ℂ)-b*(t:ℂ))^m) = 1-(1-b)^(m+1) := by
  have hd (t : ℝ) : HasDerivAt (fun t : ℝ => ((1:ℂ)-b*(t:ℂ))^(m+1))
      (-b*(m+1 : ℕ)*((1:ℂ)-b*(t:ℂ))^m) t := by
    have hbase : HasDerivAt (fun t : ℝ => (1:ℂ)-b*(t:ℂ)) (-b) t := by
      simpa using (Complex.ofRealCLM.hasDerivAt.const_mul b).const_sub (1:ℂ)
    have hp := hbase.pow (m+1)
    simp only [Nat.add_sub_cancel] at hp
    convert hp using 1 <;> first | rfl | ring
  have hc : Continuous (fun t : ℝ => -b*(m+1 : ℕ)*((1:ℂ)-b*(t:ℂ))^m) := by fun_prop
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t)
    (hc.intervalIntegrable 0 1)
  rw [intervalIntegral.integral_const_mul] at h
  simp only [Complex.ofReal_one, Complex.ofReal_zero, mul_one, mul_zero, sub_zero, one_pow] at h
  linear_combination -h

theorem centered_integral_remainder {m : ℕ} (hm : 2 ≤ m) (q : Fin m → ℂ)
    (hs : secondMoment q ≤ 1) {a : ℝ} (ha : 0 ≤ a) (ha1 : a < 1) :
    ‖(∫ t in (0:ℝ)..1, originProduct q a t) - (∫ t in (0:ℝ)..1, (centerFactor q a t)^m)‖ ≤
      (5*m*a^2*(secondMoment q-‖meanComplex q‖^2)/6) * centerIntegral m a (meanRe q) := by
  have hmpos : 0 < m := by omega
  have hx := (meanRe_bounds hmpos q hs).2
  have hV : 0 ≤ secondMoment q-‖meanComplex q‖^2 := by
    have h := mean_sq_le_secondMoment hmpos q
    rw [← norm_meanComplex_sq q] at h
    linarith
  let K := 5*m*a^2*(secondMoment q-‖meanComplex q‖^2)/6
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hbound (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) 1) :
      ‖originProduct q a t - (centerFactor q a t)^m‖ ≤
        K*(t^2 * beta a (meanRe q) t ^ (((m-1:ℕ):ℝ)/2) / (1-a*meanRe q*t)) := by
    have h := centered_remainder_estimate hm q hs ha ha1 ht.1 ht.2
    have hBs : 0 ≤ betaS a (meanRe q) (secondMoment q) t := by
      have hv : 0 ≤ m*betaS a (meanRe q) (secondMoment q) t := by
        rw [← sum_origin_norm_sq hmpos q a t]
        exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
      have hmR : (0:ℝ)<m := by positivity
      nlinarith
    have hpow := Real.rpow_le_rpow hBs (betaS_le_beta a (meanRe q) (secondMoment q) t hs)
      (show (0:ℝ) ≤ ((m-1:ℕ):ℝ)/2 by positivity)
    have hfrac := div_le_div₀ (mul_nonneg (sq_nonneg t)
      (Real.rpow_nonneg (beta_pos_on_unit ha ha1 hx ht.1 ht.2).le (((m-1:ℕ):ℝ)/2)))
      (mul_le_mul_of_nonneg_left hpow (sq_nonneg t))
      (origin_gap_pos ha ha1 hx ht.1 ht.2) (centerFactor_norm_lower q a t)
    have hmul := mul_le_mul_of_nonneg_left hfrac hK
    apply h.trans
    convert hmul using 1 <;> dsimp [K, centerFactor] <;> ring
  have hfc : Continuous fun t : ℝ => originProduct q a t := by unfold originProduct; fun_prop
  have hdc : Continuous fun t : ℝ => (centerFactor q a t)^m := by unfold centerFactor; fun_prop
  rw [← intervalIntegral.integral_sub (hfc.intervalIntegrable 0 1) (hdc.intervalIntegrable 0 1)]
  have hi : ‖∫ t in (0:ℝ)..1, (originProduct q a t - (centerFactor q a t)^m)‖ ≤
      ∫ t in (0:ℝ)..1, K*(t^2*beta a (meanRe q) t^(((m-1:ℕ):ℝ)/2)/(1-a*meanRe q*t)) := by
    apply intervalIntegral.norm_integral_le_of_norm_le (by norm_num)
    · exact Filter.Eventually.of_forall (fun t ht => hbound t ⟨ht.1.le,ht.2⟩)
    · exact (centerIntegral_integrable ha ha1 hx m).const_mul K
  rw [intervalIntegral.integral_const_mul] at hi
  exact hi

theorem norm_centerFactor_sq_le_beta {m : ℕ} (hm : 0 < m) (q : Fin m → ℂ)
    (hs : secondMoment q ≤ 1) (a t : ℝ) : ‖centerFactor q a t‖^2 ≤ beta a (meanRe q) t := by
  have hnorm := norm_meanComplex_le_one hm q hs
  have hid := affine_normSq (meanComplex q) 1 (-a*t)
  have hfac : (1:ℂ)+((-a*t:ℝ):ℂ)*meanComplex q = centerFactor q a t := by
    unfold centerFactor
    push_cast
    ring
  simp only [Complex.ofReal_one] at hid
  rw [hfac, Complex.normSq_eq_norm_sq] at hid
  have hr : (meanComplex q).re = meanRe q := rfl
  rw [hr, Complex.normSq_eq_norm_sq] at hid
  have hsq : ‖meanComplex q‖^2 ≤ 1 := by nlinarith [norm_nonneg (meanComplex q)]
  have hmul := mul_le_mul_of_nonneg_left hsq (sq_nonneg (a*t))
  unfold beta
  nlinarith

theorem norm_pow_le_rpow_of_sq_le (z : ℂ) {B : ℝ} (h : ‖z‖^2 ≤ B) (k : ℕ) :
    ‖z^k‖ ≤ B^((k:ℝ)/2) := by
  have hp := Real.rpow_le_rpow (sq_nonneg ‖z‖) h (show (0:ℝ) ≤ k/2 by positivity)
  have he : (‖z‖^2)^((k:ℝ)/2) = ‖z‖^k := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg z), ← Real.rpow_natCast ‖z‖ k]
    congr 1
    norm_num
    ring
  rwa [he, ← norm_pow] at hp

/-- The centered scalar inequality, under the first-origin integral bound. -/
theorem centered_scalar_inequality {m : ℕ} (hm : 2 ≤ m) (q : Fin m → ℂ)
    (hs : secondMoment q ≤ 1) {a : ℝ} (ha : 0 ≤ a) (ha1 : a < 1)
    (horigin : ‖(m+1 : ℕ)*(∫ t in (0:ℝ)..1, originProduct q a t)‖ ≤ 1) :
    1 ≤ a*‖meanComplex q‖ + centerCoefficient m a (meanRe q)*‖meanComplex q‖*(1-‖meanComplex q‖^2) +
      beta a (meanRe q) 1 ^ (((m+1:ℕ):ℝ)/2) := by
  have hmpos : 0 < m := by omega
  let r := ‖meanComplex q‖
  let F := ∫ t in (0:ℝ)..1, originProduct q a t
  let Z := ∫ t in (0:ℝ)..1, (centerFactor q a t)^m
  let U : ℂ := (a:ℂ)*meanComplex q
  let N : ℂ := (m+1 : ℕ)
  have hn : ‖N‖ = (m+1 : ℕ) := by simp only [N, Complex.norm_natCast]
  have hu : ‖U‖ = a*r := by simp [U, r, norm_mul, abs_of_nonneg ha]
  have hrepr : U*N*Z = 1-(centerFactor q a 1)^(m+1) := by
    have h := centerFactor_integral m U
    have hf : (fun t : ℝ => ((1:ℂ)-U*(t:ℂ))^m) =
        (fun t : ℝ => (centerFactor q a t)^m) := by
      funext t
      congr 1
      dsimp [U, centerFactor]
      ring
    rw [hf] at h
    simpa [U, N, Z, centerFactor] using h
  have heq : (1:ℂ) = (centerFactor q a 1)^(m+1) + U*(N*F) + U*N*(Z-F) := by
    linear_combination -hrepr
  have htri := norm_add_le ((centerFactor q a 1)^(m+1) + U*(N*F)) (U*N*(Z-F))
  rw [← heq, norm_one] at htri
  have htri2 := norm_add_le ((centerFactor q a 1)^(m+1)) (U*(N*F))
  have hfirst : ‖U*(N*F)‖ ≤ a*r := by
    rw [norm_mul, hu]
    exact (mul_le_mul_of_nonneg_left horigin (by positivity)).trans_eq (mul_one _)
  have hlast : ‖U*N*(Z-F)‖ ≤ centerCoefficient m a (meanRe q)*r*(secondMoment q-r^2) := by
    have hb := centered_integral_remainder hm q hs ha ha1
    change ‖F-Z‖ ≤ _ at hb
    rw [norm_sub_rev] at hb
    have hmul := mul_le_mul_of_nonneg_left hb (show 0 ≤ a*r*(m+1:ℕ) by positivity)
    rw [norm_mul, norm_mul, hu, hn]
    convert hmul using 1 <;> first | rfl | (unfold centerCoefficient; dsimp only [r]; push_cast; ring)
  have hend := norm_pow_le_rpow_of_sq_le (centerFactor q a 1)
    (norm_centerFactor_sq_le_beta hmpos q hs a 1) (m+1)
  have hC := centerCoefficient_nonneg ha ha1 (meanRe_bounds hmpos q hs).2 m
  have hv : centerCoefficient m a (meanRe q)*r*(secondMoment q-r^2) ≤
      centerCoefficient m a (meanRe q)*r*(1-r^2) := by
    exact mul_le_mul_of_nonneg_left (sub_le_sub_right hs _) (mul_nonneg hC (norm_nonneg _))
  change 1 ≤ a*r + centerCoefficient m a (meanRe q)*r*(1-r^2) + _
  linarith

end QuadraticTangZhang
