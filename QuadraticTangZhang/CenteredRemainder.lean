import QuadraticTangZhang.CenteredIdentity
import QuadraticTangZhang.DeletedProducts
import QuadraticTangZhang.Moments
import QuadraticTangZhang.Scalar
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! # A. The centered remainder estimate

The proof first treats an arbitrary centered family. This makes explicit
the mean-square bound needed during the interpolation, including the cases
where one or more individual factors vanish.
-/

namespace QuadraticTangZhang
open Polynomial MeasureTheory
open scoped BigOperators

theorem centered_sum_norm_sq {m : ℕ} (w : Fin m → ℂ) (hw : ∑ j, w j = 0)
    (D : ℂ) (c : ℝ) :
    (∑ j, ‖D - (c:ℂ)*w j‖^2) = m*‖D‖^2 + c^2*(∑ j, ‖w j‖^2) := by
  have hre : ∑ j, (w j).re = 0 := by simpa using congrArg Complex.re hw
  have him : ∑ j, (w j).im = 0 := by simpa using congrArg Complex.im hw
  have hid (j : Fin m) : ‖D-(c:ℂ)*w j‖^2 =
      ‖D‖^2 - 2*c*D.re*(w j).re - 2*c*D.im*(w j).im + c^2*‖w j‖^2 := by
    simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.sub_re,
      Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  simp_rw [hid]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hre, him,
    mul_zero, sub_zero, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

theorem centered_remainder_general {m : ℕ} (hm : 2 ≤ m) (w : Fin m → ℂ)
    (hw : ∑ j, w j = 0) {D : ℂ} (hD : D ≠ 0) (c : ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hmean : m*‖D‖^2 + c^2*(∑ j, ‖w j‖^2) ≤ m*B) :
    ‖(∏ j, (D-(c:ℂ)*w j)) - D^m‖ ≤
      (5*c^2*(∑ j, ‖w j‖^2)/(6*‖D‖)) * B^(((m-1:ℕ):ℝ)/2) := by
  let P : ℂ[X] := ∏ j : Fin m, (C D - C (c:ℂ) * X * C (w j))
  let K : ℝ := (5*c^2*(∑ j, ‖w j‖^2)/(3*‖D‖)) * B^(((m-1:ℕ):ℝ)/2)
  have hDpos : 0 < ‖D‖ := norm_pos_iff.mpr hD
  have hV : 0 ≤ ∑ j, ‖w j‖^2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hP (t : ℝ) : P.eval (t:ℂ) = ∏ j, (D-(c:ℂ)*(t:ℂ)*w j) := by
    simp [P, eval_prod]
  have hd (t : ℝ) : D * P.derivative.eval (t:ℂ) =
      -(c:ℂ)^2 * (t:ℂ) * ∑ j, (w j)^2 *
        ∏ k ∈ (Finset.univ : Finset (Fin m)).erase j, (D-(c:ℂ)*(t:ℂ)*w k) := by
    have h := centered_interpolation_polynomial Finset.univ D (c:ℂ) w hw
    have he := congrArg (fun Q : ℂ[X] => Q.eval (t:ℂ)) h
    simpa [P, eval_finsetSum, eval_prod] using he
  have hderiv (t : ℝ) : HasDerivAt (fun t : ℝ => P.eval (t:ℂ))
      (P.derivative.eval (t:ℂ)) t := (P.hasDerivAt (t:ℂ)).comp_ofReal
  have hc : Continuous (fun t : ℝ => P.derivative.eval (t:ℂ)) := by fun_prop
  have hbound (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) 1) : ‖P.derivative.eval (t:ℂ)‖ ≤ K*t := by
    have ht0 := ht.1
    have ht2 : t^2 ≤ 1 := by nlinarith [ht.1, ht.2]
    have hfmean : (∑ j, ‖D-(c:ℂ)*(t:ℂ)*w j‖^2) ≤ m*B := by
      have h := centered_sum_norm_sq w hw D (c*t)
      simp only [Complex.ofReal_mul] at h
      rw [h]
      have hmul := mul_le_mul_of_nonneg_left ht2 (mul_nonneg (sq_nonneg c) hV)
      nlinarith
    have hdel (j : Fin m) :
        ‖∏ k ∈ (Finset.univ : Finset (Fin m)).erase j, (D-(c:ℂ)*(t:ℂ)*w k)‖ ≤
          (5/3:ℝ) * B^(((m-1:ℕ):ℝ)/2) := by
      have h := norm_deleted_prod_le Finset.univ (by simpa using hm) j (Finset.mem_univ j)
        (fun k => D-(c:ℂ)*(t:ℂ)*w k) hB (by simpa using hfmean)
      simpa only [Finset.card_univ, Fintype.card_fin] using h
    have hsum : ‖∑ j, (w j)^2 * ∏ k ∈ (Finset.univ : Finset (Fin m)).erase j,
        (D-(c:ℂ)*(t:ℂ)*w k)‖ ≤ (∑ j, ‖w j‖^2) * ((5/3:ℝ)*B^(((m-1:ℕ):ℝ)/2)) := by
      apply (norm_sum_le _ _).trans
      rw [Finset.sum_mul]
      apply Finset.sum_le_sum
      intro j _
      rw [norm_mul, norm_pow]
      exact mul_le_mul_of_nonneg_left (hdel j) (sq_nonneg _)
    have hnorm := congrArg norm (hd t)
    simp only [norm_mul, norm_neg, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      sq_abs, abs_of_nonneg ht.1] at hnorm
    have hmul := mul_le_mul_of_nonneg_left hsum (show 0 ≤ c^2*t by positivity)
    rw [← hnorm] at hmul
    apply (mul_le_mul_iff_right₀ hDpos).mp
    convert hmul using 1 <;> dsimp [K] <;> field_simp <;> ring
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hderiv t)
    (hc.intervalIntegrable 0 1)
  have hnorm : ‖∫ t in (0:ℝ)..1, P.derivative.eval (t:ℂ)‖ ≤ ∫ t in (0:ℝ)..1, K*t := by
    apply intervalIntegral.norm_integral_le_of_norm_le (by norm_num : (0:ℝ) ≤ 1)
    · exact Filter.Eventually.of_forall (fun t ht => hbound t ⟨ht.1.le, ht.2⟩)
    · exact ((by fun_prop : Continuous (fun t : ℝ => K*t)).intervalIntegrable 0 1)
  rw [hFTC] at hnorm
  have hp0 : P.eval (0:ℂ) = D^m := by simp [P, eval_prod]
  have hp1 : P.eval (1:ℂ) = ∏ j, (D-(c:ℂ)*w j) := by simp [P, eval_prod]
  simp only [Complex.ofReal_zero, Complex.ofReal_one, hp0, hp1] at hnorm
  have hint : (∫ t in (0:ℝ)..1, K*t) = K/2 := by
    rw [intervalIntegral.integral_const_mul, integral_id]
    norm_num
    ring
  rw [hint] at hnorm
  convert hnorm using 1 <;> dsimp [K] <;> ring

noncomputable def meanComplex {m : ℕ} (q : Fin m → ℂ) : ℂ := ⟨meanRe q, meanIm q⟩

theorem norm_meanComplex_sq {m : ℕ} (q : Fin m → ℂ) :
    ‖meanComplex q‖^2 = meanRe q^2 + meanIm q^2 := by
  rw [← Complex.normSq_eq_norm_sq]
  simp [meanComplex, Complex.normSq_apply, pow_two]

theorem sum_sub_meanComplex {m : ℕ} (hm : 0 < m) (q : Fin m → ℂ) :
    ∑ j, (q j - meanComplex q) = 0 := by
  apply Complex.ext
  · simpa [meanComplex] using sum_centered_re hm q
  · simpa [meanComplex] using sum_centered_im hm q

theorem centered_variance_sum {m : ℕ} (hm : 0 < m) (q : Fin m → ℂ) :
    (∑ j, ‖q j-meanComplex q‖^2) = m*(secondMoment q-‖meanComplex q‖^2) := by
  have h := variance_identity hm q
  simp only [Complex.normSq_eq_norm_sq] at h
  change (∑ j, ‖q j-meanComplex q‖^2) / m = _ at h
  rw [← norm_meanComplex_sq q] at h
  have hm0 : (m:ℝ) ≠ 0 := by positivity
  exact (div_eq_iff hm0).mp h |>.trans (by ring)

theorem norm_meanComplex_le_one {m : ℕ} (hm : 0 < m) (q : Fin m → ℂ)
    (hs : secondMoment q ≤ 1) : ‖meanComplex q‖ ≤ 1 := by
  have h := (mean_sq_le_secondMoment hm q).trans hs
  rw [← norm_meanComplex_sq q] at h
  nlinarith [norm_nonneg (meanComplex q)]

theorem one_sub_meanComplex_ne_zero {m : ℕ} (hm : 0 < m) (q : Fin m → ℂ)
    (hs : secondMoment q ≤ 1) {u : ℝ} (hu : 0 ≤ u) (hu1 : u < 1) :
    (1:ℂ)-(u:ℂ)*meanComplex q ≠ 0 := by
  intro heq
  have he : (u:ℂ)*meanComplex q = 1 := (sub_eq_zero.mp heq).symm
  have hn := congrArg norm he
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hu, norm_one] at hn
  have h := mul_le_mul_of_nonneg_left (norm_meanComplex_le_one hm q hs) hu
  nlinarith

theorem sum_origin_norm_sq {m : ℕ} (hm : 0 < m) (q : Fin m → ℂ) (a t : ℝ) :
    (∑ j, ‖(1:ℂ)-(a:ℂ)*(t:ℂ)*q j‖^2) = m*betaS a (meanRe q) (secondMoment q) t := by
  have h := affine_secondMoment hm q 1 (-a*t)
  have heq : (fun j => (1:ℂ)+((-a*t:ℝ):ℂ)*q j) =
      (fun j => (1:ℂ)-(a:ℂ)*(t:ℂ)*q j) := by funext j; push_cast; ring
  simp only [Complex.ofReal_one] at h
  rw [heq] at h
  change (∑ j, Complex.normSq ((1:ℂ)-(a:ℂ)*(t:ℂ)*q j)) / m = _ at h
  simp only [Complex.normSq_eq_norm_sq] at h
  have hm0 : (m:ℝ) ≠ 0 := by positivity
  have hx := (div_eq_iff hm0).mp h
  rw [hx]
  unfold betaS
  ring

/-- The manuscript's centered remainder estimate, with n-1 = m. -/
theorem centered_remainder_estimate {m : ℕ} (hm : 2 ≤ m) (q : Fin m → ℂ)
    (hs : secondMoment q ≤ 1) {a t : ℝ} (ha : 0 ≤ a) (ha1 : a < 1)
    (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    ‖(∏ j, ((1:ℂ)-(a:ℂ)*(t:ℂ)*q j)) -
        ((1:ℂ)-(a:ℂ)*(t:ℂ)*meanComplex q)^m‖ ≤
      (5*m*a^2*t^2*(secondMoment q-‖meanComplex q‖^2) /
        (6*‖(1:ℂ)-(a:ℂ)*(t:ℂ)*meanComplex q‖)) *
        betaS a (meanRe q) (secondMoment q) t ^ (((m-1:ℕ):ℝ)/2) := by
  have hmpos : 0 < m := by omega
  let w : Fin m → ℂ := fun j => q j-meanComplex q
  let D : ℂ := 1-(a:ℂ)*(t:ℂ)*meanComplex q
  have hw : ∑ j, w j = 0 := sum_sub_meanComplex hmpos q
  have hD : D ≠ 0 := by
    have hat : a*t < 1 := lt_of_le_of_lt (by nlinarith) ha1
    simpa only [D, Complex.ofReal_mul] using
      one_sub_meanComplex_ne_zero hmpos q hs (mul_nonneg ha ht) hat
  have hfac (j : Fin m) : D-((a*t:ℝ):ℂ)*w j = (1:ℂ)-(a:ℂ)*(t:ℂ)*q j := by
    dsimp [D, w]
    push_cast
    ring
  have hmean := centered_sum_norm_sq w hw D (a*t)
  simp_rw [hfac] at hmean
  rw [sum_origin_norm_sq hmpos q a t] at hmean
  have hB : 0 ≤ betaS a (meanRe q) (secondMoment q) t := by
    have hnonneg : 0 ≤ m*betaS a (meanRe q) (secondMoment q) t := by
      rw [← sum_origin_norm_sq hmpos q a t]
      exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    have hmR : (0:ℝ) < m := by positivity
    nlinarith
  have h := centered_remainder_general hm w hw hD (a*t) hB hmean.symm.le
  simp_rw [hfac] at h
  have hV : (∑ j, ‖w j‖^2) = m*(secondMoment q-‖meanComplex q‖^2) :=
    centered_variance_sum hmpos q
  rw [hV] at h
  convert h using 1 <;> dsimp [D] <;> ring

end QuadraticTangZhang
