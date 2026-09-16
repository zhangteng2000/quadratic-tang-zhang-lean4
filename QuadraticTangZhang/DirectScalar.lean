import QuadraticTangZhang.CenteredScalar

/-! # C. The differential origin identity and the direct scalar inequality -/

namespace QuadraticTangZhang
open Polynomial MeasureTheory
open scoped BigOperators

noncomputable def originErrorSum {m : ℕ} (q : Fin m → ℂ) (a t : ℝ) : ℂ :=
  ∑ j, (q j)^2 * ∏ k ∈ (Finset.univ : Finset (Fin m)).erase j,
    ((1:ℂ)-(a:ℂ)*(t:ℂ)*q k)

noncomputable def originRemainder {m : ℕ} (q : Fin m → ℂ) (a : ℝ) : ℂ :=
  (a:ℂ)^2 * ∫ t in (0:ℝ)..1, (t:ℂ)*originErrorSum q a t

noncomputable def directIntegral (m : ℕ) (a x : ℝ) : ℝ :=
  ∫ t in (0:ℝ)..1, t * beta a x t ^ (((m-1:ℕ):ℝ)/2)

theorem sum_eq_card_mul_mean {m : ℕ} (hm : 0 < m) (q : Fin m → ℂ) :
    (∑ j, q j) = (m:ℂ)*meanComplex q := by
  have h := sum_sub_meanComplex hm q
  simpa only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, sub_eq_zero] using h

theorem differential_origin_identity {m : ℕ} (hm : 0 < m) (q : Fin m → ℂ) (a : ℝ) :
    (1:ℂ) = originProduct q a 1 + (m:ℂ)*(a:ℂ)*meanComplex q*
      (∫ t in (0:ℝ)..1, originProduct q a t) + originRemainder q a := by
  let P : ℂ[X] := ∏ j, (1-C (a:ℂ)*X*C (q j))
  have hp (t : ℝ) : P.eval (t:ℂ) = originProduct q a t := by
    simp [P, originProduct, eval_prod]
  have hd (t : ℝ) : P.derivative.eval (t:ℂ) =
      -(a:ℂ)*(∑ j, q j)*originProduct q a t - (a:ℂ)^2*((t:ℂ)*originErrorSum q a t) := by
    have h := origin_derivative_polynomial Finset.univ (a:ℂ) q
    have hval := congrArg (fun Q : ℂ[X] => Q.eval (t:ℂ)) h
    simpa only [P, originProduct, originErrorSum, eval_prod, eval_finsetSum,
      eval_sub, eval_mul, eval_one, eval_C, eval_X, eval_pow, eval_neg, mul_assoc] using hval
  have hderiv (t : ℝ) : HasDerivAt (fun t : ℝ => P.eval (t:ℂ))
      (P.derivative.eval (t:ℂ)) t := (P.hasDerivAt (t:ℂ)).comp_ofReal
  have hc : Continuous fun t : ℝ => P.derivative.eval (t:ℂ) := by fun_prop
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hderiv t)
    (hc.intervalIntegrable 0 1)
  simp_rw [hd] at hFTC
  have hc1 : Continuous fun t : ℝ => -(a:ℂ)*(∑ j, q j)*originProduct q a t := by
    unfold originProduct
    fun_prop
  have hc2 : Continuous fun t : ℝ => (a:ℂ)^2*((t:ℂ)*originErrorSum q a t) := by
    unfold originErrorSum
    fun_prop
  rw [intervalIntegral.integral_sub (hc1.intervalIntegrable 0 1) (hc2.intervalIntegrable 0 1),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hFTC
  have hp0 : P.eval (0:ℂ) = 1 := by simp [P, eval_prod]
  have hp1 : P.eval (1:ℂ) = originProduct q a 1 := by simpa using hp 1
  simp only [Complex.ofReal_zero, Complex.ofReal_one, hp0, hp1] at hFTC
  rw [sum_eq_card_mul_mean hm q] at hFTC
  dsimp [originRemainder]
  linear_combination hFTC

theorem originProduct_norm_le_beta {m : ℕ} (hm : 0 < m) (q : Fin m → ℂ)
    (hs : secondMoment q ≤ 1) {a t : ℝ} (ha : 0 ≤ a) (ha1 : a < 1)
    (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    ‖originProduct q a t‖ ≤ beta a (meanRe q) t ^ ((m:ℝ)/2) := by
  have hB := (beta_pos_on_unit ha ha1 (meanRe_bounds hm q hs).2 ht ht1).le
  have hsum := sum_origin_norm_sq hm q a t
  have hmean := mul_le_mul_of_nonneg_left (betaS_le_beta a (meanRe q) (secondMoment q) t hs)
    (Nat.cast_nonneg m : (0:ℝ) ≤ m)
  rw [← hsum] at hmean
  have h := norm_prod_le_moment Finset.univ (by simpa using hm)
    (fun j => (1:ℂ)-(a:ℂ)*(t:ℂ)*q j) hB (by simpa using hmean)
  simpa only [originProduct, Finset.card_univ, Fintype.card_fin] using h

theorem originErrorSum_norm_bound {m : ℕ} (hm : 2 ≤ m) (q : Fin m → ℂ)
    (hs : secondMoment q ≤ 1) {a t : ℝ} (ha : 0 ≤ a) (ha1 : a < 1)
    (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    ‖originErrorSum q a t‖ ≤ (5/3:ℝ)*m*beta a (meanRe q) t^(((m-1:ℕ):ℝ)/2) := by
  have hmpos : 0 < m := by omega
  have hB := (beta_pos_on_unit ha ha1 (meanRe_bounds hmpos q hs).2 ht ht1).le
  have hsum := sum_origin_norm_sq hmpos q a t
  have hmean := mul_le_mul_of_nonneg_left (betaS_le_beta a (meanRe q) (secondMoment q) t hs)
    (Nat.cast_nonneg m : (0:ℝ) ≤ m)
  rw [← hsum] at hmean
  have hdel (j : Fin m) :
      ‖∏ k ∈ (Finset.univ : Finset (Fin m)).erase j, ((1:ℂ)-(a:ℂ)*(t:ℂ)*q k)‖ ≤
        (5/3:ℝ)*beta a (meanRe q) t^(((m-1:ℕ):ℝ)/2) := by
    have h := norm_deleted_prod_le Finset.univ (by simpa using hm) j (Finset.mem_univ j)
      (fun k => (1:ℂ)-(a:ℂ)*(t:ℂ)*q k) hB (by simpa using hmean)
    simpa only [Finset.card_univ,Fintype.card_fin] using h
  have hqsum : (∑ j, ‖q j‖^2) ≤ m := by
    unfold secondMoment at hs
    simp only [Complex.normSq_eq_norm_sq] at hs
    exact (div_le_one (by positivity : (0:ℝ)<m)).mp hs
  unfold originErrorSum
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ (∑ j, ‖q j‖^2)*((5/3:ℝ)*beta a (meanRe q) t^(((m-1:ℕ):ℝ)/2)) := by
      rw [Finset.sum_mul]
      apply Finset.sum_le_sum
      intro j _
      rw [norm_mul,norm_pow]
      exact mul_le_mul_of_nonneg_left (hdel j) (sq_nonneg _)
    _ ≤ m*((5/3:ℝ)*beta a (meanRe q) t^(((m-1:ℕ):ℝ)/2)) :=
      mul_le_mul_of_nonneg_right hqsum (mul_nonneg (by norm_num) (Real.rpow_nonneg hB _))
    _ = _ := by ring

theorem originRemainder_norm_bound {m : ℕ} (hm : 2 ≤ m) (q : Fin m → ℂ)
    (hs : secondMoment q ≤ 1) {a : ℝ} (ha : 0 ≤ a) (ha1 : a < 1) :
    ‖originRemainder q a‖ ≤ (5/3:ℝ)*a^2*m*directIntegral m a (meanRe q) := by
  have hb (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) 1) :
      ‖(t:ℂ)*originErrorSum q a t‖ ≤ (5/3:ℝ)*m*(t*beta a (meanRe q) t^(((m-1:ℕ):ℝ)/2)) := by
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg ht.1]
    have h := mul_le_mul_of_nonneg_left (originErrorSum_norm_bound hm q hs ha ha1 ht.1 ht.2) ht.1
    convert h using 1 <;> first | rfl | ring
  have hcB : Continuous fun t : ℝ => beta a (meanRe q) t := by unfold beta; fun_prop
  have hcP := (Real.continuous_rpow_const (show (0:ℝ) ≤ ((m-1:ℕ):ℝ)/2 by positivity)).comp hcB
  have hc : Continuous fun t : ℝ => (5/3:ℝ)*m*(t*beta a (meanRe q) t^(((m-1:ℕ):ℝ)/2)) :=
    (continuous_id.mul hcP).const_mul _
  have hi : ‖∫ t in (0:ℝ)..1, (t:ℂ)*originErrorSum q a t‖ ≤
      ∫ t in (0:ℝ)..1, (5/3:ℝ)*m*(t*beta a (meanRe q) t^(((m-1:ℕ):ℝ)/2)) := by
    apply intervalIntegral.norm_integral_le_of_norm_le (by norm_num)
    · exact Filter.Eventually.of_forall (fun t ht => hb t ⟨ht.1.le,ht.2⟩)
    · exact hc.intervalIntegrable 0 1
  rw [intervalIntegral.integral_const_mul] at hi
  have h := mul_le_mul_of_nonneg_left hi (sq_nonneg a)
  unfold originRemainder
  rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs]
  convert h using 1 <;> first | rfl | (unfold directIntegral; ring)

theorem direct_scalar_inequality {m : ℕ} (hm : 2 ≤ m) (q : Fin m → ℂ)
    (hs : secondMoment q ≤ 1) {a : ℝ} (ha : 0 ≤ a) (ha1 : a < 1)
    (horigin : ‖(m+1 : ℕ)*(∫ t in (0:ℝ)..1, originProduct q a t)‖ ≤ 1) :
    1 ≤ beta a (meanRe q) 1 ^ ((m:ℝ)/2) + m*a/(m+1) +
      (5/3:ℝ)*a^2*m*directIntegral m a (meanRe q) := by
  have hmpos : 0 < m := by omega
  have hidentity := differential_origin_identity hmpos q a
  have htri := norm_add_le (originProduct q a 1 + (m:ℂ)*(a:ℂ)*meanComplex q*
    (∫ t in (0:ℝ)..1, originProduct q a t)) (originRemainder q a)
  rw [← hidentity,norm_one] at htri
  have htri2 := norm_add_le (originProduct q a 1) ((m:ℂ)*(a:ℂ)*meanComplex q*
    (∫ t in (0:ℝ)..1, originProduct q a t))
  have hF := originProduct_norm_le_beta hmpos q hs ha ha1 (by norm_num : (0:ℝ)≤1) le_rfl
  have hR := originRemainder_norm_bound hm q hs ha ha1
  have hnormInt : ‖∫ t in (0:ℝ)..1, originProduct q a t‖ ≤ 1/(m+1) := by
    rw [norm_mul,Complex.norm_natCast] at horigin
    have hmR : (0:ℝ)<m+1 := by positivity
    rw [le_div_iff₀ hmR]
    push_cast at horigin
    nlinarith
  have hmid : ‖(m:ℂ)*(a:ℂ)*meanComplex q*(∫ t in (0:ℝ)..1, originProduct q a t)‖ ≤ m*a/(m+1) := by
    simp only [norm_mul,Complex.norm_natCast,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg ha]
    have h1 := mul_le_mul_of_nonneg_left (norm_meanComplex_le_one hmpos q hs)
      (show 0 ≤ (m:ℝ)*a by positivity)
    have h2 := mul_le_mul h1 hnormInt (norm_nonneg _) (show 0 ≤ (m:ℝ)*a*1 by positivity)
    simpa only [mul_one,one_mul,div_eq_mul_inv] using h2
  linarith

end QuadraticTangZhang
