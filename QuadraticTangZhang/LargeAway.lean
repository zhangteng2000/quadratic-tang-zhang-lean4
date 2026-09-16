import QuadraticTangZhang.AwayIncreasingBounds

namespace QuadraticTangZhang

theorem away_decreasing_small_a {m : ℕ} {a x s r : ℝ} (hw : ScalarConditions m a x s r)
    (hm : 1000000 ≤ m) (ha : a ≤ 1/2) : 7/((m:ℝ)*x^2) < 292/1000 := by
  have hmR : (1000000:ℝ)≤m := by exact_mod_cast hm
  have hm0 : (0:ℝ)<m := by positivity
  have hd : 3/4 ≤ 1-a^2 := by nlinarith [hw.a_pos]
  have hL : 375000 ≤ awayLambda m a := by
    have h := mul_le_mul (show (500000:ℝ)≤((m:ℝ)+2)/2 by linarith) hd (by norm_num) (by positivity)
    dsimp [awayLambda]
    linarith
  have hL0 : 0<awayLambda m a := by linarith
  have hLog := log_three_eighths_million.trans_le (Real.log_le_log (by norm_num) hL)
  have hLog0 : 0<Real.log (awayLambda m a) := by linarith
  have hLu : awayLambda m a ≤ ((m:ℝ)+2)/2 := by
    unfold awayLambda
    apply mul_le_of_le_one_right (by positivity)
    nlinarith [sq_nonneg a]
  have hxs : Real.log (awayLambda m a)/awayLambda m a ≤ x^2 :=
    (away_rho_log hw hm (by linarith)).trans
      (rho_le_sq (by nlinarith [hw.a_pos,hw.a_lt_one]) hw.moment_upper)
  have hx2 : 0<x^2 := (div_pos hLog0 hL0).trans_le hxs
  calc
    7/((m:ℝ)*x^2) ≤ 7/((m:ℝ)*(Real.log (awayLambda m a)/awayLambda m a)) := by gcongr
    _ = 7*awayLambda m a/((m:ℝ)*Real.log (awayLambda m a)) := by field_simp
    _ ≤ 7*(((m:ℝ)+2)/2)/((m:ℝ)*12) := by gcongr
    _ < 292/1000 := by rw [div_lt_iff₀ (by positivity)]; nlinarith

theorem away_decreasing_large_a {m : ℕ} {a x s r : ℝ} (hw : ScalarConditions m a x s r)
    (hm : 1000000 ≤ m) (ha : 1/2 ≤ a) : 7/((m:ℝ)*x^2) ≤ 112/1000000 := by
  have hmR : (1000000:ℝ)≤m := by exact_mod_cast hm
  have hb := beta_rational_bound hw.a_pos hw.a_lt_one hw.x_le_one hw.moment_lower hw.moment_upper
    (by omega : 0<m) hw.polar
  have hx : 1/4 ≤ x := by linarith [hb.2.2.2]
  have hx2 : 1/16 ≤ x^2 := by nlinarith
  calc
    7/((m:ℝ)*x^2) ≤ 7/((m:ℝ)*(1/16)) := by gcongr
    _ = 112/(m:ℝ) := by ring
    _ ≤ 112/1000000 := by gcongr

theorem large_away_scalar_exclusion {m : ℕ} {a x s r : ℝ} (hw : ScalarConditions m a x s r)
    (hm : 1000000 ≤ m) (haway : 1/10 ≤ 1-a^2) : False := by
  have hred := away_direct_reduction hw hm haway
  have hmR : (1000000:ℝ)≤m := by exact_mod_cast hm
  by_cases ha : a ≤ 1/2
  · have hF := away_endpoint_small_a hw hm ha
    have hD := away_decreasing_small_a hw hm ha
    have hd : 3/4 ≤ 1-a^2 := by nlinarith [hw.a_pos]
    have hI := small_a_increasing_bound hmR hd (show 1-a^2≤1 by nlinarith [sq_nonneg a])
    have hI' : (5/3:ℝ)*a^2*m*((m:ℝ)*(1-a^2)/2)^(-awaySigma m/(1-a^2)) < 5/26 := by
      convert hI using 1 <;> first | rfl | (unfold awaySigma; ring)
    linarith
  · have haHalf : 1/2 ≤ a := le_of_lt (lt_of_not_ge ha)
    have hF := away_endpoint_large_a hw hm haHalf haway
    have hD := away_decreasing_large_a hw hm haHalf
    have hd : 1-a^2 ≤ 3/4 := by nlinarith
    have hI := large_a_increasing_bound hmR haway hd
    have hI' : (5/3:ℝ)*a^2*m*((m:ℝ)*(1-a^2)/2)^(-awaySigma m/(1-a^2)) < 1/25 := by
      convert hI using 1 <;> first | rfl | (unfold awaySigma; ring)
    have ha95 : a < 19/20 := by nlinarith [hw.a_pos]
    linarith

end QuadraticTangZhang
