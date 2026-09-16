import QuadraticTangZhang.CertificateVerifier
import QuadraticTangZhang.ExponentialIntegrals
import QuadraticTangZhang.PowerTailBounds

namespace QuadraticTangZhang

noncomputable def awayLambda (m : ℕ) (a : ℝ) : ℝ := ((m:ℝ)+2)/2*(1-a^2)
noncomputable def awaySigma (m : ℕ) : ℝ := ((m:ℝ)-1)/((m:ℝ)+2)

theorem away_lambda_lower {m : ℕ} {a x s r : ℝ} (hw : ScalarConditions m a x s r)
    (hm : 1000000 ≤ m) (haway : 1/10 ≤ 1-a^2) : 50000 ≤ awayLambda m a := by
  have hmR : (1000000:ℝ) ≤ m := by exact_mod_cast hm
  have h := mul_le_mul (show (500000:ℝ) ≤ ((m:ℝ)+2)/2 by linarith) haway
    (by norm_num : (0:ℝ)≤1/10) (by positivity : (0:ℝ)≤((m:ℝ)+2)/2)
  dsimp [awayLambda]
  linarith

theorem away_rho_log {m : ℕ} {a x s r : ℝ} (hw : ScalarConditions m a x s r)
    (hm : 1000000 ≤ m) (haway : 1/10 ≤ 1-a^2) :
    Real.log (awayLambda m a)/awayLambda m a ≤ rho a x s := by
  have hL := away_lambda_lower hw hm haway
  have heq : ((m:ℝ)/2+1)*(1-a^2)=awayLambda m a := by unfold awayLambda; ring
  have h := rho_log_lower_bound hw.a_pos.le hw.a_lt_one hw.moment_lower
    (by omega : 0<m) hw.polar (by rw [heq]; linarith)
  simpa only [heq] using h

theorem power_bound_from_log_gap {B v L e : ℝ} (hB : 0 ≤ B) (hv : v ≤ 1-B)
    (hL : 0 < L) (he : 0 ≤ e) (hlog : Real.log L/L ≤ v) : B^e ≤ L^(-e/L) := by
  apply (rpow_le_exp_gap hB (by linarith) he).trans
  rw [Real.rpow_def_of_pos hL]
  apply Real.exp_le_exp.mpr
  have h := mul_le_mul_of_nonneg_left hlog he
  have hid : Real.log L*(-e/L)=-(e*(Real.log L/L)) := by ring
  rw [hid]
  linarith

theorem away_endpoint_power {m : ℕ} {a x s r : ℝ} (hw : ScalarConditions m a x s r)
    (hm : 1000000 ≤ m) (haway : 1/10 ≤ 1-a^2) :
    beta a x 1^(((m-1:ℕ):ℝ)/2) ≤
      ((m:ℝ)*(1-a^2)/2)^(-awaySigma m/(1-a^2)) := by
  have hL := away_lambda_lower hw hm haway
  have hmR : (1000000:ℝ) ≤ m := by exact_mod_cast hm
  have hd : 0 < 1-a^2 := by linarith
  have hbase : 0 < (m:ℝ)*(1-a^2)/2 := by positivity
  have hLb : (m:ℝ)*(1-a^2)/2 ≤ awayLambda m a := by unfold awayLambda; nlinarith
  have hβ := beta_pos_on_unit hw.a_pos.le hw.a_lt_one hw.x_le_one (by norm_num : (0:ℝ)≤1) le_rfl
  have hgap := rho_le_gap (x := x) (by nlinarith [hw.a_pos,hw.a_lt_one] : a^2≤1) hw.moment_upper
  have h := power_bound_from_log_gap hβ.le hgap (by linarith : 0<awayLambda m a)
    (by positivity : (0:ℝ)≤((m-1:ℕ):ℝ)/2) (away_rho_log hw hm haway)
  have hexp : -(((m-1:ℕ):ℝ)/2)/awayLambda m a = -awaySigma m/(1-a^2) := by
    rw [Nat.cast_sub (by omega : 1≤m),Nat.cast_one]
    unfold awayLambda awaySigma
    field_simp <;> ring
  rw [hexp] at h
  apply h.trans
  apply Real.rpow_le_rpow_of_nonpos hbase hLb
  unfold awaySigma
  have : 0 ≤ (m:ℝ)-1 := by linarith
  exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (by positivity)) hd.le

theorem away_decreasing_numeric {m a x : ℝ} (hm : 1000000 ≤ m) (ha : 0 < a) (hx : 0 < x) :
    (5/3:ℝ)*a^2*m*(4/((m-1)^2*a^2*x^2)) ≤ 7/(m*x^2) := by
  have hm0 : 0 < m := by linarith
  have hm1 : 0 < m-1 := by linarith
  have hml : (99/100:ℝ)*m ≤ m-1 := by linarith
  have heq : (5/3:ℝ)*a^2*m*(4/((m-1)^2*a^2*x^2)) = (20/3:ℝ)*m/((m-1)^2*x^2) := by
    field_simp
    ring
  rw [heq]
  calc
    _ ≤ (20/3:ℝ)*m/(((99/100:ℝ)*m)^2*x^2) := by gcongr
    _ = (200000/29403:ℝ)/(m*x^2) := by field_simp; ring
    _ ≤ _ := div_le_div_of_nonneg_right (by norm_num) (by positivity)

theorem away_direct_reduction {m : ℕ} {a x s r : ℝ} (hw : ScalarConditions m a x s r)
    (hm : 1000000 ≤ m) (haway : 1/10 ≤ 1-a^2) :
    1 ≤ beta a x 1^((m:ℝ)/2)+a+7/((m:ℝ)*x^2)+
      (5/3:ℝ)*a^2*m*((m:ℝ)*(1-a^2)/2)^(-awaySigma m/(1-a^2)) := by
  have hb := beta_rational_bound hw.a_pos hw.a_lt_one hw.x_le_one hw.moment_lower hw.moment_upper
    (by omega : 0<m) hw.polar
  have hx : 0 < x := by linarith [hb.2.2.2,hw.a_pos]
  have hi := direct_integral_split_bound (by omega : 2≤m) hw.a_pos hw.a_lt_one hx hw.x_le_one
  have hc : (0:ℝ) ≤ (5/3)*a^2*m := by positivity
  have hR := mul_le_mul_of_nonneg_left hi hc
  have hmcast : ((m-1:ℕ):ℝ)=(m:ℝ)-1 := by rw [Nat.cast_sub (by omega : 1≤m),Nat.cast_one]
  have hdec := away_decreasing_numeric (m := (m:ℝ)) (by exact_mod_cast hm) hw.a_pos hx
  rw [← hmcast] at hdec
  have hinc := mul_le_mul_of_nonneg_left (away_endpoint_power hw hm haway) hc
  have hT : (m:ℝ)*a/(m+1) ≤ a := by
    rw [div_le_iff₀ (by positivity : (0:ℝ)<m+1)]
    nlinarith [hw.a_pos]
  nlinarith [hw.direct]

theorem away_endpoint_exp {m : ℕ} {a x s r c : ℝ} (hw : ScalarConditions m a x s r)
    (hm : 1000000 ≤ m) (haway : 1/10 ≤ 1-a^2)
    (hc : c < ((m:ℝ)/2/awayLambda m a)*Real.log (awayLambda m a)) :
    beta a x 1^((m:ℝ)/2) < Real.exp (-c) := by
  have hβ := beta_pos_on_unit hw.a_pos.le hw.a_lt_one hw.x_le_one (by norm_num : (0:ℝ)≤1) le_rfl
  have hgap := rho_le_gap (x := x) (by nlinarith [hw.a_pos,hw.a_lt_one] : a^2≤1) hw.moment_upper
  have hpow := rpow_le_exp_gap hβ.le (show beta a x 1≤1-rho a x s by linarith) (show (0:ℝ)≤(m:ℝ)/2 by positivity)
  have hlog := mul_le_mul_of_nonneg_left (away_rho_log hw hm haway) (show (0:ℝ)≤(m:ℝ)/2 by positivity)
  have hid : (m:ℝ)/2*(Real.log (awayLambda m a)/awayLambda m a)=
      ((m:ℝ)/2/awayLambda m a)*Real.log (awayLambda m a) := by ring
  rw [hid] at hlog
  apply hpow.trans_lt
  exact Real.exp_lt_exp.mpr (by linarith)

theorem away_endpoint_small_a {m : ℕ} {a x s r : ℝ} (hw : ScalarConditions m a x s r)
    (hm : 1000000 ≤ m) (ha : a ≤ 1/2) : beta a x 1^((m:ℝ)/2) < 1/10000 := by
  have hmR : (1000000:ℝ)≤m := by exact_mod_cast hm
  have hd : 3/4 ≤ 1-a^2 := by nlinarith [hw.a_pos]
  have hL : 375000 ≤ awayLambda m a := by
    have h := mul_le_mul (show (500000:ℝ)≤((m:ℝ)+2)/2 by linarith) hd (by norm_num) (by positivity)
    dsimp [awayLambda]
    linarith
  have hL0 : 0 < awayLambda m a := by linarith
  have hLog := log_three_eighths_million.trans_le (Real.log_le_log (by norm_num) hL)
  have hLu : awayLambda m a ≤ ((m:ℝ)+2)/2 := by
    unfold awayLambda
    apply mul_le_of_le_one_right (by positivity)
    nlinarith [sq_nonneg a]
  have hratio : (5/6:ℝ) ≤ (m:ℝ)/2/awayLambda m a := by rw [le_div_iff₀ hL0]; linarith
  have hmul := mul_le_mul_of_nonneg_right hratio (show 0 ≤ Real.log (awayLambda m a) by linarith)
  have hF := away_endpoint_exp (c := 10) hw hm (by linarith) (by linarith)
  apply hF.trans
  have he := pow_lt_pow_left₀ exp_one_bounds.1 (by norm_num : (0:ℝ)≤27/10) (by norm_num : (10:ℕ)≠0)
  rw [Real.exp_one_pow] at he
  rw [Real.exp_neg,inv_eq_one_div]
  apply one_div_lt_one_div_of_lt (by norm_num)
  norm_num at he
  linarith

theorem away_endpoint_large_a {m : ℕ} {a x s r : ℝ} (hw : ScalarConditions m a x s r)
    (hm : 1000000 ≤ m) (ha : 1/2 ≤ a) (haway : 1/10 ≤ 1-a^2) :
    beta a x 1^((m:ℝ)/2) < 1/125 := by
  have hmR : (1000000:ℝ)≤m := by exact_mod_cast hm
  have hd : 1-a^2 ≤ 3/4 := by nlinarith [hw.a_pos]
  have hL := away_lambda_lower hw hm haway
  have hL0 : 0 < awayLambda m a := by linarith
  have hLog := log_fifty_thousand.trans_le (Real.log_le_log (by norm_num) hL)
  have hLu : awayLambda m a ≤ 3*((m:ℝ)+2)/8 := by
    have h := mul_le_mul_of_nonneg_left hd (show (0:ℝ)≤((m:ℝ)+2)/2 by positivity)
    dsimp [awayLambda]
    nlinarith
  have hratio : (5/4:ℝ) ≤ (m:ℝ)/2/awayLambda m a := by rw [le_div_iff₀ hL0]; linarith
  have hmul := mul_le_mul_of_nonneg_right hratio (show 0 ≤ Real.log (awayLambda m a) by linarith)
  have hF := away_endpoint_exp (c := 5) hw hm haway (by linarith)
  apply hF.trans
  have he := pow_lt_pow_left₀ exp_one_bounds.1 (by norm_num : (0:ℝ)≤27/10) (by norm_num : (5:ℕ)≠0)
  rw [Real.exp_one_pow] at he
  rw [Real.exp_neg,inv_eq_one_div]
  apply one_div_lt_one_div_of_lt (by norm_num)
  norm_num at he
  linarith

end QuadraticTangZhang
