import QuadraticTangZhang.AwayScalarBounds

namespace QuadraticTangZhang

theorem scaled_negative_power_identity {m d p : ℝ} (hm : 0 < m) (hd : 0 < d) :
    m*(m*d/2)^(-p)=(2/d)^p*m^(1-p) := by
  have hb : m*d/2=m/(2/d) := by field_simp
  have htwo : 0 < (2:ℝ)/d := by positivity
  rw [Real.rpow_neg (by positivity),hb,Real.div_rpow hm.le htwo.le,
    Real.rpow_sub hm,Real.rpow_one]
  have hpM := Real.rpow_pos_of_pos hm p
  have hpD := Real.rpow_pos_of_pos htwo p
  field_simp

theorem small_a_increasing_bound {m d : ℝ} (hm : 1000000 ≤ m) (hd : 3/4 ≤ d) (hd1 : d ≤ 1) :
    (5/3:ℝ)*(1-d)*m*(m*d/2)^(-((m-1)/(m+2))/d) < 5/26 := by
  let e := 1-d
  let p := ((m-1)/(m+2))/d
  have hm0 : 0 < m := by linarith
  have hd0 : 0 < d := by linarith
  have hm2 : 0 < m+2 := by linarith
  have he : 0 ≤ e := by dsimp [e]; linarith
  have hσ0 : 0 ≤ (m-1)/(m+2) := div_nonneg (by linarith) hm2.le
  have hσ1 : (m-1)/(m+2) ≤ 1 := (div_le_one hm2).mpr (by linarith)
  have hp0 : 0 ≤ p := div_nonneg hσ0 hd0.le
  have hp1 : p ≤ 4/3 := by dsimp [p]; rw [div_le_iff₀ hd0]; linarith
  have hbase : (2:ℝ)/d ≤ 8/3 := by rw [div_le_iff₀ hd0]; linarith
  have hfactor : (2/d)^p ≤ 4 := by
    apply (Real.rpow_le_rpow (by positivity) hbase hp0).trans
    exact (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤8/3) hp1).trans small_a_factor_power.le
  have hneg : -e/d ≤ -e := by
    rw [div_le_iff₀ hd0]
    nlinarith [mul_nonneg he (sub_nonneg.mpr hd1)]
  have hcor : (3/(m+2))/d ≤ 4/(m+2) := by
    calc
      _ ≤ (3/(m+2))/(3/4:ℝ) := by gcongr
      _ = _ := by ring
  have hform : 1-p=-e/d+(3/(m+2))/d := by dsimp [p,e]; field_simp; ring
  have hexp : 1-p ≤ -e+4/(m+2) := by rw [hform]; linarith
  have hmpow := Real.rpow_le_rpow_of_exponent_le (show 1 ≤ m by linarith) hexp
  rw [Real.rpow_add hm0] at hmpow
  have hmcorr := large_degree_power_correction hm
  have hmpow' : m^(1-p) ≤ m^(-e)*(1001/1000:ℝ) :=
    hmpow.trans (mul_le_mul_of_nonneg_left hmcorr.le (Real.rpow_nonneg hm0.le _))
  have heq : (5/3:ℝ)*(1-d)*m*(m*d/2)^(-((m-1)/(m+2))/d)=
      (5/3:ℝ)*e*((2/d)^p*m^(1-p)) := by
    have h := scaled_negative_power_identity (p := p) hm0 hd0
    have hneg : -((m-1)/(m+2))/d = -p := by dsimp [p]; ring
    rw [hneg,← h]
    dsimp [e]
    ring
  rw [heq]
  have hbound : (5/3:ℝ)*e*((2/d)^p*m^(1-p)) ≤
      (4*(5/3)*(1001/1000):ℝ)*(e*m^(-e)) := by
    have h := mul_le_mul_of_nonneg_left (mul_le_mul hfactor hmpow'
      (Real.rpow_nonneg hm0.le _) (by norm_num : (0:ℝ)≤4))
      (show (0:ℝ)≤(5/3)*e by positivity)
    convert h using 1 <;> first | rfl | ring
  have hmax := mul_le_mul_of_nonneg_left (epsilon_power_bound (by linarith : 1<m) he)
    (by norm_num : (0:ℝ)≤4*(5/3)*(1001/1000))
  have hlog := (large_log_bounds hm).1
  have hlog0 : 0 < Real.log m := by linarith
  have hconst : (4*(5/3)*(1001/1000):ℝ)/Real.exp 1 < 5/2 := by
    rw [div_lt_iff₀ (Real.exp_pos 1)]
    nlinarith [exp_one_bounds.1]
  have hquot := div_lt_div_of_pos_right hconst hlog0
  have hquot2 := div_lt_div_of_pos_left (by norm_num : (0:ℝ)<5/2) (by norm_num : (0:ℝ)<13) hlog
  have hnorm : (4*(5/3)*(1001/1000):ℝ)*(1/(Real.exp 1*Real.log m)) =
      ((4*(5/3)*(1001/1000):ℝ)/Real.exp 1)/Real.log m := by ring
  rw [hnorm] at hmax
  norm_num at hquot2
  exact hbound.trans_lt (hmax.trans_lt (hquot.trans hquot2))

theorem large_a_increasing_bound {m d : ℝ} (hm : 1000000 ≤ m) (hd : 1/10 ≤ d) (hd1 : d ≤ 3/4) :
    (5/3:ℝ)*(1-d)*m*(m*d/2)^(-((m-1)/(m+2))/d) < 1/25 := by
  have hm0 : 0 < m := by linarith
  have hd0 : 0 < d := by linarith
  have hbase : 1 ≤ m*d/2 := by nlinarith
  have hσ : (99999/100000:ℝ) ≤ (m-1)/(m+2) := by
    rw [le_div_iff₀ (by linarith : 0<m+2)]
    linarith
  have hp0 : 0 ≤ (m-1)/(m+2)/d := by positivity
  have hdgap : 0 ≤ 1-d := by linarith
  have hN : 0 ≤ (5/3:ℝ)*(1-d)*m := by positivity
  have toBound (c p : ℝ) (hc : 0 < c) (hcd : c*m ≤ m*d/2)
      (hp : p ≤ (m-1)/(m+2)/d) (hp1 : 0 ≤ p) :
      (m*d/2)^(-((m-1)/(m+2))/d) ≤ 1/(c*m)^p := by
    have hneg : -((m-1)/(m+2))/d = -((m-1)/(m+2)/d) := by ring
    rw [hneg,Real.rpow_neg (by positivity),inv_eq_one_div]
    have hpow := Real.rpow_le_rpow (mul_pos hc hm0).le hcd hp1
    have hexp := Real.rpow_le_rpow_of_exponent_le hbase hp
    exact one_div_le_one_div_of_le (Real.rpow_pos_of_pos (mul_pos hc hm0) p) (hpow.trans hexp)
  by_cases hdhalf : d ≤ 1/2
  · have he : (7/4:ℝ) ≤ (m-1)/(m+2)/d := by rw [le_div_iff₀ hd0]; linarith
    have hb := toBound (1/20) (7/4) (by norm_num) (by nlinarith) he (by norm_num)
    have h := mul_le_mul_of_nonneg_left hb hN
    have hnum : (5/3:ℝ)*(1-d)*m ≤ (5/3:ℝ)*m := by nlinarith
    have hdiv := div_le_div_of_nonneg_right hnum (Real.rpow_nonneg (show 0≤m/20 by positivity) (7/4:ℝ))
    have htail := away_tail_bin_one hm
    have heq : (1/20:ℝ)*m=m/20 := by ring
    rw [heq] at h
    simp only [mul_one_div] at h
    exact (h.trans hdiv).trans_lt (htail.trans (by norm_num))
  · have hdh : 1/2 ≤ d := le_of_lt (lt_of_not_ge hdhalf)
    by_cases hdfive : d ≤ 5/8
    · have he : (3/2:ℝ) ≤ (m-1)/(m+2)/d := by rw [le_div_iff₀ hd0]; linarith
      have hb := toBound (1/4) (3/2) (by norm_num) (by nlinarith) he (by norm_num)
      have h := mul_le_mul_of_nonneg_left hb hN
      have hnum : (5/3:ℝ)*(1-d)*m ≤ (5/6:ℝ)*m := by nlinarith
      have hdiv := div_le_div_of_nonneg_right hnum (Real.rpow_nonneg (show 0≤m/4 by positivity) (3/2:ℝ))
      have htail := away_tail_bin_two hm
      have heq : (1/4:ℝ)*m=m/4 := by ring
      rw [heq] at h
      simp only [mul_one_div] at h
      exact (h.trans hdiv).trans_lt (htail.trans (by norm_num))
    · have hd58 : 5/8 ≤ d := le_of_lt (lt_of_not_ge hdfive)
      have he : (21/16:ℝ) ≤ (m-1)/(m+2)/d := by rw [le_div_iff₀ hd0]; linarith
      have hb := toBound (5/16) (21/16) (by norm_num) (by nlinarith) he (by norm_num)
      have h := mul_le_mul_of_nonneg_left hb hN
      have hnum : (5/3:ℝ)*(1-d)*m ≤ (5/8:ℝ)*m := by nlinarith
      have hdiv := div_le_div_of_nonneg_right hnum (Real.rpow_nonneg (show 0≤5*m/16 by positivity) (21/16:ℝ))
      have htail := away_tail_bin_three hm
      have heq : (5/16:ℝ)*m=5*m/16 := by ring
      rw [heq] at h
      simp only [mul_one_div] at h
      exact (h.trans hdiv).trans_lt htail

end QuadraticTangZhang
