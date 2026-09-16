import QuadraticTangZhang.NearPowerTails
import QuadraticTangZhang.BoundaryTail

namespace QuadraticTangZhang

theorem large_inverse_four_lt {m : ℝ} (hm : 1000000 ≤ m) : 1/m^4 < 1/(2*m) := by
  have hm0 : 0 < m := by linarith
  apply one_div_lt_one_div_of_lt (by positivity)
  have h2 : 2 ≤ m^2 := by nlinarith [sq_nonneg (m-2)]
  nlinarith [sq_nonneg (m^2-2),sq_nonneg (m-2)]

theorem near_endpoint_tail {m : ℕ} {a x s r : ℝ} (hw : ScalarConditions m a x s r)
    (hm : 1000000 ≤ m) (hnear : 1-a^2 ≤ 1/10) :
    beta a x 1^(((m+1:ℕ):ℝ)/2) < (1-a^2)/4 := by
  let α := (m:ℝ)/2*(1-a^2)
  let p := ((m:ℝ)+1)/2
  let v := ((m:ℝ)-3)/2
  have hmR : (1000000:ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0:ℝ) < m := by positivity
  have hα : 0 < α := mul_pos (by positivity) (by nlinarith [hw.a_pos,hw.a_lt_one])
  have hb := beta_rational_bound hw.a_pos hw.a_lt_one hw.x_le_one hw.moment_lower hw.moment_upper
    (by omega : 0<m) hw.polar
  have htails := scalar_near_power_tails hw hm hnear
  have hB1 : beta a x 1 ≤ 1 := hb.2.1.le.trans hb.2.2.1.le
  have hE : beta a x 1^p ≤ 1/(m:ℝ)^4 := by
    apply (Real.rpow_le_rpow_of_exponent_ge hb.1 hB1 (show v ≤ p by dsimp [v,p]; linarith)).trans
    exact htails.1
  have hinv := large_inverse_four_lt hmR
  have hαeq : (1-a^2)/4=α/(2*(m:ℝ)) := by
    dsimp [α]
    field_simp
    ring
  have goalP : beta a x 1^p < (1-a^2)/4 := by
    rw [hαeq]
    by_cases hbig : 1 ≤ α
    · exact hE.trans_lt (hinv.trans_le (div_le_div_of_nonneg_right hbig (by positivity)))
    · have hα1 : α ≤ 1 := le_of_lt (lt_of_not_ge hbig)
      have hpow : ((1/2:ℝ)^p) ≤ 1/(m:ℝ)^4 := by
        have he := Real.rpow_le_rpow_of_exponent_ge (by norm_num : (0:ℝ)<1/2)
          (by norm_num : (1/2:ℝ)≤1) (show v ≤ p by dsimp [v,p]; linarith)
        have hbase := Real.rpow_le_rpow (by norm_num : (0:ℝ)≤1/2)
          (by norm_num : (1/2:ℝ)≤133/160) (show 0 ≤ v by dsimp [v]; linarith)
        exact he.trans (hbase.trans htails.2)
      have hmono := boundary_tail_monotone (k := p) hα hα1 (by dsimp [p]; linarith : (1:ℝ)≤p-1)
      norm_num only [one_add_one_eq_two,div_one] at hmono
      have hratio : (α/(1+α))^p ≤ α*((1/2:ℝ)^p) := by
        have h := (div_le_iff₀ hα).mp hmono
        nlinarith [h]
      have hβ := Real.rpow_le_rpow hb.1.le hb.2.1.le (show 0 ≤ p by dsimp [p]; positivity)
      have hβ' : beta a x 1^p ≤ α/(m:ℝ)^4 := by
        apply hβ.trans (hratio.trans _)
        simpa only [mul_one_div] using mul_le_mul_of_nonneg_left hpow hα.le
      apply hβ'.trans_lt
      simpa only [mul_one_div] using mul_lt_mul_of_pos_left hinv hα
  simpa only [p,Nat.cast_add,Nat.cast_one] using goalP

end QuadraticTangZhang
