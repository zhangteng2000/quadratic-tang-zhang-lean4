import QuadraticTangZhang.NearIntegralBounds
import QuadraticTangZhang.NearEndpointBounds

/-! The near-boundary large-degree case. A relaxed coefficient 6001/m,
rather than the manuscript's sharper 61/m, is ample at m ≥ 10^6. -/
namespace QuadraticTangZhang

theorem near_coefficient_numeric {m a : ℝ} (hm : 1000000 ≤ m) (ha : 1/2 ≤ a) (ha1 : a ≤ 1) :
    (5/6:ℝ)*a^3*m*(m+1)*((8/3:ℝ)/(3*a^2*(m-1)/8)^3+4/m^4) < 6001/m := by
  have hm0 : 0 < m := by linarith
  have hm1 : 0 < m-1 := by linarith
  have ha0 : 0 < a := by linarith
  have hmlo : m/2 ≤ m-1 := by linarith
  have hmhi : m+1 ≤ 2*m := by linarith
  have hsplit : (5/6:ℝ)*a^3*m*(m+1)*((8/3:ℝ)/(3*a^2*(m-1)/8)^3+4/m^4) =
      (10240/243:ℝ)*m*(m+1)/(a^3*(m-1)^3)+(10/3:ℝ)*a^3*m*(m+1)/m^4 := by
    field_simp
    ring
  rw [hsplit]
  have hfirst : (10240/243:ℝ)*m*(m+1)/(a^3*(m-1)^3) ≤ (1310720/243:ℝ)/m := by
    calc
      _ ≤ (10240/243:ℝ)*m*(2*m)/((1/2:ℝ)^3*(m/2)^3) := by gcongr
      _ = _ := by field_simp; ring
  have hlast : (10/3:ℝ)*a^3*m*(m+1)/m^4 ≤ (20/3:ℝ)/m^2 := by
    calc
      _ ≤ (10/3:ℝ)*1^3*m*(2*m)/m^4 := by gcongr
      _ = _ := by field_simp; ring
  have hsmall : (20/3:ℝ)/m^2 < 1/m := by
    rw [div_lt_div_iff₀ (by positivity) hm0]
    nlinarith
  have hfirst' : (1310720/243:ℝ)/m < 6000/m := div_lt_div_of_pos_right (by norm_num) hm0
  have heq : (6000:ℝ)/m+1/m=6001/m := by ring
  linarith

theorem near_centerCoefficient_lt {m : ℕ} {a x s r : ℝ} (hw : ScalarConditions m a x s r)
    (hm : 1000000 ≤ m) (hnear : 1-a^2 ≤ 1/10) :
    centerCoefficient m a x < 6001/(m:ℝ) := by
  have hmR : (1000000:ℝ) ≤ m := by exact_mod_cast hm
  have ha2 : 9/10 ≤ a^2 := by linarith
  have haHalf : 1/2 ≤ a := by nlinarith [hw.a_pos]
  have hb := beta_rational_bound hw.a_pos hw.a_lt_one hw.x_le_one hw.moment_lower hw.moment_upper
    (by omega : 0<m) hw.polar
  have hI := near_center_integral_bound hw.degree hw.a_pos hw.a_lt_one ha2 hb.2.2.2.le hw.x_le_one
  have htails := scalar_near_power_tails hw hm hnear
  have hmcast : ((m-1:ℕ):ℝ)=(m:ℝ)-1 := by rw [Nat.cast_sub (by omega : 1≤m),Nat.cast_one]
  rw [hmcast] at hI
  have hI' : centerIntegral m a x ≤ (8/3:ℝ)/(3*a^2*((m:ℝ)-1)/8)^3+4/(m:ℝ)^4 := by
    apply hI.trans
    apply add_le_add_right
    calc
      _ ≤ 2*(1/(m:ℝ)^4+1/(m:ℝ)^4) := mul_le_mul_of_nonneg_left (add_le_add htails.2 htails.1) (by norm_num)
      _ = _ := by ring
  have hC := mul_le_mul_of_nonneg_left hI' (show (0:ℝ)≤(5/6)*a^3*m*((m:ℝ)+1) by positivity)
  have hC' : centerCoefficient m a x ≤
      (5/6:ℝ)*a^3*m*((m:ℝ)+1)*((8/3:ℝ)/(3*a^2*((m:ℝ)-1)/8)^3+4/(m:ℝ)^4) := by
    convert hC using 1 <;> first | rfl | (unfold centerCoefficient; ring)
  exact hC'.trans_lt (near_coefficient_numeric hmR haHalf hw.a_lt_one.le)

theorem large_near_scalar_exclusion {m : ℕ} {a x s r : ℝ} (hw : ScalarConditions m a x s r)
    (hm : 1000000 ≤ m) (hnear : 1-a^2 ≤ 1/10) : False := by
  have hC := near_centerCoefficient_lt hw hm hnear
  have hE := near_endpoint_tail hw hm hnear
  have hC0 := centerCoefficient_nonneg hw.a_pos.le hw.a_lt_one hw.x_le_one m
  have hmR : (1000000:ℝ) ≤ m := by exact_mod_cast hm
  have haHalf : 1/2 ≤ a := by nlinarith [hw.a_pos]
  have hbound : (6001:ℝ)/m ≤ 6001/1000000 := by gcongr
  exact exclude_center_boundary hw.a_pos.le hw.a_lt_one hC0 (by linarith) hw.r_nonneg hw.r_le_one hE hw.centered

end QuadraticTangZhang
