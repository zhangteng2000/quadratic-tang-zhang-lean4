import QuadraticTangZhang.LogGrowth

namespace QuadraticTangZhang

theorem scaled_power_tail_mono {c M m p : ℝ} (hc : 0 < c) (hM : 0 < M)
    (hm : M ≤ m) (hp : 1 ≤ p) : m/(c*m)^p ≤ M/(c*M)^p := by
  have hm0 := hM.trans_le hm
  have hr : 1 ≤ m/M := (le_div_iff₀ hM).mpr (by simpa using hm)
  have hrpow : m/M ≤ (m/M)^p := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hr hp
  have hsplit : (c*m)^p=(c*M)^p*(m/M)^p := by
    rw [← Real.mul_rpow (mul_pos hc hM).le (div_pos hm0 hM).le]
    congr 1
    field_simp
  calc
    m/(c*m)^p = m/((c*M)^p*(m/M)^p) := by rw [hsplit]
    _ ≤ m/((c*M)^p*(m/M)) := by gcongr
    _ = M/(c*M)^p := by field_simp

theorem fractional_power_gt {b c : ℝ} (hb : 0 ≤ b) (hc : 0 ≤ c)
    (k q : ℕ) (hq : 0 < q) (h : c^q < b^k) : c < b^((k:ℝ)/q) := by
  have hqR : (0:ℝ) < q := by exact_mod_cast hq
  apply (Real.rpow_lt_rpow_iff hc (Real.rpow_nonneg hb _) hqR).mp
  rw [← Real.rpow_mul hb,div_mul_cancel₀ _ hqR.ne',Real.rpow_natCast,Real.rpow_natCast]
  exact h

theorem fractional_power_lt {b c : ℝ} (hb : 0 ≤ b) (hc : 0 ≤ c)
    (k q : ℕ) (hq : 0 < q) (h : b^k < c^q) : b^((k:ℝ)/q) < c := by
  have hqR : (0:ℝ) < q := by exact_mod_cast hq
  apply (Real.rpow_lt_rpow_iff (Real.rpow_nonneg hb _) hc hqR).mp
  rw [← Real.rpow_mul hb,div_mul_cancel₀ _ hqR.ne',Real.rpow_natCast,Real.rpow_natCast]
  exact h

theorem small_a_factor_power : ((8/3:ℝ)^(4/3:ℝ)) < 4 := by
  exact fractional_power_lt (by norm_num) (by norm_num) 4 3 (by decide) (by norm_num)

theorem scaled_tail_bound {m c p w D : ℝ} (hm : 1000000 ≤ m) (hc : 0 < c)
    (hp : 1 ≤ p) (hw : 0 ≤ w) (hbase : w*1000000/(c*1000000)^p < D) :
    w*m/(c*m)^p < D := by
  have h := mul_le_mul_of_nonneg_left (scaled_power_tail_mono hc (by norm_num) hm hp) hw
  have hbase' : w*(1000000/(c*1000000)^p) < D := by simpa only [mul_div_assoc] using hbase
  simpa only [← mul_div_assoc] using h.trans_lt hbase'

theorem away_tail_bin_one {m : ℝ} (hm : 1000000 ≤ m) :
    (5/3:ℝ)*m/(m/20)^(7/4:ℝ) < 1/100 := by
  have hb : (500000000/3:ℝ) < (50000:ℝ)^(7/4:ℝ) :=
    fractional_power_gt (by norm_num) (by norm_num) 7 4 (by decide) (by norm_num)
  have hbase : (5/3:ℝ)*1000000/((1/20:ℝ)*1000000)^(7/4:ℝ) < 1/100 := by
    norm_num only [show (1/20:ℝ)*1000000=50000 by norm_num]
    rw [div_lt_iff₀ (Real.rpow_pos_of_pos (by norm_num) _)]
    linarith
  have h := scaled_tail_bound hm (by norm_num : (0:ℝ)<1/20) (by norm_num : (1:ℝ)≤7/4)
    (by norm_num : (0:ℝ)≤5/3) hbase
  convert h using 1 <;> first | rfl | ring

theorem away_tail_bin_two {m : ℝ} (hm : 1000000 ≤ m) :
    (5/6:ℝ)*m/(m/4)^(3/2:ℝ) < 1/100 := by
  have hb : (250000000/3:ℝ) < (250000:ℝ)^(3/2:ℝ) :=
    fractional_power_gt (by norm_num) (by norm_num) 3 2 (by decide) (by norm_num)
  have hbase : (5/6:ℝ)*1000000/((1/4:ℝ)*1000000)^(3/2:ℝ) < 1/100 := by
    norm_num only [show (1/4:ℝ)*1000000=250000 by norm_num] <;>
      (rw [div_lt_iff₀ (Real.rpow_pos_of_pos (by norm_num) _)]; linarith)
  have h := scaled_tail_bound hm (by norm_num : (0:ℝ)<1/4) (by norm_num : (1:ℝ)≤3/2)
    (by norm_num : (0:ℝ)≤5/6) hbase
  convert h using 1 <;> first | rfl | ring

theorem away_tail_bin_three {m : ℝ} (hm : 1000000 ≤ m) :
    (5/8:ℝ)*m/(5*m/16)^(21/16:ℝ) < 1/25 := by
  have hb : (15625000:ℝ) < (312500:ℝ)^(21/16:ℝ) :=
    fractional_power_gt (by norm_num) (by norm_num) 21 16 (by decide) (by norm_num)
  have hbase : (5/8:ℝ)*1000000/((5/16:ℝ)*1000000)^(21/16:ℝ) < 1/25 := by
    norm_num only [show (5/16:ℝ)*1000000=312500 by norm_num]
    rw [div_lt_iff₀ (Real.rpow_pos_of_pos (by norm_num) _)]
    linarith
  have h := scaled_tail_bound hm (by norm_num : (0:ℝ)<5/16) (by norm_num : (1:ℝ)≤21/16)
    (by norm_num : (0:ℝ)≤5/8) hbase
  convert h using 1 <;> first | rfl | ring

end QuadraticTangZhang
