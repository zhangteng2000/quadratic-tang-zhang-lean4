import QuadraticTangZhang.RectangleGap
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

namespace QuadraticTangZhang

theorem boundary_tail_monotone {k b B : ℝ} (hb : 0 < b) (hbB : b ≤ B) (hBk : B ≤ k-1) :
    (b/(1+b))^k/b ≤ (B/(1+B))^k/B := by
  let f : ℝ → ℝ := fun t => (k-1)*Real.log t-k*Real.log (1+t)
  have hd (t : ℝ) (ht : t ∈ Set.Icc b B) :
      HasDerivAt f ((k-1)/t-k/(1+t)) t := by
    have ht0 : 0 < t := hb.trans_le ht.1
    have ht1 : 0 < 1+t := by linarith
    convert ((Real.hasDerivAt_log ht0.ne').const_mul (k-1)).sub
      ((((hasDerivAt_id t).const_add 1).log ht1.ne').const_mul k) using 1 <;>
      first | rfl | (simp only [div_eq_mul_inv,id_eq]; ring)
  have hmono : MonotoneOn f (Set.Icc b B) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _)
      (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
      (fun t ht => (hd t (interior_subset ht)).hasDerivWithinAt)
    intro t ht
    have htc := interior_subset ht
    have ht0 : 0 < t := hb.trans_le htc.1
    have ht1 : 0 < 1+t := by linarith
    rw [sub_nonneg,div_le_div_iff₀ ht1 ht0]
    nlinarith [htc.2]
  have h := hmono ⟨le_rfl,hbB⟩ ⟨hbB,le_rfl⟩ hbB
  have hB : 0 < B := hb.trans_le hbB
  have hbr : 0 < b/(1+b) := div_pos hb (by linarith)
  have hBr : 0 < B/(1+B) := div_pos hB (by linarith)
  apply (Real.log_le_log_iff (div_pos (Real.rpow_pos_of_pos hbr k) hb)
    (div_pos (Real.rpow_pos_of_pos hBr k) hB)).mp
  rw [Real.log_div (Real.rpow_pos_of_pos hbr k).ne' hb.ne',
    Real.log_div (Real.rpow_pos_of_pos hBr k).ne' hB.ne',
    Real.log_rpow hbr,Real.log_rpow hBr,
    Real.log_div hb.ne' (by linarith : 1+b ≠ 0),
    Real.log_div hB.ne' (by linarith : 1+B ≠ 0)]
  dsimp [f] at h
  nlinarith

theorem rectangle_boundary_tail {a x s A : ℝ} {m L M : ℕ}
    (ha : 0 < a) (ha1 : a < 1) (hx : x ≤ 1) (hxs : x^2 ≤ s) (hs : s ≤ 1)
    (hm : 0 < m) (hLm : L ≤ m) (hmM : m ≤ M) (hA : 0 ≤ A) (hAa : A ≤ a)
    (hsmall : (M:ℝ)/2*(1-A^2) ≤ ((L:ℝ)-1)/2)
    (hpolar : 1 ≤ ∫ t in (0:ℝ)..1, polarQuadratic a x s t^((m:ℝ)/2)) :
    beta a x 1^(((m:ℝ)+1)/2) ≤
      (1-a^2)*((M:ℝ)/2/((M:ℝ)/2*(1-A^2))*
        (((M:ℝ)/2*(1-A^2))/(1+(M:ℝ)/2*(1-A^2)))^(((L:ℝ)+1)/2)) := by
  let α := (m:ℝ)/2*(1-a^2)
  let U := (M:ℝ)/2*(1-A^2)
  let k := ((L:ℝ)+1)/2
  have hα : 0 < α := mul_pos (by positivity) (by nlinarith)
  have hαU : α ≤ U := by
    apply mul_le_mul
    · exact div_le_div_of_nonneg_right (by exact_mod_cast hmM) (by norm_num)
    · nlinarith
    · nlinarith
    · positivity
  have hU : 0 < U := hα.trans_le hαU
  have hb := beta_rational_bound ha ha1 hx hxs hs hm hpolar
  have hratio : 0 < α/(1+α) := div_pos hα (by linarith)
  have hp : beta a x 1^(((m:ℝ)+1)/2) ≤ (α/(1+α))^k := by
    apply (Real.rpow_le_rpow hb.1.le hb.2.1.le (by positivity)).trans
    apply Real.rpow_le_rpow_of_exponent_ge hratio hb.2.2.1.le
    dsimp [k]
    have : (L:ℝ) ≤ m := by exact_mod_cast hLm
    linarith
  have hmono := boundary_tail_monotone hα hαU (show U ≤ k-1 by dsimp [U,k]; linarith)
  have heq : (α/(1+α))^k = (1-a^2)*((m:ℝ)/2)*((α/(1+α))^k/α) := by
    have hc : (1-a^2)*((m:ℝ)/2)=α := by dsimp [α]; ring
    rw [hc,mul_div_cancel₀ _ hα.ne']
  calc
    beta a x 1^(((m:ℝ)+1)/2) ≤ (α/(1+α))^k := hp
    _ = (1-a^2)*((m:ℝ)/2)*((α/(1+α))^k/α) := heq
    _ ≤ (1-a^2)*((M:ℝ)/2)*((U/(1+U))^k/U) := by
      apply mul_le_mul
      · apply mul_le_mul_of_nonneg_left _ (by nlinarith)
        exact div_le_div_of_nonneg_right (by exact_mod_cast hmM) (by norm_num)
      · exact hmono
      · positivity
      · have : 0 ≤ 1-a^2 := by nlinarith
        positivity
    _ = _ := by dsimp [U,k]; ring

end QuadraticTangZhang
