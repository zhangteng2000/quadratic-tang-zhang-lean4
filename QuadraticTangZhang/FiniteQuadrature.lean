import QuadraticTangZhang.ConvexQuadrature

/-! # Soundness of a finite rational quadrature mesh

The mesh endpoints, their order, and each upper enclosure are explicit hypotheses.
The eventual Boolean verifier checks the mesh conditions; no property of an
external mesh generator is trusted.
-/
namespace QuadraticTangZhang
open MeasureTheory

def chordOne (l r u v : ℚ) : ℚ :=
  (r-l)*(l/2+(r-l)/6)*u+(r-l)*(l/2+(r-l)/3)*v

def chordTwo (l r u v : ℚ) : ℚ :=
  (r-l)*(l^2/2+l*(r-l)/3+(r-l)^2/12)*u+
    (r-l)*(l^2/2+2*l*(r-l)/3+(r-l)^2/4)*v

def quadOne (N : ℕ) (p v : ℕ → ℚ) : ℚ :=
  ∑ i ∈ Finset.range N, chordOne (p i) (p (i+1)) (v i) (v (i+1))

def quadTwo (N : ℕ) (p v : ℕ → ℚ) : ℚ :=
  ∑ i ∈ Finset.range N, chordTwo (p i) (p (i+1)) (v i) (v (i+1))

theorem segment_quadrature_one {f : ℝ → ℝ} {l r u v : ℚ}
    (hl : 0 ≤ l) (hlr : l ≤ r) (hr : r ≤ 1)
    (hf : ConvexOn ℝ (Set.Icc (0:ℝ) 1) f) (hc : ContinuousOn f (Set.Icc (0:ℝ) 1))
    (hu : f (l:ℝ) ≤ (u:ℝ)) (hv : f (r:ℝ) ≤ (v:ℝ)) :
    (∫ t in (l:ℝ)..(r:ℝ), t*f t) ≤ (chordOne l r u v:ℝ) := by
  have hl0 : (0:ℝ) ≤ l := by exact_mod_cast hl
  have hlr' : (l:ℝ) ≤ r := by exact_mod_cast hlr
  have hr1 : (r:ℝ) ≤ 1 := by exact_mod_cast hr
  rcases hlr'.eq_or_lt with heq | hlt
  · have hq : l=r := by exact_mod_cast heq
    subst r
    simp [chordOne]
  have hsub : Set.Icc (l:ℝ) ((l:ℝ)+((r:ℝ)-l)) ⊆ Set.Icc (0:ℝ) 1 := by
    intro t ht
    constructor <;> linarith [ht.1,ht.2]
  have h := convex_quadrature_weight_one hl0 (sub_pos.mpr hlt)
    (hf.subset hsub (convex_Icc _ _)) (hc.mono hsub)
  simp only [add_sub_cancel] at h
  have hw1 : 0 ≤ ((r:ℝ)-l)*((l:ℝ)/2+((r:ℝ)-l)/6) := by positivity
  have hw2 : 0 ≤ ((r:ℝ)-l)*((l:ℝ)/2+((r:ℝ)-l)/3) := by positivity
  have hu' := mul_le_mul_of_nonneg_left hu hw1
  have hv' := mul_le_mul_of_nonneg_left hv hw2
  unfold chordOne
  push_cast
  linarith

theorem segment_quadrature_two {f : ℝ → ℝ} {l r u v : ℚ}
    (hl : 0 ≤ l) (hlr : l ≤ r) (hr : r ≤ 1)
    (hf : ConvexOn ℝ (Set.Icc (0:ℝ) 1) f) (hc : ContinuousOn f (Set.Icc (0:ℝ) 1))
    (hu : f (l:ℝ) ≤ (u:ℝ)) (hv : f (r:ℝ) ≤ (v:ℝ)) :
    (∫ t in (l:ℝ)..(r:ℝ), t^2*f t) ≤ (chordTwo l r u v:ℝ) := by
  have hl0 : (0:ℝ) ≤ l := by exact_mod_cast hl
  have hlr' : (l:ℝ) ≤ r := by exact_mod_cast hlr
  have hr1 : (r:ℝ) ≤ 1 := by exact_mod_cast hr
  rcases hlr'.eq_or_lt with heq | hlt
  · have hq : l=r := by exact_mod_cast heq
    subst r
    simp [chordTwo]
  have hsub : Set.Icc (l:ℝ) ((l:ℝ)+((r:ℝ)-l)) ⊆ Set.Icc (0:ℝ) 1 := by
    intro t ht
    constructor <;> linarith [ht.1,ht.2]
  have h := convex_quadrature_weight_two hl0 (sub_pos.mpr hlt)
    (hf.subset hsub (convex_Icc _ _)) (hc.mono hsub)
  simp only [add_sub_cancel] at h
  have hw1 : 0 ≤ ((r:ℝ)-l)*((l:ℝ)^2/2+(l:ℝ)*((r:ℝ)-l)/3+((r:ℝ)-l)^2/12) := by positivity
  have hw2 : 0 ≤ ((r:ℝ)-l)*((l:ℝ)^2/2+2*(l:ℝ)*((r:ℝ)-l)/3+((r:ℝ)-l)^2/4) := by positivity
  have hu' := mul_le_mul_of_nonneg_left hu hw1
  have hv' := mul_le_mul_of_nonneg_left hv hw2
  unfold chordTwo
  push_cast
  linarith

theorem finite_quadrature_one_sound {f : ℝ → ℝ} {N : ℕ} {p v : ℕ → ℚ}
    (hp0 : p 0=0) (hpN : p N=1)
    (hp : ∀ i ≤ N, 0 ≤ p i ∧ p i ≤ 1) (hmono : ∀ i < N, p i ≤ p (i+1))
    (hf : ConvexOn ℝ (Set.Icc (0:ℝ) 1) f) (hc : ContinuousOn f (Set.Icc (0:ℝ) 1))
    (hv : ∀ i ≤ N, f (p i:ℝ) ≤ (v i:ℝ)) :
    (∫ t in (0:ℝ)..1, t*f t) ≤ (quadOne N p v:ℝ) := by
  have hint (i : ℕ) (hi : i < N) : IntervalIntegrable (fun t : ℝ => t*f t) volume (p i:ℝ) (p (i+1):ℝ) := by
    have hle : (p i:ℝ) ≤ p (i+1) := by exact_mod_cast hmono i hi
    apply ((continuous_id.continuousOn.mul hc).mono _).intervalIntegrable_of_Icc hle
    intro t ht
    have hi0 : (0:ℝ) ≤ p i := by exact_mod_cast (hp i (by omega)).1
    have hi1 : (p (i+1):ℝ) ≤ 1 := by exact_mod_cast (hp (i+1) (by omega)).2
    exact ⟨hi0.trans ht.1,ht.2.trans hi1⟩
  have hsum := intervalIntegral.sum_integral_adjacent_intervals hint
  rw [hp0,hpN] at hsum
  norm_cast at hsum
  rw [← hsum]
  unfold quadOne
  push_cast
  apply Finset.sum_le_sum
  intro i hi
  have hiN := Finset.mem_range.mp hi
  exact segment_quadrature_one (hp i (by omega)).1 (hmono i hiN)
    (hp (i+1) (by omega)).2 hf hc (hv i (by omega)) (hv (i+1) (by omega))

theorem finite_quadrature_two_sound {f : ℝ → ℝ} {N : ℕ} {p v : ℕ → ℚ}
    (hp0 : p 0=0) (hpN : p N=1)
    (hp : ∀ i ≤ N, 0 ≤ p i ∧ p i ≤ 1) (hmono : ∀ i < N, p i ≤ p (i+1))
    (hf : ConvexOn ℝ (Set.Icc (0:ℝ) 1) f) (hc : ContinuousOn f (Set.Icc (0:ℝ) 1))
    (hv : ∀ i ≤ N, f (p i:ℝ) ≤ (v i:ℝ)) :
    (∫ t in (0:ℝ)..1, t^2*f t) ≤ (quadTwo N p v:ℝ) := by
  have hint (i : ℕ) (hi : i < N) : IntervalIntegrable (fun t : ℝ => t^2*f t) volume (p i:ℝ) (p (i+1):ℝ) := by
    have hle : (p i:ℝ) ≤ p (i+1) := by exact_mod_cast hmono i hi
    apply (((continuous_id.pow 2).continuousOn.mul hc).mono _).intervalIntegrable_of_Icc hle
    intro t ht
    have hi0 : (0:ℝ) ≤ p i := by exact_mod_cast (hp i (by omega)).1
    have hi1 : (p (i+1):ℝ) ≤ 1 := by exact_mod_cast (hp (i+1) (by omega)).2
    exact ⟨hi0.trans ht.1,ht.2.trans hi1⟩
  have hsum := intervalIntegral.sum_integral_adjacent_intervals hint
  rw [hp0,hpN] at hsum
  norm_cast at hsum
  rw [← hsum]
  unfold quadTwo
  push_cast
  apply Finset.sum_le_sum
  intro i hi
  have hiN := Finset.mem_range.mp hi
  exact segment_quadrature_two (hp i (by omega)).1 (hmono i hiN)
    (hp (i+1) (by omega)).2 hf hc (hv i (by omega)) (hv (i+1) (by omega))

end QuadraticTangZhang
