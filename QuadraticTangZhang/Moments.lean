import Mathlib.Analysis.Complex.Norm
import Mathlib.Tactic

/-! # Exact finite second-moment identities and the boundary rigidity argument -/

namespace QuadraticTangZhang
open scoped BigOperators

noncomputable def meanRe {m : ℕ} (q : Fin m → ℂ) : ℝ := (∑ i, (q i).re) / m
noncomputable def meanIm {m : ℕ} (q : Fin m → ℂ) : ℝ := (∑ i, (q i).im) / m
noncomputable def secondMoment {m : ℕ} (q : Fin m → ℂ) : ℝ :=
  (∑ i, Complex.normSq (q i)) / m

theorem normSq_sub_coordinates (q : ℂ) (x y : ℝ) :
    Complex.normSq (q - ⟨x, y⟩) =
      Complex.normSq q - 2 * x * q.re - 2 * y * q.im + (x ^ 2 + y ^ 2) := by
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
  ring

theorem sum_normSq_sub {m : ℕ} (q : Fin m → ℂ) (x y : ℝ) :
    ∑ i, Complex.normSq (q i - ⟨x, y⟩) =
      (∑ i, Complex.normSq (q i)) - 2 * x * (∑ i, (q i).re) -
        2 * y * (∑ i, (q i).im) + m * (x ^ 2 + y ^ 2) := by
  simp_rw [normSq_sub_coordinates]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

theorem variance_identity {m : ℕ} (hm : 0 < m) (q : Fin m → ℂ) :
    (∑ i, Complex.normSq (q i - ⟨meanRe q, meanIm q⟩)) / m =
      secondMoment q - (meanRe q ^ 2 + meanIm q ^ 2) := by
  rw [sum_normSq_sub]
  have hm0 : (m : ℝ) ≠ 0 := by positivity
  unfold meanRe meanIm secondMoment
  field_simp
  ring

theorem mean_sq_le_secondMoment {m : ℕ} (hm : 0 < m) (q : Fin m → ℂ) :
    meanRe q ^ 2 + meanIm q ^ 2 ≤ secondMoment q := by
  have h : 0 ≤ (∑ i, Complex.normSq (q i - ⟨meanRe q, meanIm q⟩)) / m := by
    exact div_nonneg (Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _) (Nat.cast_nonneg _)
  rw [variance_identity hm] at h
  linarith

theorem secondMoment_nonneg {m : ℕ} (q : Fin m → ℂ) : 0 ≤ secondMoment q := by
  exact div_nonneg (Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _) (Nat.cast_nonneg _)

theorem meanRe_bounds {m : ℕ} (hm : 0 < m) (q : Fin m → ℂ)
    (hs : secondMoment q ≤ 1) : -1 ≤ meanRe q ∧ meanRe q ≤ 1 := by
  have := mean_sq_le_secondMoment hm q
  constructor <;> nlinarith [sq_nonneg (meanIm q), sq_nonneg (meanRe q + 1),
    sq_nonneg (meanRe q - 1)]

theorem sum_centered_re {m : ℕ} (hm : 0 < m) (q : Fin m → ℂ) :
    ∑ i, ((q i).re - meanRe q) = 0 := by
  have hm0 : (m : ℝ) ≠ 0 := by positivity
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, meanRe]
  field_simp
  ring

theorem sum_centered_im {m : ℕ} (hm : 0 < m) (q : Fin m → ℂ) :
    ∑ i, ((q i).im - meanIm q) = 0 := by
  have hm0 : (m : ℝ) ≠ 0 := by positivity
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, meanIm]
  field_simp
  ring

/-- The boundary inequality's second-moment consequence. Its first-moment premise is explicit. -/
theorem boundary_secondMoment {m : ℕ} (hm : 0 < m) (q : Fin m → ℂ)
    (hfirst : (m : ℝ) ≤ ∑ i, (q i).re) : 1 ≤ secondMoment q := by
  have h := Finset.sum_nonneg (s := Finset.univ) (fun (i : Fin m) _ =>
    Complex.normSq_nonneg (q i - ⟨1, 0⟩))
  rw [sum_normSq_sub] at h
  dsimp [secondMoment]
  apply (le_div_iff₀ (show (0 : ℝ) < m by positivity)).mpr
  norm_num at h ⊢
  linarith

theorem boundary_rigidity {m : ℕ} (hm : 0 < m) (q : Fin m → ℂ)
    (hfirst : (m : ℝ) ≤ ∑ i, (q i).re) (hs : secondMoment q = 1) :
    ∀ i, q i = 1 := by
  have hsum : (∑ i, Complex.normSq (q i)) = m := by
    unfold secondMoment at hs
    exact (div_eq_one_iff_eq (show (m : ℝ) ≠ 0 by positivity)).mp hs
  have hnonneg : ∀ i ∈ (Finset.univ : Finset (Fin m)),
      0 ≤ Complex.normSq (q i - ⟨1, 0⟩) := fun i _ => Complex.normSq_nonneg _
  have hz : ∑ i, Complex.normSq (q i - ⟨1, 0⟩) = 0 := by
    have hn := Finset.sum_nonneg hnonneg
    rw [sum_normSq_sub, hsum] at hn ⊢
    norm_num at hn ⊢
    linarith
  intro i
  have hi := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hz i (Finset.mem_univ i)
  have heq := Complex.normSq_eq_zero.mp hi
  exact sub_eq_zero.mp heq

theorem boundary_equality_iff {m : ℕ} (hm : 0 < m) (q : Fin m → ℂ)
    (hfirst : (m : ℝ) ≤ ∑ i, (q i).re) :
    secondMoment q = 1 ↔ ∀ i, q i = 1 := by
  constructor
  · exact boundary_rigidity hm q hfirst
  · intro h
    simp [secondMoment, h, Nat.ne_of_gt hm]

theorem affine_normSq (q : ℂ) (a b : ℝ) :
    Complex.normSq ((a : ℂ) + (b : ℂ) * q) =
      a ^ 2 + 2 * a * b * q.re + b ^ 2 * Complex.normSq q := by
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

theorem affine_secondMoment {m : ℕ} (hm : 0 < m) (q : Fin m → ℂ) (a b : ℝ) :
    secondMoment (fun i => (a : ℂ) + (b : ℂ) * q i) =
      a ^ 2 + 2 * a * b * meanRe q + b ^ 2 * secondMoment q := by
  have hm0 : (m : ℝ) ≠ 0 := by positivity
  unfold secondMoment meanRe
  simp_rw [affine_normSq]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

end QuadraticTangZhang
