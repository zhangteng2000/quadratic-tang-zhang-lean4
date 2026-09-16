import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Algebra.Polynomial.Splits
import Mathlib.Tactic

/-! # The Meir--Sharma boundary first-moment inequality from polynomial identities -/

namespace QuadraticTangZhang
open Polynomial

theorem boundary_reciprocal_real {z : ℂ} (hz : ‖z‖ ≤ 1) (hz1 : z ≠ 1) :
    (1 / 2 : ℝ) ≤ (1 / (1 - z)).re := by
  have hnorm : Complex.normSq z ≤ 1 := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg z]
  have hpos : 0 < Complex.normSq (1 - z) :=
    (Complex.normSq_pos).mpr (sub_ne_zero.mpr (Ne.symm hz1))
  simp only [one_div, Complex.inv_re]
  apply (le_div_iff₀ hpos).mpr
  simp only [Complex.sub_re, Complex.one_re, Complex.normSq_apply,
    Complex.sub_im, Complex.one_im] at *
  nlinarith

theorem root_reciprocal_identity (P : ℂ[X]) (hP : P.eval 1 ≠ 0) :
    ((((X - C 1) * P).derivative.roots).map (fun z : ℂ => 1 / (1 - z))).sum =
      2 * ((P.roots.map fun z : ℂ => 1 / (1 - z)).sum) := by
  have hfirst : (((X - C 1) * P).derivative).eval 1 = P.eval 1 := by
    simp [derivative_mul]
  have hsecond : (((X - C 1) * P).derivative.derivative).eval 1 = 2 * P.derivative.eval 1 := by
    simp [derivative_mul]
    ring
  rw [← (IsAlgClosed.splits _).eval_derivative_div_eval_of_ne_zero (hfirst ▸ hP),
    hfirst, hsecond, ← (IsAlgClosed.splits P).eval_derivative_div_eval_of_ne_zero hP]
  ring

theorem re_multiset_sum (S : Multiset ℂ) : S.sum.re = (S.map Complex.re).sum := by
  exact map_multiset_sum Complex.reAddGroupHom S

/-- Boundary first-moment inequality for a polynomial with its simple root factored out. -/
theorem boundary_firstMoment_factored (P : ℂ[X]) (hP : P.eval 1 ≠ 0)
    (hroots : ∀ z ∈ P.roots, ‖z‖ ≤ 1) :
    (P.natDegree : ℝ) ≤
      ((((X - C 1) * P).derivative.roots).map (fun z : ℂ => (1 / (1 - z)).re)).sum := by
  have hne : ∀ z ∈ P.roots, z ≠ 1 := by
    intro z hz heq
    subst z
    exact hP (isRoot_of_mem_roots hz)
  have hlower : (P.roots.card : ℝ) * (1 / 2) ≤
      (P.roots.map fun z : ℂ => (1 / (1 - z)).re).sum := by
    have h := Multiset.card_nsmul_le_sum (s := P.roots.map fun z : ℂ => (1 / (1 - z)).re)
      (a := (1 / 2 : ℝ)) (by
        intro x hx
        obtain ⟨z, hz, rfl⟩ := Multiset.mem_map.mp hx
        exact boundary_reciprocal_real (hroots z hz) (hne z hz))
    simpa [nsmul_eq_mul] using h
  have hid := congrArg Complex.re (root_reciprocal_identity P hP)
  simp only [re_multiset_sum, Multiset.map_map, Function.comp_def, Complex.mul_re,
    Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero] at hid
  rw [(IsAlgClosed.splits P).natDegree_eq_card_roots]
  linarith

theorem multiset_variance_one (S : Multiset ℂ) :
    (S.map fun q => Complex.normSq (q - 1)).sum =
      (S.map Complex.normSq).sum - 2 * (S.map Complex.re).sum + S.card := by
  induction S using Multiset.induction_on with
  | empty => simp
  | @cons q S ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.card_cons, Nat.cast_add,
      Nat.cast_one, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
      Complex.one_re, Complex.one_im] at ih ⊢
    linarith

theorem multiset_boundary_secondMoment (S : Multiset ℂ)
    (hfirst : (S.card : ℝ) ≤ (S.map Complex.re).sum) :
    (S.card : ℝ) ≤ (S.map Complex.normSq).sum := by
  have hnonneg : 0 ≤ (S.map fun q => Complex.normSq (q - 1)).sum := by
    apply Multiset.sum_nonneg
    intro x hx
    obtain ⟨z, hz, rfl⟩ := Multiset.mem_map.mp hx
    exact Complex.normSq_nonneg _
  rw [multiset_variance_one] at hnonneg
  linarith

theorem boundary_secondMoment_factored (P : ℂ[X]) (hP : P.eval 1 ≠ 0)
    (hroots : ∀ z ∈ P.roots, ‖z‖ ≤ 1) :
    (P.natDegree : ℝ) ≤
      ((((X - C 1) * P).derivative.roots).map (fun z : ℂ => Complex.normSq (1 / (1 - z)))).sum := by
  have hP0 : P ≠ 0 := by intro heq; simp [heq] at hP
  have hcard : (((X - C 1) * P).derivative.roots).card = P.natDegree := by
    rw [← (IsAlgClosed.splits _).natDegree_eq_card_roots, natDegree_derivative,
      natDegree_mul (X_sub_C_ne_zero 1) hP0, natDegree_X_sub_C]
    omega
  have hf := boundary_firstMoment_factored P hP hroots
  have h := multiset_boundary_secondMoment
    ((((X - C 1) * P).derivative.roots).map (fun z : ℂ => 1 / (1 - z)))
    (by simpa only [Multiset.card_map, Multiset.map_map, Function.comp_def, hcard] using hf)
  simpa only [Multiset.card_map, Multiset.map_map, Function.comp_def, hcard] using h

end QuadraticTangZhang
