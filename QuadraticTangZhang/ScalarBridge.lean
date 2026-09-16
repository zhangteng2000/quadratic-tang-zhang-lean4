import QuadraticTangZhang.CertificateVerifier
import QuadraticTangZhang.Reciprocal
import Mathlib.Data.Fintype.Basic

/-! # Connecting actual polynomial counterexamples to the certified scalar conditions -/
namespace QuadraticTangZhang
open Polynomial MeasureTheory

theorem exists_fin_family (q : Multiset ℂ) :
    ∃ f : Fin q.card → ℂ, Finset.univ.val.map f=q := by
  induction q using Quotient.inductionOn with
  | h l =>
    refine ⟨fun i => l[i], ?_⟩
    rw [Fin.univ_val_map]
    simp

theorem counterexample_produces_scalars (p : ℂ[X]) (hdeg : 6 ≤ p.natDegree)
    (hroots : RootsInClosedDisk p) {a : ℝ} (ha : 0 < a) (ha1 : a < 1)
    (hpa : p.eval (a:ℂ)=0) (henergy : criticalEnergy p (a:ℂ) ≤ (p.natDegree-1:ℕ)) :
    ∃ x s r : ℝ, ScalarConditions (p.natDegree-1) a x s r := by
  have hp0 : p ≠ 0 := by intro h; simp [h] at hdeg
  have hd0 : p.derivative ≠ 0 := derivative_ne_zero.mpr (by omega)
  have hsimple : p.derivative.eval (a:ℂ) ≠ 0 := by
    intro h
    exact not_lt_of_ge henergy (main_at_common_zero ((mem_roots hd0).mpr h))
  let q := criticalReciprocals p (a:ℂ)
  have hqcard : q.card=p.natDegree-1 := criticalReciprocals_card _ _
  have hqpos : 0 < q.card := by omega
  have hqrpos : (0:ℝ) < q.card := by exact_mod_cast hqpos
  have hq0 : ∀ v ∈ q, v ≠ 0 := criticalReciprocals_ne_zero p _ hsimple
  have hqsum : (q.map fun v => ‖v‖^2).sum ≤ (q.card:ℝ) := by
    rw [hqcard]
    exact reciprocal_sum_le_of_energy_le p _ hsimple henergy
  obtain ⟨f,hf⟩ := exists_fin_family q
  have hsum (g : ℂ → ℝ) : (q.map g).sum=∑ i, g (f i) := by
    calc
      (q.map g).sum=((Finset.univ.val.map f).map g).sum := congrArg (fun z => (z.map g).sum) hf.symm
      _ = _ := by rw [Multiset.map_map]; rfl
  have hprod (g : ℂ → ℂ) : (q.map g).prod=∏ i, g (f i) := by
    calc
      (q.map g).prod=((Finset.univ.val.map f).map g).prod := congrArg (fun z => (z.map g).prod) hf.symm
      _ = _ := by rw [Multiset.map_map]; rfl
  have hs1 : secondMoment f ≤ 1 := by
    unfold secondMoment
    simp_rw [Complex.normSq_eq_norm_sq]
    rw [div_le_one hqrpos]
    simpa only [hsum (fun v => ‖v‖^2)] using hqsum
  have hxs : meanRe f^2 ≤ secondMoment f := by
    have hh := mean_sq_le_secondMoment hqpos f
    nlinarith [sq_nonneg (meanIm f)]
  have hx1 : meanRe f ≤ 1 := by nlinarith [sq_nonneg (meanRe f-1)]
  have hx : (q.map Complex.re).sum=(q.card:ℝ)*meanRe f := by
    rw [hsum]
    unfold meanRe
    field_simp
  have hs : (q.map fun v => ‖v‖^2).sum=(q.card:ℝ)*secondMoment f := by
    rw [hsum]
    unfold secondMoment
    simp_rw [Complex.normSq_eq_norm_sq]
    field_simp
  obtain ⟨z,hzcard,hzroots,hpz⟩ := Sendov.exists_root_multiset (by omega : 1 ≤ p.natDegree)
    rfl hroots hpa
  have hpq := criticalReciprocals_factorization p (a:ℂ)
  have hc0 := leadingCoeff_ne_zero.mpr hp0
  have ha0 : (a:ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have ha2 : (a:ℂ)^2 ≠ 1 := by exact_mod_cast (show a^2 ≠ 1 by nlinarith)
  have hpol := Sendov.polar_identity hc0 ha0 ha2 hzcard hqcard hq0 hpa hpz hpq
  have hden := Sendov.prod_sub_mul_prod hc0 hq0 hpz hpq
  have hstar := Sendov.one_le_integral_prod_norm (by omega : 2 ≤ p.natDegree)
    (by rw [abs_of_pos ha]; exact ha1.le) hzroots hpol hden
  have hraw := exact_polar_inequality hqpos hx hs hstar
  have hqprod : ‖q.prod‖ ≤ 1 := by
    have h := norm_prod_le_moment Finset.univ (by simpa using hqpos) f (by norm_num : (0:ℝ)≤1)
      (by simpa only [Finset.card_univ,Fintype.card_fin,mul_one,hsum (fun v => ‖v‖^2)] using hqsum)
    have heq : q.prod=∏ i, f i := by simpa using hprod id
    simpa only [Real.one_rpow,heq] using h
  have hzprod : ‖z.prod‖ ≤ 1 := by
    rw [Sendov.norm_multiset_prod]
    have h := Sendov.prod_map_le_of_le (s := z) (f := id) (g := fun _ => (1:ℂ))
      (fun w hw => by simpa using hzroots w hw)
    simpa using h
  have horig := Sendov.first_origin_identity hc0 ha0 hzcard hq0 hpa hpz hpq
  have horigin : ‖(q.card+1:ℕ)*(∫ t in (0:ℝ)..1, originProduct f a t)‖ ≤ 1 := by
    have hn : q.card+1=p.natDegree := by omega
    rw [hn]
    have hfun : (fun t : ℝ => (q.map (fun v => 1-(a:ℂ)*(t:ℂ)*v)).prod) = originProduct f a := by
      funext t
      exact hprod _
    rw [hfun] at horig
    rw [horig,norm_mul,norm_mul,norm_pow,norm_neg,norm_one,one_pow,one_mul]
    nlinarith [norm_nonneg q.prod,norm_nonneg z.prod]
  have hw : ScalarConditions q.card a (meanRe f) (secondMoment f) ‖meanComplex f‖ :=
    ⟨by omega,ha,ha1,hx1,hxs,hs1,norm_nonneg _,norm_meanComplex_le_one hqpos f hs1,hraw,
      centered_scalar_inequality (by omega) f hs1 ha.le ha1 horigin,
      direct_scalar_inequality (by omega) f hs1 ha.le ha1 horigin⟩
  exact ⟨meanRe f,secondMoment f,‖meanComplex f‖,by simpa only [hqcard] using hw⟩

theorem interior_of_scalar_exclusion (p : ℂ[X]) (hdeg : 6 ≤ p.natDegree)
    (hroots : RootsInClosedDisk p) {a : ℝ} (ha : 0 < a) (ha1 : a < 1) (hpa : p.eval (a:ℂ)=0)
    (hexclude : ∀ x s r : ℝ, ¬ScalarConditions (p.natDegree-1) a x s r) :
    (p.natDegree-1:ℕ) < criticalEnergy p (a:ℂ) := by
  by_contra h
  obtain ⟨x,s,r,hw⟩ := counterexample_produces_scalars p hdeg hroots ha ha1 hpa (le_of_not_gt h)
  exact hexclude x s r hw

end QuadraticTangZhang
