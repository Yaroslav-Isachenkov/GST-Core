import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open MeasureTheory Set Filter
open scoped Topology

namespace GSTStage09

-- Constant functions are absolutely continuous.
theorem constant_ac (a b value : ℝ) :
    AbsolutelyContinuousOnInterval (fun _ : ℝ => value) a b := by
  rw [absolutelyContinuousOnInterval_iff]
  intro epsilon hepsilon
  refine ⟨1, zero_lt_one, ?_⟩
  intro E hE hlength
  simpa using hepsilon

-- A distance bound on the image of an AC trajectory is enough
-- to preserve absolute continuity under composition.
theorem composition_ac
    (f g : ℝ → ℝ) (a b L : ℝ)
    (hf : AbsolutelyContinuousOnInterval f a b)
    (hbound : ∀ s ∈ uIcc a b, ∀ t ∈ uIcc a b,
      dist (g (f s)) (g (f t)) ≤ L * dist (f s) (f t)) :
    AbsolutelyContinuousOnInterval (fun t => g (f t)) a b := by
  unfold AbsolutelyContinuousOnInterval at hf ⊢
  apply squeeze_zero' ?_ ?_
    (by simpa using hf.const_mul L)
  · exact Filter.Eventually.of_forall
      (fun _ => Finset.sum_nonneg (fun _ _ => dist_nonneg))
  · rw [eventually_inf_principal]
    filter_upwards with E hE
    simp only [AbsolutelyContinuousOnInterval.disjWithin, mem_setOf_eq] at hE
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    exact hbound
      (E.2 i).1 (hE.left i hi).left
      (E.2 i).2 (hE.left i hi).right

-- The inverse-distance estimate remains an explicit premise here.
theorem ratio_ac
    (phi psi : ℝ → ℝ) (a b Linv : ℝ)
    (hphi : AbsolutelyContinuousOnInterval phi a b)
    (hpsi : AbsolutelyContinuousOnInterval psi a b)
    (hinv : ∀ s ∈ uIcc a b, ∀ t ∈ uIcc a b,
      dist ((psi s)⁻¹) ((psi t)⁻¹) ≤
        Linv * dist (psi s) (psi t)) :
    AbsolutelyContinuousOnInterval
      (fun t => phi t / psi t) a b := by
  have hi : AbsolutelyContinuousOnInterval
      (fun t => (psi t)⁻¹) a b :=
    composition_ac psi (fun x => x⁻¹) a b Linv hpsi hinv
  simpa only [div_eq_mul_inv] using hphi.fun_mul hi

-- The logarithm-distance estimate remains an explicit premise here.
theorem entropy_ac
    (xi : ℝ → ℝ) (a b Llog : ℝ)
    (hxi : AbsolutelyContinuousOnInterval xi a b)
    (hlog : ∀ s ∈ uIcc a b, ∀ t ∈ uIcc a b,
      dist (Real.log (xi s)) (Real.log (xi t)) ≤
        Llog * dist (xi s) (xi t)) :
    AbsolutelyContinuousOnInterval
      (fun t => xi t - 1 - Real.log (xi t)) a b := by
  have hl : AbsolutelyContinuousOnInterval
      (fun t => Real.log (xi t)) a b :=
    composition_ac xi Real.log a b Llog hxi hlog
  exact (hxi.fun_sub (constant_ac a b 1)).fun_sub hl

-- Assembly of the actual weighted entropy expression.
-- AC of the discount and the component trajectories, together
-- with the two distance estimates, are explicit assumptions.
theorem weighted_entropy_ac
    (phi psi d : ℝ → ℝ) (a b rho Linv Llog : ℝ)
    (hphi : AbsolutelyContinuousOnInterval phi a b)
    (hpsi : AbsolutelyContinuousOnInterval psi a b)
    (hd : AbsolutelyContinuousOnInterval d a b)
    (hdiscount : AbsolutelyContinuousOnInterval
      (fun t => Real.exp (-rho * t)) a b)
    (hinv : ∀ s ∈ uIcc a b, ∀ t ∈ uIcc a b,
      dist ((psi s)⁻¹) ((psi t)⁻¹) ≤
        Linv * dist (psi s) (psi t))
    (hlog : ∀ s ∈ uIcc a b, ∀ t ∈ uIcc a b,
      dist (Real.log (phi s / psi s))
           (Real.log (phi t / psi t)) ≤
        Llog * dist (phi s / psi s) (phi t / psi t)) :
    AbsolutelyContinuousOnInterval
      (fun t =>
        Real.exp (-rho * t) * psi t * d t *
          (phi t / psi t - 1 - Real.log (phi t / psi t)))
      a b := by
  have hratio := ratio_ac phi psi a b Linv hphi hpsi hinv
  have hentropy :=
    entropy_ac (fun t => phi t / psi t) a b Llog hratio hlog
  exact ((hdiscount.fun_mul hpsi).fun_mul hd).fun_mul hentropy

#print axioms constant_ac
#print axioms composition_ac
#print axioms ratio_ac
#print axioms entropy_ac
#print axioms weighted_entropy_ac

end GSTStage09
