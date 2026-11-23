import GSTStage148
import Mathlib.Analysis.Calculus.Deriv.MeanValue

open Set

namespace GSTStage149

theorem linear_ode_unique_on_interval
    (f g b : ℝ → ℝ) (c a T : ℝ)
    (hfCont : ContinuousOn f (Icc a T))
    (hgCont : ContinuousOn g (Icc a T))
    (hf : ∀ s ∈ Ioo a T, HasDerivAt f (c * f s + b s) s)
    (hg : ∀ s ∈ Ioo a T, HasDerivAt g (c * g s + b s) s)
    (hinit : f a = g a) :
    EqOn f g (Icc a T) := by
  let H : ℝ → ℝ := fun s => Real.exp (-c * s) * (f s - g s)
  have hHCont : ContinuousOn H (Icc a T) :=
    (Real.continuous_exp.comp
      (continuous_const.mul continuous_id)).continuousOn.mul
        (hfCont.sub hgCont)
  have hHD : ∀ s ∈ Ioo a T, HasDerivAt H 0 s := by
    intro s hs
    have he := ((hasDerivAt_id s).const_mul (-c)).exp
    have hd := he.mul ((hf s hs).sub (hg s hs))
    convert hd using 1
    all_goals simp only [Pi.sub_apply, id_eq]
    all_goals ring
  have hHa : H a = 0 := by
    simp only [H, hinit, sub_self, mul_zero]
  intro x hx
  rcases eq_or_lt_of_le hx.1 with hax | hax
  · subst x
    exact hinit
  · have hcont : ContinuousOn H (Icc a x) :=
      hHCont.mono (Icc_subset_Icc le_rfl hx.2)
    have hderiv : ∀ s ∈ Ioo a x, HasDerivAt H 0 s := by
      intro s hs
      exact hHD s ⟨hs.1, lt_of_lt_of_le hs.2 hx.2⟩
    have hmvt : ∃ s ∈ Ioo a x,
        (0 : ℝ) = (H x - H a) / (x - a) := by
      apply exists_hasDerivAt_eq_slope <;> assumption
    obtain ⟨s, _hs, he⟩ := hmvt
    have hden : x - a ≠ 0 := ne_of_gt (sub_pos.mpr hax)
    have hnum := (div_eq_iff hden).mp he.symm
    have hHx : H x = 0 := by
      rw [hHa] at hnum
      linarith
    have hprod : Real.exp (-c * x) * (f x - g x) = 0 := hHx
    have hsub : f x - g x = 0 :=
      (mul_eq_zero.mp hprod).resolve_left (ne_of_gt (Real.exp_pos _))
    exact sub_eq_zero.mp hsub

end GSTStage149

#print axioms GSTStage149.linear_ode_unique_on_interval
