import GSTStage47
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.Calculus.Deriv.Slope

open MeasureTheory Set Filter
open scoped Topology
open GSTStage11 GSTStage31

namespace GSTStage48

theorem right_neighborhood_below
    (f : ℝ → ℝ) (v s B : ℝ)
    (hf : HasDerivAt f v s)
    (hs : f s ≤ B)
    (hboundary : f s = B → v < 0) :
    ∀ᶠ t in 𝓝[>] s, f t ≤ B := by
  rcases lt_or_eq_of_le hs with hlt | heq
  · have hnear : ∀ᶠ t in 𝓝 s, f t < B :=
      hf.continuousAt.eventually (Iio_mem_nhds hlt)
    filter_upwards [hnear.filter_mono nhdsWithin_le_nhds] with t ht
    exact ht.le
  · have hv : v < 0 := hboundary heq
    have hslope : Tendsto (slope f s) (𝓝[>] s) (𝓝 v) :=
      (hasDerivAt_iff_tendsto_slope_left_right.mp hf).2
    have hnear : ∀ᶠ t in 𝓝[>] s, slope f s t < 0 :=
      hslope.eventually (Iio_mem_nhds hv)
    filter_upwards [hnear, self_mem_nhdsWithin] with t ht hst
    have hpos : 0 < t - s := sub_pos.mpr (show s < t from hst)
    have hdiv : (f t - f s) / (t - s) < 0 := by
      change (t - s)⁻¹ * (f t - f s) < 0 at ht
      simpa only [div_eq_mul_inv, mul_comm] using ht
    have hdiff := (div_lt_iff₀ hpos).mp hdiv
    linarith

theorem rectangle_invariant
    (f g F G : ℝ → ℝ) (a b A B : ℝ)
    (hf : ContinuousOn f (Icc a b))
    (hg : ContinuousOn g (Icc a b))
    (hfODE : ∀ t ∈ Ico a b, HasDerivAt f (F t) t)
    (hgODE : ∀ t ∈ Ico a b, HasDerivAt g (G t) t)
    (ha : f a ≤ A ∧ g a ≤ B)
    (hF : ∀ t ∈ Ico a b, f t = A → g t ≤ B → F t < 0)
    (hG : ∀ t ∈ Ico a b, f t ≤ A → g t = B → G t < 0) :
    ∀ t ∈ Icc a b, f t ≤ A ∧ g t ≤ B := by
  let K : Set ℝ := {t | f t ≤ A ∧ g t ≤ B}
  have hclosed : IsClosed (K ∩ Icc a b) := by
    have hfc : IsClosed {t | t ∈ Icc a b ∧ f t ≤ A} :=
      isClosed_Icc.isClosed_le hf continuousOn_const
    have hgc : IsClosed {t | t ∈ Icc a b ∧ g t ≤ B} :=
      isClosed_Icc.isClosed_le hg continuousOn_const
    have heq :
        K ∩ Icc a b =
          {t | t ∈ Icc a b ∧ f t ≤ A} ∩
          {t | t ∈ Icc a b ∧ g t ≤ B} := by
      ext t
      simp only [K, mem_inter_iff, mem_setOf_eq]
      tauto
    rw [heq]
    exact hfc.inter hgc
  have hstart : a ∈ K := ha
  have hright : ∀ t ∈ K ∩ Ico a b, K ∈ 𝓝[>] t := by
    intro t ht
    have hp : f t ≤ A ∧ g t ≤ B := ht.1
    have hpf := right_neighborhood_below
      f (F t) t A (hfODE t ht.2) hp.1
      (fun heq => hF t ht.2 heq hp.2)
    have hpg := right_neighborhood_below
      g (G t) t B (hgODE t ht.2) hp.2
      (fun heq => hG t ht.2 hp.1 heq)
    exact hpf.and hpg
  exact hclosed.Icc_subset_of_forall_mem_nhdsWithin hstart hright

theorem candidate_rectangle_invariant
    (x : StateData) (r s T M : ℝ)
    (hr : 0 < r) (hi : 0 < x.phiInitial)
    (ha : 0 < x.a) (hq : 0 < x.q)
    (hs : 0 < s) (hsT : s ≤ T)
    (hM : 0 < M) (hMtarget : M < x.target)
    (hclip : GSTStage44.Clipping x r)
    (hp : p x s ≤ 0) (ho : state x s ≤ M) :
    ∀ t ∈ Icc s T, p x t ≤ 0 ∧ state x t ≤ M := by
  have hT : 0 ≤ T := le_trans hs.le hsT
  have hpc : ContinuousOn (p x) (Icc s T) := by
    apply ((GSTStage28.p_solution (toCostateData x) T hT).1.continuousOn).mono
    intro t ht
    rw [uIcc_of_le hT]
    exact ⟨le_trans hs.le ht.1, ht.2⟩
  have hoc : ContinuousOn (state x) (Icc s T) := by
    apply (state_continuousOn x).mono
    intro t ht
    exact le_trans hs.le ht.1
  apply rectangle_invariant
    (p x) (state x)
    (fun t => (x.rho + x.a) * p x t +
      2 * x.q * (state x t - x.target))
    (fun t => -x.a * state x t +
      x.c * (resource x.u x.eta x.B x.phiInitial t * x.u t))
    s T 0 M hpc hoc ?_ ?_ ⟨hp, ho⟩ ?_ ?_
  · intro t ht
    exact GSTStage47.p_ode_at x t (lt_of_lt_of_le hs ht.1)
  · intro t ht
    exact GSTStage47.state_ode_at x r hclip t (lt_of_lt_of_le hs ht.1)
  · intro t _ht hpzero hom
    change (x.rho + x.a) * p x t +
      2 * x.q * (state x t - x.target) < 0
    rw [hpzero, mul_zero, zero_add]
    exact mul_neg_of_pos_of_neg (mul_pos (by norm_num) hq)
      (sub_neg.mpr (lt_of_le_of_lt hom hMtarget))
  · intro t ht hpnonpos homeq
    have ht0 : 0 ≤ t := le_trans hs.le ht.1
    have hu := GSTStage46.control_zero_of_p_nonpos
      x r hr hi hclip t ht0 hpnonpos
    change -x.a * state x t +
      x.c * (resource x.u x.eta x.B x.phiInitial t * x.u t) < 0
    rw [hu, homeq]
    nlinarith [mul_pos ha hM]

theorem candidate_rectangle_invariant_forever
    (x : StateData) (r s M : ℝ)
    (hr : 0 < r) (hi : 0 < x.phiInitial)
    (ha : 0 < x.a) (hq : 0 < x.q)
    (hs : 0 < s) (hM : 0 < M) (hMtarget : M < x.target)
    (hclip : GSTStage44.Clipping x r)
    (hp : p x s ≤ 0) (ho : state x s ≤ M) :
    ∀ t : ℝ, s ≤ t → p x t ≤ 0 ∧ state x t ≤ M := by
  intro t hst
  exact candidate_rectangle_invariant
    x r s t M hr hi ha hq hs hst hM hMtarget hclip hp ho
    t ⟨hst, le_rfl⟩

#print axioms right_neighborhood_below
#print axioms rectangle_invariant
#print axioms candidate_rectangle_invariant
#print axioms candidate_rectangle_invariant_forever

end GSTStage48
