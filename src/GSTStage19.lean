import GSTStage08
import GSTStage12
import Mathlib.Tactic.Ring

open MeasureTheory Set Filter
open scoped Topology
open GSTStage11 GSTStage12

namespace GSTStage19

noncomputable def weight
    (v : ℝ → ℝ) (eta rho t : ℝ) : ℝ :=
  Real.exp (-rho * t - cumulative v eta t)

theorem weight_positive (v : ℝ → ℝ) (eta rho t : ℝ) :
    0 < weight v eta rho t := by
  exact Real.exp_pos _

theorem weight_ac
    (v : ℝ → ℝ) (eta rho T : ℝ)
    (hv : IntervalIntegrable v volume 0 T) :
    AbsolutelyContinuousOnInterval (weight v eta rho) 0 T := by
  have hi : AbsolutelyContinuousOnInterval
      (fun t : ℝ => t) 0 T := by
    have hc : IntervalIntegrable
        (fun _ : ℝ => (1 : ℝ)) volume 0 T :=
      intervalIntegrable_const
    simpa using
      hc.absolutelyContinuousOnInterval_intervalIntegral
        (c := 0) (left_mem_uIcc)
  exact exp_ac
    (fun t => -rho * t - cumulative v eta t) 0 T
    ((hi.const_mul (-rho)).fun_sub (cumulative_ac v eta T hv))

theorem weighted_d_derivative_ae
    (v d S : ℝ → ℝ) (eta rho c T : ℝ)
    (hv : IntervalIntegrable v volume 0 T)
    (hd : ∀ᵐ t : ℝ, t ∈ uIcc (0 : ℝ) T →
      HasDerivAt d ((rho + eta * v t) * d t + c * S t) t) :
    ∀ᵐ t : ℝ, t ∈ uIcc (0 : ℝ) T →
      HasDerivAt (fun s => weight v eta rho s * d s)
        (weight v eta rho t * c * S t) t := by
  filter_upwards [hv.ae_hasDerivAt_integral, hd] with t hvi hdi
  intro ht
  have hA : HasDerivAt (cumulative v eta) (eta * v t) t := by
    simpa only [cumulative] using
      (hvi ht 0 (left_mem_uIcc)).const_mul eta
  have hlinear : HasDerivAt (fun s : ℝ => -rho * s) (-rho) t := by
    simpa using (hasDerivAt_id t).const_mul (-rho)
  have hproduct := (hlinear.sub hA).exp.mul (hdi ht)
  convert hproduct using 1
  dsimp [weight]
  ring

theorem weighted_d_terminal_comparison
    (v d S : ℝ → ℝ) (eta rho c T t : ℝ)
    (hT : 0 ≤ T) (ht : t ∈ Icc (0 : ℝ) T)
    (hc : 0 ≤ c)
    (hv : IntervalIntegrable v volume 0 T)
    (hdAC : AbsolutelyContinuousOnInterval d 0 T)
    (hScont : ContinuousOn S (uIcc (0 : ℝ) T))
    (hdODE : ∀ᵐ x : ℝ, x ∈ uIcc (0 : ℝ) T →
      HasDerivAt d ((rho + eta * v x) * d x + c * S x) x)
    (hS : ∀ x ∈ Icc (0 : ℝ) T, S x ≤ 0) :
    weight v eta rho T * d T ≤ weight v eta rho t * d t := by
  let H : ℝ → ℝ := fun x => weight v eta rho x * d x
  let R : ℝ → ℝ := fun x => weight v eta rho x * c * S x
  have hw := weight_ac v eta rho T hv
  have hH : AbsolutelyContinuousOnInterval H 0 T :=
    hw.fun_mul hdAC
  have hR : ContinuousOn R (uIcc (0 : ℝ) T) :=
    (hw.continuousOn.mul continuousOn_const).mul hScont
  have hsub : uIcc t T ⊆ uIcc (0 : ℝ) T := by
    rw [uIcc_of_le ht.2, uIcc_of_le hT]
    exact Icc_subset_Icc ht.1 le_rfl
  have hderiv := weighted_d_derivative_ae v d S eta rho c T hv hdODE
  have hlocal : ∀ᵐ x : ℝ, x ∈ uIcc t T →
      HasDerivAt H (R x) x := by
    filter_upwards [hderiv] with x hx hmem
    exact hx (hsub hmem)
  have hFTC := GSTStage08.ac_integral_identity
    H R t T (hH.mono hsub) hlocal
  have hRint : IntervalIntegrable R volume t T :=
    (hR.mono hsub).intervalIntegrable
  have hzero : IntervalIntegrable
      (fun _ : ℝ => (0 : ℝ)) volume t T :=
    intervalIntegrable_const
  have hsign : ∀ x ∈ Icc t T, R x ≤ 0 := by
    intro x hx
    exact mul_nonpos_of_nonneg_of_nonpos
      (mul_nonneg (le_of_lt (weight_positive v eta rho x)) hc)
      (hS x ⟨le_trans ht.1 hx.1, hx.2⟩)
  have hint : (∫ x in t..T, R x) ≤ 0 := by
    simpa using intervalIntegral.integral_mono_on
      ht.2 hRint hzero hsign
  rw [hFTC] at hint
  exact sub_nonpos.mp hint

-- The weighted terminal limit is an explicit hypothesis.
-- No unweighted condition d(t) -> 0 is assumed.
theorem d_nonneg_from_weighted_limit
    (v d S : ℝ → ℝ) (eta rho c : ℝ)
    (hc : 0 ≤ c)
    (hv : ∀ T : ℝ, 0 ≤ T → IntervalIntegrable v volume 0 T)
    (hdAC : ∀ T : ℝ, 0 ≤ T →
      AbsolutelyContinuousOnInterval d 0 T)
    (hScont : ∀ T : ℝ, 0 ≤ T →
      ContinuousOn S (uIcc (0 : ℝ) T))
    (hdODE : ∀ᵐ t : ℝ, 0 ≤ t →
      HasDerivAt d ((rho + eta * v t) * d t + c * S t) t)
    (hS : ∀ t : ℝ, 0 ≤ t → S t ≤ 0)
    (htail : Tendsto
      (fun t => weight v eta rho t * d t) atTop (𝓝 0)) :
    ∀ t : ℝ, 0 ≤ t → 0 ≤ d t := by
  intro t ht
  have hevent : ∀ᶠ T : ℝ in atTop,
      weight v eta rho T * d T ≤ weight v eta rho t * d t := by
    filter_upwards [eventually_ge_atTop t] with T htT
    have hT : 0 ≤ T := le_trans ht htT
    have hdlocal : ∀ᵐ x : ℝ, x ∈ uIcc (0 : ℝ) T →
        HasDerivAt d ((rho + eta * v x) * d x + c * S x) x := by
      filter_upwards [hdODE] with x hx hmem
      rw [uIcc_of_le hT] at hmem
      exact hx hmem.1
    exact weighted_d_terminal_comparison
      v d S eta rho c T t hT ⟨ht, htT⟩ hc
      (hv T hT) (hdAC T hT) (hScont T hT)
      hdlocal (fun x hx => hS x hx.1)
  have hnonneg : 0 ≤ weight v eta rho t * d t :=
    le_of_tendsto htail hevent
  by_contra hn
  have hnegative : weight v eta rho t * d t < 0 :=
    mul_neg_of_pos_of_neg (weight_positive v eta rho t) (lt_of_not_ge hn)
  exact (not_lt_of_ge hnonneg) hnegative

#print axioms weight_positive
#print axioms weight_ac
#print axioms weighted_d_derivative_ae
#print axioms weighted_d_terminal_comparison
#print axioms d_nonneg_from_weighted_limit

end GSTStage19
