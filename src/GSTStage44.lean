import GSTStage43
import Mathlib.Topology.Order.Lattice

open MeasureTheory Set Filter
open scoped Topology
open GSTStage11 GSTStage31

namespace GSTStage44

def Clipping (x : StateData) (r : ℝ) : Prop :=
  ∀ t : ℝ, 0 ≤ t →
    x.u t = max 0 (min x.U
      ((resource x.u x.eta x.B x.phiInitial t * d x t) / (2 * r)))

theorem candidate_control_continuousOn
    (x : StateData) (r T : ℝ) (hT : 0 ≤ T)
    (hclip : Clipping x r) :
    ContinuousOn x.u (uIcc (0 : ℝ) T) := by
  have hu := GSTStage27.bounded_control_integrable
    x.u x.U T hT x.huMeas x.hu
  have hres := resource_continuousOn
    x.u x.eta x.B x.phiInitial T hu
  have hd : ContinuousOn (d x) (uIcc (0 : ℝ) T) :=
    ((state_costates_verified x).1 T hT).continuousOn
  have hexpr : ContinuousOn
      (fun t => max 0 (min x.U
        ((resource x.u x.eta x.B x.phiInitial t * d x t) / (2 * r))))
      (uIcc (0 : ℝ) T) :=
    continuousOn_const.sup
      (continuousOn_const.inf ((hres.mul hd).div_const (2 * r)))
  apply hexpr.congr
  intro t ht
  have ht0 : 0 ≤ t := by
    rw [uIcc_of_le hT] at ht
    exact ht.1
  exact hclip t ht0

theorem negative_ud_continuousOn
    (x : StateData) (r T : ℝ) (hT : 0 ≤ T)
    (hclip : Clipping x r) :
    ContinuousOn (fun t => -(x.u t * d x t))
      (uIcc (0 : ℝ) T) := by
  exact ((candidate_control_continuousOn x r T hT hclip).mul
    (((state_costates_verified x).1 T hT).continuousOn)).neg

theorem discounted_z_terminal_comparison
    (x : StateData) (r T t : ℝ)
    (hr : 0 < r) (hi : 0 < x.phiInitial)
    (hT : 0 ≤ T) (ht : t ∈ Icc (0 : ℝ) T)
    (hclip : Clipping x r) :
    Real.exp (-x.rho * T) * z x T ≤
      Real.exp (-x.rho * t) * z x t := by
  have hz := GSTStage43.z_solution_rewritten x T hT
  have hode : ∀ᵐ s : ℝ, s ∈ uIcc (0 : ℝ) T →
      HasDerivAt (z x)
        ((x.rho + (0 : ℝ) * (0 : ℝ)) * z x s +
          (1 : ℝ) * (-(x.u s * d x s))) s := by
    filter_upwards [hz.2] with s hs
    intro hmem
    simpa only [zero_mul, add_zero, one_mul, sub_eq_add_neg]
      using hs hmem
  have hsign : ∀ s ∈ Icc (0 : ℝ) T,
      -(x.u s * d x s) ≤ 0 := by
    intro s hs
    exact neg_nonpos.mpr
      (GSTStage43.candidate_ud_nonneg x r hr hi hclip s hs.1)
  have h := GSTStage19.weighted_d_terminal_comparison
    (fun _ : ℝ => 0) (z x) (fun s => -(x.u s * d x s))
    0 x.rho 1 T t hT ht (by norm_num)
    (intervalIntegrable_const)
    hz.1
    (negative_ud_continuousOn x r T hT hclip)
    hode hsign
  simpa [GSTStage19.weight, cumulative] using h

theorem candidate_z_nonneg
    (x : StateData) (r : ℝ)
    (hr : 0 < r) (hi : 0 < x.phiInitial)
    (hclip : Clipping x r) :
    ∀ t : ℝ, 0 ≤ t → 0 ≤ z x t := by
  intro t ht
  have hevent : ∀ᶠ T : ℝ in atTop,
      Real.exp (-x.rho * T) * z x T ≤
        Real.exp (-x.rho * t) * z x t := by
    filter_upwards [eventually_ge_atTop t] with T htT
    exact discounted_z_terminal_comparison
      x r T t hr hi (le_trans ht htT) ⟨ht, htT⟩ hclip
  have hnonneg : 0 ≤ Real.exp (-x.rho * t) * z x t :=
    le_of_tendsto (GSTStage43.discounted_z_tendsto_zero x) hevent
  by_contra hn
  have hnegative : Real.exp (-x.rho * t) * z x t < 0 :=
    mul_neg_of_pos_of_neg (Real.exp_pos _) (lt_of_not_ge hn)
  exact (not_lt_of_ge hnonneg) hnegative

#print axioms candidate_control_continuousOn
#print axioms negative_ud_continuousOn
#print axioms discounted_z_terminal_comparison
#print axioms candidate_z_nonneg

end GSTStage44
