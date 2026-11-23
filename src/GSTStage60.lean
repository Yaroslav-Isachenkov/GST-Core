import GSTStage59
open MeasureTheory Set Filter
open scoped Topology
open GSTStage11 GSTStage31

namespace GSTStage60

noncomputable def w (x : StateData) (t : ℝ) : ℝ :=
  resource x.u x.eta x.B x.phiInitial t * d x t

theorem resource_ode_at
    (x : StateData) (r : ℝ)
    (hclip : GSTStage44.Clipping x r)
    (t : ℝ) (ht : 0 < t) :
    HasDerivAt (resource x.u x.eta x.B x.phiInitial)
      (x.B - x.eta * x.u t *
        resource x.u x.eta x.B x.phiInitial t) t := by
  have hu : ∀ T : ℝ, 0 ≤ T →
      IntervalIntegrable x.u volume 0 T := by
    intro T hT
    exact GSTStage27.bounded_control_integrable
      x.u x.U T hT x.huMeas x.hu
  apply GSTStage47.hasDerivAt_of_local_ac_ae
    (resource x.u x.eta x.B x.phiInitial)
    (fun s => x.B - x.eta * x.u s *
      resource x.u x.eta x.B x.phiInitial s)
    ?_ ?_ ?_ t ht
  · intro T hT
    exact GSTStage12.resource_ac
      x.u x.eta x.B x.phiInitial T (hu T hT)
  · intro T hT
    exact GSTStage12.resource_ode_ae
      x.u x.eta x.B x.phiInitial T (hu T hT)
  · intro T hT
    have hres := GSTStage11.resource_continuousOn
      x.u x.eta x.B x.phiInitial T (hu T hT)
    have huc := GSTStage44.candidate_control_continuousOn
      x r T hT hclip
    exact continuousOn_const.sub
      ((continuousOn_const.mul huc).mul hres)

theorem d_ode_at
    (x : StateData) (r : ℝ)
    (hclip : GSTStage44.Clipping x r)
    (t : ℝ) (ht : 0 < t) :
    HasDerivAt (d x)
      ((x.rho + x.eta * x.u t) * d x t + x.c * S x t) t := by
  apply GSTStage47.hasDerivAt_of_local_ac_ae
    (d x)
    (fun s => (x.rho + x.eta * x.u s) * d x s + x.c * S x s)
    ?_ ?_ ?_ t ht
  · intro T hT
    exact (state_costates_verified x).1 T hT
  · intro T hT
    have hode : ∀ᵐ s : ℝ, 0 ≤ s →
        HasDerivAt (d x)
          ((x.rho + x.eta * x.u s) * d x s + x.c * S x s) s :=
      (state_costates_verified x).2.1
    filter_upwards [hode] with s hs
    intro hmem
    rw [uIcc_of_le hT] at hmem
    exact hs hmem.1
  · intro T hT
    have hd : ContinuousOn (d x) (uIcc (0 : ℝ) T) :=
      ((state_costates_verified x).1 T hT).continuousOn
    have hS : ContinuousOn (S x) (uIcc (0 : ℝ) T) :=
      GSTStage28.s_continuous (toCostateData x) T hT
    have huc := GSTStage44.candidate_control_continuousOn
      x r T hT hclip
    exact
      ((continuousOn_const.add (continuousOn_const.mul huc)).mul hd).add
        (continuousOn_const.mul hS)

theorem w_hasDerivAt
    (x : StateData) (r : ℝ)
    (hclip : GSTStage44.Clipping x r)
    (t : ℝ) (ht : 0 < t) :
    HasDerivAt (w x)
      (x.rho * w x t + x.B * d x t +
        x.c * resource x.u x.eta x.B x.phiInitial t * S x t) t := by
  have hres := resource_ode_at x r hclip t ht
  have hd := d_ode_at x r hclip t ht
  convert hres.mul hd using 1
  dsimp [w]
  ring

#print axioms resource_ode_at
#print axioms d_ode_at
#print axioms w_hasDerivAt
end GSTStage60
