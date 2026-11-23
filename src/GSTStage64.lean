import GSTStage63
import Mathlib.Analysis.Calculus.DerivativeTest
open MeasureTheory Set Filter
open scoped Topology
open GSTStage31 GSTStage57 GSTStage62

namespace GSTStage64

theorem no_local_max_of_positive_second_derivative
    (f g : ℝ → ℝ) (t v : ℝ)
    (hf : ∀ᶠ s in 𝓝 t, HasDerivAt f (g s) s)
    (hg : HasDerivAt g v t)
    (hv : 0 < v)
    (hmax : IsLocalMax f t) :
    False := by
  have hft : HasDerivAt f (g t) t := hf.self_of_nhds
  have hz : g t = 0 := hmax.hasDerivAt_eq_zero hft
  have heq : deriv f =ᶠ[𝓝 t] g := by
    filter_upwards [hf] with s hs
    exact hs.deriv
  have hsecond : HasDerivAt (deriv f) v t :=
    hg.congr_of_eventuallyEq heq
  have hpositive : 0 < deriv (deriv f) t := by
    rw [hsecond.deriv]
    exact hv
  have hfirst : deriv f t = 0 := hft.deriv.trans hz
  have hmin : IsLocalMin f t :=
    isLocalMin_of_deriv_deriv_pos hpositive hfirst hft.continuousAt
  have hupper : ∀ᶠ s in 𝓝 t, f s ≤ f t := hmax
  have hlower : ∀ᶠ s in 𝓝 t, f t ≤ f s := hmin
  have hconstant : f =ᶠ[𝓝 t] (fun _ => f t) := by
    filter_upwards [hupper, hlower] with s hs₁ hs₂
    exact le_antisymm hs₁ hs₂
  have hzero : deriv (deriv f) t = 0 := by
    have h := hconstant.deriv.deriv_eq
    simpa using h
  exact (ne_of_gt hpositive) hzero

theorem candidate_no_positive_local_maximum_interior
    (x : StateData) (r t : ℝ)
    (hr : 0 < r) (hi : 0 < x.phiInitial)
    (ha : 0 < x.a) (hq : 0 < x.q)
    (hoTarget : x.omegaInitial < x.target)
    (hdiscount : x.eta * x.U ≤ x.rho)
    (hclip : GSTStage44.Clipping x r)
    (ht : 0 < t) (hu0 : 0 < x.u t) (huU : x.u t < x.U)
    (hS : 0 < S x t)
    (hlocal : ∀ᶠ s in 𝓝 t, S x s ≤ S x t) :
    False := by
  have hstationary :=
    GSTStage58.s_rate_zero_at_local_maximum x r t hclip ht hlocal
  obtain ⟨hsecond, hpositive⟩ :=
    GSTStage63.candidate_sRate_derivative_positive_interior
      x r t hr hi ha hq hoTarget hdiscount hclip ht hu0 huU hS hstationary
  have hfirst : ∀ᶠ s in 𝓝 t, HasDerivAt (S x) (sRate x s) s := by
    filter_upwards [Ioi_mem_nhds ht] with s hs
    exact GSTStage57.s_hasDerivAt x r hclip s (show 0 < s from hs)
  exact no_local_max_of_positive_second_derivative
    (S x) (sRate x) t (secondRate x r t)
    hfirst hsecond hpositive hlocal

#print axioms no_local_max_of_positive_second_derivative
#print axioms candidate_no_positive_local_maximum_interior
end GSTStage64
