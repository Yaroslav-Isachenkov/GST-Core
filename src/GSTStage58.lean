import GSTStage57
import Mathlib.Analysis.Calculus.LocalExtr.Basic

open MeasureTheory Set Filter
open scoped Topology
open GSTStage31 GSTStage57

namespace GSTStage58

theorem s_rate_zero_at_local_maximum
    (x : StateData) (r t : ℝ)
    (hclip : GSTStage44.Clipping x r)
    (ht : 0 < t)
    (hlocal : ∀ᶠ s in 𝓝 t, S x s ≤ S x t) :
    sRate x t = 0 := by
  have hm : IsLocalMax (S x) t := hlocal
  exact hm.hasDerivAt_eq_zero
    (GSTStage57.s_hasDerivAt x r hclip t ht)

theorem no_local_maximum_at_zero_control
    (x : StateData) (r t : ℝ)
    (ha : 0 < x.a) (hq : 0 < x.q)
    (ho : 0 < x.omegaInitial)
    (hclip : GSTStage44.Clipping x r)
    (ht : 0 < t) (hu : x.u t = 0)
    (hlocal : ∀ᶠ s in 𝓝 t, S x s ≤ S x t) :
    False := by
  have hzero := s_rate_zero_at_local_maximum x r t hclip ht hlocal
  have hnegative := GSTStage57.s_rate_negative_of_control_zero
    x ha hq ho t ht.le hu
  rw [hzero] at hnegative
  exact (lt_irrefl (0 : ℝ)) hnegative

theorem control_positive_at_local_maximum
    (x : StateData) (r t : ℝ)
    (ha : 0 < x.a) (hq : 0 < x.q)
    (ho : 0 < x.omegaInitial)
    (hclip : GSTStage44.Clipping x r)
    (ht : 0 < t)
    (hlocal : ∀ᶠ s in 𝓝 t, S x s ≤ S x t) :
    0 < x.u t := by
  by_contra hn
  have hu : x.u t = 0 :=
    le_antisymm (le_of_not_gt hn) (x.hu t ht.le).1
  exact no_local_maximum_at_zero_control
    x r t ha hq ho hclip ht hu hlocal

-- A positive value of S produces a stationary positive local maximum
-- with strictly positive control.
theorem candidate_positive_stationary_maximum
    (x : StateData) (r : ℝ)
    (hr : 0 < r) (hi : 0 < x.phiInitial)
    (ha : 0 < x.a) (hq : 0 < x.q)
    (ho : 0 < x.omegaInitial)
    (hthreshold :
      x.omegaInitial < x.rho * x.target / (x.rho + x.a))
    (hclip : GSTStage44.Clipping x r)
    (s : ℝ) (hs : 0 ≤ s) (hpositive : 0 < S x s) :
    ∃ t : ℝ, 0 < t ∧ 0 < S x t ∧
      sRate x t = 0 ∧ 0 < x.u t ∧
      (∀ᶠ v in 𝓝 t, S x v ≤ S x t) := by
  obtain ⟨T, t, _hsT, ht, _htT, hpos, _hmax, hlocal⟩ :=
    GSTStage55.candidate_s_positive_interior_maximum
      x r hr hi ha hq ho hthreshold hclip s hs hpositive
  exact ⟨t, ht, hpos,
    s_rate_zero_at_local_maximum x r t hclip ht hlocal,
    control_positive_at_local_maximum x r t ha hq ho hclip ht hlocal,
    hlocal⟩

#print axioms s_rate_zero_at_local_maximum
#print axioms no_local_maximum_at_zero_control
#print axioms control_positive_at_local_maximum
#print axioms candidate_positive_stationary_maximum

end GSTStage58
