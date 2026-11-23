import GSTStage42
import GSTStage65

open MeasureTheory Set Filter
open scoped Topology
open GSTStage31

namespace GSTStage66

theorem candidate_sufficiency_and_uniqueness
    (x : StateData) (r : ℝ)
    (hr : 0 < r) (hU : 0 < x.U)
    (hi : 0 < x.phiInitial)
    (ha : 0 < x.a) (hq : 0 < x.q)
    (ho : 0 < x.omegaInitial)
    (hthreshold :
      x.omegaInitial < x.rho * x.target / (x.rho + x.a))
    (hdiscount : x.eta * x.U ≤ x.rho)
    (hrThreshold :
      x.a * x.q * x.target ^ 2 /
        (4 * x.U ^ 2 * (x.rho + x.a)) < r)
    (hclip : GSTStage44.Clipping x r) :
    (∀ t : ℝ, 0 ≤ t → S x t ≤ 0) ∧
    (∀ u : ℝ → ℝ,
      AEMeasurable u (volume.restrict (Ioi (0 : ℝ))) →
      (∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)), 0 ≤ u t ∧ u t ≤ x.U) →
      IntegrableOn (GSTStage36.discountedCost x r u) (Ioi (0 : ℝ)) ∧
      IntegrableOn (GSTStage34.gap x r u) (Ioi (0 : ℝ)) ∧
      ((∫ t in Ioi (0 : ℝ), GSTStage34.gap x r u t) ≤
        GSTStage37.objective x r x.u - GSTStage37.objective x r u) ∧
      (GSTStage37.objective x r u ≤ GSTStage37.objective x r x.u) ∧
      (GSTStage37.objective x r u = GSTStage37.objective x r x.u →
        u =ᵐ[volume.restrict (Ioi (0 : ℝ))] x.u) ∧
      (¬ (u =ᵐ[volume.restrict (Ioi (0 : ℝ))] x.u) →
        GSTStage37.objective x r u < GSTStage37.objective x r x.u)) := by
  have hS : ∀ t : ℝ, 0 ≤ t → S x t ≤ 0 :=
    GSTStage65.candidate_S_nonpos
      x r hr hU hi ha hq ho hthreshold hdiscount hrThreshold hclip
  exact ⟨hS,
    GSTStage42.theorem2_sufficiency_and_uniqueness
      x r hq hr hU hi hS hclip⟩

#print axioms candidate_sufficiency_and_uniqueness
#check candidate_sufficiency_and_uniqueness

end GSTStage66
