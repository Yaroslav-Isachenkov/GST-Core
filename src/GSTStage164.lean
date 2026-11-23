import GSTStage163

open MeasureTheory Set Filter
open scoped Topology
open GSTStage31 GSTStage34 GSTStage36 GSTStage37

namespace GSTStage164

theorem fixed_candidate_sufficiency_and_uniqueness
    (x : StateData)
    (ha : x.a = 1 / 10) (hc : x.c = 1)
    (heta : x.eta = 1 / 20) (hrho : x.rho = 1 / 20)
    (hq : x.q = 1) (hU : x.U = 1) (htarget : x.target = 1)
    (hphi : x.phiInitial = 1 / 2)
    (homega : x.omegaInitial = 1 / 5)
    (hclip : GSTStage44.Clipping x (1 / 10)) :
    (∀ t : ℝ, 0 ≤ t → S x t ≤ 0) ∧
    (∀ u : ℝ → ℝ,
      AEMeasurable u (volume.restrict (Ioi (0 : ℝ))) →
      (∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)),
        0 ≤ u t ∧ u t ≤ x.U) →
      IntegrableOn (discountedCost x (1 / 10) u) (Ioi (0 : ℝ)) ∧
      IntegrableOn (gap x (1 / 10) u) (Ioi (0 : ℝ)) ∧
      ((∫ t in Ioi (0 : ℝ), gap x (1 / 10) u t) ≤
        objective x (1 / 10) x.u - objective x (1 / 10) u) ∧
      (objective x (1 / 10) u ≤ objective x (1 / 10) x.u) ∧
      (objective x (1 / 10) u = objective x (1 / 10) x.u →
        u =ᵐ[volume.restrict (Ioi (0 : ℝ))] x.u) ∧
      (¬ (u =ᵐ[volume.restrict (Ioi (0 : ℝ))] x.u) →
        objective x (1 / 10) u < objective x (1 / 10) x.u)) := by
  have hS := GSTStage163.fixed_candidate_S_nonpos
    x ha hc heta hrho hq hU htarget hphi homega hclip
  have hqPos : 0 < x.q := by
    rw [hq]
    norm_num
  have hUPos : 0 < x.U := by
    rw [hU]
    norm_num
  have hi : 0 < x.phiInitial := by
    rw [hphi]
    norm_num
  refine ⟨hS, ?_⟩
  exact GSTStage42.theorem2_sufficiency_and_uniqueness
    x (1 / 10) hqPos (by norm_num) hUPos hi hS hclip

end GSTStage164

#print axioms GSTStage164.fixed_candidate_sufficiency_and_uniqueness
