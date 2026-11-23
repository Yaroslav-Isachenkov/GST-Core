import GSTStage181

open MeasureTheory Set Filter
open scoped Topology
open GSTStage34 GSTStage36 GSTStage37 GSTStage115 GSTStage180

namespace GSTStage182

theorem source_lift_objective_identity
    (p : CoreParameters) (n : ℝ) (hn : 0 ≤ n)
    (u : ℝ → ℝ) (hi : 0 < p.phiInitial)
    (hmeas : Measurable u)
    (hbound : ∀ t : ℝ, 0 ≤ t → 0 ≤ u t ∧ u t ≤ p.U) :
    let v := liftedControl u p.eta (p.b * n) p.phiInitial
    IntegrableOn
      (fun t => Real.exp (-p.rho * t) * ((u t)^2 - (v t)^2))
      (Ioi (0 : ℝ)) ∧
    objective (p.toStateData n hn) p.r v -
        objective (p.toStateData 0 le_rfl) p.r u =
      p.r * ∫ t in Ioi (0 : ℝ),
        Real.exp (-p.rho * t) * ((u t)^2 - (v t)^2) := by
  let v := liftedControl u p.eta (p.b * n) p.phiInitial
  obtain ⟨hvMeas, hvBound, htraj⟩ :=
    GSTStage181.source_lift_canonical_trajectories
      u p.eta (p.b * n) p.phiInitial p.a p.c p.omegaInitial p.U
      hi (mul_nonneg p.hb.le hn) hmeas hbound
  have hSq : ∀ f : ℝ → ℝ, Measurable f →
      (∀ t : ℝ, 0 ≤ t → 0 ≤ f t ∧ f t ≤ p.U) →
      IntegrableOn (fun t => Real.exp (-p.rho * t) * (f t)^2)
        (Ioi (0 : ℝ)) := by
    intro f hf hb
    apply discounted_square_integrable f p.rho p.hrho hf
    refine ⟨p.U, p.hU.le, ?_⟩
    intro t ht
    rw [abs_of_nonneg (hb t ht).1]
    have hUt := mul_nonneg p.hU.le ht
    nlinarith only [(hb t ht).2, hUt]
  have hUint := hSq u hmeas hbound
  have hVint := hSq v hvMeas hvBound
  have hsave : IntegrableOn
      (fun t => Real.exp (-p.rho * t) * ((u t)^2 - (v t)^2))
      (Ioi (0 : ℝ)) := by
    simpa only [Pi.sub_apply, mul_sub] using hUint.sub hVint
  have hC0 := discounted_cost_integrable
    (p.toStateData 0 le_rfl) p.r u hmeas hbound
  have hCn := discounted_cost_integrable
    (p.toStateData n hn) p.r v hvMeas hvBound
  have hpoint :
      (fun t => discountedCost (p.toStateData 0 le_rfl) p.r u t -
        discountedCost (p.toStateData n hn) p.r v t) =ᵐ[
          volume.restrict (Ioi (0 : ℝ))]
      (fun t => p.r *
        (Real.exp (-p.rho * t) * ((u t)^2 - (v t)^2))) := by
    change ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)),
      discountedCost (p.toStateData 0 le_rfl) p.r u t -
        discountedCost (p.toStateData n hn) p.r v t =
      p.r * (Real.exp (-p.rho * t) * ((u t)^2 - (v t)^2))
    rw [ae_restrict_iff' measurableSet_Ioi]
    refine Filter.Eventually.of_forall ?_
    intro t ht
    have hO := (htraj t (le_of_lt ht)).2
    change GSTStage29.omega v p.eta (p.b * n) p.phiInitial
        p.a p.c p.omegaInitial t =
      GSTStage29.omega u p.eta 0 p.phiInitial
        p.a p.c p.omegaInitial t at hO
    simp only [discountedCost, competitorState,
      CoreParameters.toStateData, GSTStage06.runningCost, mul_zero]
    rw [hO]
    ring
  refine ⟨hsave, ?_⟩
  change
    -(∫ t in Ioi (0 : ℝ), discountedCost (p.toStateData n hn) p.r v t) -
      -(∫ t in Ioi (0 : ℝ),
        discountedCost (p.toStateData 0 le_rfl) p.r u t) =
    p.r * ∫ t in Ioi (0 : ℝ),
      Real.exp (-p.rho * t) * ((u t)^2 - (v t)^2)
  calc
    _ = ∫ t in Ioi (0 : ℝ),
        (discountedCost (p.toStateData 0 le_rfl) p.r u t -
          discountedCost (p.toStateData n hn) p.r v t) := by
      rw [integral_sub hC0 hCn]
      ring
    _ = ∫ t in Ioi (0 : ℝ),
        p.r * (Real.exp (-p.rho * t) * ((u t)^2 - (v t)^2)) :=
      integral_congr_ae hpoint
    _ = p.r * ∫ t in Ioi (0 : ℝ),
        Real.exp (-p.rho * t) * ((u t)^2 - (v t)^2) :=
      integral_const_mul _ _

theorem source_lift_objective_nondec
    (p : CoreParameters) (n : ℝ) (hn : 0 ≤ n)
    (u : ℝ → ℝ) (hi : 0 < p.phiInitial)
    (hmeas : Measurable u)
    (hbound : ∀ t : ℝ, 0 ≤ t → 0 ≤ u t ∧ u t ≤ p.U) :
    objective (p.toStateData 0 le_rfl) p.r u ≤
      objective (p.toStateData n hn) p.r
        (liftedControl u p.eta (p.b * n) p.phiInitial) := by
  let v := liftedControl u p.eta (p.b * n) p.phiInitial
  have hid := (source_lift_objective_identity p n hn u hi hmeas hbound).2
  have hsave : 0 ≤ ∫ t in Ioi (0 : ℝ),
      Real.exp (-p.rho * t) * ((u t)^2 - (v t)^2) := by
    apply integral_nonneg_of_ae
    change ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)),
      0 ≤ Real.exp (-p.rho * t) * ((u t)^2 - (v t)^2)
    rw [ae_restrict_iff' measurableSet_Ioi]
    refine Filter.Eventually.of_forall ?_
    intro t ht
    have hb := (source_lift_bounds_and_flow
      u p.eta (p.b * n) p.phiInitial t hi
      (mul_nonneg p.hb.le hn) (le_of_lt ht)
      (hbound t (le_of_lt ht)).1).2.1
    have hsquare : 0 ≤ (u t)^2 - (v t)^2 := by
      change 0 ≤ v t ∧ v t ≤ u t at hb
      nlinarith only [hb.1, hb.2]
    exact mul_nonneg (Real.exp_pos _).le hsquare
  have hnonneg := mul_nonneg p.hr.le hsave
  change 0 ≤ p.r * (∫ t in Ioi (0 : ℝ),
    Real.exp (-p.rho * t) *
      ((u t)^2 -
        (liftedControl u p.eta (p.b * n) p.phiInitial t)^2)) at hnonneg
  linarith only [hid, hnonneg]

end GSTStage182

#print axioms GSTStage182.source_lift_objective_identity
#print axioms GSTStage182.source_lift_objective_nondec
