import GSTStage182

open MeasureTheory Set Filter
open scoped Topology
open GSTStage37 GSTStage115 GSTStage180 GSTStage182

namespace GSTStage183

theorem source_lift_saving_integral_pos
    (p : CoreParameters) (n : ℝ) (hn : 0 < n)
    (u : ℝ → ℝ) (hi : 0 < p.phiInitial)
    (hmeas : Measurable u)
    (hbound : ∀ t : ℝ, 0 ≤ t → 0 ≤ u t ∧ u t ≤ p.U)
    (hnonzero : ¬ u =ᵐ[volume.restrict (Ioi (0 : ℝ))] 0) :
    0 < ∫ t in Ioi (0 : ℝ),
      Real.exp (-p.rho * t) *
        ((u t)^2 -
          (liftedControl u p.eta (p.b * n) p.phiInitial t)^2) := by
  let v := liftedControl u p.eta (p.b * n) p.phiInitial
  let f : ℝ → ℝ :=
    fun t => Real.exp (-p.rho * t) * ((u t)^2 - (v t)^2)
  have hB : 0 < p.b * n := mul_pos p.hb hn
  have hInt : IntegrableOn f (Ioi (0 : ℝ)) :=
    (source_lift_objective_identity p n hn.le u hi hmeas hbound).1
  have hnonneg : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] f := by
    change ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)), 0 ≤ f t
    rw [ae_restrict_iff' measurableSet_Ioi]
    refine Filter.Eventually.of_forall ?_
    intro t ht
    have hb := (source_lift_bounds_and_flow
      u p.eta (p.b * n) p.phiInitial t hi hB.le
      (le_of_lt ht) (hbound t (le_of_lt ht)).1).2.1
    change 0 ≤ v t ∧ v t ≤ u t at hb
    have hsquare : 0 ≤ (u t)^2 - (v t)^2 := by
      nlinarith only [hb.1, hb.2]
    exact mul_nonneg (Real.exp_pos _).le hsquare
  change 0 < ∫ t in Ioi (0 : ℝ), f t
  by_contra hnot
  have hzero : (∫ t in Ioi (0 : ℝ), f t) = 0 :=
    le_antisymm (le_of_not_gt hnot) (integral_nonneg_of_ae hnonneg)
  have hfae : f =ᵐ[volume.restrict (Ioi (0 : ℝ))] 0 :=
    (MeasureTheory.integral_eq_zero_iff_of_nonneg_ae hnonneg hInt).mp hzero
  apply hnonzero
  filter_upwards [hfae, ae_restrict_mem measurableSet_Ioi] with t hz ht
  change u t = 0
  have htPos : 0 < t := ht
  have hu0 : 0 ≤ u t := (hbound t htPos.le).1
  by_contra hne
  have huPos : 0 < u t := by
    by_contra hnotpos
    exact hne (le_antisymm (le_of_not_gt hnotpos) hu0)
  have hv0 : 0 ≤ v t :=
    (source_lift_bounds_and_flow
      u p.eta (p.b * n) p.phiInitial t hi hB.le htPos.le hu0).2.1.1
  have hvlt : v t < u t :=
    source_lift_control_strict
      u p.eta (p.b * n) p.phiInitial t hi hB htPos huPos
  have hsum : 0 < u t + v t :=
    lt_of_lt_of_le huPos (le_add_of_nonneg_right hv0)
  have hproduct : 0 < (u t - v t) * (u t + v t) :=
    mul_pos (sub_pos.mpr hvlt) hsum
  have hsquare : 0 < (u t)^2 - (v t)^2 := by
    nlinarith only [hproduct]
  have hfPos : 0 < f t := mul_pos (Real.exp_pos _) hsquare
  have hfZero : f t = 0 := hz
  exact (ne_of_gt hfPos) hfZero

theorem source_lift_objective_strict
    (p : CoreParameters) (n : ℝ) (hn : 0 < n)
    (u : ℝ → ℝ) (hi : 0 < p.phiInitial)
    (hmeas : Measurable u)
    (hbound : ∀ t : ℝ, 0 ≤ t → 0 ≤ u t ∧ u t ≤ p.U)
    (hnonzero : ¬ u =ᵐ[volume.restrict (Ioi (0 : ℝ))] 0) :
    objective (p.toStateData 0 le_rfl) p.r u <
      objective (p.toStateData n hn.le) p.r
        (liftedControl u p.eta (p.b * n) p.phiInitial) := by
  have hid :=
    (source_lift_objective_identity p n hn.le u hi hmeas hbound).2
  have hpos := source_lift_saving_integral_pos
    p n hn u hi hmeas hbound hnonzero
  have hgain := mul_pos p.hr hpos
  linarith only [hid, hgain]

end GSTStage183

#print axioms GSTStage183.source_lift_saving_integral_pos
#print axioms GSTStage183.source_lift_objective_strict
