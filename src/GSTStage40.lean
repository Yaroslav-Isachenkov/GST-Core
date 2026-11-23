import GSTStage39

open MeasureTheory Set Filter
open scoped Topology
open GSTStage11 GSTStage31 GSTStage34 GSTStage36 GSTStage37 GSTStage39

namespace GSTStage40

theorem interval_integral_eq_of_ae
    (f g : ℝ → ℝ) (T : ℝ) (hT : 0 ≤ T)
    (h : f =ᵐ[volume.restrict (Ioi (0 : ℝ))] g) :
    (∫ t in (0 : ℝ)..T, f t) = ∫ t in (0 : ℝ)..T, g t := by
  have hg : ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)), f t = g t := h
  rw [ae_restrict_iff' measurableSet_Ioi] at hg
  apply intervalIntegral.integral_congr_ae
  filter_upwards [hg] with t ht
  intro hmem
  rw [uIoc_of_le hT] at hmem
  exact ht (show t ∈ Ioi (0 : ℝ) from hmem.1)

theorem cumulative_eq_of_ae
    (u v : ℝ → ℝ) (eta t : ℝ) (ht : 0 ≤ t)
    (h : u =ᵐ[volume.restrict (Ioi (0 : ℝ))] v) :
    cumulative u eta t = cumulative v eta t := by
  unfold cumulative
  rw [interval_integral_eq_of_ae u v t ht h]

theorem resource_eq_of_ae
    (u v : ℝ → ℝ) (eta B initial t : ℝ) (ht : 0 ≤ t)
    (h : u =ᵐ[volume.restrict (Ioi (0 : ℝ))] v) :
    resource u eta B initial t = resource v eta B initial t := by
  have he :
      (fun s => Real.exp (cumulative u eta s))
        =ᵐ[volume.restrict (Ioi (0 : ℝ))]
      (fun s => Real.exp (cumulative v eta s)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    change (0 : ℝ) < s at hs
    rw [cumulative_eq_of_ae u v eta s hs.le h]
  have hi := interval_integral_eq_of_ae
    (fun s => Real.exp (cumulative u eta s))
    (fun s => Real.exp (cumulative v eta s)) t ht he
  unfold resource
  rw [cumulative_eq_of_ae u v eta t ht h, hi]

theorem linear_state_eq_of_ae
    (f g : ℝ → ℝ) (a initial t : ℝ) (ht : 0 ≤ t)
    (h : f =ᵐ[volume.restrict (Ioi (0 : ℝ))] g) :
    GSTStage29.linearState f a initial t =
      GSTStage29.linearState g a initial t := by
  have he :
      (fun s => Real.exp (a * s) * f s)
        =ᵐ[volume.restrict (Ioi (0 : ℝ))]
      (fun s => Real.exp (a * s) * g s) := by
    filter_upwards [h] with s hs
    rw [hs]
  have hi := interval_integral_eq_of_ae
    (fun s => Real.exp (a * s) * f s)
    (fun s => Real.exp (a * s) * g s) t ht he
  change
    Real.exp (-a * t) *
        (initial + ∫ s in (0 : ℝ)..t, Real.exp (a * s) * f s) =
      Real.exp (-a * t) *
        (initial + ∫ s in (0 : ℝ)..t, Real.exp (a * s) * g s)
  rw [hi]

theorem omega_eq_of_ae
    (u v : ℝ → ℝ)
    (eta B phiInitial a c omegaInitial t : ℝ) (ht : 0 ≤ t)
    (h : u =ᵐ[volume.restrict (Ioi (0 : ℝ))] v) :
    GSTStage29.omega u eta B phiInitial a c omegaInitial t =
      GSTStage29.omega v eta B phiInitial a c omegaInitial t := by
  have hf :
      GSTStage29.resourceForcing u eta B phiInitial c
        =ᵐ[volume.restrict (Ioi (0 : ℝ))]
      GSTStage29.resourceForcing v eta B phiInitial c := by
    filter_upwards [h, ae_restrict_mem measurableSet_Ioi] with s hs hmem
    change (0 : ℝ) < s at hmem
    change
      c * (resource u eta B phiInitial s * u s) =
        c * (resource v eta B phiInitial s * v s)
    rw [resource_eq_of_ae u v eta B phiInitial s hmem.le h, hs]
  exact linear_state_eq_of_ae
    (GSTStage29.resourceForcing u eta B phiInitial c)
    (GSTStage29.resourceForcing v eta B phiInitial c)
    a omegaInitial t ht hf

theorem discounted_cost_ae_eq
    (x : StateData) (r : ℝ) (u v : ℝ → ℝ)
    (h : u =ᵐ[volume.restrict (Ioi (0 : ℝ))] v) :
    discountedCost x r u
      =ᵐ[volume.restrict (Ioi (0 : ℝ))]
    discountedCost x r v := by
  filter_upwards [h, ae_restrict_mem measurableSet_Ioi] with t ht hmem
  change (0 : ℝ) < t at hmem
  have ho : competitorState x u t = competitorState x v t :=
    omega_eq_of_ae u v x.eta x.B x.phiInitial x.a x.c
      x.omegaInitial t hmem.le h
  change discountedCost x r u t = discountedCost x r v t
  unfold discountedCost
  rw [ho, ht]

theorem objective_eq_of_ae
    (x : StateData) (r : ℝ) (u v : ℝ → ℝ)
    (h : u =ᵐ[volume.restrict (Ioi (0 : ℝ))] v) :
    objective x r u = objective x r v := by
  have hi :
      (∫ t in Ioi (0 : ℝ), discountedCost x r u t) =
        ∫ t in Ioi (0 : ℝ), discountedCost x r v t :=
    integral_congr_ae (discounted_cost_ae_eq x r u v h)
  change
    -(∫ t in Ioi (0 : ℝ), discountedCost x r u t) =
      -(∫ t in Ioi (0 : ℝ), discountedCost x r v t)
  rw [hi]

theorem gap_ae_eq
    (x : StateData) (r : ℝ) (u v : ℝ → ℝ)
    (h : u =ᵐ[volume.restrict (Ioi (0 : ℝ))] v) :
    gap x r u =ᵐ[volume.restrict (Ioi (0 : ℝ))] gap x r v := by
  filter_upwards [h, ae_restrict_mem measurableSet_Ioi] with t ht hmem
  change (0 : ℝ) < t at hmem
  have ho : competitorState x u t = competitorState x v t :=
    omega_eq_of_ae u v x.eta x.B x.phiInitial x.a x.c
      x.omegaInitial t hmem.le h
  change gap x r u t = gap x r v t
  unfold gap
  rw [ho, ht]

-- Applies the general invariance results to the representative of stage39.
-- Integrability of the original a.e.-bounded control's cost is handled
-- separately when transferring the comparison theorem.
theorem representative_invariance
    (x : StateData) (r : ℝ) (u : ℝ → ℝ)
    (huBound : ∀ᵐ t : ℝ, 0 ≤ t → 0 ≤ u t ∧ u t ≤ x.U) :
    (∀ t : ℝ, 0 ≤ t →
      resource (boundedRepresentative x.U u) x.eta x.B x.phiInitial t =
        resource u x.eta x.B x.phiInitial t) ∧
    (∀ t : ℝ, 0 ≤ t →
      competitorState x (boundedRepresentative x.U u) t =
        competitorState x u t) ∧
    objective x r (boundedRepresentative x.U u) = objective x r u ∧
    (∫ t in Ioi (0 : ℝ), gap x r (boundedRepresentative x.U u) t) =
      ∫ t in Ioi (0 : ℝ), gap x r u t := by
  have h := representative_ae_on_Ioi x.U u huBound
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro t ht
    exact resource_eq_of_ae
      (boundedRepresentative x.U u) u x.eta x.B x.phiInitial t ht h
  · intro t ht
    exact omega_eq_of_ae
      (boundedRepresentative x.U u) u
      x.eta x.B x.phiInitial x.a x.c x.omegaInitial t ht h
  · exact objective_eq_of_ae x r (boundedRepresentative x.U u) u h
  · exact integral_congr_ae
      (gap_ae_eq x r (boundedRepresentative x.U u) u h)

#print axioms interval_integral_eq_of_ae
#print axioms cumulative_eq_of_ae
#print axioms resource_eq_of_ae
#print axioms linear_state_eq_of_ae
#print axioms omega_eq_of_ae
#print axioms discounted_cost_ae_eq
#print axioms objective_eq_of_ae
#print axioms gap_ae_eq
#print axioms representative_invariance

end GSTStage40
