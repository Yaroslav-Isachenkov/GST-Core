import GSTStage91

open MeasureTheory Set Filter
open scoped Topology

namespace GSTStage92

theorem continuousOn_interval_memLp
    (f : ℝ → ℝ) (T : ℝ)
    (hf : ContinuousOn f (Icc (0 : ℝ) T)) :
    MemLp f 2 (volume.restrict (Icc (0 : ℝ) T)) := by
  obtain ⟨C, hC⟩ : ∃ C : ℝ,
      ∀ y ∈ f '' Icc (0 : ℝ) T, ‖y‖ ≤ C :=
    (isCompact_Icc.image_of_continuousOn hf).isBounded.exists_norm_le
  apply MemLp.of_bound
    (hf.aestronglyMeasurable measurableSet_Icc) C
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  exact hC (f t) (mem_image_of_mem f ht)

theorem continuous_interval_product_limit
    (T : ℝ)
    (u phi : ℕ → ℝ → ℝ) (a Phi : ℝ → ℝ)
    (v : ℕ → Lp ℝ 2 (volume.restrict (Icc (0 : ℝ) T)))
    (w : Lp ℝ 2 (volume.restrict (Icc (0 : ℝ) T)))
    (F : ℕ → BoundedContinuousFunction (Icc (0 : ℝ) T) ℝ)
    (Flim : BoundedContinuousFunction (Icc (0 : ℝ) T) ℝ)
    (C : ℝ)
    (hv : ∀ n, (v n : ℝ → ℝ) =ᵐ[
      volume.restrict (Icc (0 : ℝ) T)] u n)
    (hw : (w : ℝ → ℝ) =ᵐ[
      volume.restrict (Icc (0 : ℝ) T)] a)
    (hbound : ∀ n, ‖v n‖ ≤ C)
    (hweak : ∀ g : Lp ℝ 2 (volume.restrict (Icc (0 : ℝ) T)),
      Tendsto (fun n => inner ℝ (v n) g)
        atTop (𝓝 (inner ℝ w g)))
    (hphi : ∀ n, ContinuousOn (phi n) (Icc (0 : ℝ) T))
    (hPhi : ContinuousOn Phi (Icc (0 : ℝ) T))
    (hF : ∀ n t (ht : t ∈ Icc (0 : ℝ) T),
      F n ⟨t, ht⟩ = phi n t)
    (hFlim : ∀ t (ht : t ∈ Icc (0 : ℝ) T),
      Flim ⟨t, ht⟩ = Phi t)
    (hconv : Tendsto F atTop (𝓝 Flim)) :
    Tendsto (fun n => ∫ t in Icc (0 : ℝ) T, phi n t * u n t)
      atTop (𝓝 (∫ t in Icc (0 : ℝ) T, Phi t * a t)) := by
  let hf : ∀ n, MemLp (phi n) 2
      (volume.restrict (Icc (0 : ℝ) T)) :=
    fun n => continuousOn_interval_memLp (phi n) T (hphi n)
  let hlim : MemLp Phi 2 (volume.restrict (Icc (0 : ℝ) T)) :=
    continuousOn_interval_memLp Phi T hPhi
  have hstrong :
      Tendsto (fun n => (hf n).toLp (phi n))
        atTop (𝓝 (hlim.toLp Phi)) :=
    GSTStage91.interval_BC_to_L2_tendsto
      T F Flim phi Phi hf hlim hF hFlim hconv
  exact GSTStage90.original_product_integral_tendsto
    u phi a Phi v w
    (fun n => (hf n).toLp (phi n)) (hlim.toLp Phi) C
    hv hw (fun n => (hf n).coeFn_toLp) hlim.coeFn_toLp
    hbound hweak hstrong

end GSTStage92

#print axioms GSTStage92.continuousOn_interval_memLp
#print axioms GSTStage92.continuous_interval_product_limit
