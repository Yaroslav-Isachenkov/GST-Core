import GSTStage93
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

open MeasureTheory Set Filter
open scoped Topology

namespace GSTStage94

theorem continuous_subinterval_product_limit
    (T t : ℝ) (htT : t ≤ T)
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
    (hF : ∀ n s (hs : s ∈ Icc (0 : ℝ) T),
      F n ⟨s, hs⟩ = phi n s)
    (hFlim : ∀ s (hs : s ∈ Icc (0 : ℝ) T),
      Flim ⟨s, hs⟩ = Phi s)
    (hconv : Tendsto F atTop (𝓝 Flim)) :
    Tendsto (fun n => ∫ s in Icc (0 : ℝ) t, phi n s * u n s)
      atTop (𝓝 (∫ s in Icc (0 : ℝ) t, Phi s * a s)) := by
  let psi : ℕ → ℝ → ℝ :=
    fun n => (Icc (0 : ℝ) t).indicator (phi n)
  let Psi : ℝ → ℝ := (Icc (0 : ℝ) t).indicator Phi
  have hpsi (n : ℕ) :
      MemLp (psi n) 2 (volume.restrict (Icc (0 : ℝ) T)) := by
    exact (GSTStage92.continuousOn_interval_memLp
      (phi n) T (hphi n)).indicator measurableSet_Icc
  have hPsi :
      MemLp Psi 2 (volume.restrict (Icc (0 : ℝ) T)) := by
    exact (GSTStage92.continuousOn_interval_memLp
      Phi T hPhi).indicator measurableSet_Icc

  have hzero : Tendsto (fun n => ‖F n - Flim‖) atTop (𝓝 0) := by
    have hc : Tendsto (fun _ : ℕ => Flim) atTop (𝓝 Flim) :=
      tendsto_const_nhds
    simpa only [sub_self, norm_zero] using (hconv.sub hc).norm

  have hstrong :
      Tendsto (fun n => (hpsi n).toLp (psi n))
        atTop (𝓝 (hPsi.toLp Psi)) := by
    apply GSTStage91.L2_tendsto_of_ae_uniform_error
      (fun n => (hpsi n).toLp (psi n)) (hPsi.toLp Psi)
      (fun n => ‖F n - Flim‖) (fun n => norm_nonneg _) ?_ hzero
    intro n
    filter_upwards [
      (hpsi n).coeFn_toLp,
      hPsi.coeFn_toLp,
      ae_restrict_mem measurableSet_Icc
    ] with s hs1 hs2 hsT
    rw [hs1, hs2]
    by_cases hs : s ∈ Icc (0 : ℝ) t
    · have hb := (F n - Flim).norm_coe_le_norm ⟨s, hsT⟩
      change ‖F n ⟨s, hsT⟩ - Flim ⟨s, hsT⟩‖ ≤ ‖F n - Flim‖ at hb
      rw [hF n s hsT, hFlim s hsT] at hb
      simpa only [psi, Psi, Set.indicator_of_mem hs] using hb
    · simp only [psi, Psi, Set.indicator_of_notMem hs,
        sub_self, norm_zero]
      exact norm_nonneg _

  have hl := GSTStage90.original_product_integral_tendsto
    u psi a Psi v w
    (fun n => (hpsi n).toLp (psi n)) (hPsi.toLp Psi) C
    hv hw (fun n => (hpsi n).coeFn_toLp) hPsi.coeFn_toLp
    hbound hweak hstrong

  have hsub : Icc (0 : ℝ) t ⊆ Icc (0 : ℝ) T :=
    fun s hs => ⟨hs.1, le_trans hs.2 htT⟩
  have hi (p q : ℝ → ℝ) :
      (∫ s in Icc (0 : ℝ) T,
        ((Icc (0 : ℝ) t).indicator p) s * q s) =
      ∫ s in Icc (0 : ℝ) t, p s * q s := by
    have he :
        (fun s => ((Icc (0 : ℝ) t).indicator p) s * q s) =
        (Icc (0 : ℝ) t).indicator (fun s => p s * q s) := by
      funext s
      by_cases hs : s ∈ Icc (0 : ℝ) t <;> simp [hs]
    rw [he, integral_indicator measurableSet_Icc]
    rw [Measure.restrict_restrict measurableSet_Icc,
        inter_eq_left.mpr hsub]

  have he (n : ℕ) :
      (∫ s in Icc (0 : ℝ) T, psi n s * u n s) =
        ∫ s in Icc (0 : ℝ) t, phi n s * u n s :=
    hi (phi n) (u n)
  have helim :
      (∫ s in Icc (0 : ℝ) T, Psi s * a s) =
        ∫ s in Icc (0 : ℝ) t, Phi s * a s :=
    hi Phi a
  rw [helim] at hl
  exact hl.congr' (Filter.Eventually.of_forall he)

end GSTStage94

#print axioms GSTStage94.continuous_subinterval_product_limit
