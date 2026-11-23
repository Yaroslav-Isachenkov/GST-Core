import GSTStage110

open MeasureTheory Set Filter
open scoped Topology
open GSTStage31 GSTStage36

namespace GSTStage111

theorem halfline_ae_cost_integrable
    (x : StateData) (r : ℝ) (a : ℝ → ℝ)
    (haMeas : Measurable a)
    (haBound : ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)),
      0 ≤ a t ∧ a t ≤ x.U) :
    IntegrableOn (discountedCost x r a) (Ioi (0 : ℝ)) := by
  have hb := haBound
  rw [ae_restrict_iff' measurableSet_Ioi] at hb
  have hz : ∀ᵐ t : ℝ ∂volume, t ≠ 0 := by
    simp [ae_iff, measure_singleton]
  have hb' : ∀ᵐ t : ℝ, 0 ≤ t → 0 ≤ a t ∧ a t ≤ x.U := by
    filter_upwards [hb, hz] with t ht hzero
    intro hnonneg
    have hpos : 0 < t := by
      by_contra hn
      exact hzero (le_antisymm (le_of_not_gt hn) hnonneg)
    exact ht hpos
  exact (GSTStage41.integrable_of_ae_bounds x r a haMeas hb').1

theorem discounted_cost_nonneg
    (x : StateData) (r : ℝ) (a : ℝ → ℝ)
    (hq : 0 ≤ x.q) (hr : 0 ≤ r) (t : ℝ) :
    0 ≤ discountedCost x r a t := by
  dsimp only [discountedCost, GSTStage06.runningCost]
  exact mul_nonneg (Real.exp_pos _).le
    (add_nonneg (mul_nonneg hq (sq_nonneg _))
      (mul_nonneg hr (sq_nonneg _)))

theorem integral_lower_of_nat_intervals
    (f : ℕ → ℝ → ℝ) (g : ℝ → ℝ)
    (hf : ∀ n, IntegrableOn (f n) (Ioi (0 : ℝ)))
    (hg : IntegrableOn g (Ioi (0 : ℝ)))
    (hfNonneg : ∀ n, ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)), 0 ≤ f n t)
    (hfinite : ∀ m : ℕ, ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n in atTop,
        (∫ t in Icc (0 : ℝ) (m : ℝ), g t) ≤
          (∫ t in Icc (0 : ℝ) (m : ℝ), f n t) + ε) :
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n in atTop,
        (∫ t in Ioi (0 : ℝ), g t) ≤
          (∫ t in Ioi (0 : ℝ), f n t) + ε := by
  have hset (b : ℝ → ℝ) (T : ℝ) (hT : 0 ≤ T) :
      (∫ t in (0 : ℝ)..T, b t) = ∫ t in Icc (0 : ℝ) T, b t := by
    rw [intervalIntegral.integral_of_le hT, integral_Icc_eq_integral_Ioc]

  have hpartial (m n : ℕ) :
      (∫ t in Icc (0 : ℝ) (m : ℝ), f n t) ≤
        ∫ t in Ioi (0 : ℝ), f n t := by
    have hb : ∀ᵐ t ∂volume.restrict (Ioi (m : ℝ)), 0 ≤ f n t :=
      (hfNonneg n).filter_mono
        (ae_mono (Measure.restrict_mono
          (show Ioi (m : ℝ) ⊆ Ioi (0 : ℝ) from
            fun t ht => by
              change (m : ℝ) < t at ht
              change (0 : ℝ) < t
              exact lt_of_le_of_lt
                (show (0 : ℝ) ≤ (m : ℝ) from Nat.cast_nonneg m) ht)
          le_rfl))
    have htNonneg : 0 ≤ GSTStage25.tail (f n) (m : ℝ) :=
      integral_nonneg_of_ae hb
    have htRep := GSTStage25.tail_representation
      (f n) (m : ℝ) (hf n) (Nat.cast_nonneg m)
    rw [hset (f n) (m : ℝ) (Nat.cast_nonneg m)] at htRep
    change GSTStage25.tail (f n) (m : ℝ) =
      (∫ t in Ioi (0 : ℝ), f n t) -
        (∫ t in Icc (0 : ℝ) (m : ℝ), f n t) at htRep
    linarith

  have hconv :
      Tendsto (fun T : ℝ => ∫ t in (0 : ℝ)..T, g t)
        atTop (𝓝 (∫ t in Ioi (0 : ℝ), g t)) :=
    intervalIntegral_tendsto_integral_Ioi 0 hg tendsto_id

  intro ε hε
  have he : ∀ᶠ T : ℝ in atTop,
      (∫ t in Ioi (0 : ℝ), g t) - ε / 2 <
        ∫ t in (0 : ℝ)..T, g t :=
    (tendsto_order.1 hconv).1
      ((∫ t in Ioi (0 : ℝ), g t) - ε / 2) (by linarith)
  obtain ⟨R, hR⟩ := eventually_atTop.1 he
  obtain ⟨m, hm⟩ := exists_nat_gt R
  have happrox := hR (m : ℝ) (le_of_lt hm)
  rw [hset g (m : ℝ) (Nat.cast_nonneg m)] at happrox
  filter_upwards [hfinite m (ε / 2) (half_pos hε)] with n hn
  have hp := hpartial m n
  linarith

end GSTStage111

#print axioms GSTStage111.halfline_ae_cost_integrable
#print axioms GSTStage111.discounted_cost_nonneg
#print axioms GSTStage111.integral_lower_of_nat_intervals
