import GSTStage85
import Mathlib.MeasureTheory.Function.Floor

open MeasureTheory Set Filter
open scoped Topology

namespace GSTStage86

theorem glue_ae_compatible_interval_functions
    (f : ℕ → ℝ → ℝ) (hf : ∀ m, Measurable (f m))
    (hcompat : ∀ (m k : ℕ),
      f m =ᵐ[volume.restrict
        (Icc (0 : ℝ) (m : ℝ) ∩ Icc (0 : ℝ) (k : ℝ))] f k) :
    ∃ a : ℝ → ℝ, Measurable a ∧
      ∀ m : ℕ, a =ᵐ[volume.restrict (Icc (0 : ℝ) (m : ℝ))] f m := by
  let a : ℝ → ℝ := fun t => f (Nat.ceil t) t
  have heval : Measurable (fun p : ℝ × ℕ => f p.2 p.1) :=
    measurable_from_prod_countable_left hf
  have ha : Measurable a :=
    heval.comp (measurable_id.prodMk
      (Nat.measurable_ceil : Measurable (Nat.ceil : ℝ → ℕ)))
  refine ⟨a, ha, ?_⟩
  intro m
  have hc (n : ℕ) : ∀ᵐ t ∂volume,
      t ∈ Icc (0 : ℝ) (n : ℝ) ∩ Icc (0 : ℝ) (m : ℝ) →
        f n t = f m t := by
    exact (ae_restrict_iff'
      (measurableSet_Icc.inter measurableSet_Icc)).mp (hcompat n m)
  have hall : ∀ᵐ t ∂volume, ∀ n : ℕ,
      t ∈ Icc (0 : ℝ) (n : ℝ) ∩ Icc (0 : ℝ) (m : ℝ) →
        f n t = f m t := ae_all_iff.mpr hc
  change ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) (m : ℝ)), a t = f m t
  rw [ae_restrict_iff' measurableSet_Icc]
  filter_upwards [hall] with t ht htm
  exact ht (Nat.ceil t) ⟨⟨htm.1, Nat.le_ceil t⟩, htm⟩


theorem ae_bounds_on_halfline_of_nat_intervals
    (a : ℝ → ℝ) (U : ℝ)
    (hb : ∀ m : ℕ,
      ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) (m : ℝ)),
        0 ≤ a t ∧ a t ≤ U) :
    ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)), 0 ≤ a t ∧ a t ≤ U := by
  have hc (m : ℕ) : ∀ᵐ t ∂volume,
      t ∈ Icc (0 : ℝ) (m : ℝ) → 0 ≤ a t ∧ a t ≤ U :=
    (ae_restrict_iff' measurableSet_Icc).mp (hb m)
  have hall : ∀ᵐ t ∂volume, ∀ m : ℕ,
      t ∈ Icc (0 : ℝ) (m : ℝ) → 0 ≤ a t ∧ a t ≤ U :=
    ae_all_iff.mpr hc
  rw [ae_restrict_iff' measurableSet_Ioi]
  filter_upwards [hall] with t ht hpos
  exact ht (Nat.ceil t) ⟨le_of_lt hpos, Nat.le_ceil t⟩

#print axioms GSTStage86.glue_ae_compatible_interval_functions
#print axioms GSTStage86.ae_bounds_on_halfline_of_nat_intervals

end GSTStage86
