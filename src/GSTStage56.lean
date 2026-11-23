import GSTStage55

open MeasureTheory Set Filter
open scoped Topology
open GSTStage31

namespace GSTStage56

theorem canonical_signs
    (x : StateData) (r : ℝ)
    (hr : 0 < r) (hi : 0 < x.phiInitial)
    (ha : 0 < x.a) (hq : 0 < x.q)
    (hoPositive : 0 < x.omegaInitial)
    (hoTarget : x.omegaInitial < x.target)
    (hclip : GSTStage44.Clipping x r) :
    ∀ t : ℝ, 0 ≤ t →
      0 ≤ z x t ∧
      0 < p x t ∧
      p x t < 2 * x.q * x.target / (x.rho + x.a) := by
  intro t ht
  have hz : 0 ≤ z x t :=
    GSTStage44.candidate_z_nonneg x r hr hi hclip t ht
  have hp := GSTStage52.candidate_p_strict_bounds
    x r hr hi ha hq hoPositive hoTarget hclip t ht
  exact ⟨hz, hp.1, hp.2⟩

-- Lemma 2: signs and the conditional statement about S.
-- The state and costates are the previously verified integral constructions.
-- Candidate existence and global nonpositivity of S are not asserted.
theorem lemma2_canonical_candidate
    (x : StateData) (r : ℝ)
    (hr : 0 < r) (hi : 0 < x.phiInitial)
    (ha : 0 < x.a) (hq : 0 < x.q)
    (hoPositive : 0 < x.omegaInitial)
    (hoTarget : x.omegaInitial < x.target)
    (hclip : GSTStage44.Clipping x r) :
    (∀ t : ℝ, 0 ≤ t →
      0 ≤ z x t ∧
      0 < p x t ∧
      p x t < 2 * x.q * x.target / (x.rho + x.a)) ∧
    (x.omegaInitial < x.rho * x.target / (x.rho + x.a) →
      S x 0 < 0 ∧
      ∀ s : ℝ, 0 ≤ s → 0 < S x s →
        ∃ T m : ℝ, s < T ∧
          0 < m ∧ m < T ∧ 0 < S x m ∧
          (∀ t ∈ Icc (0 : ℝ) T, S x t ≤ S x m) ∧
          (∀ᶠ t in 𝓝 m, S x t ≤ S x m)) := by
  refine ⟨canonical_signs
    x r hr hi ha hq hoPositive hoTarget hclip, ?_⟩
  intro hthreshold
  refine ⟨GSTStage53.s_initial_negative
    x ha hq hoPositive hthreshold, ?_⟩
  intro s hs hpositive
  exact GSTStage55.candidate_s_positive_interior_maximum
    x r hr hi ha hq hoPositive hthreshold hclip s hs hpositive

#print axioms canonical_signs
#print axioms lemma2_canonical_candidate
#check lemma2_canonical_candidate

end GSTStage56
