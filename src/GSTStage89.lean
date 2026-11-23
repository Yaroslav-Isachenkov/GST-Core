import GSTStage88

open Filter
open scoped Topology

namespace GSTStage89

theorem weak_strong_inner_tendsto
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (v : ℕ → E) (w : E)
    (h : ℕ → E) (hlim : E) (C : ℝ)
    (hbound : ∀ n, ‖v n‖ ≤ C)
    (hweak : ∀ g : E,
      Tendsto (fun n => inner ℝ (v n) g)
        atTop (𝓝 (inner ℝ w g)))
    (hstrong : Tendsto h atTop (𝓝 hlim)) :
    Tendsto (fun n => inner ℝ (v n) (h n))
      atTop (𝓝 (inner ℝ w hlim)) := by
  have hnorm :
      Tendsto (fun n => ‖h n - hlim‖) atTop (𝓝 0) := by
    have hc : Tendsto (fun _ : ℕ => hlim) atTop (𝓝 hlim) :=
      tendsto_const_nhds
    simpa only [sub_self, norm_zero] using (hstrong.sub hc).norm

  have hupper :
      Tendsto (fun n => C * ‖h n - hlim‖) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul hnorm

  have habs (n : ℕ) :
      |inner ℝ (v n) (h n - hlim)| ≤ C * ‖h n - hlim‖ := by
    have hcs :
        |inner ℝ (v n) (h n - hlim)| ≤
          ‖v n‖ * ‖h n - hlim‖ := by
      have hcs' :
          ‖inner ℝ (v n) (h n - hlim)‖ ≤
            ‖v n‖ * ‖h n - hlim‖ :=
        norm_inner_le_norm (v n) (h n - hlim)
      simpa only [Real.norm_eq_abs] using hcs'
    exact hcs.trans
      (mul_le_mul_of_nonneg_right (hbound n) (norm_nonneg _))

  have hsmall :
      Tendsto (fun n => inner ℝ (v n) (h n - hlim))
        atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le
      (show Tendsto (fun n => -(C * ‖h n - hlim‖))
        atTop (𝓝 0) by simpa using hupper.neg)
      hupper
    · intro n
      exact (abs_le.mp (habs n)).1
    · intro n
      exact (abs_le.mp (habs n)).2

  have hsum := (hweak hlim).add hsmall
  simpa only [inner_sub_right, add_sub_cancel, add_zero] using hsum

end GSTStage89

#print axioms GSTStage89.weak_strong_inner_tendsto
