import GSTStage149

open Set

namespace GSTStage150

def SaturatedSystemOn
    (F O P Z : ℝ → ℝ) (B a T : ℝ) : Prop :=
  (ContinuousOn F (Icc a T) ∧
   ContinuousOn O (Icc a T) ∧
   ContinuousOn P (Icc a T) ∧
   ContinuousOn Z (Icc a T)) ∧
  (∀ s ∈ Ioo a T,
    HasDerivAt F (B - F s / 20) s ∧
    HasDerivAt O (-O s / 10 + F s) s ∧
    HasDerivAt P (3 / 20 * P s + 2 * (O s - 1)) s ∧
    HasDerivAt Z (Z s / 10 - P s) s)

theorem saturated_system_unique_on_interval
    (F₁ O₁ P₁ Z₁ F₂ O₂ P₂ Z₂ : ℝ → ℝ)
    (B a T : ℝ)
    (h₁ : SaturatedSystemOn F₁ O₁ P₁ Z₁ B a T)
    (h₂ : SaturatedSystemOn F₂ O₂ P₂ Z₂ B a T)
    (hinit : F₁ a = F₂ a ∧ O₁ a = O₂ a ∧
      P₁ a = P₂ a ∧ Z₁ a = Z₂ a) :
    EqOn F₁ F₂ (Icc a T) ∧
    EqOn O₁ O₂ (Icc a T) ∧
    EqOn P₁ P₂ (Icc a T) ∧
    EqOn Z₁ Z₂ (Icc a T) := by
  rcases h₁ with ⟨⟨hF₁, hO₁, hP₁, hZ₁⟩, hd₁⟩
  rcases h₂ with ⟨⟨hF₂, hO₂, hP₂, hZ₂⟩, hd₂⟩

  have hF : EqOn F₁ F₂ (Icc a T) := by
    apply GSTStage149.linear_ode_unique_on_interval
      F₁ F₂ (fun _ => B) (-1 / 20) a T hF₁ hF₂
    · intro s hs
      convert (hd₁ s hs).1 using 1
      all_goals ring
    · intro s hs
      convert (hd₂ s hs).1 using 1
      all_goals ring
    · exact hinit.1

  have hO : EqOn O₁ O₂ (Icc a T) := by
    apply GSTStage149.linear_ode_unique_on_interval
      O₁ O₂ F₁ (-1 / 10) a T hO₁ hO₂
    · intro s hs
      convert (hd₁ s hs).2.1 using 1
      all_goals ring
    · intro s hs
      have hd := (hd₂ s hs).2.1
      rw [← hF ⟨hs.1.le, hs.2.le⟩] at hd
      convert hd using 1
      all_goals ring
    · exact hinit.2.1

  have hP : EqOn P₁ P₂ (Icc a T) := by
    apply GSTStage149.linear_ode_unique_on_interval
      P₁ P₂ (fun s => 2 * (O₁ s - 1)) (3 / 20) a T hP₁ hP₂
    · intro s hs
      exact (hd₁ s hs).2.2.1
    · intro s hs
      have hd := (hd₂ s hs).2.2.1
      rw [← hO ⟨hs.1.le, hs.2.le⟩] at hd
      exact hd
    · exact hinit.2.2.1

  have hZ : EqOn Z₁ Z₂ (Icc a T) := by
    apply GSTStage149.linear_ode_unique_on_interval
      Z₁ Z₂ (fun s => -P₁ s) (1 / 10) a T hZ₁ hZ₂
    · intro s hs
      convert (hd₁ s hs).2.2.2 using 1
      all_goals ring
    · intro s hs
      have hd := (hd₂ s hs).2.2.2
      rw [← hP ⟨hs.1.le, hs.2.le⟩] at hd
      convert hd using 1
      all_goals ring
    · exact hinit.2.2.2

  exact ⟨hF, hO, hP, hZ⟩

end GSTStage150

#print axioms GSTStage150.saturated_system_unique_on_interval
