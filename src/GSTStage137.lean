import GSTStage136

open MeasureTheory Set Filter
open scoped Topology
open GSTStage11 GSTStage31

namespace GSTStage137

theorem clipping_quadratic_maximum
    (r U w u : ℝ)
    (hr : 0 < r) (hU : 0 ≤ U)
    (hu0 : 0 ≤ u) (huU : u ≤ U) :
    let v := max 0 (min U (w / (2 * r)))
    r * (u - v) ^ 2 ≤
      (-r * v ^ 2 + w * v) - (-r * u ^ 2 + w * u) := by
  by_cases hUzero : U = 0
  · have huzero : u = 0 := by
      rw [hUzero] at huU
      exact le_antisymm huU hu0
    simp [hUzero, huzero]
  · have hUpos : 0 < U := by
      rcases lt_or_eq_of_le hU with hlt | heq
      · exact hlt
      · exact (hUzero heq.symm).elim
    let v := max 0 (min U (w / (2 * r)))
    have hsign : (-2 * r * v + w) * (u - v) ≤ 0 :=
      GSTStage07.clipping_variational_sign r U w u hr hUpos hu0 huU
    change r * (u - v) ^ 2 ≤
      (-r * v ^ 2 + w * v) - (-r * u ^ 2 + w * u)
    nlinarith only [hsign]

noncomputable def hamiltonian
    (x : StateData) (r t v : ℝ) : ℝ :=
  -x.q * (state x t - x.target) ^ 2 - r * v ^ 2 +
    p x t * (-x.a * state x t +
      x.c * resource x.u x.eta x.B x.phiInitial t * v) +
    z x t * (x.B -
      x.eta * resource x.u x.eta x.B x.phiInitial t * v)

theorem hamiltonian_maximum_of_clipping
    (x : StateData) (r : ℝ) (hr : 0 < r)
    (hclip : ∀ t : ℝ, 0 ≤ t →
      x.u t = max 0 (min x.U
        ((resource x.u x.eta x.B x.phiInitial t * d x t) /
          (2 * r)))) :
    ∀ t : ℝ, 0 ≤ t → ∀ v : ℝ, 0 ≤ v → v ≤ x.U →
      r * (v - x.u t) ^ 2 ≤
        hamiltonian x r t (x.u t) - hamiltonian x r t v ∧
      hamiltonian x r t v ≤ hamiltonian x r t (x.u t) := by
  intro t ht v hv0 hvU
  have hU : 0 ≤ x.U := (x.hu 0 le_rfl).1.trans (x.hu 0 le_rfl).2
  have h := clipping_quadratic_maximum r x.U
    (resource x.u x.eta x.B x.phiInitial t * d x t) v
    hr hU hv0 hvU
  dsimp only at h
  rw [← hclip t ht] at h
  have heq :
      hamiltonian x r t (x.u t) - hamiltonian x r t v =
        (-r * (x.u t) ^ 2 +
          (resource x.u x.eta x.B x.phiInitial t * d x t) * x.u t) -
        (-r * v ^ 2 +
          (resource x.u x.eta x.B x.phiInitial t * d x t) * v) := by
    dsimp only [hamiltonian, d, GSTStage18.canonicalD]
    ring
  have hgap : r * (v - x.u t) ^ 2 ≤
      hamiltonian x r t (x.u t) - hamiltonian x r t v := by
    rw [heq]
    exact h
  have hnonneg : 0 ≤ r * (v - x.u t) ^ 2 :=
    mul_nonneg hr.le (sq_nonneg _)
  exact ⟨hgap, by linarith⟩

end GSTStage137

#print axioms GSTStage137.clipping_quadratic_maximum
#print axioms GSTStage137.hamiltonian_maximum_of_clipping
