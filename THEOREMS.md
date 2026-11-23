# Paper-to-Lean map

This navigation map follows the correspondence table in Section 12 of the English PDF and the archived semantic coverage records. Links lead to unchanged source files. The declarations, definitions and explicit hypotheses in Lean are authoritative for what the kernel checks. This map is not a new proof of equivalence between a PDF and Lean.

## Shared conventions

`state` / `omega` denote Ω, `resource` denotes φ, and `target` denotes Ω⋆. The source is the constant B = b n. The optimization problem maximizes a negative discounted quadratic cost. States and controls are functions on ℝ, with the relevant dynamics on t ≥ 0. The integrals over `Ioi 0` agree with those over [0,∞). Some comparison classes allow almost-everywhere measurability and bounds; Stage189 relates the value to measurable, pointwise-admissible controls. Uniqueness of general controls is almost everywhere.

## Theorems 1–7

| Paper result | Principal declarations | Hypotheses and interpretation |
| --- | --- | --- |
| **1. Attainment** | [GSTStage115.theorem1_existence](src/GSTStage115.lean); [GSTStage189.exists_continuous_core_optimizer](src/GSTStage189.lean) | Positive model coefficients, nonnegative initial states, and every n ≥ 0. An optimum exists; continuity is available for an optimal representative. |
| **2. Global sufficiency and uniqueness** | [GSTStage42.theorem2_sufficiency_and_uniqueness](src/GSTStage42.lean) | A canonical clipped candidate, positive initial resource, and S(t) = a p(t) + 2q(Ω(t) − Ω⋆) ≤ 0 for all nonnegative times. Includes the quantitative gap and uniqueness almost everywhere. |
| **3. Threshold family** | [GSTStage66.candidate_sufficiency_and_uniqueness](src/GSTStage66.lean); [GSTStage139.core_exists_unique_optimal_under_thresholds](src/GSTStage139.lean) | φᵢ > 0; 0 < Ωᵢ < ρΩ⋆/(ρ+a); ηU ≤ ρ; r > aqΩ⋆²/[4U²(ρ+a)]. These are sufficient conditions, for every n ≥ 0. |
| **4. Fixed numerical core** | [GSTStage164.fixed_candidate_sufficiency_and_uniqueness](src/GSTStage164.lean); [GSTStage166.fixed_exists_unique_optimal_for_every_source](src/GSTStage166.lean) | a=1/10, c=1, η=ρ=1/20, q=U=Ω⋆=1, r=1/10, Ωᵢ=1/5, φᵢ=1/2; arbitrary constant B ≥ 0. Existence, global optimality and uniqueness almost everywhere. |
| **5. Zero-source decay** | [GSTStage171.theorem5_zero_source](src/GSTStage171.lean) | B=0, admissible measurable bounded controls and nonnegative initial states. Establishes integral budgets and Ω(t)→0; does not assert φ(t)→0. |
| **6. Preservation criterion** | [GSTStage179.preserving_region_iff_thresholds](src/GSTStage179.lean) | For positive a,c,η,h,s and B ≥ 0, preservation of Ω ≥ h and φ ≥ s from every initial point of that region is equivalent to ah/(cs) ≤ U and ηah/c ≤ B. The preserving strategy is not asserted optimal for the original unconstrained objective. |
| **7. Strict value improvement** | [GSTStage189.theorem7_strict_value_improvement](src/GSTStage189.lean) | For fixed positive model coefficients and the same nonnegative initial data, n > 0 implies Vₙ > V₀. Does not assert strict monotonicity between every two positive source levels or a universal numerical gain. |

## Supporting results

| Topic | Declarations |
| --- | --- |
| Global trajectories and uniqueness | [GSTStage12.resource_is_solution](src/GSTStage12.lean); [GSTStage13.resource_representation](src/GSTStage13.lean); [GSTStage29.omega_solution](src/GSTStage29.lean); [GSTStage30.omega_representation](src/GSTStage30.lean) |
| Value as a real supremum | [GSTStage189.coreValue_eq_of_optimizer](src/GSTStage189.lean); [GSTStage189.coreValue_eq_measurable_sup](src/GSTStage189.lean) |
| Necessary clipping and continuous representative | [GSTStage128.optimal_control_clipping_ae](src/GSTStage128.lean); [GSTStage129.continuous_optimal_representative](src/GSTStage129.lean); [GSTStage131.optimal_representative_self_clipping](src/GSTStage131.lean) |
| Canonical costates and Hamiltonian maximum | [GSTStage138.canonical_costate_properties](src/GSTStage138.lean); [GSTStage138.core_exists_optimal_with_necessary_conditions](src/GSTStage138.lean) |
| Costate uniqueness under polynomial growth | [GSTStage135.state_costate_pair_unique_of_polynomial_growth](src/GSTStage135.lean) |
| State bound (30) | [GSTStage190.candidate_state_bounds_of_S_nonpos](src/GSTStage190.lean); [GSTStage190.candidate_state_bounds_under_thresholds](src/GSTStage190.lean); [GSTStage191.fixed_candidate_state_bounds](src/GSTStage191.lean) |

Canonical costates are defined by future integrals, not arbitrary finite-horizon terminal data. Bound (30) is not a uniform strictly positive lower bound on the infinite horizon. Global state results use local absolute continuity and almost-everywhere differential equations.

## Scope and evidence

The source parameter n is external and constant. No theorem here optimizes population size, proves physical irreplaceability, or establishes deployment safety. Mathematical assumptions must be evaluated separately in any empirical application. Not every intermediate displayed PDF formula is claimed as a standalone Lean theorem; equivalent proof routes occur.

The original [consolidated coverage report](evidence/full_core_document_coverage.json) identifies the following more detailed, unchanged historical reviews:

- [Theorems 1–3, necessary conditions, and bound (30)](evidence/semantic/stage191/theorems1_3_pmp_equation30_document_coverage.json)
- [Theorem 4](evidence/semantic/stage166/theorem4_document_coverage.json)
- [Theorem 5](evidence/semantic/stage171/theorem5_document_coverage.json)
- [Theorem 6](evidence/semantic/stage179/theorem6_document_coverage.json)
- [Theorem 7](evidence/semantic/stage189/theorem7_document_coverage.json)

Those historical reviews concern the Ukrainian edition. The English PDF's own map was used to prepare this document. The November rebuild rechecks source compilation and recorded axiom dependencies; it does not by itself re-audit the semantic correspondence.
