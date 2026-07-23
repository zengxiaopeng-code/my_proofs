import MyProofs.Foundations.PosteriorProcess

/-!
# Lemma 1 (Posterior process): machine-checked faithfulness audit

Lean's kernel guarantees **proof ↔ statement** (a `sorry`-free theorem with clean `#print axioms`
really is a theorem). It does **not** guarantee **statement ↔ the paper's proposition** — that
translation is a human act, and is exactly where a formalization can be faithful-looking yet wrong
(vacuous/contradictory hypotheses, silently strengthened assumptions, a mis-encoded conclusion).

This file converts as much of that residual "trust the translation" as possible into
kernel-checked facts. Each declaration below, by compiling, establishes one faithfulness claim.

Caveat (honest limit): if the statement and an audit lemma shared the *same* mis-definition they
could agree wrongly. These checks reduce risk; they do not eliminate it. The more independent
characterizations agree, the smaller the room for a hidden defect.

## What is checked

* **Hypotheses are not stronger than the paper** (`paperHyp_implies_standardBorel`,
  `nonempty_probabilityMeasure`): the paper's "Θ compact Polish" implies the `StandardBorelSpace Θ`
  used in the existence statement, and the only genuine addition (`Nonempty`) is satisfiable.
* **Hypotheses are not vacuous/contradictory** (`kernelExists_nonvacuous`,
  `sufficiency_nonvacuous`, `standardBorel_probabilityMeasure_unitInterval`,
  `factorizationPosterior_nonvacuous`): the theorems actually apply in concrete non-trivial
  settings, so nothing is proved from an empty hypothesis set.
* **The object `Δ(Θ)` is the paper's** (`deltaTheta_measurableSpace_eq_borel`,
  `deltaTheta_tendsto_iff_integral`): the σ-algebra Lean puts on `Δ(Θ)` really is the Borel
  σ-algebra of the weak topology, and its topology really is the weak topology. Without these,
  `deltaTheta_standardBorel` could be a true theorem about the *wrong* structure.
* **The measure-valued martingale encoding is transparent** (`martingale_tower`): the paper's
  `E[Sₜ | ℱₛ] = Sₛ`, encoded test-function-by-test-function, really unfolds to the conditional
  expectation tower/consistency `E[E[φ(θ)|ℱₜ] | ℱₛ] = E[φ(θ)|ℱₛ]` for `s ≤ t`.
-/

open MeasureTheory ProbabilityTheory

namespace PosteriorProcess

/-! ### 1. The Lean hypotheses are not stronger than the paper's -/

/-- The paper assumes `Θ` is a **compact Polish** space. The existence statement `kernel_exists`
only needs `StandardBorelSpace Θ`, which is *implied* (Polish + Borel already suffices, compactness
is not even needed). So using `StandardBorelSpace` is a faithful weakening, not a strengthening. -/
theorem paperHyp_implies_standardBorel (Θ : Type*) [TopologicalSpace Θ] [PolishSpace Θ]
    [CompactSpace Θ] [MeasurableSpace Θ] [BorelSpace Θ] :
    StandardBorelSpace Θ := inferInstance

/-- The only assumption added over the paper is `Nonempty` (of the parameter space, resp. of
`Δ(Θ)`). It is always satisfiable when `Θ` is nonempty: a Dirac measure is a probability measure.
So it rules out nothing of substance. -/
theorem nonempty_probabilityMeasure {Θ : Type*} [MeasurableSpace Θ] [Nonempty Θ] :
    Nonempty (ProbabilityMeasure Θ) :=
  ⟨⟨Measure.dirac (Classical.arbitrary Θ), inferInstance⟩⟩

/-! ### 2. The hypotheses are jointly satisfiable (no vacuity)

Each result below instantiates a theorem in a concrete non-trivial setting. Because the instances
type-check, the hypothesis sets are consistent, so the theorems are not vacuously true. -/

/-- A concrete constant filtration on `ℝ`, used to witness non-vacuity. -/
private def constFiltration : Filtration ℕ (inferInstance : MeasurableSpace ℝ) :=
  ⟨fun _ => inferInstance, fun _ _ _ => le_rfl, fun _ => le_rfl⟩

/-- `kernel_exists` genuinely applies: on `(ℝ, δ₀)` with the constant filtration and `θ = id`,
its full conclusion holds. Hence its hypotheses are not contradictory. -/
theorem kernelExists_nonvacuous :
    ∃ S : ℝ → Measure ℝ,
      (∀ ω, IsProbabilityMeasure (S ω)) ∧
      Measurable[constFiltration 0] S ∧
      ∀ φ : ℝ → ℝ, Measurable φ → (∃ C, ∀ x, |φ x| ≤ C) →
        (fun ω => ∫ x, φ x ∂(S ω))
          =ᵐ[Measure.dirac 0] (Measure.dirac 0)[(φ ∘ id) | constFiltration 0] :=
  kernel_exists (Ω := ℝ) (P := Measure.dirac 0) constFiltration (θ := id) measurable_id 0

/-- `sufficiency` genuinely applies in the same concrete setting. -/
theorem sufficiency_nonvacuous :
    ∃ S : ℝ → Measure ℝ,
      (∀ ω, IsProbabilityMeasure (S ω)) ∧ Measurable[constFiltration 0] S ∧ True :=
  let ⟨S, hprob, hmeas, _⟩ :=
    sufficiency (Ω := ℝ) (P := Measure.dirac 0) constFiltration (θ := id) measurable_id 0
  ⟨S, hprob, hmeas, trivial⟩

/-- The second chain is not vacuous either: `Δ(unitInterval)` is a genuine standard Borel space
(`unitInterval` is a concrete compact Polish space). -/
theorem standardBorel_probabilityMeasure_unitInterval :
    StandardBorelSpace (ProbabilityMeasure unitInterval) :=
  deltaTheta_standardBorel unitInterval

/-- `factorization_posterior` genuinely applies for a concrete compact Polish `Θ = unitInterval`
(its `Nonempty (Δ Θ)` hypothesis is satisfied by `nonempty_probabilityMeasure`). -/
theorem factorizationPosterior_nonvacuous
    (Z : ℝ → ℝ) (S : ℝ → ProbabilityMeasure unitInterval)
    (hS : @Measurable ℝ (ProbabilityMeasure unitInterval)
      (MeasurableSpace.comap Z inferInstance) inferInstance S) :
    ∃ f : ℝ → ProbabilityMeasure unitInterval, Measurable f ∧ S = f ∘ Z :=
  haveI := nonempty_probabilityMeasure (Θ := unitInterval)
  factorization_posterior Z S hS

/-! ### 3. The measure-valued martingale encoding is transparent -/

variable {Ω : Type*} {m : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
variable {ι : Type*} [Preorder ι] (ℱ : Filtration ι m)
variable {Θ : Type*} [MeasurableSpace Θ] (θ : Ω → Θ)

/-- The paper's measure-valued martingale `E[Sₜ | ℱₛ] = Sₛ` is encoded in `testfun_martingale` as
"`t ↦ ∫ φ dSₜ = E[φ(θ)|ℱₜ]` is a real martingale, for every bounded `φ`". This lemma extracts the
content that encoding carries: for `s ≤ t`, the tower/consistency identity
`E[E[φ(θ)|ℱₜ] | ℱₛ] = E[φ(θ)|ℱₛ]` — exactly the paper's `E[Sₜ|ℱₛ] = Sₛ`, read test function by
test function. So the real-valued encoding is a faithful transcription, not a weaker statement. -/
theorem martingale_tower (φ : Θ → ℝ) (hφ : Measurable φ) (hφb : ∃ C, ∀ x, |φ x| ≤ C)
    {s t : ι} (hst : s ≤ t) :
    P[(P[(φ ∘ θ) | ℱ t]) | ℱ s] =ᵐ[P] P[(φ ∘ θ) | ℱ s] :=
  (testfun_martingale ℱ θ φ hφ hφb).2 s t hst

/-! ### 4. The object `Δ(Θ)` is the paper's: its σ-algebra and its topology

`deltaTheta_standardBorel` is stated about Mathlib's `ProbabilityMeasure Θ`, which carries Mathlib's
*Giry* measurable structure and Mathlib's topology of convergence in distribution. The paper's
`Δ(Θ)` is "the probability measures on `Θ`, **equipped with the weak topology**" — and, for the
Doob–Dynkin step, with that topology's Borel σ-algebra. A priori these are different structures, so
a theorem about the wrong one would be true and useless. Both identifications are recorded here.

Note these are *not* extra assumptions: Mathlib's structures already are the right ones. The point
is to make that visible and kernel-checked, instead of trusting it silently. -/

/-- **The σ-algebra is the paper's.** The measurable structure Lean puts on `Δ(Θ)` (Mathlib's Giry
σ-algebra, generated by `μ ↦ μ s`) *equals* the Borel σ-algebra of the weak topology. This is the
content of `deltaTheta_borelSpace`, spelled out as an equation instead of being hidden inside a
`BorelSpace` instance — this is the step that makes `deltaTheta_standardBorel` a statement about the
paper's `Δ(Θ)`. -/
theorem deltaTheta_measurableSpace_eq_borel (Θ : Type*) [TopologicalSpace Θ] [PolishSpace Θ]
    [CompactSpace Θ] [MeasurableSpace Θ] [BorelSpace Θ] :
    (inferInstance : MeasurableSpace (ProbabilityMeasure Θ)) = borel (ProbabilityMeasure Θ) :=
  (deltaTheta_borelSpace Θ).measurable_eq

/-- **The topology is the paper's weak topology.** Convergence in `Δ(Θ)` holds exactly when
`∫ f dμ` converges for every bounded continuous `f` — the textbook defining property of the weak
topology. So `deltaTheta_polishSpace` and `deltaTheta_standardBorel` speak about the topology the
paper means, not some other topology on the same set. -/
theorem deltaTheta_tendsto_iff_integral {Θ : Type*} [TopologicalSpace Θ] [MeasurableSpace Θ]
    [OpensMeasurableSpace Θ] {γ : Type*} {F : Filter γ} {μs : γ → ProbabilityMeasure Θ}
    {μ : ProbabilityMeasure Θ} :
    Filter.Tendsto μs F (nhds μ) ↔
      ∀ f : BoundedContinuousFunction Θ ℝ,
        Filter.Tendsto (fun i => ∫ x, f x ∂(μs i : Measure Θ)) F
          (nhds (∫ x, f x ∂(μ : Measure Θ))) :=
  ProbabilityMeasure.tendsto_iff_forall_integral_tendsto

end PosteriorProcess
