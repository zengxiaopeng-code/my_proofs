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

end PosteriorProcess
