import MyProofs.Model.ContinuationValue
import Mathlib.Topology.ContinuousMap.Basic

/-!
# Model: single-shot resource (Assumption 1)

Assumption 1 (single-shot resource) is formalized through its operative content: with a single-shot
resource the allocation is a stopping decision, and the continuation value obeys the stopping-form
recursion (`lem:stopping-form`)
`U_t(μ) = max{ V_t(μ), 𝔼[U_{t+1}(S_{t+1}) | S_t = μ] }`.

Following the abstract-axiomatization plan, the expected next-date value is carried as an abstract
conditional-expectation operator `condExp` with the two properties the paper actually uses:

* **monotonicity** (`condExp` is a positive Markov operator), and
* **belief martingale / Bayes-plausibility** (`affine_harmonic`): affine functionals of the belief
  `ν ↦ ∫ λ dν` are harmonic, i.e. their expected next value equals their current value. This is the
  operative form of the posterior-martingale property (Lemma `posterior-martingale`,
  `PosteriorProcess.testfun_martingale`).

The one-step consequences here are the inductive core of the affine-certificate reduction
`lem:cap-equiv`; the full reduction (a supremum over stopping times / optional sampling) is a
`Results/CriterionTransform` concern.
-/

open MeasureTheory

namespace DMC

/-- **Single-shot structure.** A `DateValues` together with the belief-martingale conditional
expectation operator and the single-shot stopping recursion (Assumption 1). -/
structure SingleShot (Θ : Type*) [TopologicalSpace Θ] [MeasurableSpace Θ]
    extends DateValues Θ where
  /-- `condExp φ t μ = 𝔼[φ(S_{t+1}) | S_t = μ]`: the expected next-date value of a belief functional
  `φ` given the current belief `μ` at date `t`. -/
  condExp : (ProbabilityMeasure Θ → ℝ) → ℕ → ProbabilityMeasure Θ → ℝ
  /-- The operator is monotone: it is a positive Markov operator. -/
  condExp_mono : ∀ {φ ψ : ProbabilityMeasure Θ → ℝ}, (∀ ν, φ ν ≤ ψ ν) →
    ∀ t μ, condExp φ t μ ≤ condExp ψ t μ
  /-- **Belief martingale** (Bayes-plausibility): the affine functional `ν ↦ ∫ λ dν` of a continuous
  `λ` is harmonic — its expected next value equals its current value. -/
  affine_harmonic : ∀ (l : C(Θ, ℝ)) (t : ℕ) (μ : ProbabilityMeasure Θ),
    condExp (fun ν => ∫ x, l x ∂(ν : Measure Θ)) t μ = ∫ x, l x ∂(μ : Measure Θ)
  /-- **Single-shot stopping recursion** (`lem:stopping-form`): at each date the seller either
  allocates now (value `V_t`) or defers (value `𝔼[U_{t+1} | μ]`), whichever is larger. -/
  stopping : ∀ t μ, U t μ = max (V t μ) (condExp (U (t + 1)) t μ)

variable {Θ : Type*} [TopologicalSpace Θ] [MeasurableSpace Θ]
  (D : SingleShot Θ) (l : C(Θ, ℝ)) (t : ℕ) (μ : ProbabilityMeasure Θ)

/-- One step: an affine price dominating `U_{t+1}` everywhere dominates the deferral value at date
`t` (monotonicity + harmonicity of the affine price). -/
theorem SingleShot.condExp_affine_le
    (h : ∀ ν, D.U (t + 1) ν ≤ ∫ x, l x ∂(ν : Measure Θ)) :
    D.condExp (D.U (t + 1)) t μ ≤ ∫ x, l x ∂(μ : Measure Θ) :=
  (D.condExp_mono h t μ).trans (D.affine_harmonic l t μ).le

/-- One inductive step of `lem:cap-equiv`: if an affine price caps the truncation value `V` at date
`t` and caps the continuation value `U` at date `t+1`, then it caps `U` at date `t`. Iterating this
along stopping times (in `Results/CriterionTransform`) yields the full affine-certificate reduction:
an affine price caps `U` at all dates iff it caps `V` at all dates. -/
theorem SingleShot.stopping_affine_le
    (hV : D.V t μ ≤ ∫ x, l x ∂(μ : Measure Θ))
    (hU1 : ∀ ν, D.U (t + 1) ν ≤ ∫ x, l x ∂(ν : Measure Θ)) :
    D.U t μ ≤ ∫ x, l x ∂(μ : Measure Θ) := by
  rw [D.stopping]
  exact max_le hV (D.condExp_affine_le l t μ hU1)

end DMC
