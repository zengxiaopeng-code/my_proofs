import Mathlib.Probability.Process.Filtration
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-!
# Lemma 1 (Posterior process): existence of the posterior kernel

Part of **Lemma 1 (Posterior process)** of the paper. The verbatim statement and proof are in
`docs/paper-lemma1.md` (the single source of truth).

This file states the existence of the posterior kernel together with its defining property:
there is an `ℱ t`-measurable kernel `S : Ω → Measure Θ` (each `S ω` a probability measure) such
that, for every bounded measurable `φ`, the map `ω ↦ ∫ φ dS(ω)` equals `E[φ(θ) | ℱ t]` almost
surely.

Mathematical basis: `Θ` compact Polish ⇒ standard Borel ⇒ regular conditional distributions
exist (Kallenberg 2002, Thm 6.3), matching Mathlib's `ProbabilityTheory.condDistrib`. The proof
is not yet filled in (`sorry`).
-/

open MeasureTheory

namespace PosteriorProcess

variable {Ω : Type*} {m : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
variable {ι : Type*} [Preorder ι] (ℱ : Filtration ι m)
variable {Θ : Type*} [MeasurableSpace Θ] [StandardBorelSpace Θ] (θ : Ω → Θ)

/-- Existence of the posterior kernel (part of Lemma 1). For each time `t` there is an
`ℱ t`-measurable kernel `S` such that, for every bounded measurable `φ`, the map
`ω ↦ ∫ φ dS(ω)` equals `E[φ(θ) | ℱ t]` almost surely. Proof not yet filled in. -/
theorem kernel_exists (hθ : Measurable θ) (t : ι) :
    ∃ S : Ω → Measure Θ,
      (∀ ω, IsProbabilityMeasure (S ω)) ∧
      Measurable[ℱ t] S ∧
      ∀ φ : Θ → ℝ, Measurable φ → (∃ C, ∀ x, |φ x| ≤ C) →
        (fun ω => ∫ x, φ x ∂(S ω)) =ᵐ[P] P[(φ ∘ θ) | ℱ t] := by
  sorry

end PosteriorProcess
