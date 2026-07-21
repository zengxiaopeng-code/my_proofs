import Mathlib.MeasureTheory.Function.FactorsThrough
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-!
# Lemma 1 (Posterior process): factorization through Z (Part (ii))

Part of **Lemma 1 (Posterior process)** of the paper. The verbatim statement and proof are in
`docs/paper-lemma1.md` (the single source of truth).

The formalization reveals that the paper's single sentence packs two independent facts:

1. Doob–Dynkin itself (`factorization`): `σ(Z)`-measurable + standard-Borel codomain ⇒
   factorization. Given by Mathlib's `Measurable.exists_eq_measurable_comp`. Proved (no `sorry`).
2. `Δ(Θ)` is standard Borel (`deltaTheta_standardBorel`), because `Θ` is compact Polish. This is
   a Mathlib gap: only `MetrizableSpace (ProbabilityMeasure Θ)` is available; the `PolishSpace`
   and `BorelSpace` instances (whose combination is StandardBorel) are missing. Not yet filled
   in (`sorry`).

`factorization_posterior` combines the two = the paper's `Δ(Θ)` version of Part (ii).
-/

open MeasureTheory

namespace PosteriorProcess

/-- Doob–Dynkin factorization (the abstract content of Part (ii); proved). If `S : Ω → Δ` is
measurable w.r.t. `σ(Z)` (`Z : Ω → E`) and the codomain `Δ` is a standard Borel space, then
`S = f ∘ Z` for some measurable `f : E → Δ`. Directly from Mathlib's Doob–Dynkin lemma. -/
theorem factorization {Ω E Δ : Type*} [MeasurableSpace E]
    [MeasurableSpace Δ] [StandardBorelSpace Δ] [Nonempty Δ]
    (Z : Ω → E) (S : Ω → Δ)
    (hS : @Measurable Ω Δ (MeasurableSpace.comap Z inferInstance) inferInstance S) :
    ∃ f : E → Δ, Measurable f ∧ S = f ∘ Z :=
  hS.exists_eq_measurable_comp

/-- Library gap (not yet filled in): `Θ` compact Polish ⇒ `Δ(Θ) = ProbabilityMeasure Θ` is
standard Borel. Needs the `PolishSpace` and `BorelSpace` instances for `ProbabilityMeasure` on
top of Mathlib's existing `MetrizableSpace (ProbabilityMeasure Θ)` — a small, self-contained
piece of infrastructure (a candidate upstream Mathlib contribution). -/
theorem deltaTheta_standardBorel (Θ : Type*) [TopologicalSpace Θ] [PolishSpace Θ]
    [CompactSpace Θ] [MeasurableSpace Θ] [BorelSpace Θ] :
    StandardBorelSpace (ProbabilityMeasure Θ) := by
  sorry

/-- Part (ii), full `Δ(Θ)` version: the abstract Doob–Dynkin factorization applied to the
posterior kernel `S : Ω → Δ(Θ)`. All logic is complete except the `deltaTheta_standardBorel`
gap; `Nonempty (Δ Θ)` is kept as a mild assumption. -/
theorem factorization_posterior {Ω E Θ : Type*} [MeasurableSpace E]
    [TopologicalSpace Θ] [PolishSpace Θ] [CompactSpace Θ] [MeasurableSpace Θ] [BorelSpace Θ]
    [Nonempty (ProbabilityMeasure Θ)]
    (Z : Ω → E) (S : Ω → ProbabilityMeasure Θ)
    (hS : @Measurable Ω (ProbabilityMeasure Θ) (MeasurableSpace.comap Z inferInstance)
      inferInstance S) :
    ∃ f : E → ProbabilityMeasure Θ, Measurable f ∧ S = f ∘ Z :=
  haveI := deltaTheta_standardBorel Θ
  factorization Z S hS

end PosteriorProcess
