import Mathlib.Probability.Process.Filtration
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Probability.Kernel.CondDistrib

/-!
# Lemma 1 (Posterior process): existence of the posterior kernel

Part of **Lemma 1 (Posterior process)** of the paper. The verbatim statement and proof are in
`docs/paper-lemma1.md` (the single source of truth).

This file states the existence of the posterior kernel together with its defining property:
there is an `ℱ t`-measurable kernel `S : Ω → Measure Θ` (each `S ω` a probability measure) such
that, for every bounded measurable `φ`, the map `ω ↦ ∫ φ dS(ω)` equals `E[φ(θ) | ℱ t]` almost
surely.

Mathematical basis: `Θ` compact Polish ⇒ standard Borel ⇒ regular conditional distributions
exist (Kallenberg 2002, Thm 6.3). The Lean proof realizes the kernel as Mathlib's
`ProbabilityTheory.condDistrib θ id P`, i.e. the regular conditional distribution of `θ` given
the sub-σ-algebra `ℱ t` — obtained by conditioning on the identity map `id : (Ω, m) → (Ω, ℱ t)`.
`condDistrib` needs only the *codomain* `Θ` to be standard Borel (matching the paper, which needs
only `Θ` Polish); the sample space `Ω` is left general. The single added hypothesis over the paper
is `[Nonempty Θ]` (the parameter space is nonempty), which `condDistrib` requires.
-/

open MeasureTheory ProbabilityTheory

namespace PosteriorProcess

variable {Ω : Type*} {m : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
variable {ι : Type*} [Preorder ι] (ℱ : Filtration ι m)
variable {Θ : Type*} [MeasurableSpace Θ] [StandardBorelSpace Θ] [Nonempty Θ] (θ : Ω → Θ)

/-- Existence of the posterior kernel (part of Lemma 1). For each time `t` there is an
`ℱ t`-measurable kernel `S` such that, for every bounded measurable `φ`, the map
`ω ↦ ∫ φ dS(ω)` equals `E[φ(θ) | ℱ t]` almost surely. The witness is the regular conditional
distribution `condDistrib θ id P` of `θ` given `ℱ t`. -/
theorem kernel_exists (hθ : Measurable θ) (t : ι) :
    ∃ S : Ω → Measure Θ,
      (∀ ω, IsProbabilityMeasure (S ω)) ∧
      Measurable[ℱ t] S ∧
      ∀ φ : Θ → ℝ, Measurable φ → (∃ C, ∀ x, |φ x| ≤ C) →
        (fun ω => ∫ x, φ x ∂(S ω)) =ᵐ[P] P[(φ ∘ θ) | ℱ t] := by
  -- Condition on `ℱ t` via the identity map `id : (Ω, m) → (Ω, ℱ t)`; the posterior kernel is the
  -- regular conditional distribution of `θ` given `ℱ t`.
  have hX : @Measurable Ω Ω m (ℱ t) id := measurable_id'' (ℱ.le t)
  refine ⟨fun ω => (@condDistrib Ω Ω Θ _ _ _ m (ℱ t) θ id P _) ω, ?_, ?_, ?_⟩
  · -- each fibre is a probability measure: `condDistrib` is a Markov kernel
    intro ω; infer_instance
  · -- measurability w.r.t. `ℱ t`: kernels are measurable into the space of measures
    exact Kernel.measurable _
  · intro φ hφ hφb
    obtain ⟨C, hC⟩ := hφb
    -- `φ ∘ θ` is bounded and measurable on a probability space, hence integrable
    have hint : Integrable (φ ∘ θ) P :=
      ⟨(hφ.comp hθ).aestronglyMeasurable,
        HasFiniteIntegral.of_bounded (C := C)
          (Filter.Eventually.of_forall fun ω => (Real.norm_eq_abs _).le.trans (hC (θ ω)))⟩
    have h := condExp_ae_eq_integral_condDistrib (μ := P) (X := (id : Ω → Ω)) (Y := θ)
      hX hθ.aemeasurable hφ.stronglyMeasurable hint
    simpa only [MeasurableSpace.comap_id, id_eq, Function.comp_def] using h.symm

end PosteriorProcess
