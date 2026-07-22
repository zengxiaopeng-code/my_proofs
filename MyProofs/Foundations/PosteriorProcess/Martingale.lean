import Mathlib.Probability.Martingale.Basic

/-!
# Lemma 1 (Posterior process): the martingale property (Part (iii))

Part of **Lemma 1 (Posterior process)** of the paper. The verbatim statement and proof are in
`docs/paper-lemma1.md` (the single source of truth).

Modelling choices (needed for the formalization to be faithful to the paper):

1. The measure-valued martingale `E[S_t | ℱ_s] = S_s` is encoded as: for every bounded Borel
   `φ`, the real-valued process `t ↦ ∫ φ dS_t` is a martingale. This is exactly the rigorous
   content given in the paper's main text (`Δ(Θ)` is not a vector space, so the conditional
   expectation is read test-function by test-function).
2. The filtration `ℱ_t` is used directly, not specialized to `σ(Z_t)` — irrelevant to the
   martingale property (`σ(Z_t)` is only used in Part (ii)).
3. Boundedness of `φ` is not used here (the conditional-expectation process is a martingale for
   any integrable function); it is kept to stay faithful to the paper.
-/

open MeasureTheory

namespace PosteriorProcess

variable {Ω : Type*} {m : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
variable {ι : Type*} [Preorder ι] (ℱ : Filtration ι m)
variable {Θ : Type*} [MeasurableSpace Θ] (θ : Ω → Θ)

/-- Martingale property (Part (iii) of Lemma 1), for a fixed test function `φ`: the real-valued
posterior process `t ↦ ∫ φ dSₜ = E[φ(θ) | ℱ_t]` is an `ℱ`-martingale. -/
theorem testfun_martingale
    (φ : Θ → ℝ) (_hφ : Measurable φ) (_hφb : ∃ C, ∀ x, |φ x| ≤ C) :
    Martingale (fun t => P[(φ ∘ θ) | ℱ t]) ℱ P :=
  martingale_condExp (φ ∘ θ) ℱ P

end PosteriorProcess
