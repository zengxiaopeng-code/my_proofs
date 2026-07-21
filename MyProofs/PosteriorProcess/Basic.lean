import Mathlib.MeasureTheory.Measure.MeasureSpace

/-!
# Lemma 1 (Posterior process): shared setup

The folder `PosteriorProcess/` corresponds to **Lemma 1 (Posterior process)** of the paper
(`\label{lem:posterior-martingale}`). It is split into one file per part:

- `Existence.lean` — existence + kernel property — `PosteriorProcess.kernel_exists`
- `Sufficiency.lean` — Part (i), sufficiency — (not yet stated)
- `DoobDynkin.lean` — Part (ii), Doob–Dynkin factorization — `PosteriorProcess.factorization`
- `Martingale.lean` — Part (iii), martingale property — `PosteriorProcess.testfun_martingale`

Paper objects and their Mathlib modelling:

- `(Ω, ℱ, ℙ)` — `[MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]`
- `t ∈ 𝕋` — `{ι : Type*} [Preorder ι]`
- filtration `(ℱ_t)` — `(ℱ : MeasureTheory.Filtration ι m)`
- `Θ` (compact Polish) — `[MeasurableSpace Θ] [StandardBorelSpace Θ]`
- `θ : Ω → Θ` — `(θ : Ω → Θ)`, `Measurable θ`
- posterior kernel `S_t : Ω → Δ(Θ)` — `Ω → Measure Θ` (each point a probability measure)
- `φ : Θ → ℝ` (bounded Borel) — `(φ : Θ → ℝ)`, `Measurable φ` + bounded
- `E[φ(θ) | ℱ_t]` — `P[(φ ∘ θ) | ℱ t]`

Each proof file re-declares the `variable`s it needs (Lean `variable`s do not cross files).
-/

open MeasureTheory

namespace PosteriorProcess

end PosteriorProcess
