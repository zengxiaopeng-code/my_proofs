import MyProofs.PosteriorProcess.Existence

/-!
# Lemma 1 (Posterior process): sufficiency (Part (i))

Part of **Lemma 1 (Posterior process)** of the paper. The verbatim statement and proof are in
`docs/paper-lemma1.md` (the single source of truth).

Planned Lean statement (to be filled in once the existence node yields a concrete kernel `S`):
for every bounded measurable `φ`,
  `P[(φ ∘ θ) | ℱ t] =ᵐ[P] P[(φ ∘ θ) | MeasurableSpace.comap S inferInstance]`.

Proof idea: the paper's main text shows `F(μ) := ∫ φ dμ` is Borel measurable on `Δ(Θ)` by the
functional monotone class theorem, whence uniqueness of conditional expectation gives the
equality of the two conditional expectations.
-/

open MeasureTheory

namespace PosteriorProcess

-- TODO: state and prove sufficiency here once `kernel_exists` yields a concrete kernel object.

end PosteriorProcess
