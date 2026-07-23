import MyProofs.Foundations.PosteriorProcess

/-!
# Model (§2.1): environment and belief space

Abstract environment of the paper (§2.1, Timeline). Following the paper's own choice
(Assumption 2, analytic equilibrium), the dynamic game is treated as an **abstract axiomatization**:
we do not construct sequentially rational Bayesian equilibria from primitives; instead the
reduced-form continuation values are carried as data (see `Model/ContinuationValue.lean`) and the
game-theoretic assumptions are hypotheses.

* The primitive state space `Θ` is compact Polish; `Belief Θ = Δ(Θ)` is the space of probability
  measures with the weak topology. It is a compact standard Borel space
  (`PosteriorProcess.deltaTheta_standardBorel`, proved in `Foundations`).
* The posterior process `S_t : Ω → Δ(Θ)` is the `ℱ_t`-measurable martingale posterior kernel of
  `PosteriorProcess.kernel_exists` / `testfun_martingale` (Lemma `posterior-martingale`).
* Dates `t ∈ ℕ`; the allocation date is `τ ∈ {1,2,…} ∪ {∅}`, encoded as `Option ℕ` (`none = ∅`).
-/

open MeasureTheory

namespace DMC

/-- The **belief space** `Δ(Θ)`: probability measures on `Θ` with the weak topology. For `Θ` compact
Polish it is a compact standard Borel space (`deltaTheta_standardBorel`). -/
abbrev Belief (Θ : Type*) [MeasurableSpace Θ] := ProbabilityMeasure Θ

/-- The allocation date `τ ∈ {1,2,…} ∪ {∅}` (Timeline). `none` is `∅`: no sale ever occurs.

Dates are `{n : ℕ // 1 ≤ n}`, not `ℕ`: the paper's `τ` starts at **1**, so a plain `Option ℕ`
would admit a spurious `some 0` with no counterpart in the paper. -/
abbrev AllocDate := Option {n : ℕ // 1 ≤ n}

end DMC
