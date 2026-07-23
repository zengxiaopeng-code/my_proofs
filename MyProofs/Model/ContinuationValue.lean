import MyProofs.Model.Basic

/-!
# Model (§2.2): continuation and truncation values

The reduced-form interface the belief-space theorems consume. The paper builds `U_t^𝒢(μ)`
(continuation value) and `V_t^𝒢(μ)` (truncation value) as suprema over `𝒢`-measurable continuation
mechanisms and universally measurable equilibrium payoff selections (Assumption 2 supplies the
descriptive-set machinery: `lem:selection-exists`, `lem:measurable-lifting`,
`lem:sequential-pasting`). We take that construction as given, packaged as `DateValues`.

* `DateValues Θ` bundles, for one conditioning richness `𝒢`, the functions `U, V : ℕ → Δ(Θ) → ℝ`
  with the properties actually used downstream: `V ≥ 0`, `V ≤ U` (deferral is an option), and
  `U` uniformly bounded above (Assumption 2(iv): equilibrium values are finite).
* `DateValues.envelope` is the paper's date-wise upper envelope `g(μ) := sup_t U_t(μ)`
  (resp. `ĝ`). The No-gain theorem compares a posterior-only `g` with a richer `ĝ ≥ g`.

The single-shot stopping recursion linking `U` and `V` (`lem:stopping-form`) lives in
`Model/SingleShot.lean`.
-/

open MeasureTheory

namespace DMC

/-- Reduced-form continuation and truncation values at each date, for **one** conditioning richness
`𝒢` (e.g. posterior-only `σ(S_t)`, or full-history `σ(Z_t)`). Instantiated once per richness; the
No-gain comparison uses two instances with `U_post ≤ U_rich`. -/
structure DateValues (Θ : Type*) [MeasurableSpace Θ] where
  /-- Continuation value `U_t(μ)`: the seller's maximal conditional expected equilibrium payoff at
  posterior `μ` and date `t`. -/
  U : ℕ → ProbabilityMeasure Θ → ℝ
  /-- Truncation value `V_t(μ)`: the static within-date value (the truncated subgame). -/
  V : ℕ → ProbabilityMeasure Θ → ℝ
  /-- Truncation values are nonnegative (the absorbing no-sale node yields payoff `0`). -/
  V_nonneg : ∀ t μ, 0 ≤ V t μ
  /-- The truncation value never exceeds the continuation value: deferring is an option. -/
  V_le_U : ∀ t μ, V t μ ≤ U t μ
  /-- Equilibrium values are finite: `U` is uniformly bounded above (Assumption 2(iv)). -/
  U_bddAbove : ∃ M, ∀ t μ, U t μ ≤ M

variable {Θ : Type*} [MeasurableSpace Θ]

/-- The date-wise upper envelope `g(μ) := sup_t U_t(μ)` (the paper's `g`, resp. `ĝ`). -/
noncomputable def DateValues.envelope (D : DateValues Θ) (μ : ProbabilityMeasure Θ) : ℝ :=
  ⨆ t : ℕ, D.U t μ

/-- The envelope is bounded above by any uniform bound on `U`. -/
theorem DateValues.envelope_le (D : DateValues Θ) {M : ℝ} (hM : ∀ t μ, D.U t μ ≤ M)
    (μ : ProbabilityMeasure Θ) : D.envelope μ ≤ M :=
  ciSup_le fun t => hM t μ

/-- Each date's continuation value is below the envelope. -/
theorem DateValues.le_envelope (D : DateValues Θ) (t : ℕ) (μ : ProbabilityMeasure Θ) :
    D.U t μ ≤ D.envelope μ := by
  obtain ⟨M, hM⟩ := D.U_bddAbove
  exact le_ciSup (f := fun t => D.U t μ) ⟨M, by rintro _ ⟨t, rfl⟩; exact hM t μ⟩ t

/-- A cap holds for the envelope exactly when it holds date by date. This is what lets the paper's
conditions — written date-wise as `U_t(μ) ≤ ∫ λ dμ` — be read off the envelope `g = sup_t U_t`, and
conversely. -/
theorem DateValues.envelope_le_iff (D : DateValues Θ) (μ : ProbabilityMeasure Θ) (c : ℝ) :
    D.envelope μ ≤ c ↔ ∀ t, D.U t μ ≤ c :=
  ⟨fun h t => (D.le_envelope t μ).trans h, fun h => ciSup_le h⟩

/-- A **richer** conditioning weakly raises the envelope: if `U_post ≤ U_rich` date by date, then
`g = envelope U_post ≤ ĝ = envelope U_rich`. This is the `g ≤ ĝ` used throughout §3. -/
theorem DateValues.envelope_mono {Dpost Drich : DateValues Θ}
    (h : ∀ t μ, Dpost.U t μ ≤ Drich.U t μ) (μ : ProbabilityMeasure Θ) :
    Dpost.envelope μ ≤ Drich.envelope μ :=
  ciSup_le fun t => (h t μ).trans (Drich.le_envelope t μ)

end DMC
