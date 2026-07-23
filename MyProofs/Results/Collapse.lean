import MyProofs.Results.NoGain

/-!
# Results (§3.2): collapse to a terminal mechanism, and the diagnostic

`prop:collapse-structure` (collapse criterion) and `cor:diagnostic` (the non-posterior gain region
`𝒩(S_0)`).

Both are read off `thm:nogain-delta-eps` (`Results/NoGain.lean`) applied with the richer state taken
to be the **full history** `𝒢_t = ℱ_t`. Two things happen at that specialization:

* The three conditions of `thm:nogain-delta-eps` collapse to two. `eq:terminal-support` is the
  richer-state cap `cond:richer-cap` for `ℱ_t`, and it *implies* the posterior support
  `cond:posterior-support`, because a richer conditioning only raises the envelope
  (`DateValues.envelope_mono`). This is exactly the reduction the paper's proof sketch performs.
* Collapse of the calendar at `S_0` is, by the value representation, the equality of the two
  concavified envelopes at the prior — the same left-hand side as no gain. We take that
  identification as the interface (it is `prop:value-representation`, not formalized here; see
  `Results/Representation.lean`), and formalize the criterion on the concavification equality.

## Modelling note on `𝒩(S_0)`

The paper writes `𝒩(S_0) = {(μ,r) : r > sup_λ ∫ λ dμ}`, "the supremum over continuous `λ` meeting
`cond:posterior-support` and `cond:tightness`" — a set the paper's own prose glosses as "the
belief-value pairs lying above **every** such price". We formalize the prose gloss
(`∀ l ∈ shadowSet, ∫ l dμ < r`) rather than the `sSup` form. The two agree whenever the price set
is nonempty and bounded above, and the prose form carries no junk value when it is not.

The tolerance `ε` is carried explicitly. The paper suppresses it in the display for `𝒩(S_0)` while
condition `cond:tightness` — which defines the admissible `λ` — depends on it (the figure labels
the set `L^ε(S_0)`), so `ε` is a parameter here.
-/

open MeasureTheory BeliefSpace

namespace DMC

variable {Θ : Type*} [TopologicalSpace Θ] [CompactSpace Θ] [MeasurableSpace Θ] [BorelSpace Θ]
  [TopologicalSpace.MetrizableSpace Θ]

/-- **`prop:collapse-structure` (collapse criterion).**

With the richer state taken to be the full history, the calendar collapses to a terminal mechanism
at `S₀` — i.e. the concavified full-history envelope equals the posterior-only one at the prior —
**iff** for every `ε > 0` there is a continuous shadow value `λ_ε : Θ → ℝ` satisfying

* `eq:terminal-support`: `U_t^{ℱ_t}(μ) ≤ ∫ λ_ε dμ` for all `μ ∈ Δ(Θ)` and all `t ∈ 𝕋`;
* `cond:tightness`: `∫ λ_ε dS₀ ≤ conc_f[sup_t U_t^{σ(S_t)}](S₀) + ε`.

Note that the posterior support `cond:posterior-support` of `thm:nogain-delta-eps` has disappeared:
it follows from `eq:terminal-support`, since `U_t^{σ(S_t)} ≤ U_t^{ℱ_t}`. This is the paper's remark
that "the richer-state cap implies the posterior support". -/
theorem collapse_iff_terminal_support (Dpost Dfull : DateValues Θ)
    (h : ∀ t μ, Dpost.U t μ ≤ Dfull.U t μ) (S₀ : ProbabilityMeasure Θ)
    (husc : UpperSemicontinuousOn
      (concF (Set.range (emb : ProbabilityMeasure Θ → E Θ)) (envelopeE Dfull))
      (Set.range emb)) :
    concFBelief Dfull.envelope S₀ = concFBelief Dpost.envelope S₀ ↔
      ∀ ε > 0, ∃ l : C(Θ, ℝ),
        (∀ (μ : ProbabilityMeasure Θ) (t : ℕ), Dfull.U t μ ≤ ∫ x, l x ∂(μ : Measure Θ)) ∧
        (∫ x, l x ∂(S₀ : Measure Θ) ≤ concFBelief Dpost.envelope S₀ + ε) := by
  rw [nogain_iff_shadow Dpost Dfull h S₀ husc]
  constructor
  · intro H ε hε
    obtain ⟨l, _, h2, h3⟩ := H ε hε
    exact ⟨l, fun μ t => (Dfull.le_envelope t μ).trans (h2 μ), h3⟩
  · intro H ε hε
    obtain ⟨l, h2, h3⟩ := H ε hε
    have hfull : ∀ μ : ProbabilityMeasure Θ,
        Dfull.envelope μ ≤ ∫ x, l x ∂(μ : Measure Θ) :=
      fun μ => (Dfull.envelope_le_iff μ _).2 (h2 μ)
    exact ⟨l, fun μ => (DateValues.envelope_mono h μ).trans (hfull μ), hfull, h3⟩

/-- `L^ε(S₀)`: the continuous shadow values admissible at tolerance `ε` — those meeting
`cond:posterior-support` (price no belief below the posterior-only benchmark `g`) and
`cond:tightness` (at the prior, cost at most the optimum up to `ε`). By construction this depends
only on `g` and `S₀`, not on the richer histories. -/
def shadowSet (Dpost : DateValues Θ) (S₀ : ProbabilityMeasure Θ) (ε : ℝ) : Set C(Θ, ℝ) :=
  {l | (∀ μ : ProbabilityMeasure Θ, Dpost.envelope μ ≤ ∫ x, l x ∂(μ : Measure Θ)) ∧
       ∫ x, l x ∂(S₀ : Measure Θ) ≤ concFBelief Dpost.envelope S₀ + ε}

/-- **The non-posterior gain region `𝒩(S₀)`**: the belief-value pairs lying strictly above every
admissible shadow price. Depends only on the posterior-only benchmark and the prior. -/
def gainRegion (Dpost : DateValues Θ) (S₀ : ProbabilityMeasure Θ) (ε : ℝ) :
    Set (ProbabilityMeasure Θ × ℝ) :=
  {p | ∀ l ∈ shadowSet Dpost S₀ ε, ∫ x, l x ∂((p.1 : ProbabilityMeasure Θ) : Measure Θ) < p.2}

/-- The set of admissible shadow prices at the belief `μ` — the set whose supremum the paper's
display for `𝒩(S₀)` takes. -/
def shadowPrices (Dpost : DateValues Θ) (S₀ : ProbabilityMeasure Θ) (ε : ℝ)
    (μ : ProbabilityMeasure Θ) : Set ℝ :=
  {r | ∃ l ∈ shadowSet Dpost S₀ ε, r = ∫ x, l x ∂(μ : Measure Θ)}

/-- **The gain region exactly as the paper displays it**: `r` strictly above the *supremum* of the
admissible prices. -/
def gainRegionSup (Dpost : DateValues Θ) (S₀ : ProbabilityMeasure Θ) (ε : ℝ) :
    Set (ProbabilityMeasure Θ × ℝ) :=
  {p | sSup (shadowPrices Dpost S₀ ε p.1) < p.2}

/-- **The two readings of `𝒩(S₀)` are compatible, and in the safe direction.** Wherever the price
set is bounded above — the only regime in which the paper's `sSup` display carries its intended
meaning — the literal `sSup` region is contained in the prose region ("above *every* such price").
They differ at most at `r = sup` with the supremum unattained, which the `sSup` form excludes and
the prose form includes.

Consequently a proof that a point avoids `gainRegion` is *stronger* than, and implies, the same
statement for the paper's `gainRegionSup` (`diagnostic_sSup`). -/
theorem gainRegionSup_subset_gainRegion (Dpost : DateValues Θ) (S₀ : ProbabilityMeasure Θ) (ε : ℝ)
    {p : ProbabilityMeasure Θ × ℝ} (hbdd : BddAbove (shadowPrices Dpost S₀ ε p.1))
    (hp : p ∈ gainRegionSup Dpost S₀ ε) : p ∈ gainRegion Dpost S₀ ε := by
  intro l hl
  exact lt_of_le_of_lt (le_csSup hbdd ⟨l, hl, rfl⟩) hp

/-- **`cor:diagnostic`.** If the full-history calendar collapses to a terminal mechanism at `S₀`,
then the full-history envelope `ĝ = sup_t U_t^{ℱ_t}` never enters the gain region: for every belief
`μ`, `(μ, ĝ(μ)) ∉ 𝒩(S₀)`.

The witness is immediate from the no-gain criterion: the shadow value it produces caps `ĝ` at
*every* belief, so `ĝ(μ)` fails to lie strictly above that one admissible price. Collapse therefore
fails as soon as `ĝ` enters `𝒩(S₀)` at some belief — the paper's diagnostic. -/
theorem diagnostic (Dpost Dfull : DateValues Θ)
    (h : ∀ t μ, Dpost.U t μ ≤ Dfull.U t μ) (S₀ : ProbabilityMeasure Θ)
    (husc : UpperSemicontinuousOn
      (concF (Set.range (emb : ProbabilityMeasure Θ → E Θ)) (envelopeE Dfull))
      (Set.range emb))
    (hcollapse : concFBelief Dfull.envelope S₀ = concFBelief Dpost.envelope S₀)
    {ε : ℝ} (hε : 0 < ε) (μ : ProbabilityMeasure Θ) :
    (μ, Dfull.envelope μ) ∉ gainRegion Dpost S₀ ε := by
  obtain ⟨l, h1, h2, h3⟩ := (nogain_iff_shadow Dpost Dfull h S₀ husc).1 hcollapse ε hε
  intro hmem
  exact absurd (hmem l ⟨h1, h3⟩) (not_lt.2 (h2 μ))

/-- **`cor:diagnostic`, stated with the paper's literal `sSup` gain region.** Follows from
`diagnostic` via `gainRegionSup_subset_gainRegion`, so nothing is lost by proving the stronger
prose form: the only extra hypothesis is that the price set is bounded above, which is exactly the
regime in which the paper's display means what it says. -/
theorem diagnostic_sSup (Dpost Dfull : DateValues Θ)
    (h : ∀ t μ, Dpost.U t μ ≤ Dfull.U t μ) (S₀ : ProbabilityMeasure Θ)
    (husc : UpperSemicontinuousOn
      (concF (Set.range (emb : ProbabilityMeasure Θ → E Θ)) (envelopeE Dfull))
      (Set.range emb))
    (hcollapse : concFBelief Dfull.envelope S₀ = concFBelief Dpost.envelope S₀)
    {ε : ℝ} (hε : 0 < ε) (μ : ProbabilityMeasure Θ)
    (hbdd : BddAbove (shadowPrices Dpost S₀ ε μ)) :
    (μ, Dfull.envelope μ) ∉ gainRegionSup Dpost S₀ ε := fun hmem =>
  diagnostic Dpost Dfull h S₀ husc hcollapse hε μ
    (gainRegionSup_subset_gainRegion Dpost S₀ ε hbdd hmem)

end DMC
