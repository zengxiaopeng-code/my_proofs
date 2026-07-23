import MyProofs.Foundations.Concavification
import MyProofs.Foundations.BeliefSpace
import MyProofs.Model.ContinuationValue

/-!
# Results (§3.1): the No-gain theorem

`thm:nogain-delta-eps`: a richer public state adds no ex-ante value at the prior iff an affine
shadow value `λ_ε ∈ C(Θ)` supports the posterior benchmark at `S_0` and majorizes every
continuation value.

This file instantiates the abstract convex-analysis core `nogain_iff`
(`Foundations/Concavification.lean`) on the belief space `Δ(Θ)`, embedded via `emb` into
`E = WeakDual ℝ C(Θ,ℝ)` (`Foundations/BeliefSpace.lean`), with `g`/`ĝ` the reduced-form envelopes
of two `DateValues` instances (`Model/ContinuationValue.lean`).

**Stage 3.1 (this commit): the pullback interface.** The paper's envelopes `g, ĝ : Δ(Θ) → ℝ` are
carried to functions on `E` by `envelopeE` (agreeing with the envelope on the embedded `K`, `0`
off it), and the three facts the abstract theorem needs — real value on `K`, boundedness on `K`,
and monotonicity `g ≤ ĝ` on `K` — are transported through `emb`.
-/

open MeasureTheory BeliefSpace

namespace DMC

variable {Θ : Type*} [TopologicalSpace Θ] [CompactSpace Θ] [MeasurableSpace Θ] [BorelSpace Θ]
  [TopologicalSpace.MetrizableSpace Θ]

/-- Carry an envelope `g : Δ(Θ) → ℝ` to a function on the ambient space `E`, equal to `g ∘ emb⁻¹`
on the embedded belief space `K = Set.range emb` and `0` off it. Since `emb` is injective this is a
genuine extension: `envelopeE D (emb μ) = D.envelope μ` (`envelopeE_emb`). -/
noncomputable def envelopeE (D : DateValues Θ) : E Θ → ℝ :=
  Function.extend emb D.envelope (fun _ => 0)

/-- On the embedded belief space, `envelopeE` reproduces the paper's envelope. -/
theorem envelopeE_emb (D : DateValues Θ) (μ : ProbabilityMeasure Θ) :
    envelopeE D (emb μ) = D.envelope μ :=
  emb_injective.extend_apply _ _ μ

/-- On `K`, the pulled-back envelope inherits the uniform bound on `U` (so it is real-valued and
bounded above there — what `concf-conc`/`nogain_iff` need). -/
theorem envelopeE_le_on_range (D : DateValues Θ) {M : ℝ} (hM : ∀ t μ, D.U t μ ≤ M)
    {x : E Θ} (hx : x ∈ Set.range (emb : ProbabilityMeasure Θ → E Θ)) :
    envelopeE D x ≤ M := by
  obtain ⟨μ, rfl⟩ := hx
  rw [envelopeE_emb]
  exact D.envelope_le hM μ

/-- On `K`, a richer conditioning raises the pulled-back envelope: the `g ≤ ĝ` of §3, transported
to `E`. -/
theorem envelopeE_mono_on_range {Dpost Drich : DateValues Θ}
    (h : ∀ t μ, Dpost.U t μ ≤ Drich.U t μ)
    {x : E Θ} (hx : x ∈ Set.range (emb : ProbabilityMeasure Θ → E Θ)) :
    envelopeE Dpost x ≤ envelopeE Drich x := by
  obtain ⟨μ, rfl⟩ := hx
  rw [envelopeE_emb, envelopeE_emb]
  exact DateValues.envelope_mono h μ

/-- The paper's finite concavification `conc_f q` **on the belief space**: the supremum of
`∑ᵢ wᵢ q(νᵢ)` over finite Bayes-plausible splits `∑ᵢ wᵢ νᵢ = μ`. This is stated directly in terms of
beliefs, with no reference to the ambient space `E`. -/
noncomputable def concFBelief (q : ProbabilityMeasure Θ → ℝ) (μ : ProbabilityMeasure Θ) : ℝ :=
  sSup {v | ∃ (n : ℕ) (w : Fin n → ℝ) (ν : Fin n → ProbabilityMeasure Θ),
    (∀ i, 0 ≤ w i) ∧ (∑ i, w i = 1) ∧ (mixFinMeasure w ν = (μ : Measure Θ)) ∧
    v = ∑ i, w i * q (ν i)}

/-- **Transparency (definition-level faithfulness).** The abstract `concF` on `K = Set.range emb`,
read at an embedded belief, *is* the paper's belief-space finite concavification `conc_f`. Finite
convex-combination splits in `E` with points in `K` correspond exactly to finite Bayes-plausible
splits of beliefs: `emb_mixFin` sends belief splits to `E`-splits, and `emb_injective` sends
`E`-splits back. This is what licenses reading `concF … (emb μ)` as the paper's `conc_f`. -/
theorem concF_emb_eq_concFBelief (D : DateValues Θ) (μ : ProbabilityMeasure Θ) :
    concF (Set.range (emb : ProbabilityMeasure Θ → E Θ)) (envelopeE D) (emb μ)
      = concFBelief D.envelope μ := by
  unfold concF concFBelief
  congr 1
  ext v
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨n, w, z, hw0, hw1, hzK, hbary, rfl⟩
    choose ν hν using hzK
    have hz : ∀ i, z i = emb (ν i) := fun i => (hν i).symm
    have h1 : emb (mixFin w hw0 hw1 ν) = emb μ := by
      rw [emb_mixFin, ← hbary]
      exact Finset.sum_congr rfl (fun i _ => by rw [hz i])
    refine ⟨n, w, ν, hw0, hw1, ?_, ?_⟩
    · exact congrArg (fun ρ : ProbabilityMeasure Θ => (ρ : Measure Θ)) (emb_injective h1)
    · exact Finset.sum_congr rfl (fun i _ => by rw [hz i, envelopeE_emb])
  · rintro ⟨n, w, ν, hw0, hw1, hmix, rfl⟩
    refine ⟨n, w, fun i => emb (ν i), hw0, hw1, fun i => ⟨ν i, rfl⟩, ?_, ?_⟩
    · rw [← emb_mixFin w hw0 hw1 ν]
      exact congrArg emb (Subtype.ext hmix)
    · exact Finset.sum_congr rfl (fun i _ => by rw [envelopeE_emb])

/-- **No-gain on the belief space (`thm:nogain-delta-eps`, abstract-shadow form).** For a
posterior-only `Dpost` and a richer `Drich` with `U_post ≤ U_rich`, the richer conditioning yields
**no additional value at the prior `S₀`** — equal finite concavifications of the two envelopes at
`emb S₀` — **iff** for every `ε > 0` a single continuous affine functional `f + c` on `E` caps both
envelopes on `K` and is `ε`-tight against `concF (envelopeE Dpost)` at `emb S₀`.

This is `nogain_iff` instantiated on `K = Set.range emb` (convex + closed, `E` locally convex), with
`g = envelopeE Dpost ≤ ĝ = envelopeE Drich`. The upper-semicontinuity hypothesis `husc` is the
paper's Assumption `regularity`. The shadow value is still a bare `f : E →L[ℝ] ℝ`; identifying it
with the paper's `∫ λ dμ` (`λ ∈ C(Θ)`) is the next step. -/
theorem nogain_belief (Dpost Drich : DateValues Θ)
    (h : ∀ t μ, Dpost.U t μ ≤ Drich.U t μ) (S₀ : ProbabilityMeasure Θ)
    (husc : UpperSemicontinuousOn
      (concF (Set.range (emb : ProbabilityMeasure Θ → E Θ)) (envelopeE Drich))
      (Set.range emb)) :
    concF (Set.range emb) (envelopeE Drich) (emb S₀)
        = concF (Set.range emb) (envelopeE Dpost) (emb S₀) ↔
      ∀ ε > 0, ∃ (f : E Θ →L[ℝ] ℝ) (c : ℝ),
        (∀ y ∈ Set.range (emb : ProbabilityMeasure Θ → E Θ), envelopeE Dpost y ≤ f y + c) ∧
        (∀ y ∈ Set.range (emb : ProbabilityMeasure Θ → E Θ), envelopeE Drich y ≤ f y + c) ∧
        (f (emb S₀) + c ≤ concF (Set.range emb) (envelopeE Dpost) (emb S₀) + ε) := by
  obtain ⟨M, hM⟩ := Drich.U_bddAbove
  exact nogain_iff (Set.range emb) convex_range_emb isClosed_range_emb
    (envelopeE Dpost) (envelopeE Drich)
    (fun y hy => envelopeE_le_on_range Dpost (fun t μ => (h t μ).trans (hM t μ)) hy)
    (fun y hy => envelopeE_le_on_range Drich hM hy)
    (fun y hy => envelopeE_mono_on_range h hy)
    ⟨S₀, rfl⟩ husc

/-- **No-gain, stated with the paper's own belief-space objects (`thm:nogain-delta-eps`).**

Same content as `nogain_belief`, but the concavifications are the paper's `concFBelief` (sup over
finite Bayes-plausible splits, `concF_emb_eq_concFBelief`) and the caps are quantified over beliefs
`μ ∈ Δ(Θ)` rather than over the embedded set `K`. The shadow value is still a continuous linear
`f` on `E` read at `emb μ`; rewriting `f (emb μ)` as the paper's `∫ λ dμ` is the remaining step. -/
theorem nogain_belief_conc (Dpost Drich : DateValues Θ)
    (h : ∀ t μ, Dpost.U t μ ≤ Drich.U t μ) (S₀ : ProbabilityMeasure Θ)
    (husc : UpperSemicontinuousOn
      (concF (Set.range (emb : ProbabilityMeasure Θ → E Θ)) (envelopeE Drich))
      (Set.range emb)) :
    concFBelief Drich.envelope S₀ = concFBelief Dpost.envelope S₀ ↔
      ∀ ε > 0, ∃ (f : E Θ →L[ℝ] ℝ) (c : ℝ),
        (∀ μ : ProbabilityMeasure Θ, Dpost.envelope μ ≤ f (emb μ) + c) ∧
        (∀ μ : ProbabilityMeasure Θ, Drich.envelope μ ≤ f (emb μ) + c) ∧
        (f (emb S₀) + c ≤ concFBelief Dpost.envelope S₀ + ε) := by
  rw [← concF_emb_eq_concFBelief Drich S₀, ← concF_emb_eq_concFBelief Dpost S₀,
    nogain_belief Dpost Drich h S₀ husc]
  constructor
  · intro H ε hε
    obtain ⟨f, c, h1, h2, h3⟩ := H ε hε
    exact ⟨f, c, fun μ => by simpa [envelopeE_emb] using h1 (emb μ) ⟨μ, rfl⟩,
      fun μ => by simpa [envelopeE_emb] using h2 (emb μ) ⟨μ, rfl⟩, h3⟩
  · intro H ε hε
    obtain ⟨f, c, h1, h2, h3⟩ := H ε hε
    refine ⟨f, c, ?_, ?_, h3⟩
    · rintro _ ⟨μ, rfl⟩; simpa [envelopeE_emb] using h1 μ
    · rintro _ ⟨μ, rfl⟩; simpa [envelopeE_emb] using h2 μ

/-- **No-gain, sufficiency direction — verbatim in the paper's own terms (`thm:nogain-delta-eps`).**

If for every `ε > 0` there is a continuous **shadow value** `λ ∈ C(Θ,ℝ)` such that

* `sup_t U_t^post(μ) ≤ ∫ λ dμ` for all beliefs `μ` (*posterior support*),
* `sup_t U_t^rich(μ) ≤ ∫ λ dμ` for all beliefs `μ` (*richer-state cap*),
* `∫ λ dS₀ ≤ conc_f[sup_t U_t^post](S₀) + ε` (*tightness at the prior*),

then the richer public state generates **no additional value at the prior**.

Every object here is the paper's: beliefs in `Δ(Θ)`, the shadow value as `∫ λ dμ` with
`λ ∈ C(Θ)`, and `conc_f` as `concFBelief`. The bridge is `evalCLM`, which turns `∫ λ d·` into the
continuous linear functional on `E` that `nogain_belief_conc` consumes. -/
theorem nogain_of_shadow (Dpost Drich : DateValues Θ)
    (h : ∀ t μ, Dpost.U t μ ≤ Drich.U t μ) (S₀ : ProbabilityMeasure Θ)
    (husc : UpperSemicontinuousOn
      (concF (Set.range (emb : ProbabilityMeasure Θ → E Θ)) (envelopeE Drich))
      (Set.range emb))
    (H : ∀ ε > 0, ∃ l : C(Θ, ℝ),
      (∀ μ : ProbabilityMeasure Θ, Dpost.envelope μ ≤ ∫ x, l x ∂(μ : Measure Θ)) ∧
      (∀ μ : ProbabilityMeasure Θ, Drich.envelope μ ≤ ∫ x, l x ∂(μ : Measure Θ)) ∧
      (∫ x, l x ∂(S₀ : Measure Θ) ≤ concFBelief Dpost.envelope S₀ + ε)) :
    concFBelief Drich.envelope S₀ = concFBelief Dpost.envelope S₀ := by
  rw [nogain_belief_conc Dpost Drich h S₀ husc]
  intro ε hε
  obtain ⟨l, h1, h2, h3⟩ := H ε hε
  refine ⟨evalCLM l, 0, ?_, ?_, ?_⟩
  · intro μ; simpa using h1 μ
  · intro μ; simpa using h2 μ
  · simpa using h3

end DMC
