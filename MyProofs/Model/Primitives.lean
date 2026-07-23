import MyProofs.Model.ContinuationValue

/-!
# Model (§2): the paper's primitives, with `U_t` as a **definition**

The rest of the `Model` layer takes the continuation value `U_t` as opaque data (`DateValues`).
The paper does not: it *defines* (§2.2, "Continuation value")

`U_t^𝒢(μ) := sup { ∫_Ω ρ dP_t^μ : Γ is 𝒢-measurable, ρ ∈ Sel(𝓡_t^Γ) }`.

This file restores that definition by putting the abstraction boundary **where the paper puts it**.
The paper never constructs the strategy-belief profiles `𝓑_t`, the sequentially rational Bayesian
equilibria `𝓔_t`, or the payoff `π_t`; it constrains them via Assumption 2 (analytic equilibrium)
and then works entirely with the induced payoff correspondence `𝓡_t^{Γ_t}`. So `R = 𝓡` is a
*parameter* here, and everything above it is defined or proved.

What this buys — each was previously an **axiom field** of `DateValues`:

* `U_bddAbove_of_bound` — Assumption 2(iv) ("equilibrium values are finite") now *implies* the
  uniform bound on `U`. The paper assumes boundedness of `𝓡_t^Γ`; `DateValues` assumed it directly
  on `U`, one level too high.
* `U_mono_of_le` — the paper's "allowing richer public states expands each date-`t` continuation
  value `U_t`" (§2.3) is now a **theorem**: a larger conditioning σ-algebra admits more mechanism
  rules, so the supremum runs over a larger set. Previously this was a bare hypothesis (the
  argument of `DateValues.envelope_mono`) — the single largest faithfulness hole in the model layer.
* `AdmissibleRichness` / `ValueCollapse` — the paper's `Z_t = (S_t, Y_t)` decomposition and the
  sandwich `σ(S_t) ⊆ 𝒢 ⊆ σ(S_t, Y_t)` are expressible verbatim (`MeasurableSpace Ω` is an order),
  so *continuation value collapse* — the notion in the paper's title — can finally be **stated**.

Deviations, stated honestly (verbatim source: `docs/paper-model.md`):

* `[deviation]` `Sel` uses Borel measurability where the paper uses *universally* measurable
  selections. This shrinks the feasible set, so the `U` defined here is `≤` the paper's.
* `[assumed]` Existence of a measurable, integrable selection is a hypothesis (`hsel`); the paper
  derives it from Assumption 2(i)–(iii) via `lem:selection-exists`, not yet formalized.
* Integrability is required explicitly in the feasible set; the paper leaves it implicit.

`mH` is passed as an *explicit* argument rather than an instance: `Ω` already carries an ambient
`MeasurableSpace`, and the whole point here is to vary a *second* σ-algebra `𝒢` on `Ω`, so relying
on typeclass synthesis for measurability of `Γ` is ambiguous.
-/

open MeasureTheory

namespace DMC
namespace Paper

variable {Ω Θ : Type*} [MeasurableSpace Ω] [MeasurableSpace Θ]
variable {H : ℕ → Type*}

/-- A conditioning σ-algebra on `Ω`, **wrapped in a structure on purpose**: a bare local of type
`MeasurableSpace Ω` is treated by Lean as an instance candidate, so it would silently outrank the
ambient `MeasurableSpace Ω` everywhere below. Wrapping keeps `𝒢` out of typeclass synthesis. -/
structure Richness (Ω : Type*) where
  /-- The underlying σ-algebra (the paper's `𝒢`). -/
  σ : MeasurableSpace Ω

/-- The paper's `Sel(𝓡_t^{Γ_t})`: the payoff selections of the date-`t` payoff correspondence
induced by the continuation mechanism rule `Γ`. `[deviation]` Borel- rather than universally
measurable (see the module docstring). -/
def Sel (R : ∀ t, (Ω → H t) → Ω → Set ℝ) (t : ℕ) (Γ : Ω → H t) : Set (Ω → ℝ) :=
  {ρ | Measurable ρ ∧ ∀ ω, ρ ω ∈ R t Γ ω}

variable (mH : ∀ t, MeasurableSpace (H t))
variable (R : ∀ t, (Ω → H t) → Ω → Set ℝ)
variable (Rtrunc : ∀ t, (Ω → H t) → Ω → Set ℝ)
variable (Pcond : ℕ → ProbabilityMeasure Θ → Measure Ω)

/-- The set the paper's supremum ranges over: the conditional expected payoffs `∫ ρ dP_t^μ`
attainable by a `𝒢`-measurable mechanism rule `Γ` together with a selection `ρ ∈ Sel(𝓡_t^Γ)`. -/
def feasible (𝒢 : Richness Ω) (t : ℕ) (μ : ProbabilityMeasure Θ) : Set ℝ :=
  {r | ∃ (Γ : Ω → H t) (ρ : Ω → ℝ), @Measurable Ω (H t) 𝒢.σ (mH t) Γ ∧ ρ ∈ Sel R t Γ ∧
        Integrable ρ (Pcond t μ) ∧ r = ∫ ω, ρ ω ∂(Pcond t μ)}

/-- **The paper's continuation value** (§2.2), as a definition rather than opaque data:
`U_t^𝒢(μ) := sup { ∫ ρ dP_t^μ : Γ is 𝒢-measurable, ρ ∈ Sel(𝓡_t^Γ) }`. -/
noncomputable def U (𝒢 : Richness Ω) (t : ℕ) (μ : ProbabilityMeasure Θ) : ℝ :=
  sSup (feasible mH R Pcond 𝒢 t μ)

/-! ### A richer conditioning σ-algebra weakly raises `U` (paper §2.3) -/

/-- Enlarging the conditioning σ-algebra enlarges the feasible set: a `𝒢₁`-measurable mechanism
rule is also `𝒢₂`-measurable when `𝒢₁ ≤ 𝒢₂`. -/
theorem feasible_mono {𝒢₁ 𝒢₂ : Richness Ω} (h : 𝒢₁.σ ≤ 𝒢₂.σ) (t : ℕ)
    (μ : ProbabilityMeasure Θ) :
    feasible mH R Pcond 𝒢₁ t μ ⊆ feasible mH R Pcond 𝒢₂ t μ := by
  rintro r ⟨Γ, ρ, hΓ, hρ, hInt, rfl⟩
  exact ⟨Γ, ρ, hΓ.mono h le_rfl, hρ, hInt, rfl⟩

/-- The feasible set is nonempty: a constant mechanism rule is measurable for *any* conditioning
σ-algebra, and `hsel` supplies a selection (the paper's `lem:selection-exists`). -/
theorem feasible_nonempty [∀ t, Nonempty (H t)]
    (hsel : ∀ (t : ℕ) (Γ : Ω → H t) (μ : ProbabilityMeasure Θ),
      ∃ ρ, ρ ∈ Sel R t Γ ∧ Integrable ρ (Pcond t μ))
    (𝒢 : Richness Ω) (t : ℕ) (μ : ProbabilityMeasure Θ) :
    (feasible mH R Pcond 𝒢 t μ).Nonempty := by
  obtain ⟨ρ, hρ, hInt⟩ := hsel t (fun _ => Classical.arbitrary (H t)) μ
  refine ⟨_, ⟨fun _ => Classical.arbitrary (H t), ρ, ?_, hρ, hInt, rfl⟩⟩
  exact @measurable_const (H t) Ω (mH t) 𝒢.σ _

/-- **Assumption 2(iv)** ("the payoff correspondence `𝓡_t^{Γ_t}` is uniformly bounded above:
equilibrium values are finite") bounds the feasible set. -/
theorem feasible_bddAbove [∀ t μ, IsProbabilityMeasure (Pcond t μ)] {M : ℝ}
    (hb : ∀ (t : ℕ) (Γ : Ω → H t) (ω : Ω) (r : ℝ), r ∈ R t Γ ω → r ≤ M)
    (𝒢 : Richness Ω) (t : ℕ) (μ : ProbabilityMeasure Θ) :
    BddAbove (feasible mH R Pcond 𝒢 t μ) := by
  refine ⟨M, ?_⟩
  rintro r ⟨Γ, ρ, -, ⟨-, hmem⟩, hInt, rfl⟩
  calc ∫ ω, ρ ω ∂(Pcond t μ)
      ≤ ∫ _ω, M ∂(Pcond t μ) :=
        integral_mono hInt (integrable_const M) (fun ω => hb t Γ ω (ρ ω) (hmem ω))
    _ = M := by simp

/-- `U` is uniformly bounded above — the **derived** form of `DateValues.U_bddAbove`
(previously an axiom field, now a consequence of Assumption 2(iv)). -/
theorem U_bddAbove_of_bound [∀ t, Nonempty (H t)] [∀ t μ, IsProbabilityMeasure (Pcond t μ)] {M : ℝ}
    (hb : ∀ (t : ℕ) (Γ : Ω → H t) (ω : Ω) (r : ℝ), r ∈ R t Γ ω → r ≤ M)
    (hsel : ∀ (t : ℕ) (Γ : Ω → H t) (μ : ProbabilityMeasure Θ),
      ∃ ρ, ρ ∈ Sel R t Γ ∧ Integrable ρ (Pcond t μ))
    (𝒢 : Richness Ω) (t : ℕ) (μ : ProbabilityMeasure Θ) :
    U mH R Pcond 𝒢 t μ ≤ M := by
  refine csSup_le (feasible_nonempty mH R Pcond hsel 𝒢 t μ) ?_
  rintro r ⟨Γ, ρ, -, ⟨-, hmem⟩, hInt, rfl⟩
  calc ∫ ω, ρ ω ∂(Pcond t μ)
      ≤ ∫ _ω, M ∂(Pcond t μ) :=
        integral_mono hInt (integrable_const M) (fun ω => hb t Γ ω (ρ ω) (hmem ω))
    _ = M := by simp

/-- **The paper's "allowing richer public states expands each date-`t` continuation value `U_t`"
(§2.3), now a theorem** instead of a hypothesis: `𝒢₁ ≤ 𝒢₂ → U^{𝒢₁} ≤ U^{𝒢₂}`. -/
theorem U_mono_of_le [∀ t, Nonempty (H t)] [∀ t μ, IsProbabilityMeasure (Pcond t μ)] {M : ℝ}
    (hb : ∀ (t : ℕ) (Γ : Ω → H t) (ω : Ω) (r : ℝ), r ∈ R t Γ ω → r ≤ M)
    (hsel : ∀ (t : ℕ) (Γ : Ω → H t) (μ : ProbabilityMeasure Θ),
      ∃ ρ, ρ ∈ Sel R t Γ ∧ Integrable ρ (Pcond t μ))
    {𝒢₁ 𝒢₂ : Richness Ω} (h : 𝒢₁.σ ≤ 𝒢₂.σ) (t : ℕ) (μ : ProbabilityMeasure Θ) :
    U mH R Pcond 𝒢₁ t μ ≤ U mH R Pcond 𝒢₂ t μ :=
  csSup_le_csSup (feasible_bddAbove mH R Pcond hb 𝒢₂ t μ)
    (feasible_nonempty mH R Pcond hsel 𝒢₁ t μ) (feasible_mono mH R Pcond h t μ)

/-! ### State decomposition and collapse (paper §2.3)

The paper writes `Z_t = (S_t, Y_t)` (posterior and non-posterior public state) and compares
conditioning σ-algebras `𝒢` in the sandwich `σ(S_t) ⊆ 𝒢 ⊆ σ(S_t, Y_t)`. Both are expressible
verbatim, since `MeasurableSpace Ω` is an order. -/

variable {𝓨 : Type*} [MeasurableSpace 𝓨]

/-- The paper's admissible conditioning richness: `σ(S_t) ⊆ 𝒢 ⊆ σ(S_t, Y_t)`. -/
def AdmissibleRichness (S : Ω → ProbabilityMeasure Θ) (Y : Ω → 𝓨) (𝒢 : Richness Ω) : Prop :=
  MeasurableSpace.comap S inferInstance ≤ 𝒢.σ ∧
    𝒢.σ ≤ MeasurableSpace.comap (fun ω => (S ω, Y ω)) inferInstance

/-- The paper's **continuation value collapse** from `σ(S_t, Y_t)` to `𝒢`:
`U_t^{σ(S_t,Y_t)}(μ) = U_t^{𝒢}(μ)` for every `μ`. Previously not expressible at all. -/
def ValueCollapse (S : Ω → ProbabilityMeasure Θ) (Y : Ω → 𝓨) (𝒢 : Richness Ω)
    (t : ℕ) : Prop :=
  ∀ μ : ProbabilityMeasure Θ,
    U mH R Pcond (⟨MeasurableSpace.comap (fun ω => (S ω, Y ω)) inferInstance⟩) t μ
      = U mH R Pcond 𝒢 t μ

/-- Collapse is exactly the reverse of the automatic inequality: the full-history value always
dominates (`U_mono_of_le`), so collapse holds iff the richer value is also `≤` the coarser one. -/
theorem valueCollapse_iff [∀ t, Nonempty (H t)] [∀ t μ, IsProbabilityMeasure (Pcond t μ)] {M : ℝ}
    (hb : ∀ (t : ℕ) (Γ : Ω → H t) (ω : Ω) (r : ℝ), r ∈ R t Γ ω → r ≤ M)
    (hsel : ∀ (t : ℕ) (Γ : Ω → H t) (μ : ProbabilityMeasure Θ),
      ∃ ρ, ρ ∈ Sel R t Γ ∧ Integrable ρ (Pcond t μ))
    {S : Ω → ProbabilityMeasure Θ} {Y : Ω → 𝓨} {𝒢 : Richness Ω}
    (hadm : AdmissibleRichness S Y 𝒢) (t : ℕ) :
    ValueCollapse mH R Pcond S Y 𝒢 t ↔
      ∀ μ, U mH R Pcond (⟨MeasurableSpace.comap (fun ω => (S ω, Y ω)) inferInstance⟩) t μ
        ≤ U mH R Pcond 𝒢 t μ := by
  refine ⟨fun h μ => (h μ).le, fun h μ => le_antisymm (h μ) ?_⟩
  exact U_mono_of_le mH R Pcond hb hsel hadm.2 t μ


/-! ### The truncation value `V_t`, and `DateValues` as a **derived** object (paper §3.3)

The paper defines `V_t` by exactly the same supremum as `U_t`, replacing the payoff correspondence
`𝓡_t^Γ` by the *truncation* correspondence `𝓥_t^Γ` (the date-`t` subgame with every public
continuation replaced by the absorbing no-sale node). So `V` is literally `U` at `Rtrunc`. -/

/-- The paper's **truncation value** (§3.3):
`V_t^𝒢(μ) := sup { ∫ ρ dP_t^μ : Γ_t is 𝒢-measurable, ρ ∈ Sel(𝓥_t^Γ) }`. -/
noncomputable def V (𝒢 : Richness Ω) (t : ℕ) (μ : ProbabilityMeasure Θ) : ℝ :=
  U mH Rtrunc Pcond 𝒢 t μ

/-- **`V ≥ 0` is now derived, not assumed.** The paper says "By construction `V_t^{𝒢_t} ≥ 0`":
the truncation's absorbing no-sale node yields the seller payoff `0`, so the zero selection is
always feasible. We assume that *primitive* (`hzero`, the paper's own words) and obtain `V ≥ 0`.
Previously this was the axiom field `DateValues.V_nonneg`. -/
theorem V_nonneg [∀ t, Nonempty (H t)] [∀ t μ, IsProbabilityMeasure (Pcond t μ)] {M : ℝ}
    (hbV : ∀ (t : ℕ) (Γ : Ω → H t) (ω : Ω) (r : ℝ), r ∈ Rtrunc t Γ ω → r ≤ M)
    (hzero : ∀ (t : ℕ) (Γ : Ω → H t) (ω : Ω), (0 : ℝ) ∈ Rtrunc t Γ ω)
    (𝒢 : Richness Ω) (t : ℕ) (μ : ProbabilityMeasure Θ) :
    0 ≤ V mH Rtrunc Pcond 𝒢 t μ := by
  refine le_csSup (feasible_bddAbove mH Rtrunc Pcond hbV 𝒢 t μ) ?_
  refine ⟨fun _ => Classical.arbitrary (H t), fun _ => (0 : ℝ), ?_,
    ⟨measurable_const, fun ω => hzero t _ ω⟩, integrable_zero _ _ _, by simp⟩
  exact @measurable_const (H t) Ω (mH t) 𝒢.σ _

/-- **`V ≤ U` is derived from the paper's `eq:stopping-form`**, rather than assumed separately:
`U_t^{𝒢}(μ) = max{ V_t^{𝒢}(μ), 𝔼[U_{t+1}(S_{t+1}) | S_t = μ] }` gives `V_t ≤ U_t` at once. The
continuation term is abstracted as `C`, since only the `max` shape matters here.

`[strengthening]` The paper *derives* the stopping form from Assumption 1 (single-shot resource)
via `lem:stopping-form` — the continuation value is the Snell envelope of the truncation values.
Here it is a hypothesis. This is the **single** remaining assumed item, replacing the four axiom
fields (`V_nonneg`, `V_le_U`, `U_bddAbove`, `stopping`) that `DateValues`/`SingleShot` carried. -/
theorem V_le_U_of_stopping (C : ℕ → ProbabilityMeasure Θ → ℝ) (𝒢 : Richness Ω)
    (hstop : ∀ t μ, U mH R Pcond 𝒢 t μ = max (V mH Rtrunc Pcond 𝒢 t μ) (C t μ))
    (t : ℕ) (μ : ProbabilityMeasure Θ) :
    V mH Rtrunc Pcond 𝒢 t μ ≤ U mH R Pcond 𝒢 t μ := by
  rw [hstop]; exact le_max_left _ _

/-- **The bridge to the existing development.** A `DateValues` built *from the paper's definitions*
instead of postulated. Two of its three axiom fields are now discharged — `U_bddAbove` from
Assumption 2(iv) (`U_bddAbove_of_bound`), `V_nonneg` from the no-sale primitive (`V_nonneg`) —
leaving only `V ≤ U`, which `V_le_U_of_stopping` supplies from `eq:stopping-form`.

Everything downstream (§3, including the belief-space no-gain theorem) consumes `DateValues` and is
unaffected; but the instance it now consumes is *derived from the paper's `U_t`*, not assumed. -/
noncomputable def toDateValues [∀ t, Nonempty (H t)] [∀ t μ, IsProbabilityMeasure (Pcond t μ)]
    {M : ℝ}
    (hb : ∀ (t : ℕ) (Γ : Ω → H t) (ω : Ω) (r : ℝ), r ∈ R t Γ ω → r ≤ M)
    (hbV : ∀ (t : ℕ) (Γ : Ω → H t) (ω : Ω) (r : ℝ), r ∈ Rtrunc t Γ ω → r ≤ M)
    (hsel : ∀ (t : ℕ) (Γ : Ω → H t) (μ : ProbabilityMeasure Θ),
      ∃ ρ, ρ ∈ Sel R t Γ ∧ Integrable ρ (Pcond t μ))
    (hzero : ∀ (t : ℕ) (Γ : Ω → H t) (ω : Ω), (0 : ℝ) ∈ Rtrunc t Γ ω)
    (𝒢 : Richness Ω)
    (hVU : ∀ t μ, V mH Rtrunc Pcond 𝒢 t μ ≤ U mH R Pcond 𝒢 t μ) :
    DateValues Θ where
  U := U mH R Pcond 𝒢
  V := V mH Rtrunc Pcond 𝒢
  V_nonneg := V_nonneg mH Rtrunc Pcond hbV hzero 𝒢
  V_le_U := hVU
  U_bddAbove := ⟨M, U_bddAbove_of_bound mH R Pcond hb hsel 𝒢⟩

/-- The derived `DateValues` really does carry the paper's continuation value: its `U` field *is*
`U_t^𝒢` as defined in §2.2, definitionally. (Transparency check.) -/
theorem toDateValues_U [∀ t, Nonempty (H t)] [∀ t μ, IsProbabilityMeasure (Pcond t μ)] {M : ℝ}
    (hb : ∀ (t : ℕ) (Γ : Ω → H t) (ω : Ω) (r : ℝ), r ∈ R t Γ ω → r ≤ M)
    (hbV : ∀ (t : ℕ) (Γ : Ω → H t) (ω : Ω) (r : ℝ), r ∈ Rtrunc t Γ ω → r ≤ M)
    (hsel : ∀ (t : ℕ) (Γ : Ω → H t) (μ : ProbabilityMeasure Θ),
      ∃ ρ, ρ ∈ Sel R t Γ ∧ Integrable ρ (Pcond t μ))
    (hzero : ∀ (t : ℕ) (Γ : Ω → H t) (ω : Ω), (0 : ℝ) ∈ Rtrunc t Γ ω)
    (𝒢 : Richness Ω)
    (hVU : ∀ t μ, V mH Rtrunc Pcond 𝒢 t μ ≤ U mH R Pcond 𝒢 t μ) (t : ℕ)
    (μ : ProbabilityMeasure Θ) :
    (toDateValues mH R Rtrunc Pcond hb hbV hsel hzero 𝒢 hVU).U t μ = U mH R Pcond 𝒢 t μ := rfl

end Paper
end DMC
