import MyProofs.Model.SingleShot

/-!
# Model (§2): machine-checked faithfulness audit

Companion to `Meta/Faithfulness.lean`, but for the **model layer** (§2) rather than Lemma 1. The
model is formalized as *definitions and axiomatized structures* (`Belief`, `AllocDate`,
`DateValues`, `SingleShot`), not theorems. Therefore `lake build` being green and `#print axioms`
being clean certify **almost nothing** about the model: the kernel checks *proof ↔ statement*, and
here there are barely any proofs to check — the risk lives entirely in whether the *definitions*
faithfully transcribe the paper.

This file converts as much of that "trust the definition" as possible into kernel-checked facts,
in three registers:

* **(A) Consistency / non-vacuity** (`frozenBeliefWitness`, `singleShot_consistent`): the axiom
  bundle carried by `SingleShot` (`V_nonneg`, `V_le_U`, `U_bddAbove`, `condExp_mono`,
  `affine_harmonic`, `stopping`) is **jointly satisfiable** — a concrete instance over the genuine
  compact Polish space `unitInterval` type-checks. Without this, a contradictory axiom set would
  make every §3 theorem vacuously true, and nothing would flag it.
* **(B) Transparency** (`DateValues.envelope_eq_iSup`, `SingleShot.stop_iff`,
  `SingleShot.condExp_const`, `allocDate_*`): each encoded object unfolds to the paper's plain
  statement — the allocation date really has a distinguished "never" apart from every real date,
  and its dates start at 1 as in the paper; `envelope` really is `sup_t U_t`; the `max` in `stopping` really encodes "stop iff
  the truncation value beats deferral"; Bayes-plausibility really fixes constants.
* **(C) Non-degeneracy** (`witness_V_lt_U`): the witness has `V < U` strictly somewhere, so
  `V_le_U` is a genuine `≤` (deferral is a real option), not a `V = U` collapse smuggled in.

Honest limit (same as `Faithfulness.lean`): if a definition and its audit lemma shared the same
mis-transcription they could agree wrongly. These checks shrink the room for a hidden defect; the
line-by-line paper↔Lean judgment (blueprint / `CORRESPONDENCE.md`) remains a human act.
-/

open MeasureTheory

namespace DMC

/-! ### (B) `AllocDate` is a faithful encoding of `{1,2,…} ∪ {∅}`

The paper's allocation date is a real date or the distinguished symbol `∅` ("no sale ever"). The
encoding must keep `∅` apart from every real date and keep distinct dates distinct. -/

/-- The "never allocate" symbol `∅ = none` is distinct from every real allocation date `some n`. -/
theorem allocDate_never_ne_date (n : {n : ℕ // 1 ≤ n}) : (none : AllocDate) ≠ some n := by simp

/-- Distinct dates encode to distinct `AllocDate`s (the encoding loses no date information). -/
theorem allocDate_date_injective :
    Function.Injective (some : {n : ℕ // 1 ≤ n} → AllocDate) :=
  Option.some_injective _

/-- **The encoded range is exactly the paper's.** Every allocation date is `≥ 1`, matching
`τ ∈ {1,2,…}`; the encoding admits no spurious date `0`. (A plain `Option ℕ` would.) -/
theorem allocDate_date_ge_one (n : {n : ℕ // 1 ≤ n}) : 1 ≤ (n : ℕ) := n.2

/-! ### (B) The envelope is transparently `sup_t U_t` -/

variable {Θ : Type*}

/-- Transparency: `DateValues.envelope` is *definitionally* the paper's `g(μ) = sup_t U_t(μ)`. -/
theorem DateValues.envelope_eq_iSup [MeasurableSpace Θ] (D : DateValues Θ)
    (μ : ProbabilityMeasure Θ) : D.envelope μ = ⨆ t : ℕ, D.U t μ := rfl

/-! ### (B) The `max` in the stopping recursion transparently encodes "stop vs. continue" -/

variable [TopologicalSpace Θ] [MeasurableSpace Θ]

/-- Transparency of `stopping`: at date `t` the seller's value equals the truncation value `V_t`
(i.e. "allocate now") **iff** deferral is (weakly) worse than allocating. So the `max` really is the
stop-or-continue decision, not an unrelated algebraic combination. -/
theorem SingleShot.stop_iff (D : SingleShot Θ) (t : ℕ) (μ : ProbabilityMeasure Θ) :
    D.U t μ = D.V t μ ↔ D.condExp (D.U (t + 1)) t μ ≤ D.V t μ := by
  rw [D.stopping t μ]; exact max_eq_left_iff

/-- Transparency of `affine_harmonic` (Bayes-plausibility) on constants: a constant belief
functional is harmonic — its expected next value is itself. This is the special case `λ ≡ c` of the
affine-harmonic axiom, and is exactly "the total probability is conserved across dates". -/
theorem SingleShot.condExp_const (D : SingleShot Θ) (c : ℝ) (t : ℕ) (μ : ProbabilityMeasure Θ) :
    D.condExp (fun _ => c) t μ = c := by
  have hfun : (fun ν : ProbabilityMeasure Θ => ∫ _x, (ContinuousMap.const Θ c) _x ∂(ν : Measure Θ))
      = fun _ => c := by
    funext ν
    simp
  have h := D.affine_harmonic (ContinuousMap.const Θ c) t μ
  rw [hfun] at h
  simpa using h

/-! ### (A) Consistency / non-vacuity: a concrete `SingleShot` instance exists

The single most important machine check for an *axiomatized* model: exhibit one witness so the axiom
bundle is provably consistent. We use the "frozen belief" special case — the belief martingale is
the constant (Dirac transition) process, so `condExp φ = φ`, which is a legitimate belief martingale
(a constant process is a martingale). `Θ = unitInterval` is a genuine nonempty compact Polish space,
so the witness is not vacuous through an empty type. -/

/-- **Consistency witness.** A concrete `SingleShot unitInterval`. The conditional-expectation
operator is evaluation-at-`μ` (frozen belief), values are `U ≡ 1`, `V ≡ 1/2`. Every axiom of
`SingleShot`/`DateValues` is discharged, so the bundle is jointly satisfiable. -/
noncomputable def frozenBeliefWitness : SingleShot unitInterval where
  U := fun _ _ => 1
  V := fun _ _ => 1 / 2
  V_nonneg := fun _ _ => by norm_num
  V_le_U := fun _ _ => by norm_num
  U_bddAbove := ⟨1, fun _ _ => le_refl 1⟩
  condExp := fun φ _ μ => φ μ
  condExp_mono := fun h _ μ => h μ
  affine_harmonic := fun _ _ _ => rfl
  stopping := fun _ _ => (max_eq_right (by norm_num)).symm

/-- The `SingleShot` axiom bundle is **consistent** (not contradictory): a witness exists. Hence the
§3 theorems that quantify over `SingleShot` are not vacuously true. -/
theorem singleShot_consistent : Nonempty (SingleShot unitInterval) :=
  ⟨frozenBeliefWitness⟩

/-! ### (C) Non-degeneracy: `V_le_U` is a real inequality, not a hidden equality -/

/-- In the witness the truncation value is *strictly* below the continuation value at every date and
belief. So `V_le_U : V ≤ U` is genuinely a `≤` — deferral is a real option — and is not secretly
forcing `V = U`. -/
theorem witness_V_lt_U (t : ℕ) (μ : ProbabilityMeasure unitInterval) :
    frozenBeliefWitness.V t μ < frozenBeliefWitness.U t μ := by
  change (1 : ℝ) / 2 < 1
  norm_num

end DMC
