import MyProofs.Foundations.PosteriorProcess
import MyProofs.Meta.ModelFaithfulness
import MyProofs.Meta.Faithfulness

/-!
# Verification audit

`#print axioms` lists the full set of axioms a theorem ultimately depends on. Criterion:

* Only `propext`, `Classical.choice`, `Quot.sound` appear
  → these are Lean/Mathlib's standard trusted axioms; the proof is complete and verified by
    the kernel.
* If `sorryAx` appears
  → there is a `sorry` somewhere on the dependency chain; not yet verified.

This is the machine-checkable criterion for "did Lean really prove it" — it cannot be faked.
-/

open PosteriorProcess

-- All four parts of Lemma 1 — each should depend only on
-- `propext` / `Classical.choice` / `Quot.sound` (no `sorryAx`).

-- Existence + kernel property
#print axioms kernel_exists
-- (i) Sufficiency
#print axioms sufficiency
#print axioms measurable_integral_bounded
-- (ii) Doob–Dynkin + Δ(Θ) standard Borel (a former Mathlib gap, proved from scratch)
#print axioms factorization
#print axioms deltaTheta_polishSpace
#print axioms deltaTheta_borelSpace
#print axioms deltaTheta_standardBorel
#print axioms factorization_posterior
-- (iii) Martingale property
#print axioms testfun_martingale
-- Δ(Θ) 是论文的对象:σ-代数 = 弱拓扑的 Borel;拓扑 = 弱拓扑
#print axioms deltaTheta_measurableSpace_eq_borel
#print axioms deltaTheta_tendsto_iff_integral

-- Model (§2) faithfulness: the axiom bundle is consistent and the encodings are transparent.
-- Each should depend only on the standard three axioms (no `sorryAx`).
#print axioms DMC.frozenBeliefWitness
#print axioms DMC.singleShot_consistent
#print axioms DMC.witness_V_lt_U
#print axioms DMC.SingleShot.stop_iff
#print axioms DMC.SingleShot.condExp_const
#print axioms DMC.DateValues.envelope_eq_iSup
#print axioms DMC.allocDate_never_ne_date
