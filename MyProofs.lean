import MyProofs.Basic
-- Foundations: reusable math (belief-space toolkit; some are Mathlib-gap fills, upstream candidates)
import MyProofs.Foundations.PosteriorProcess
import MyProofs.Foundations.Concavification
import MyProofs.Foundations.BeliefSpace
-- Model (§2): abstract axiomatization of the dynamic mechanism game
import MyProofs.Model.Basic
import MyProofs.Model.ContinuationValue
import MyProofs.Model.SingleShot
import MyProofs.Model.Primitives
-- Results (§3): the main theorems
import MyProofs.Results.Representation
import MyProofs.Results.NoGain
import MyProofs.Results.Collapse
import MyProofs.Results.CriterionTransform
-- Applications (§4)
import MyProofs.Applications.Screening
import MyProofs.Applications.Certification
-- Meta: machine-checkable audit and faithfulness scaffolding
import MyProofs.Meta.Audit
import MyProofs.Meta.Faithfulness
import MyProofs.Meta.ModelFaithfulness
