/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.Compiler
import Vegas.Compile.ConditionalExecution
import Vegas.Compile.ConditionalPublicationSite
import Vegas.Compile.ConditionalOpeningController
import Vegas.Compile.ConditionalPublication
import Vegas.Compile.ConditionalResolution
import Vegas.Compile.PublicChoice
import Vegas.Compile.PublicChoiceSite
import Vegas.Compile.PublicChoiceExecution
import Vegas.Compile.PublicChoiceValidation
import Vegas.Compile.PublicChoiceController
import Vegas.Compile.ApplicationImage
import Vegas.Compile.ApplicationImageSamples
import Vegas.Compile.ApplicationImageBindings
import Vegas.Compile.ApplicationBindingOrigins
import Vegas.Compile.ApplicationImageInvariants
import Vegas.Compile.ApplicationPlan
import Vegas.Compile.ApplicationPlanCoverage
import Vegas.Compile.ApplicationPlanAllocation
import Vegas.Compile.ApplicationPlanOrigin
import Vegas.Compile.ApplicationGuardSoundness
import Vegas.Compile.BindingResolution
import Vegas.Compile.ConditionalOpeningValidation
import Vegas.Compile.ConditionalImage
import Vegas.Compile.ConditionalImageRefinement
import Vegas.Compile.PublicChoiceImage
import Vegas.Compile.SampleImage
import Vegas.Compile.SampleImageRefinement
import Vegas.Compile.ApplicationImageController
import Vegas.Compile.ConditionalImageController
import Vegas.Compile.ApplicationImageReadout
import Vegas.Compile.ApplicationImageRegistration
import Vegas.Compile.ApplicationImageBindingInclusion
import Vegas.Compile.ApplicationImageProvenance
import Vegas.Compile.ApplicationImageCoverage
import Vegas.Compile.ApplicationImageReadoutAvailability
import Vegas.Compile.SourceReadoutAvailability
import Vegas.Compile.BindingImageController
import Vegas.Compile.BindingImageExecution
import Vegas.Compile.ApplicationSampleExecution
import Vegas.Compile.PublicChoiceImageExecution
import Vegas.Compile.PublicChoiceSourceCoupling
import Vegas.Compile.BindingSourceCoupling
import Vegas.Compile.ConditionalSourceCoupling
import Vegas.Compile.ApplicationPolicy
import Vegas.Compile.ApplicationPolicyFreshness
import Vegas.Compile.ApplicationPolicyLocality
import Vegas.Compile.ApplicationPolicyBindings
import Vegas.Compile.ApplicationPolicyProvenance
import Vegas.Compile.ApplicationImageRefinement
import Vegas.Compile.BindingImageRefinement
import Vegas.Compile.ApplicationImageOutcome
import Vegas.Compile.ApplicationImageStateRefinement
import Vegas.Compile.PublicationStateRefinement
import Vegas.Compile.ApplicationPlanRefinement
import Vegas.Compile.ApplicationSourceOutcome
import Vegas.Compile.ApplicationPlanOutcome
import Vegas.Compile.SourceChoiceController
import Vegas.Compile.PublicGuard
import Vegas.Compile.DecisionSite
import Vegas.Compile.FieldMap
import Vegas.Compile.SourceAdequacy
import Vegas.Compile.SourceOrder
import Vegas.Compile.SourceInformation
import Vegas.Compile.PolicyInformation
import Vegas.Compile.SourceLaw
import Vegas.Compile.SourceExecution
import Vegas.Compile.SourceExecutionGraph
import Vegas.Compile.SourceExecutionLaw
import Vegas.Compile.SourceExecutionOutcome
import Vegas.Compile.SourceOutcome
import Vegas.Compile.SourceObservation
import Vegas.Compile.SourcePolicy
import Vegas.Compile.SourceBacktranslation
import Vegas.Compile.SourceStrategy
import Vegas.Compile.Machine
import Vegas.Compile.SealedMessages
import Vegas.Compile.SealedDecode
import Vegas.Compile.SealedExecution
import Vegas.Compile.SealedRules
import Vegas.Compile.SealedDecodeLaws
import Vegas.Compile.SealedRefinement
import Vegas.Compile.SealedSource
import Vegas.Compile.SealedTimeoutRefinement

/-!
# Compilation: checked Vegas programs and runtime components

`Compiler` lowers a `GraphProgram` / `WFProgram` into a canonical
`EventGraph.Graph` with typed fields, causal dependencies, guarded commit
nodes, exact finite laws, and terminal payoff projections.
Structural application plans generate binding, chance, and publication instructions.
Arbitrary supported public-message executions refine reachable graph states;
completed runs have the public outcome of a written-order source execution.
Whole-profile laws and strategic correspondence for this target remain separate
obligations.
-/
