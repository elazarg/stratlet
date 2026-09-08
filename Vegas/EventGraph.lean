/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.EventGraph.Basic
import Vegas.EventGraph.Batch
import Vegas.EventGraph.Build
import Vegas.EventGraph.Confluence
import Vegas.EventGraph.Execution
import Vegas.EventGraph.Fence
import Vegas.EventGraph.FiniteState
import Vegas.EventGraph.Frontier
import Vegas.EventGraph.Information
import Vegas.EventGraph.HistoryInformation
import Vegas.EventGraph.IndependentWrites
import Vegas.EventGraph.IndependentWriteProduct
import Vegas.EventGraph.KernelExecution
import Vegas.EventGraph.KernelFrontierWrites
import Vegas.EventGraph.KernelBehavioral
import Vegas.EventGraph.KernelIndependent
import Vegas.EventGraph.KernelNative
import Vegas.EventGraph.KernelProduct
import Vegas.EventGraph.KernelSupport
import Vegas.EventGraph.KernelPolicy
import Vegas.EventGraph.KernelPlan
import Vegas.EventGraph.KernelRound
import Vegas.EventGraph.KernelSchedule
import Vegas.EventGraph.Linearization
import Vegas.EventGraph.Protocol
import Vegas.EventGraph.ProtocolOrder
import Vegas.EventGraph.PolicyLocalization
import Vegas.EventGraph.PolicyRoundtrip
import Vegas.EventGraph.Recall
import Vegas.EventGraph.Sequential
import Vegas.EventGraph.Skeleton
import Vegas.EventGraph.SourceOrder
import Vegas.EventGraph.TopologicalOrder
import Vegas.EventGraph.Validate
import Vegas.EventGraph.VisibleOrder

/-! Typed dependency graphs, schedule-free execution, and protocol denotation. -/
