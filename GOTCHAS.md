# Vegas / StratLet: Probabilistic Semantics & Design Notes

## 1. Core Definitions (PL-to-Probability Map)
We implement a **Weighted Finite-Support Multiset** semantics.

| Concept | Implementation (Vegas) | Formal Interpretation |
| :--- | :--- | :--- |
| **Distribution** | `WDist α := List (α × W)` | Finite weighted multiset (not yet a measure). |
| **Sample Space** | List indices | The set of explicit execution paths. |
| **Total Evidence** | `WDist.mass` | The partition function ($Z$). |
| **Conditioning** | `CmdStmtObs.observe` | **Hard evidence** (guard/filter). Soft likelihood not yet modeled. |
| **Aggregation** | `WDist.combine` | Summing weights for equal outcomes. |
| **Posterior** | `WDist.normalize` | The derived probability measure (requires `mass > 0`). |

## 2. The "Time Machine" (Global Normalization)
**CRITICAL:** Distinguish between the *local* operation and the *global* interpretation.

* **Operational View (Local):** `observe(false)` is a standard filtering operation. It drops the current branch (returns `[]` or `zero`). It does **not** affect the weights of other branches during execution.
* **Denotational View (Global):** When interpreting the result as a Probability Distribution (via `normalize`), removing a branch mathematically increases the relative probability of all surviving branches. This "retroactive" effect is a property of the normalization operator, not the control flow.

## 3. Formalization Hazards & Constraints

### A. The "Zero Mass" Trap (Partiality)
* **Issue:** If `observe` rejects all branches, `mass = 0`.
* **Constraint:** `WDist.normalize` is partial.
* **Theorem Hazard:** Any theorem stating "this program defines a probability distribution" must carry a hypothesis `WDist.mass dist > 0` (i.e., the program is **satisfiable**).

### B. Notion of Equality (The Quotient)
* **Implementation:** `WDist` is a `List`, so `[(A,1), (A,1)]` $\neq$ `[(A,2)]` structurally.
* **Semantics:** True program equality must be defined on the **Quotient** of `WDist` modulo:
    1.  **Permutation** (Order doesn't matter).
    2.  **Combination** (Summing weights of duplicate values).
* **Note:** Without `combine`, extensional reasoning is fragile.

### C. Disintegration & Commutativity
* **Intuition:** We often want to swap sampling and observation.
    * *Target:* `x <- sample; observe(P x)` $\equiv$ `observe(∃x, P x); x <- sample_conditional`
* **Hazard:** This is a **Disintegration** property. It requires:
    1.  A definable conditional kernel.
    2.  `mass > 0` (Conditioning on measure zero is undefined).

### D. Finite Support (Termination)
* **Constraint:** `WDist` uses `List`, enforcing **Finite Support**.
* **Implication:** The language cannot support unbounded `while` loops or continuous distributions (Gaussian) without changing the core monad to a Stream or Measure type.

## 4. Strategic & Game Theoretic Context

### A. Rationality vs. Mechanical Probability
* **Rational Agents:** Look ahead, compute `max(utility)`, and propagate values backward.
* **Probabilistic Programs:** Explore all paths blindly; `sum(weights)` determines the result.

### B. Correlation & Independence
* **Default:** Independence is **not** guaranteed.
* **Mechanism:** Correlation arises naturally if a kernel depends on the `Env`. If Player A's choice is in the environment, and Player B reads it, their actions are correlated.
* **Design Note:** To enforce independence, we must explicitly restrict access to the `Env` or use private randomness sources.
