# Vegas/LetCore -- Core Calculus Infrastructure

This module provides the foundational typed infrastructure on which all higher layers are built: de Bruijn-indexed environments, an abstract language interface, and a generic program calculus parameterized by effect commands.

## Design Overview

The core design principle is **parameterization**: rather than committing to a fixed set of effects (sampling, choosing, observing), `LetCore` defines a generic `Prog` type that is indexed by two command families -- one for binding commands (which produce a value) and one for statement commands (which produce `Unit`). Each higher layer (probabilistic, strategic, protocol) instantiates these command families with its own effects, while reusing the same evaluator, environment machinery, and structural lemmas.

Environments use de Bruijn indices rather than named variables. This eliminates capture-avoiding substitution entirely and makes weakening a structural operation on indices. The tradeoff is that programs are less human-readable, but the formal properties are cleaner.

## Key Types

**`Env.Var Gamma tau`** -- A de Bruijn index into context `Gamma` selecting a variable of type `tau`. Constructors: `vz` (head) and `vs` (shift). Weakening (`Var.weaken`) lifts a variable into an extended context.

**`Env.Env Val Gamma`** -- A runtime environment: a heterogeneous tuple of values matching the types in context `Gamma`. Defined recursively as nested pairs, with `get`, `cons`, `head`, `tail` operations.

**`Language`** -- The abstract interface that higher layers instantiate. Bundles:
- `Ty : Type` -- a universe of object-language types
- `Val : Ty -> Type` -- runtime value interpretation
- `Expr Gamma tau` -- expression syntax, indexed by context and return type
- `eval : Expr Gamma tau -> Env Val Gamma -> Val tau` -- expression evaluator
- `bool : Ty`, `toBool`, `fromBool` -- boolean infrastructure for `observe` conditions
- Decidable equality on types and values (needed for discrete probability support)

**`ExprLaws L`** -- Additional structure on a `Language` needed by lemmas: expression weakening, boolean constants, conjunction, variable expressions, and their evaluation laws.

**`Prog CB CS Gamma tau`** -- The generic program syntax. Four constructors:
- `ret e` -- return the value of expression `e`
- `letDet e k` -- evaluate `e`, bind the result, continue with `k`
- `doBind c k` -- execute bind-command `c` (from family `CB`), bind result, continue
- `doStmt s k` -- execute statement-command `s` (from family `CS`), continue

**`LangSem CB CS M`** -- A semantics packages an effect carrier `M` with handlers for bind and statement commands.

**`evalWith S p env`** / **`evalProg_gen`** -- The generic evaluator. Given a `LangSem`, recursively evaluates a `Prog` by dispatching to the handlers for each command.

**`DProg`** -- The deterministic fragment: no bind-commands (`CmdBindD = Empty`), statement-commands are only `observe`. Evaluated into `Option` via `evalProgOption`.

## What Is Not Modeled

- No substitution or beta-reduction on programs (evaluation is big-step, not rewriting).
- No polymorphism or higher-order functions in the object language.
- No operational (small-step) semantics at this layer; adequacy would be proved separately.
- No type inference or elaboration; programs are fully explicitly typed by construction.

## Design Decisions

- **De Bruijn indices** rather than named variables: avoids alpha-equivalence issues entirely. Programs are canonical up to structural equality.
- **CmdB / CmdS split**: binding commands (`doBind`) produce a value that extends the context; statement commands (`doStmt`) are effectful but do not bind. This distinction is fundamental to the type structure and avoids a dummy binding for statements.
- **Generic evaluator via `Eff`**: the `Eff` record (`pure`, `bind`, `fail`) is a minimal effect interface, not a full monad. This lets the same evaluator target `Option`, `WDist`, or any other carrier.

## Further Reading

- de Bruijn, N.G. "Lambda calculus notation with nameless dummies" (1972) -- the original de Bruijn index paper.
- Benton, Hur, Kennedy, McBride. "Strongly Typed Term Representations in Coq" (JFP 2012) -- intrinsically typed syntax with de Bruijn indices in a proof assistant.

## File Listing

| File | Description |
|------|-------------|
| `Env.lean` | De Bruijn indices (`Var`), runtime environments (`Env`), lookup, weakening, extensionality |
| `Language.lean` | `Language` interface and `ExprLaws` type class |
| `Prog.lean` | Generic `Prog` calculus, `evalProg_gen`, `evalWith`, `LangSem`, deterministic fragment `DProg` |
| `ProgLemmas.lean` | Simp lemmas and equational laws: observe fusion, observe hoisting past letDet, weakening |
| `Concrete.lean` | `BasicLang : Language` with `Ty := {int, bool}`, concrete expressions, `basicExprLaws` |
