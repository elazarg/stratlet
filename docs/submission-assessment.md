# Research positioning and submission criteria

## Assessment

The maintained manuscript's technical completion gate is
[paper-scope.md](paper-scope.md). The broader public-ledger expansion is a
separate research target, not a prerequisite silently added to this paper.

The defensible contribution is a mechanized compiler construction for finite
imperfect-information games, with concrete back-translations for private
request windows and public serialization. The main composed theorem has real
content beyond a correctness interface: it derives the source information
discipline, reconstructs private retry memory, admits order-aware deviations,
and proves law comparisons against unchanged opponents.

The broad principle that simulating deviations preserves equilibrium is not
novel. Neither are programming games, commit-before-disclose, source-level
nonresponse, conditional-utility optimization at a quitting decision, or Kuhn's
correspondence. A paper centered on those claims would have a weak novelty case.
Counting Lean declarations or combining familiar words does not repair it.

The examined work does not establish that the exact Vegas construction is
already available elsewhere. That is a bounded literature finding, not proof
of priority. A plausible PL contribution remains in the construction and its
mechanization, but whether it is sufficiently substantial is a reviewer
judgment. Exactness is partly purchased by a deliberately restricted runtime;
it is not automatically an improvement over computational soundness.

## Closest comparisons and source locators

These are primary papers and author/institutional resources. The manuscript
contains the concise comparisons; the locators here support further checking.
No formal embedding or subsumption theorem between these frameworks is proved.

| Work | Where to inspect | Consequence for positioning |
| --- | --- | --- |
| [Halpern and Pass, computational game-theoretic framework](https://www.cs.cornell.edu/home/halpern/papers/newgtsec.pdf) | Universal implementation; Theorems 4.2 and 4.3 | Simulation and equilibrium preservation, including costs and coalitions, are established foundations. |
| [Halpern, Pass, Seeman, computational extensive-form games](https://arxiv.org/pdf/1506.03030) | Definition 3.3, UG2 and UG4(c); Theorems 4.2 and 4.6; footnote 4 on replaying memory | The unilateral opponent-preserving comparison is close prior art; replay itself is not a new idea. |
| [Bartoletti and Zunino, BitML](https://eprint.iacr.org/2018/122) | Section 2 examples; Sections 5--6 strategies; Section 9, Theorem 2 | Compare actual strategic soundness, not merely transfer safety. Even Odds--Evens is a shared example, not a novel application. |
| [Melkonian, Agda thesis](https://omelkonian.github.io/data/phd-thesis.pdf) | Chapter 7, printed pp. 184--185 and Section 7.4 | Substantial mechanization, but expressly not a complete computational-soundness proof. Do not infer completion from the thesis title. |
| [Psomas, Terzoglou, Wei, Zikas, pseudo-equilibria](https://arxiv.org/abs/2506.22089v2) | Definitions 3.1--3.3; Theorem 3.1; ideal-crypto replacement result | Different computational solution concept; not an equivalent description of our exact serializer theorem. |
| [Jakobsen, Sørensen, Conitzer, timeability](https://arxiv.org/pdf/1502.03430) | Theorem 1 and Section 3 | Timing-based implementation obstructions have a substantial prior theory; our order model is not a timing completeness result. |
| [Pauly, mechanism programming](https://doi.org/10.1093/logcom/exi014) | Operational game semantics and Hoare calculus | Deriving a game from a program is not new by itself. |
| [CheckMate](https://pm.inf.ethz.ch/publications/BruggerKovacsKomelRainRawson23.pdf) | Game-model input, security encoding and evaluation | Automated strategic analysis is a separate contribution, not one supplied by this compiler theorem. |

Search also covered verified/secure compilation, probabilistic and game
description languages, and formalized game analysis. Relevant follow-up
directions include [CheckMate's compositional and game-modeling work](https://sophierain.github.io/)
and [certified concurrent abstraction layers](https://flint.cs.yale.edu/publications/ccal.html).
These are not assessed here as formally subsumed competitors. Before claiming
priority for a general replay/serialization technique, compare its invariant
with concurrent refinement and information-flow simulation proofs, not only
papers that mention Nash equilibrium. The search is not a systematic review
of every concurrency or mechanism-design formalization.

## What is derived, and what is supplied

| Layer | Established by Vegas | Supplied or built into the model |
| --- | --- | --- |
| Checked core | Graph construction, legal observations, perfect recall, bounded execution | Well-formed source; finite-domain hypothesis where used |
| Request interface | Controller back-translation and exact all-profile history laws | Legal timeout choice, accepting encoder/decoder, finite window; private attempts and frozen information |
| Serializer | Order replay and deviation-mixture law | All legal frontier choices resolve before ordering; no current-payload access; atomic internal closure |
| Composition | Automatic interface lift, counterfactual finite-site cover, same-error Nash equivalence | Independently sampled finite private controller mixtures; fixed arbitrary behavioral scheduler compiled through its encoder |
| Finite disclosure case | Full-policy outcome and payoff correspondence; sealed-offer equilibrium and adversarial buyer guarantee through the runtime | Hand-specified finite game, ideal private guard, no initial/buyer quitting or Kotlin semantic bridge |
| Real contracts | Separate executable passes and component proofs | No proved bridge to public delivery/deadlines, cryptography, or whole generated handlers |

Request back-translation is uniform in opponents. The serializer witness is
profile- and horizon-local. The composed result therefore must not be described
as a uniform atomic-source back-translation, or as an equivalence of all target
equilibria. Nash reflection concerns compiled profiles. The scheduler is an
environment coordinate; its utility and optimality are irrelevant, but its
admitted observations and actions are essential.

The source of the strategic theorem is the canonical graph-derived game.
Written-order source reconstruction is support-level. There is no separately
proved distribution-level equivalence with a written-order source strategy
semantics. Kotlin and Lean are distinct implementations. The Lean syntax lacks
Kotlin's nonresponse-handler constructs. Choosing an optional value is not the
same as withholding a mandatory reveal.

The source-quitting criterion is useful mechanism analysis: optimize the
conditional continuation/outside-option comparison after every upstream
deviation. Its mathematical calculation is elementary. The staged case study's
stronger evidence is the proved correspondence for the complete checkpoint
information, not an assumption that the player observes only a selected signal.
It manually provides its quitting checkpoint; general compilation does not
insert that checkpoint.

## GameTheory attribution

GameTheory is Elazar Gershuni's separately maintained unpublished GitHub library.
Use a software citation with repository and pinned revision. Do not invent a
venue, call it independently published prior art, or present this manuscript as
the publication of the library. A software citation acknowledges and identifies
a dependency; it does not commit the author to a general library paper here.

Describe only the interfaces and generic theorems needed to understand the
Vegas proof. The artifact must include/retrieve their checked definitions and
proofs; a library boundary is not an axiom. General probability, game forms,
perfect-recall/Kuhn infrastructure, and presentations are dependency work.
The graph instantiation and runtime constructions are the paper's subject.
Any future library paper should disclose overlapping software and explanations
without treating all library results as already contributed by Vegas.

## Submission decision and finite stopping rule

Prepare a serious submission for expert feedback rather than opening another
unbounded theorem program. The present result can support that decision, but
the manuscript and artifact do not establish likely top-tier acceptance.
The strongest foreseeable objection is that the target models encode away
the operational difficulty and the remaining construction is a routine
application of established simulation and perfect-recall machinery.

A substantive answer needs to show exactly what is reconstructed rather than
assumed: the private-memory invariant, public-order replay, unchanged opponents,
and finite counterfactual coverage. The paper and proof guide make these
inspectable. A reviewer may still judge them insufficiently novel; do not answer
that objection with repository size or additional toy impossibilities.

Before actual submission:

1. Have a game-theory/cryptography reader assess the comparison with game
   representation and a PL reader assess the concrete construction. This is
   a recommendation for the authors, not authorization to contact anyone.
2. Read the main composed Lean statement alongside every premise in the prose.
   Confirm intended interpretations of quitting, observations, and utilities.
3. Reproduce the artifact from a fresh checkout on a reviewer-like machine.
   A successful incremental development build is not this test. Record resource
   use if reporting it; no build-time or scalability measurement is claimed.
4. Select a venue, apply its current page/anonymity/supplement rules, and verify
   the resulting PDF. The maintained manuscript is an identified reading copy,
   not a venue-compliant anonymized submission.
5. Present the sealed-offer instance as an integration of the proved compiler
   boundary, not a novel mechanism or a verified deployed escrow. Its
   full-policy comparison and actual compiled payoffs address the selected
   technical completion gate. Another finite example would not resolve a
   reviewer objection that the runtime model itself is too idealized.

Public delivery/deadline scheduling, a Kotlin-to-Lean checker, cryptographic
realization, coalition/sequential equilibrium, and EVM handler simulation are
separate research tasks. They become submission blockers only if the paper
claims those guarantees. The detailed delivery obligations remain in
[runtime-models.md](runtime-models.md).
