# Insights — ChatGPT for Lean Proofs

## Integration approach

We use direct OpenAI API calls via Python's `urllib` from bash. This was chosen over:
- **claude-chatgpt-mcp** (https://github.com/syedazharmbnr1/claude-chatgpt-mcp) — Rejected. It automates the ChatGPT macOS desktop app via AppleScript/UI automation. macOS-only, unreliable (open bugs: "input rarely works"), no model selection, slower than API. Not suitable.
- The direct API approach gives us: cross-platform support, explicit model control, low latency, and full reliability.

## Model selection

Use the newest available model. As of 2026-02-10, available GPT-5.x models:
- `gpt-5.2` — current best (use this). Confirmed working. Note: requires `max_completion_tokens` not `max_tokens` (already handled in `ask_gpt.py`).
- `gpt-5.2-pro` — heavier, slower, possibly better for hard proofs (untested)

Also available: `4o`, `o3`, `o3-pro`, `o4-mini` (reasoning models). Untested for Lean proofs.

**No `gpt-5.3` yet** as of 2026-02-09.

## Prompt construction

- **Include complete context for the goal** - if there's a proof that partially works, attach the context, goal and Lean's warnings for anywhere it does not. 
- **Include all referenced definitions.** ChatGPT has no access to our codebase. Every type, function, and inductive that appears in the goal must be in the prompt. You can use `lean-defs.py` to automate parts of the process of collecting proofs.
- **Hint at proof strategy.** "Proceed by induction on p, case splitting on c" significantly improves output quality vs. just saying "prove this."
- **Low temperature (0.2)** for proof tasks. Creativity hurts here.
- **Learn and apply** - once you understand how one proof or part of a proof works, apply it to others.

## Common failure modes

- **Invented names:** ChatGPT references lemmas or constructors that don't exist. Always verify.
- **Scoping errors:** It uses `let`-bound names from function definitions as if they're in proof scope (e.g. `Kfull` from inside `toProb?`).
- **Missing explicit parameters:** Our codebase uses `(L := L)` throughout. ChatGPT drops these.
- **Over-optimistic `simp`:** It writes `simp [f, g]` expecting it to close goals that actually need manual steps.
- **`Option.map` reasoning:** ChatGPT struggles with goals involving `Option.map f x = some y`. It tries `injection`/`contradiction` where `simp` + case split on the inner option is needed.
- **Smart vs raw constructor mismatch:** ChatGPT doesn't understand that Lean's `simp` matches syntactically, not up to definitional equality. When simp lemmas are stated with smart constructors (e.g. `.sample id v K k`) but the goal has raw constructors (`Prog.doBind (CmdBindProto.sample ...) k`), simp silently fails. ChatGPT will suggest `simp [evalProto_sample_bind, ih]` and not understand why it doesn't work. The fix is `change`/`congr_arg` through definitional equality instead of simp.

## When Claude is better than ChatGPT

- **Semantic analysis of proof obstacles:** When the issue is understanding WHY a proof can't go through (e.g., the observe case mismatch in EU preservation), Claude's ability to trace through definitional reductions and identify the exact semantic mismatch is faster and more reliable than ChatGPT.
- **Definitional equality reasoning:** Claude understands that `ObserveFree (.letDet e k)` unfolds to `ObserveFree k` definitionally, so no explicit `have hofk := ...` is needed. ChatGPT tends to add unnecessary extraction steps.
- **When the proof is simple once the approach is clear:** For the observe case, the actual Lean proof was `exact absurd hof (by simp [ObserveFree])` — a one-liner. Claude can write this directly; ChatGPT wraps it in scaffolding.

## When to use ChatGPT as a "rubber duck"

- When you've identified the approach but want confirmation it's sound before restructuring the theorem. In the ObserveFree case, asking ChatGPT "which of these 3 approaches is best?" confirmed option A quickly.

## Workflow

1. Identify a `sorry`.
2. Read surrounding context — gather all definitions referenced in the goal.
3. Construct prompt: definitions + theorem + strategy hint.
4. Call gpt-5.2 via Python snippet (see CLAUDE.md).
5. Paste into Lean file, attempt build.
6. Fix errors — typically: add `(L := L)`, fix names, strengthen `simp` calls.
7. MANDATORY: Record result in EMPIRICAL.md so the process will improve over time.
8. Optional but important: Record and significant insights in autoproof/INSIGHTS.md
