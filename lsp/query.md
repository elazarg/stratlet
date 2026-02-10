Prove this Lean 4 theorem. I'll provide the key definitions.

## Definitions

```lean
-- ProgCore.Prog is an inductive with constructors:
--   .ret (e : L.Expr Γ τ)
--   .letDet (e : L.Expr Γ τ') (k : Prog CB CS (τ' :: Γ) τ)
--   .doStmt (s : CS Γ) (k : Prog CB CS Γ τ)
--   .doBind (c : CB Γ τ') (k : Prog CB CS (τ' :: Γ) τ)

-- CmdBindProto has constructors:
--   .sample (id : YieldId) (v : View Γ) (K : ObsKernel v τ)
--   .choose (id : YieldId) (who : Player) (v : View Γ) (A : Act v τ)

-- evalProto σ p env = ProgCore.evalWith (ProtoSem σ) p env
-- evalProto is a def (not abbrev), unfolding through evalWith → evalProg_gen

-- These simp lemmas hold by rfl:
@[simp] lemma evalProto_ret σ e env : evalProto σ (.ret e) env = WDist.pure (L.eval e env) := rfl
@[simp] lemma evalProto_letDet σ e k env : evalProto σ (.letDet e k) env = evalProto σ k (L.eval e env, env) := rfl
@[simp] lemma evalProto_sample_bind σ id v K k env : evalProto σ (.sample id v K k) env = WDist.bind (K (v.proj env)) (fun x => evalProto σ k (x, env)) := rfl
@[simp] lemma evalProto_choose_bind σ id who v A k env : evalProto σ (.choose id who v A k) env = WDist.bind (σ.choose who id v A (v.proj env)) (fun x => evalProto σ k (x, env)) := rfl

-- observe simp lemma (not rfl, proved by cases on toBool):
@[simp] lemma evalProto_observe σ c k env : evalProto σ (.observe c k) env = if L.toBool (L.eval c env) then evalProto σ k env else WDist.zero

-- applyProfile definition (structural recursion):
def applyProfile (π : PProfile) : ProtoProg Γ τ → ProtoProg Γ τ
  | .ret e        => .ret e
  | .letDet e k   => .letDet e (applyProfile π k)
  | .doStmt s k   => .doStmt s (applyProfile π k)
  | .doBind c k   =>
      match c with
      | .sample id v K => .doBind (.sample id v K) (applyProfile π k)
      | .choose id who v A =>
          match π.choose? who id v A with
          | some Kdec => .doBind (.sample id v Kdec) (applyProfile π k)
          | none      => .doBind (.choose id who v A) (applyProfile π k)

-- Extends definition:
def Extends (σ : Profile) (π : PProfile) : Prop :=
  ∀ {Γ τ} (who : Player) (id : YieldId) (v : View Γ) (A : Act v τ) (Kdec : L.Env v.Δ → WDist (L.Val τ)),
    π.choose? who id v A = some Kdec → σ.choose who id v A = Kdec

-- ProgCore simp lemmas (hold by rfl):
@[simp] theorem evalWith_letDet S e k env : evalWith S (.letDet e k) env = evalWith S k (L.eval e env, env) := rfl
@[simp] theorem evalWith_doBind S c k env : evalWith S (.doBind c k) env = S.E.bind (S.handleBind c env) (fun v => evalWith S k (v, env)) := rfl
@[simp] theorem evalWith_doStmt S s k env : evalWith S (.doStmt s k) env = S.E.bind (S.handleStmt s env) (fun _ => evalWith S k env) := rfl

-- ProtoSem simp lemmas:
@[simp] lemma ProtoSem_handleBind_sample σ id v K env : (ProtoSem σ).handleBind (.sample id v K) env = K (v.proj env) := rfl
@[simp] lemma ProtoSem_handleBind_choose σ id who v A env : (ProtoSem σ).handleBind (.choose id who v A) env = σ.choose who id v A (v.proj env) := rfl

-- WDist.bind_pure: WDist.bind (WDist.pure a) f = f a  (this is a simp lemma)
-- WDist.zero_bind: WDist.bind WDist.zero f = WDist.zero  (this is a simp lemma)

-- EffWDist:
def EffWDist : ProgCore.Eff WDist where
  pure := WDist.pure
  bind := WDist.bind
  fail := WDist.zero
```

## Theorem to prove

```lean
theorem evalProto_applyProfile_of_extends
    (σ : Profile (L := L)) (π : PProfile (L := L))
    (hExt : Extends (L := L) σ π) :
    ∀ {Γ τ} (p : ProtoProg (L := L) Γ τ) (env : L.Env Γ),
      evalProto σ (applyProfile (L := L) π p) env
        =
      evalProto σ p env := by
  intro Γ τ p
  induction p with
  | ret e => intro env; simp [applyProfile]
  | letDet e k ih => intro env; simp only [applyProfile, evalProto_letDet]; exact ih env
  | doStmt s k ih =>
      intro env; cases s with
      | observe cond => simp only [applyProfile, evalProto_observe]; split <;> [exact ih env; rfl]
  | doBind c k ih =>
      intro env; cases c with
      | sample id v K =>
          -- applyProfile preserves sample: .doBind (.sample id v K) (applyProfile π k)
          -- Both sides reduce to WDist.bind (K (v.proj env)) (fun x => evalProto σ ? (x, env))
          -- Need: evalProto σ (applyProfile π k) (x, env) = evalProto σ k (x, env) for all x
          sorry
      | choose id who v A =>
          -- Two cases on π.choose? who id v A
          sorry
```

## My Difficulty

The problem is with the `simp` tactic. The terms `evalProto σ (.doBind (.sample id v K) (applyProfile π k)) env` and `evalProto σ (.doBind (.sample id v K) k) env` should both reduce to `WDist.bind (K (v.proj env)) (fun x => evalProto σ _ (x, env))`. The key equation is `∀ x, evalProto σ (applyProfile π k) (x, env) = evalProto σ k (x, env)` which is exactly the IH.

For the choose case with `π.choose? = some Kdec`, we need `hExt` to rewrite `σ.choose who id v A` to `Kdec`.

Please provide JUST the proof term for the two sorry cases (sample and choose). Use `simp` lemmas listed above, and the IH `ih : ∀ env, evalProto σ (applyProfile π k) env = evalProto σ k env`. Feel free to use `congr`, `ext`, `funext`, `simp`, etc.

IMPORTANT: the `.sample` and `.choose` smart constructors expand to `.doBind (.sample ...)` and `.doBind (.choose ...)` respectively. The `applyProfile` equations for .doBind use a nested `match c with | .sample ... | .choose ...` which means `simp [applyProfile]` alone may not fully reduce. You may need to use `show ... = ...` or unfold manually.
