import Vegas.LetGames.Denotations
import Vegas.LetGames.EUBridge

/-!
# WF_GameProg: Well-Formedness Bundle for ParentProtoProg

Bundles the scattered well-formedness predicates into a single structure:
- `NodupActions` (from Denotations)
- `NonEmptyActions` (from Denotations)
- `WFChanceOnProg` (from Proto)
- `ObserveFree` (from EUBridge)
- `NoDupYieldIds` (from Proto)

Master theorems combine existing results:
- `WF_GameProg.wfTree`: well-formed programs produce well-formed EFG trees
- `WF_GameProg.euPreservation`: Proto EU = directEU for well-formed programs
-/

namespace Proto

open Defs Prog Env

/-- Well-formedness bundle for a `ParentProtoProg` used as a game program.
    Collects all the side conditions needed for the EFG bridge. -/
structure WF_GameProg {Γ : BasicLang.Ctx} {τ : BasicLang.Ty}
    (p : ParentProtoProg (W := NNReal) (L := BasicLang) Γ τ) : Prop where
  nodupActions : NodupActions (L := BasicLang) p
  nonEmptyActions : NonEmptyActions (L := BasicLang) p
  wfChance : WFChanceOnProg ReachAll (ParentProtoProg.embed p)
  observeFree : ObserveFree p
  nodupYieldIds : NoDupYieldIds (ParentProtoProg.embed p)
  constantArity : ConstantArityAtSite (L := BasicLang) p

/-! ## Master theorems -/

/-- A well-formed game program produces a well-formed EFG tree. -/
theorem WF_GameProg.wfTree
    {Γ : BasicLang.Ctx} {τ : BasicLang.Ty}
    {p : ParentProtoProg (W := NNReal) (L := BasicLang) Γ τ}
    (h : WF_GameProg p)
    (u : Proto.Utility (L := BasicLang) τ)
    (env : BasicLang.Env Γ) :
    EFG.WFTree (p.toEFG u env) :=
  Proto.toEFG_wfTree _ u env h.nodupActions h.nonEmptyActions h.wfChance

/-- For well-formed programs, Proto EU equals direct EU. -/
theorem WF_GameProg.euPreservation
    {Γ : BasicLang.Ctx} {τ : BasicLang.Ty}
    {p : ParentProtoProg (W := NNReal) (L := BasicLang) Γ τ}
    (h : WF_GameProg p)
    (σ : Profile (L := BasicLang) (W := NNReal))
    (u : Proto.Utility (L := BasicLang) τ) (who : Player)
    (env : BasicLang.Env Γ) :
    EU_dist (p.eval σ env) u who = p.directEU σ u who env :=
  eu_preservation_directEU σ u who _ env h.observeFree

/-! ## Constructor closure lemmas -/

/-- `ret` is trivially well-formed (no yields at all). -/
theorem WF_GameProg.ret {Γ : BasicLang.Ctx} {τ : BasicLang.Ty}
    (e : BasicLang.Expr Γ τ) :
    WF_GameProg (ParentProtoProg.ret (W := NNReal) e) where
  nodupActions := trivial
  nonEmptyActions := trivial
  wfChance := trivial
  observeFree := trivial
  nodupYieldIds := List.nodup_nil
  constantArity := trivial

/-- `letDet` preserves well-formedness. -/
theorem WF_GameProg.letDet {Γ : BasicLang.Ctx} {τ τ' : BasicLang.Ty}
    (e : BasicLang.Expr Γ τ')
    {k : ParentProtoProg (W := NNReal) (L := BasicLang) (τ' :: Γ) τ}
    (hk : WF_GameProg k) :
    WF_GameProg (ParentProtoProg.letDet e k) where
  nodupActions := hk.nodupActions
  nonEmptyActions := hk.nonEmptyActions
  wfChance := hk.wfChance
  observeFree := hk.observeFree
  nodupYieldIds := hk.nodupYieldIds
  constantArity := hk.constantArity

/-- `sample` preserves well-formedness with additional conditions on the kernel. -/
theorem WF_GameProg.sample {Γ : BasicLang.Ctx} {τ τ' : BasicLang.Ty}
    (id : YieldId) (ps : ParentSite (L := BasicLang) Γ)
    (K : ObsKernel (W := NNReal) (viewOfVarSpec ps.vars) τ')
    {k : ParentProtoProg (W := NNReal) (L := BasicLang) (τ' :: Γ) τ}
    (hk : WF_GameProg k)
    (hprob : ∀ env : BasicLang.Env Γ, IsProb (K ((viewOfVarSpec ps.vars).proj env)))
    (hfresh : id ∉ k.yieldIds) :
    WF_GameProg (ParentProtoProg.sample id ps K k) where
  nodupActions := hk.nodupActions
  nonEmptyActions := hk.nonEmptyActions
  wfChance := ⟨fun env _ => hprob env, hk.wfChance⟩
  observeFree := hk.observeFree
  constantArity := hk.constantArity
  nodupYieldIds := by
    change (id :: Proto.yieldIds (ParentProtoProg.embed k)).Nodup
    rw [ParentProtoProg.yieldIds_embed]
    refine List.nodup_cons.mpr ⟨hfresh, ?_⟩
    have := hk.nodupYieldIds
    unfold NoDupYieldIds at this
    rwa [ParentProtoProg.yieldIds_embed] at this

/-- `choose` preserves well-formedness with conditions on actions and id uniqueness. -/
theorem WF_GameProg.choose {Γ : BasicLang.Ctx} {τ τ' : BasicLang.Ty}
    (id : YieldId) (who : Player) (ps : ParentSite (L := BasicLang) Γ)
    (A : Act (viewOfVarSpec ps.vars) τ')
    {k : ParentProtoProg (W := NNReal) (L := BasicLang) (τ' :: Γ) τ}
    (hk : WF_GameProg k)
    (hnd : ∀ obs, (A obs).Nodup)
    (hne : ∀ obs, A obs ≠ [])
    (hfresh : id ∉ k.yieldIds)
    (hca : ∀ obs₁ obs₂, (A obs₁).length = (A obs₂).length) :
    WF_GameProg (ParentProtoProg.choose id who ps A k) where
  nodupActions := ⟨hnd, hk.nodupActions⟩
  nonEmptyActions := ⟨hne, hk.nonEmptyActions⟩
  wfChance := hk.wfChance
  observeFree := hk.observeFree
  constantArity := ⟨hca, hk.constantArity⟩
  nodupYieldIds := by
    change (id :: Proto.yieldIds (ParentProtoProg.embed k)).Nodup
    rw [ParentProtoProg.yieldIds_embed]
    refine List.nodup_cons.mpr ⟨hfresh, ?_⟩
    have := hk.nodupYieldIds
    unfold NoDupYieldIds at this
    rwa [ParentProtoProg.yieldIds_embed] at this

end Proto
