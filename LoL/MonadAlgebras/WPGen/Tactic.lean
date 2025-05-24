import Lean

import LoL.MonadAlgebras.WPGen.Attr
-- import LoL.MonadAlgebras.WPGen.SpecAttr

open Lean Parser Meta Elab Term Command Tactic

def findSpec (prog : Expr) : TacticM (Ident × LoL.SpecType) := do
  let specs ← specAttr.find? prog
  let some ⟨specType, specName, _⟩ := specs.max? | throwError s!"no specs found for {prog}"
  -- let spec <- Term.elabTerm (mkIdent specName) none
  return (mkIdent specName, specType)

def Lean.MVarId.isWPGenGoal : MVarId → TacticM Bool
| mvarId => do
  let goalType <- mvarId.getType
  let_expr WPGen _m _mInst _α _l _lInst _mPropInst _ := goalType | return false
  return true

def isWPGenGoal : TacticM Bool := do
  (<- getMainGoal).isWPGenGoal

def hideNonWPGenGoals : TacticM Unit := do
  let goals <- getGoals
  let goals' <- goals.filterM (·.isWPGenGoal)
  setGoals goals'

elab "is_not_wpgen_goal" : tactic => do
  if ← isWPGenGoal then
    throwError "is a WPGen goal"
  else
    return

elab "hide_non_wpgen_goals" : tactic => do
  hideNonWPGenGoals

elab "show_all_goals" : tactic => do
  setGoals (← getUnassignedExprMVars).toList
  synthesizeSyntheticMVarsNoPostponing

elab "foo" : tactic => withMainContext do
  let mid <- mkFreshExprSyntheticOpaqueMVar (<- getMainTarget)
  (<- getMainGoal).assign mid


macro "try_resolve_spec_goals" : tactic => `(tactic| try is_not_wpgen_goal; solve | rfl | solve_by_elim | simp)

def generateWPStep : TacticM Unit := withMainContext do
  let goalType <- getMainTarget
  let_expr WPGen _m _mInst _α _l _lInst _mPropInst x := goalType | throwError "{goalType} is not a WPGen"
  match <- findSpec x with
  | (spec, .wpgen) =>
    evalTactic $ <- `(tactic| apply $spec)
  | (spec, .triple) =>
    evalTactic $ <- `(tactic|
      eapply $(mkIdent ``WPGen.spec_triple);
      apply $spec
      hide_non_wpgen_goals)


elab "wpgen_app" : tactic => generateWPStep
macro "wpgen_step" : tactic => `(tactic| (wpgen_app <;> intros <;> try_resolve_spec_goals))
macro "wpgen_intro" : tactic => `(tactic| (apply WPGen.intro; rotate_right))
macro "wpgen" : tactic => `(tactic| (
  wpgen_intro
  repeat' wpgen_step
  ))

macro "mwp" : tactic => `(tactic| (wpgen <;> try simp only [logicSimp, wpSimp]))

attribute [spec high, wpSimp] WPGen.forWithInvariantDecreasing WPGen.forWithInvariantLoop WPGen.if
attribute [spec, wpSimp] WPGen.bind WPGen.pure WPGen.assert WPGen.forWithInvariant WPGen.map
attribute [wpSimp] spec WPGen.spec_triple_invs

@[spec, wpSimp]
def WPGen.set (i : ℕ) : WPGen (set i : StateM ℕ Unit) := by
  refine ⟨fun post _ => post .unit i, True, ?_⟩
  sorry

@[spec, wpSimp]
def WPGen_get : WPGen (get : StateM ℕ ℕ) := by
  refine ⟨fun post s => post s s, True, ?_⟩
  sorry

@[logicSimp]
lemma leE (l : Type u) [PartialOrder l] (a b : α -> l) : a ≤ b ↔ ∀ x, a x ≤ b x := by
  rfl
@[logicSimp]
lemma lePropE (a b : Prop) : (a ≤ b) = (a → b) := by
  rfl

@[logicSimp]
lemma pureE (l : Type u) [CompleteLattice l] (a : Prop) : (⌜a⌝ : α -> l) = fun _ => ⌜a⌝ := by
  simp [LE.pure]; split <;> rfl

@[logicSimp]
lemma purePropE  : (⌜a⌝ : Prop) = a := by
  simp [LE.pure]

@[logicSimp]
lemma infPropE (a b : Prop) : (a ⊓ b) = (a ∧ b) := by
  rfl

@[logicSimp]
lemma infE (l : Type u) [CompleteLattice l] (a b : α -> l) : (a ⊓ b) = fun x => a x ⊓ b x := by
  rfl

@[logicSimp]
lemma supE (l : Type u) [CompleteLattice l] (a b : α -> l) : (a ⊔ b) = fun x => a x ⊔ b x := by
  rfl

@[logicSimp]
lemma supPropE (a b : Prop) : (a ⊔ b) = (a ∨ b) := by
  rfl

@[logicSimp]
lemma iInfE (l : Type u) [CompleteLattice l] (a : ι -> α -> Prop) : (⨅ i, a i) = fun x => ⨅ i, a i x := by
  ext; simp

@[logicSimp]
lemma iSupE (l : Type u) [CompleteLattice l] (a : ι -> α -> Prop) : (⨆ i, a i) = fun x => ⨆ i, a i x := by
  ext; simp

attribute [logicSimp] forall_const implies_true and_true true_and
attribute [simp←] Nat.mul_add_one

def mult (n : Nat) : StateM Nat Unit := do
  let s <- get
  for i in [1:n+1] do
    invariant fun s' => s' = s * i
    let accOld <- get
    set (accOld + s)

lemma mult_spec (i n : Nat) :
  triple (· = n) (mult i) (fun _ => (· = n * (i + 1))) := by
  unfold mult
  mwp
  { -- proving invariant preservation
    intros; mwp; simp }
  simp













  -- let stx ← stx?.getDM do
  --   unless prog.getAppFn'.isConst do throwError s!"not an application of a constant: {prog}"

  --   if specs.isEmpty then throwError s!"no specs found for {prog}"
  --   if specs.size > 1 then throwError s!"multiple specs found for {prog}: {specs}"
  --   return mkIdent specs[0]!
  -- trace[mpl.tactics.spec] "spec syntax: {stx}"
  -- let P ← mkFreshExprMVar (mkApp (mkConst ``PreCond) ps) (userName := `P)
  -- let Q ← mkFreshExprMVar (mkApp2 (mkConst ``PostCond) α ps) (userName := `Q)
  -- let expectedTy := mkApp7 (mkConst ``triple [u]) m ps instWP α prog P Q
  -- check expectedTy
  -- trace[mpl.tactics.spec] "expected type: {← instantiateMVars expectedTy}"
  -- let (spec, mvarIds) ← elabTermForSpec stx expectedTy
  -- trace[mpl.tactics.spec] "inferred spec: {← instantiateMVars spec}"
  -- Term.synthesizeSyntheticMVarsNoPostponing
  -- trace[mpl.tactics.spec] "inferred spec, post synthesis: {← instantiateMVars spec}"
  -- let mvarIds ← mvarIds.filterM (not <$> ·.isAssigned)
  -- return (spec, mvarIds, P, Q)
