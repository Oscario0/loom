import Mathlib.Logic.Function.Basic
import Aesop
import LoL.QuotientExtra
import LoL.Meta
import LoL.MProp.HoareTriples

universe u v w

section Outcomes

variable {m : Type u -> Type v} {l : Type u} [Monad m] [PartialOrder l] [MPropPartialOrder m l]

def isReachable {α : Type u} (out : α) (x : m α) :=
  ¬ mtriple (pure True) x fun x => pure (x ≠ out)

def outcomes {α : Type u} (x : m α) := { out : α // isReachable (l := l) out x }

end Outcomes

section NonDetermenisticTransformer

structure NonDetT (m : Type u -> Type v) (l : Type u)
  [Monad m] [PartialOrder l] [MPropPartialOrder m l] (α : Type u) where
  tp  : Type w
  sem : tp → m α

variable {m : Type u -> Type v} {l : Type u} {α β : Type u} [Monad m] [PartialOrder l] [MPropPartialOrder m l]

def NonDetT.pure (x : α) : NonDetT m l α := ⟨PUnit, fun _ => return x⟩

def NonDetT.bind (x : NonDetT m l α) (f : α → NonDetT m l β) : NonDetT m l β :=
  ⟨
    (tp : x.tp) × (out : outcomes (l := l) (x.sem tp)) × (f out.val).tp,
    fun ⟨_, out, tp'⟩ => f out.val |>.sem tp'
  ⟩

def NonDetT.pick (τ : Type u) : NonDetT m l τ := ⟨τ, Pure.pure⟩

structure PropType (α : Prop) : Type w where
  prf : α

def NonDetT.assume (as : Prop) : NonDetT m l PUnit := ⟨PropType as, fun _ => return .unit⟩

instance : Monad (NonDetT m l) where
  pure := .pure
  bind := .bind

instance foo : MonadLift m (NonDetT m l) where
  monadLift := fun x => ⟨PUnit, fun _ => x⟩

class MonadInfNonDet (m : Type u → Type v) where
  pick : (τ : Type u) → m τ
  assume : Prop → m PUnit

export MonadInfNonDet (pick assume)

instance : MonadInfNonDet (NonDetT m l) where
  pick   := .pick
  assume := .assume

theorem pick_tp (τ : Type u) : (pick (m := NonDetT m l) τ).tp = τ := rfl
theorem assume_tp (as : Prop) : (assume (m := NonDetT m l) as).tp = PropType as := rfl
theorem lift_tp {α : Type u} (x : m α) : (liftM (n := NonDetT m l) x).tp = PUnit := rfl

theorem pick_isReachable τ out t [LawfulMonad m] :
  isReachable out ((pick (m := NonDetT m l) τ).sem t) = (out = t) := by
    simp [isReachable, pick, NonDetT.pick]
    rw [mtriple_pure]; constructor
    { contrapose; simp; intro neq;
      solve_by_elim [MPropPartialOrder.μ_ord_pure] }
    rintro rfl; simp; intro
    apply MPropPartialOrder.μ_nontriv (m := m)
    apply le_antisymm <;> try assumption
    apply MPropPartialOrder.μ_bot

theorem pick_outcomes [LawfulMonad m] (τ : Type u) (t : τ) :
  outcomes ((pick (m := NonDetT m l) τ).sem t) = { out // out = t } := by
    simp [outcomes, pick_isReachable]

theorem pick_outcomesE [LawfulMonad m] (τ : Type u) (t : τ)
  (out : outcomes ((pick (m := NonDetT m l) τ).sem t)) :
  out.val = t := by
    have: isReachable out.val ((pick (m := NonDetT m l) τ).sem t) := by apply out.prop
    rwa [pick_isReachable] at this

instance NonDetM.Setoid : Setoid (NonDetT m l α) where
  r := fun ⟨tp₁, val₁⟩ ⟨tp₂, val₂⟩ => ∃ f : tp₁ -> tp₂, f.Bijective ∧ ∀ x, val₁ x = val₂ (f x)
  iseqv := {
    refl := by
      rintro ⟨tp, val⟩; simp; exists id; simp; exact Function.bijective_id
    symm := by
      rintro ⟨tp₁, val₁⟩ ⟨tp₂, val₂⟩; simp; intro f bij valf
      exists f.surjInv bij.2; constructor
      { refine Function.bijective_iff_has_inverse.mpr ?_; exists f; constructor
        { refine Function.RightInverse.leftInverse ?_
          exact Function.rightInverse_surjInv bij.right }
        refine Function.LeftInverse.rightInverse ?_
        exact Function.leftInverse_surjInv bij }
      simp [valf, Function.surjInv_eq]
    trans := by
      rintro ⟨tp₁, val₁⟩ ⟨tp₂, val₂⟩ ⟨tp₃, val₃⟩; simp; intros f₁ bij₁ valf₁ f₂ bij₂ valf₂
      exists f₂ ∘ f₁; constructor
      { exact Function.Bijective.comp bij₂ bij₁ }
      aesop
  }

lemma bind_eq {x y : NonDetT m l α} {f g : α → NonDetT m l β} :
  x ≈ y ->
  (∀ a, f a ≈ g a) ->
  (NonDetT.bind x f) ≈ (NonDetT.bind y g) := by
  rcases x with ⟨tp₁, val₁⟩
  rcases y with ⟨tp₂, val₂⟩
  rintro ⟨eq, bij, valf⟩
  simp only [HasEquiv.Equiv, Setoid.r]; intro r
  rcases Classical.skolem.mp r with ⟨eqf, bijf⟩; clear r
  simp only [NonDetT.bind]
  exists by
    intro ⟨t, outs, ftp⟩
    -- intros ⟨⟩




notation "NonDetT" t => NonDetT t _

end NonDetermenisticTransformer


section Example

open TotalCorrectness

abbrev myM := NonDetT (StateT Nat (ExceptT String Id))

def ex : myM ℕ :=
  do
    let x ← pick ℕ
    let y ← pick ℕ
    set (x + y)
    assume (x > y)
    pure (x + y)


-- set_option pp.explicit true

example (P : _ -> Prop) : P (ex) := by
  dsimp [ex, bind, pure]
  unfold InfNonDetT.bind InfNonDetT.pure;
  simp [set]
  simp [pick_tp, assume_tp, lift_tp, pick_outcomesE]
  -- #check @pick_outcomes (StateT Nat (ExceptT String Id)) _ inferInstance inferInstance inferInstance inferInstance ℕ
  -- simp []
  have : ∀ (tp : ℕ) (out : outcomes ((@pick myM instMonadInfNonDetInfNonDetT ℕ).sem tp)), out.val = tp := by
    intro; simp [pick_outcomesE]



#reduce! ex

end Example
