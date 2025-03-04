import Mathlib.Logic.Function.Basic
import Aesop
import LoL.QuotientExtra
import LoL.Meta


universe u v w

structure NonDetM (α : Type u) where
  tp : Type v
  val : tp → α

variable {α : Type u} {β : Type v}

def NonDetM.pure (x : α) : NonDetM α := ⟨Unit, fun _ => x⟩

def NonDetM.bind (x : NonDetM α) (f : α → NonDetM β) : NonDetM β :=
  ⟨Σ (t : x.tp), f (x.val t) |>.tp, fun b => f (x.val b.fst) |>.val b.snd⟩

instance : Monad NonDetM where
  pure := NonDetM.pure
  bind := NonDetM.bind


abbrev NonDetM.choose (τ : Type u) : NonDetM τ := ⟨τ, id⟩
abbrev NonDetM.assume (as : Prop) : NonDetM Unit := ⟨PLift as, fun _ => ()⟩

def NonDetM.run (x : NonDetM α) [Inhabited x.tp] : α := x.val default

abbrev succ (x : Int) : NonDetM Int :=
  do
    let y <- NonDetM.choose Int
    NonDetM.assume (y > x)
    let z <- NonDetM.choose Int
    NonDetM.assume (z < x)
    return y + z

example (P : _ -> Prop) i : P ((succ i)) := by
  dsimp [succ, bind, pure, NonDetM.choose, NonDetM.assume, NonDetM.pure, NonDetM.bind]
  -- simp [StateT.bind, StateT.get, pure, NonDetM.pure, liftM, monadLift, MonadLift.monadLift]
  -- simp [succ', bind, pure, NonDetM.choose, NonDetM.assume, NonDetM.pure, NonDetM.bind, StateT.lift, StateT.pure]


abbrev succ' : StateT Int NonDetM Int :=
  do
    let x <- get
    set (x + 1)
    let y <- NonDetM.choose Int
    NonDetM.assume (y > x)
    return y

example (P : _ -> Prop) i : P ((succ' i).tp) := by
  simp [succ', bind, pure, NonDetM.choose, NonDetM.assume, NonDetM.pure, NonDetM.bind]
  simp [StateT.bind, StateT.get, pure, NonDetM.pure, liftM, monadLift, MonadLift.monadLift]
  simp [succ', bind, pure, NonDetM.choose, NonDetM.assume, NonDetM.pure, NonDetM.bind, StateT.lift, StateT.pure]


  sorry

#reduce! ((succ 5).tp)

#reduce (succ 5).val (by
  dsimp [succ, bind, pure, NonDetM.choose, NonDetM.assume, NonDetM.pure, NonDetM.bind]
  exact ⟨6, PLift.up (by omega), ()⟩)





instance NonDetM.Setoid : Setoid (NonDetM α) where
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

lemma bind_eq {x y : NonDetM α} {f g : α → NonDetM β} :
  x ≈ y ->
  (∀ a, f a ≈ g a) ->
  (NonDetM.bind x f) ≈ (NonDetM.bind y g) := by
  rcases x with ⟨tp₁, val₁⟩
  rcases y with ⟨tp₂, val₂⟩
  rintro ⟨eq, bij, valf⟩
  simp [HasEquiv.Equiv, Setoid.r]; intro r
  rcases Classical.skolem.mp r with ⟨fr, fbij⟩
  simp [NonDetM.bind]
  admit


abbrev LawfullNonDetM α := Quotient (@NonDetM.Setoid α)

variable {α : Type u} {β : Type v}

abbrev LawfullNonDetM.mk : NonDetM α -> LawfullNonDetM α := Quotient.mk NonDetM.Setoid

def LawfullNonDetM.pure (x : α) := NonDetM.pure x |> LawfullNonDetM.mk

noncomputable def LawfullNonDetM.bind (x : LawfullNonDetM α) (f : α → LawfullNonDetM β) : LawfullNonDetM β :=
  Quotient.liftOn x (fun x => Quotient.liftOnFun f (fun f => NonDetM.bind x f))
  (by
   intro a b eq; simp; sorry ) |> LawfullNonDetM.mk
