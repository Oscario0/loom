
import Mathlib.Logic.Function.Basic
import Mathlib.Order.CompleteBooleanAlgebra
import Mathlib.Order.Lattice
import Mathlib.Order.Basic

import LoL.MProp.WP
import LoL.MProp.WLP
import LoL.MProp.NonDetT.Basic

universe u v w

section NonDetermenisticTransformer

structure State (σ) where
  visited  : List σ

/- from  -/
def Gen : Type u -> Type v := sorry
instance : Monad Gen := sorry

example : True := by grind

class Sample (t : Type u) (p : τ -> Prop) where
  gen : Gen (List t)
  -- prop : ∀ x, x ∈ gen -> p x

class inductive SampleNonDet {m α} : NonDetT m α -> Type _ where
  | pure : ∀ (x : α), SampleNonDet (NonDetT.pure x)
  | vis {β} (x : m β) (f : β → NonDetT m α) :
      (∀ y, SampleNonDet (f y)) → SampleNonDet (.vis x f)
  | pickCont (τ : Type u) (p : τ -> Prop) (f : τ → NonDetT m α) {_ : Sample τ p} :
      (∀ x, SampleNonDet (f x)) → SampleNonDet (.pickCont τ p f)

instance : Monad List where
  pure := List.singleton
  bind x f := x.flatMap f

def NonDetT.sample {σ α : Type} [BEq σ] [BEq α] [Hashable σ] [Hashable α] (s₀ : σ) :
  (x : NonDetT (StateM σ) α) -> [SampleNonDet x] -> Gen (List σ)
    | .pure _, _ => return [s₀]
    | .vis x f, .vis _ _ _ =>
       let (res, s) := x.run s₀
       NonDetT.sample s (f res)
    | .pickCont _ p f, .pickCont _ _ _ _ => do
      let ts <- Sample.gen p
      let mut sts := []
      for t in ts do
        let st <- NonDetT.sample s₀ (f t)
        sts := sts ++ st
      return sts
