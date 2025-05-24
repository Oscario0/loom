import Mathlib.Logic.Function.Basic
import Mathlib.Order.CompleteBooleanAlgebra
import Mathlib.Order.Lattice
import Mathlib.Order.Basic
import Aesop

import LoL.QuotientExtra
import LoL.Meta
import LoL.MonadAlgebras.WP
import LoL.MonadAlgebras.WLP

universe u v w

/-
  it seems like we cannot have a uniform definition of GhostT that works for arbitrary monads because of two reasons:
  1. the type inference gets very messy
  2. when compose two monads `m` as code and `n` as ghost code, its important to know that their effects are independent.
    This is not true if one of then is `Except` with partial correctness for exceptions.
  3. such instances should be proven for each partricuar combination of monads.
-/

section GhostStateTransformer

variable {mc mg : Type u -> Type v} {α β : Type u} [Monad mc] [Monad mg]

inductive GhostT (mc mg : Type u -> Type v) (α : Type u) where
  | code {β} (c : mc β) (cont : β -> GhostT mc mg α) : GhostT mc mg α
  | ghost (c : mg PUnit) (cont : GhostT mc mg α) : GhostT mc mg α
  | pure (x : α) : GhostT mc mg α

def GhostT.bind (x : GhostT mc mg α) (f : α -> GhostT mc mg β) : GhostT mc mg β :=
  match x with
  | .code c g => .code c (fun x => bind (g x) f)
  | .ghost c g => .ghost c (bind g f)
  | .pure x => f x

instance : Monad (GhostT mc mg) where
  pure := .pure
  bind := .bind

instance : MonadLift mc (GhostT mc mg) where
  monadLift := fun x => .code x .pure

def GhostT.ghostCode (x : mg PUnit) : GhostT mc mg PUnit :=
  .ghost x $ .pure .unit

variable [CompleteLattice lc] [CompleteLattice lg] [MPropOrdered mc lc] [MPropOrdered mg lg]

variable {m : Type u -> Type v} [Monad m] [MonadLift mc m] [MonadLift mg m] [CompleteLattice l] [MPropOrdered m l]

class LawfulMPropLift (n m) [Monad n] [Monad m] [MonadLift n m] [PartialOrder l'] [MPropOrdered n l']  [PartialOrder l] [MPropOrdered m l] where
  ι : l' →o l
  μ_ι : ∀ x : n l', MPropOrdered.μ (liftM (n := m) $ ι <$> x) = ι (MPropOrdered.μ x)

variable [LawfulMPropLift mc m] [LawfulMPropLift mg m]

class IndepLift (mc mg : Type u -> Type v) (m : outParam (Type u -> Type v)) where
  [lift₁ : MonadLift mc m]
  [lift₂ : MonadLift mg m]

-- instance [IndepLift mc mg m] : MonadLiftT mc m := IndepLift.lift₁ mg

-- class LawfulIndepLift (m : outParam (Type u -> Type v)) [MonadLift mc m] [MonadLift mg m] [Monad m] [PartialOrder l] [MPropOrdered m l] [LawfulMPropLift mc m] [LawfulMPropLift mg m] where


-- def GhostT.μ : GhostT mc mg l -> l
--   | .code c g => wp (liftM (n := m) c) (fun x => μ (g x))
--   | .ghost c g => wp (liftM (n := m) c) (fun _ => μ g)
--   | .pure l => l

-- instance (m : outParam (Type u -> Type v)) [Monad m] [MPropOrdered m l] [MonadLift mc m] [MonadLift mg m] [LawfulMPropLift mc m] [LawfulMPropLift mg m] [LawfulIndepLift (mc := mc) (mg := mg) m] : MPropOrdered (GhostT mc mg) l where
--   μ := GhostT.μ
--   μ_ord_pure := by aesop
