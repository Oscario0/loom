import Mathlib.Data.Set.Basic

universe u

/-
Notes: try to comprehend a haskell NoNDet monad definition.

define `assume` and `choose` functions.
Hypothesis: Should be able to define a partial `Many` interpreter!
-/

def NonDetM (α : Type u) := Set α
