import LoL.MProp.EffectObservations
import LoL.MProp.Instances

universe u v w

variable {m : Type u -> Type v} [Monad m] [LawfulMonad m] {α : Type u}
variable {l : Type u} [Preorder l]
variable [MProp m l]

def triple (pre : m PProp) (c : m α) (post : α -> m PProp) : Prop :=
  MProp.μ pre ≤ liftM (n := Cont l) c (MProp.μ (m := m) ∘ post)

def spec (pre : m PProp) (post : α -> m PProp) : Cont l α :=
  fun post => MProp.μ pre

lemma tripe_refine (pre : m PProp) (c : m α) (post : α -> m PProp) :
  triple pre c post →
  liftM (n := Cont l) c ≤
