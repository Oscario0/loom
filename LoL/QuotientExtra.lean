universe u v w

namespace Quotient

variable {α : Sort u} {β : Sort v} {γ : Sort w}

noncomputable def Quotient.rep {s : Setoid α} (q : Quotient s) : α :=
  Classical.choose (Quotient.exists_rep q)

protected noncomputable abbrev liftOnFun
  {s : Setoid α} (q : γ -> Quotient s) (f : (γ -> α) → β) : β :=
  f (fun x => Quotient.rep (q x))

@[simp]
theorem liftOnFun_correct {s : Setoid α} (q : γ -> α) (f : (γ -> α) → β) :
  ((a b : γ -> α) → (∀ x, a x ≈ b x) → f a = f b) ->
  Quotient.liftOnFun (fun x => Quotient.mk s (q x)) f = f q := by
  intro h
  apply h; simp [Quotient.rep]; intro y
  have h := fun x => Classical.choose_spec (@Quotient.exists_rep _ s x)
  exact exact (h (Quotient.mk s (q y)))




end Quotient
