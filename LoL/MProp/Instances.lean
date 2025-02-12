import LoL.MProp.EffectObservations

instance : MPropPartialOrder Id Prop where
  μ := id
  μSur := by exact Function.surjective_id
  μOrd := by simp

instance (σ : Type) (l : Type) (m : Type -> Type)
  [PartialOrder l]
  [Monad m] [LawfulMonad m] [inst: MPropPartialOrder m l] : MPropPartialOrder (StateT σ m) (σ -> l) where
  μ := fun sp s => Prod.fst <$> sp s |> inst.μ
  μSur := by
    intro x; simp [funext_iff];
    apply (Classical.skolem (p := fun s b => MPropPartialOrder.μ (Prod.fst <$> b) = x s)).mp
    intro s; rcases inst.μSur (x s) with ⟨y, h⟩; exists (y >>= fun y => pure (y, s))
    simp [h]
  μOrd := by
    intros α f g
    simp [Function.comp, Pi.hasLe, Pi.partialOrder, Pi.preorder, inferInstanceAs]; intros le x s
    have leM := @inst.μOrd (α × σ) (fun as => Prod.fst <$> f as.1 as.2) (fun as => Prod.fst <$> g as.1 as.2)
    simp only [Function.comp, Pi.hasLe, <-map_bind] at leM
    apply leM; simp only [implies_true, le]

instance (ρ : Type) (l : Type) (m : Type -> Type)
  [PartialOrder l]
  [Monad m] [LawfulMonad m] [inst: MPropPartialOrder m l] : MPropPartialOrder (ReaderT ρ m) (ρ -> l) where
  μ := fun rp r => rp r |> inst.μ
  μSur := by
    intro x; simp [funext_iff];
    apply (Classical.skolem (p := fun r b => MPropPartialOrder.μ b = x r)).mp
    intro r; rcases inst.μSur (x r) with ⟨y, h⟩; exists y
  μOrd := by
    intros α f g
    simp [Function.comp, Pi.hasLe, Pi.partialOrder, Pi.preorder, inferInstanceAs]; intros le x r
    have leM := @inst.μOrd α (f · r) (g · r)
    simp only [Function.comp, Pi.hasLe, <-map_bind] at leM
    apply leM; simp only [implies_true, le]


abbrev Except.getD {ε α} (default : α)  : Except ε α -> α
  | Except.ok p => p
  | Except.error _ => default

abbrev Except.bind' {m : Type -> Type} {ε α β} [Monad m] : Except ε α -> (α -> ExceptT ε m β) -> ExceptT ε m β :=
  fun x f => bind (m := ExceptT ε m) (pure (f := m) x) f

lemma Except.bind'_bind {m : Type -> Type} {ε α β} [Monad m] [LawfulMonad m] (i : m (Except ε α)) (f : α -> ExceptT ε m β) :
  (i >>= fun a => Except.bind' a f) = bind (m := ExceptT ε m) i f := by
  simp [Except.bind', bind, bind_assoc, ExceptT.bind]; rfl

def MPropExcept (df : Prop) (ε : Type) (l : Type) (m : Type -> Type)
  [PartialOrder l]
  [Monad m] [LawfulMonad m] [inst: MPropPartialOrder m l] : MPropPartialOrder (ExceptT ε m) l where
  μ := fun e => inst.μ $ Except.getD df <$> e
  μSur := by
    intro x; simp [funext_iff];
    rcases inst.μSur x with ⟨y, h⟩
    exists Functor.map (β := Except _ _) .ok y; simp [h]
  μOrd := by
    intros α f g
    simp [Function.comp, Pi.hasLe, Pi.partialOrder, Pi.preorder, inferInstanceAs]; intros le x
    have leM := @inst.μOrd (Except ε α)
      (fun x => Except.getD df <$> Except.bind' x f)
      (fun x => Except.getD df <$> Except.bind' x g)
    simp only [Function.comp, Pi.hasLe, <-map_bind, Except.bind'_bind] at leM
    apply leM; rintro (e | p) <;> simp [Except.bind', ExceptT.instMonad, ExceptT.bind, ExceptT.bindCont]
    apply le

namespace PatialCorrectness
scoped
instance (ε : Type) (l : Type) (m : Type -> Type)
  [PartialOrder l]
  [Monad m] [LawfulMonad m] [inst: MPropPartialOrder m l] : MPropPartialOrder (ExceptT ε m) l := MPropExcept True ε l m
end PatialCorrectness

namespace TotalCorrectness
instance (ε : Type) (l : Type) (m : Type -> Type)
  [PartialOrder l]
  [Monad m] [LawfulMonad m] [inst: MPropPartialOrder m l] : MPropPartialOrder (ExceptT ε m) l := MPropExcept False ε l m
end TotalCorrectness

#guard_msgs (drop info) in
#synth MPropPartialOrder (StateM Int) (Int -> Prop)

#guard_msgs (drop info) in
#synth MPropPartialOrder (ReaderT Bool (StateM Int)) (Bool -> Int -> Prop)
