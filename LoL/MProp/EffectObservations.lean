import LoL.MonadUtil
import LoL.SpecMonad

universe u v w

variable (m : Type -> Type u)

class MProp [Monad m] (l : outParam (Type u)) where
  μ : m Prop -> l
  μSur : μ.Surjective
  bind : ∀ {α : Type} (x : m α) (f g : α -> m Prop),
    μ ∘ f = μ ∘ g ->
    μ (x >>= f) = μ (x >>= g)

noncomputable def MProp.ι {m} {l : Type u} [Monad m] [MProp m l] : l -> m Prop :=
  fun x => (μSur x).choose

lemma MProp.cancel {m} {l : Type u} [Monad m] [MProp m l] (x : l) : μ (MProp.ι (m := m) x) = x :=
  (μSur x).choose_spec

lemma MProp.cancelM {l} [Monad m] [MProp m l] {α : Type} (x : m α) (f : _ -> _) :
    μ (x >>= MProp.ι ∘ μ ∘ f) = μ (x >>= f) := by
  apply MProp.bind; unfold Function.comp; simp [MProp.cancel]

noncomputable
abbrev MProp.lift {m : Type -> Type} {l : Type} [Monad m] [LawfulMonad m] [MProp m l] :
  {α : Type} -> m α -> Cont l α := fun x f => μ $ f <$> x >>= MProp.ι

noncomputable
instance (l : Type) {m : Type -> Type} [Monad m] [LawfulMonad m] [MProp m l] : LawfulMonadLift m (Cont l) where
  monadLift := MProp.lift
  monadMapPure := by
    intro α x; simp [monadLift, pure]; unfold MProp.lift; simp [map_pure, MProp.cancel]
  monadMapBind := by
    intros α β x f; simp [monadLift, bind]; unfold MProp.lift; ext g
    rw (config := { occs := .pos [2] }) [map_eq_pure_bind]
    simp only [bind_assoc, pure_bind]
    erw [MProp.cancelM]; simp


class MPropOrdered (l : outParam (Type u)) [Monad m] [Preorder l] extends MProp m l where
  μOrd {α : Type} :
    ∀ (f g : α -> m Prop), μ ∘ f <= μ ∘ g -> (μ $ · >>= f) ≤ (μ $ · >>= g)

lemma Cont.monotone_lift {l : Type} {m : Type -> Type} [Monad m] [LawfulMonad m] [Preorder l] [MPropOrdered m l] :
  ∀ {α : Type} (x : m α), MProp.lift x |>.monotone := by
  unfold Cont.monotone; intros; simp [MProp.lift]
  apply MPropOrdered.μOrd; intro; simp [MProp.cancel, *]

class MPropPartialOrder (l : outParam (Type u)) [Monad m] [PartialOrder l] where
  μ : m Prop -> l
  μSur : μ.Surjective
  μOrd {α : Type} :
    ∀ (f g : α -> m Prop), μ ∘ f <= μ ∘ g -> (μ $ · >>= f) ≤ (μ $ · >>= g)

instance OfMPropPartialOrdered {m : Type -> Type} {l : Type} [Monad m] [PartialOrder l] [MPropPartialOrder m l] : MPropOrdered m l where
  μ := MPropPartialOrder.μ
  μSur := MPropPartialOrder.μSur
  μOrd := MPropPartialOrder.μOrd
  bind := by intros; apply PartialOrder.le_antisymm <;> apply MPropPartialOrder.μOrd <;> simp_all only [le_refl]

-- instance (σ : Type) : MPropPartialOrder (StateM σ) (σ -> Prop) where
--   μ := fun sp s => sp s |>.1
--   μSur := by intro x; simp; exists fun s => (x s, s)
--   μOrd := by
--     simp [funext_iff, bind, StateT.bind];
--     intros α f g h x s; simp; split; solve_by_elim [h]

-- instance (σ : Type) : MPropPartialOrder (ReaderM σ) (σ -> Prop) where
--   μ := fun sp s => sp s
--   μSur := by intro x; simp
--   μOrd := by
--     simp [funext_iff, bind, ReaderT.bind];
--     intros α f g h x s; simp; solve_by_elim [h]
