import LoL.MonadAlgebras.EffectObservations
import Plausible.Gen

abbrev UProp : Type u := ULift Prop

instance : Coe Prop UProp where
  coe p := ⟨p⟩

instance : Nonempty UProp := inferInstance

universe u v w

instance : MPropOrdered Id Prop where
  μ := id
  μ_ord_pure := by simp
  μ_ord_bind := by solve_by_elim


instance : MPropDetertministic Id Prop where
  demonic := by
    intros α c p q;
    simp [MProp.lift, MProp.μ, MPropOrdered.μ]
  angelic := by
    intros α c p q;
    simp [MProp.lift, MProp.μ, MPropOrdered.μ]

instance (σ : Type u) (l : Type u) (m : Type u -> Type v)
  [PartialOrder l]
  [Monad m] [LawfulMonad m] [inst: MPropOrdered m l] : MPropOrdered (StateT σ m) (σ -> l) where
  μ := (MPropOrdered.μ $ (fun fs => fs.1 fs.2) <$> · ·)
  μ_ord_pure := by intro f; ext s₁; simp [pure, StateT.pure, MPropOrdered.μ_ord_pure]
  μ_ord_bind := by
    intros α f g
    simp [Function.comp, Pi.hasLe, Pi.partialOrder, Pi.preorder, inferInstanceAs]; intros le x s
    have leM := @inst.μ_ord_bind (α × σ) (fun as => (fun fs => fs.1 fs.2) <$> f as.1 as.2) (fun as => (fun fs => fs.1 fs.2) <$> g as.1 as.2)
    simp only [Function.comp, Pi.hasLe, <-map_bind] at leM
    apply leM; simp only [implies_true, le]


instance (σ : Type u) (l : Type u) (m : Type u -> Type v)
  [CompleteLattice l]
  [Monad m] [LawfulMonad m] [inst: MPropOrdered m l] [inst': MPropDetertministic m l]
   : MPropDetertministic (StateT σ m) (σ -> l) where
    demonic := by
      intros α ι c p _ s;
      simp [MProp.lift, MProp.μ, MPropOrdered.μ, Functor.map, StateT.map]
      have h := inst'.demonic (α := α × σ) (c := c s) (ι := ι) (p := fun i x => p i x.1 x.2)
      simp [MProp.lift, MProp.μ] at h
      apply h
    angelic := by
      intros α ι c p _ s;
      simp [MProp.lift, MProp.μ, MPropOrdered.μ, Functor.map, StateT.map]
      have h := inst'.angelic (α := α × σ) (c := c s) (ι := ι) (p := fun i x => p i x.1 x.2)
      simp [MProp.lift, MProp.μ] at h
      apply h

instance (ρ : Type u) (l : Type u) (m : Type u -> Type v)
  [PartialOrder l]
  [Monad m] [LawfulMonad m] [inst: MPropOrdered m l] : MPropOrdered (ReaderT ρ m) (ρ -> l) where
  μ := fun rp r => inst.μ $ (· r) <$> rp r
  μ_ord_pure := by
    intros l; simp [pure, ReaderT.pure]; ext r
    solve_by_elim [MPropOrdered.μ_ord_pure]
  μ_ord_bind := by
    intros α f g
    simp [Function.comp, Pi.hasLe, Pi.partialOrder, Pi.preorder, inferInstanceAs]; intros le x r
    have leM := @inst.μ_ord_bind (α) (fun a => (· r) <$> f a r) (fun a => (· r) <$> g a r)
    simp only [Function.comp, Pi.hasLe, <-map_bind] at leM
    apply leM; simp only [implies_true, le]

-- instance (σ : Type u) (l : Type u) (m : Type u -> Type v)
--   [CompleteLattice l]
--   [Monad m] [LawfulMonad m] [inst: MPropOrdered m l]
--   [inst : MPropTotal m l] : MPropTotal (ReaderT σ m) (σ -> l) where
--   μ_total := by
--     simp [MPropOrdered.μ, Functor.map, StateT.map]; intros; ext s; apply inst.μ_total

instance (σ : Type u) (l : Type u) (m : Type u -> Type v)
  [CompleteLattice l]
  [Monad m] [LawfulMonad m] [inst: MPropOrdered m l] [inst': MPropDetertministic m l]
   : MPropDetertministic (ReaderT σ m) (σ -> l) where
  demonic := by
      intros α ι c p _ s;
      simp [MProp.lift, MProp.μ, MPropOrdered.μ, Functor.map]
      have h := inst'.demonic (α := α) (c := c s) (p := fun i x => p i x s)
      simp [MProp.lift, MProp.μ] at h
      apply h
  angelic := by
      intros α ι c p _ s;
      simp [MProp.lift, MProp.μ, MPropOrdered.μ, Functor.map]
      have h := inst'.angelic (α := α) (c := c s) (p := fun i x => p i x s)
      simp [MProp.lift, MProp.μ] at h
      apply h

abbrev Except.getD {ε α} (default : ε -> α)  : Except ε α -> α
  | Except.ok p => p
  | Except.error e => default e

abbrev Except.bind' {m : Type u -> Type v} {ε α β} [Monad m] : Except ε α -> (α -> ExceptT ε m β) -> ExceptT ε m β :=
  fun x f => bind (m := ExceptT ε m) (pure (f := m) x) f

lemma Except.bind'_bind {m : Type u -> Type v} {ε α β} [Monad m] [LawfulMonad m] (i : m (Except ε α)) (f : α -> ExceptT ε m β) :
  (i >>= fun a => Except.bind' a f) = bind (m := ExceptT ε m) i f := by
  simp [Except.bind', bind, bind_assoc, ExceptT.bind]; rfl

noncomputable
def MPropExcept (ε : Type u) (df : ε -> Prop) (l : Type u) (m : Type u -> Type v)
  [PartialOrder l] [OrderTop l] [OrderBot l]
  [Monad m] [LawfulMonad m] [inst: MPropOrdered m l] : MPropOrdered (ExceptT ε m) l where
  μ := fun e => inst.μ $ Except.getD (⌜df ·⌝) <$> e
  μ_ord_pure := by
    intro l; simp [pure, ExceptT.pure, ExceptT.mk]
    solve_by_elim [MPropOrdered.μ_ord_pure]
  μ_ord_bind := by
    intros α f g
    simp [Function.comp, Pi.hasLe, Pi.partialOrder, Pi.preorder, inferInstanceAs]; intros le x
    have leM := @inst.μ_ord_bind (Except ε α)
      (fun x => Except.getD (⌜df ·⌝) <$> Except.bind' x f)
      (fun x => Except.getD (⌜df ·⌝) <$> Except.bind' x g)
    simp only [Function.comp, Pi.hasLe, <-map_bind, Except.bind'_bind] at leM
    apply leM; rintro (e | p) <;> simp [Except.bind', ExceptT.instMonad, ExceptT.bind, ExceptT.bindCont]
    apply le

section ExeceptHandler

variable (ε : Type u) (l : Type u) (m : Type u -> Type v) [Monad m] [LawfulMonad m]

class IsHandler {ε : Type*} (handler : outParam (ε -> Prop)) where

set_option linter.unusedVariables false in
noncomputable
instance OfHd {hd : ε -> Prop}
  [PartialOrder l] [OrderTop l] [OrderBot l]
  [Monad m] [LawfulMonad m] [inst: MPropOrdered m l] [hdInst : IsHandler hd] : MPropOrdered (ExceptT ε m) l := MPropExcept ε hd l m

instance MPropExceptPartDetertministic (hd : ε -> Prop)
  [CompleteLattice l] [IsHandler hd]
  [Monad m] [LawfulMonad m] [inst: MPropOrdered m l]
  [inst': MPropDetertministic m l] : MPropDetertministic (ExceptT ε m) l where
  demonic := by
    intros α ι c p _
    simp [MProp.lift, MProp.μ, MPropOrdered.μ, Functor.map, ExceptT.map, ExceptT.mk]
    simp [OfHd, MPropExcept]
    have h := inst'.demonic (α := Except ε α) (c := c)
      (p := fun i e =>
        match e with
        | Except.ok a    => p i a
        | Except.error e => ⌜hd e⌝ )
    simp [MProp.lift, MProp.μ] at h
    have h₁ : ∀ p : ι -> α -> l,
      ⨅ i,
      (MPropOrdered.μ (m := m) (do
        bind (m := m) c fun a =>
        Except.getD (⌜hd ·⌝) <$>
            match a with
            | Except.ok a => pure (Except.ok (p i a))
            | Except.error e => pure (Except.error e))) =
      ⨅ i,
      MPropOrdered.μ (Functor.map (f := m) (α := Except ε α)
        (fun a =>
          match a with
            | Except.ok a => (p i a)
            | Except.error e => ⌜hd e⌝) c) := by
      intro p; congr; ext i; rw [map_eq_pure_bind]; apply MProp.bind (m := m); ext a; cases a <;> simp
    (repeat erw [h₁]); clear h₁; apply le_trans; apply h
    apply le_of_eq;rw [map_eq_pure_bind]; apply MProp.bind (m := m); ext a; cases a <;> simp
    simp [Except.getD, MProp.μ, iInf_const]
  angelic := by
    intros α ι c p _
    simp [MProp.lift, MProp.μ, MPropOrdered.μ, Functor.map, ExceptT.map, ExceptT.mk]
    simp [OfHd, MPropExcept]
    have h := inst'.angelic (α := Except ε α) (c := c)
      (p := fun i e =>
        match e with
        | Except.ok a    => p i a
        | Except.error e => ⌜hd e⌝ )
    simp [MProp.lift, MProp.μ] at h
    have h₁ : ∀ p : ι -> α -> l,
      ⨆ i,
      (MPropOrdered.μ (m := m) (do
        bind (m := m) c fun a =>
        Except.getD (⌜hd ·⌝) <$>
            match a with
            | Except.ok a => pure (Except.ok (p i a))
            | Except.error e => pure (Except.error e))) =
      ⨆ i,
      MPropOrdered.μ (Functor.map (f := m) (α := Except ε α)
        (fun a =>
          match a with
            | Except.ok a => (p i a)
            | Except.error e => ⌜hd e⌝) c) := by
      intro p; congr; ext i; rw [map_eq_pure_bind]; apply MProp.bind (m := m); ext a; cases a <;> simp
    (repeat erw [h₁]); clear h₁; apply le_trans'; apply h
    apply le_of_eq;rw [map_eq_pure_bind]; apply MProp.bind (m := m); ext a; cases a <;> simp
    simp [Except.getD, MProp.μ, iSup_const]

end ExeceptHandler

instance (g : Type) (l : Type u) (m : Type u -> Type v)
  [PartialOrder l]
  [Monad m] [LawfulMonad m]
  [inst: MPropOrdered m l] : MPropOrdered (Plausible.RandGT g m) (ULift g -> l) :=
  inferInstanceAs (MPropOrdered (StateT (ULift g) m) (ULift g -> l))

-- instance : MPropOrdered Plausible.Gen (ULift StdGen -> Prop) where
--   μ m g := ∀ n, MPropOrdered.μ (m n) g
--   ι p n := MPropOrdered.ι p
--   μ_surjective := by intro p; simp; ext; rfl
--   μ_top := by
--     intro p; simp [pure, ReaderT.pure, MPropOrdered.μ];
--     unfold StateT.pure;
--     simp [pure]; intro g; simp
--   μ_bot := by
--     intro p; simp [pure, ReaderT.pure, MPropOrdered.μ];
--     unfold StateT.pure;
--     simp [pure]; intro g; simp
--   μ_ord_pure := by
--     intro p₁ p₂ imp; simp [pure, ReaderT.pure, MPropOrdered.μ];
--     unfold StateT.pure;
--     simp [pure]; intro g; simpa
--   μ_ord_bind := by
--     intro α f g le; simp [bind, ReaderT.bind, StateT.bind]
--     intro g; simpa

namespace PartialCorrectness
scoped instance PartialHandler {ε} : IsHandler (ε := ε) fun _ => True where
end PartialCorrectness

namespace TotalCorrectness
scoped instance TotalHandler {ε} : IsHandler (ε := ε) fun _ => False where
end TotalCorrectness

#guard_msgs (drop info) in
#synth MPropOrdered (StateM Int) (Int -> Prop)

#guard_msgs (drop info) in
#synth MPropOrdered (ReaderT Bool (StateM Int)) (Bool -> Int -> Prop)
