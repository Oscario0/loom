import Mathlib.Logic.Function.Basic
import Mathlib.Order.CompleteBooleanAlgebra
import Mathlib.Order.Lattice
import Mathlib.Order.Basic
import Aesop

import LoL.QuotientExtra
import LoL.Meta
import LoL.MProp.WP
import LoL.MProp.WLP

universe u v w

section NonDetermenisticTransformer

variable {m : Type u -> Type v} {l : Type u} {α β : Type u} [Monad m] [inst: CompleteBooleanAlgebra l] [MPropOrdered m l]

private lemma join_himp (x y z : l) : x ⊓ y ⇨ z = xᶜ ⊔ (y ⇨ z) := by
  apply le_antisymm
    <;> simp [himp_eq]
    <;> constructor
    <;> solve_by_elim [le_sup_of_le_right, le_sup_of_le_left, le_refl]

open Classical in
private lemma iInf_pi {α} {τ : α -> Type u} (p : (a : α) -> τ a -> l) [inst': ∀ a, Inhabited (τ a)] a :
  ⨅ (t : (α : α) -> τ α), p a (t a) = ⨅ (t : τ a), p a t := by
    apply le_antisymm <;> simp
    { intro i;
      refine iInf_le_of_le (fun x =>
        if h : x = a then by rw [h]; exact i else (inst' x).default) ?_
      simp }
    intro i; apply iInf_le_of_le (i a); simp

open Classical in
private lemma iSup_pi {α} {τ : α -> Type u} (p : (a : α) -> τ a -> l) [inst': ∀ a, Inhabited (τ a)] a :
  ⨆ (t : (α : α) -> τ α), p a (t a) = ⨆ (t : τ a), p a t := by
    apply le_antisymm <;> simp
    { intro i; exact le_iSup (p a) (i a) }
    intro i
    refine le_iSup_of_le (fun x =>
      if h : x = a then by rw [h]; exact i else (inst' x).default) ?_
    simp


structure NonDet (m : Type u -> Type v) (l : Type u) (α : Type u) where
  tp  : Type u
  inh : Inhabited tp
  pre : tp -> l
  sem : tp -> m α

structure NonDetCps (m : Type u -> Type v) [Monad m] (l : Type u) [PartialOrder l] (α : Type u) where
  tpc : (α -> Type u) -> Type u
  pre {τ : α -> Type u} [mprop : MPropOrdered m l] (cont : (a : α) -> τ a -> l) : tpc τ -> l
  sem {τ : α -> Type u} {β : Type u} (cont : (a : α) -> τ a -> m β) : tpc τ -> m β

structure NonDetT (m : Type u -> Type v) {l : Type u} [Monad m] [CompleteBooleanAlgebra l] [HasMProp m l] (α : Type u)
  extends NonDetCps m l α where
  inh (τ : α -> Type u) : (∀ a, Inhabited (τ a)) -> Inhabited (tpc τ)
  pre_sem_iInf [mprop : MPropOrdered m l] [MPropDetertministic m l]
    {τ τ' : α -> Type u} {_ : ∀ a, Inhabited (τ a)} { _ : ∀ a, Inhabited (τ' a)}
    (cp₁ : (a : α) -> τ a -> l) (cp₂ : (a : α) -> τ' a -> l)
    (cs₁ : (a : α) -> τ a -> m UProp) (cs₂ : (a : α) -> τ' a -> m UProp) :
    (∀ a, ⨅ t,  cp₁ a t ⇨ MProp.μ (cs₁ a t) <= ⨅ t, cp₂ a t ⇨ MProp.μ (cs₂ a t)) ->
    ⨅ t, pre cp₁ t ⇨ MProp.μ (sem cs₁ t) <=
    ⨅ t, pre cp₂ t ⇨ MProp.μ (sem cs₂ t)
  pre_sem_iSup  [mprop : MPropOrdered m l] [MPropDetertministic m l]
    {τ τ' : α -> Type u} {_ : ∀ a, Inhabited (τ a)} { _ : ∀ a, Inhabited (τ' a)}
    (cp₁ : (a : α) -> τ a -> l) (cp₂ : (a : α) -> τ' a -> l)
    (cs₁ : (a : α) -> τ a -> m UProp) (cs₂ : (a : α) -> τ' a -> m UProp) :
    (∀ a, ⨆ t,  cp₁ a t ⊓ MProp.μ (cs₁ a t) <= ⨆ t, cp₂ a t ⊓ MProp.μ (cs₂ a t)) ->
    ⨆ t, pre cp₁ t ⊓ MProp.μ (sem cs₁ t) <=
    ⨆ t, pre cp₂ t ⊓ MProp.μ (sem cs₂ t)
  sem_bind {τ : α -> Type u} {β γ} (t : tpc τ)
    (cont : (a : α) -> τ a -> m β)
    (cont' : β -> m γ) :
    sem cont t >>= cont' = sem (cont · · >>= cont') t
  pre_mono [mprop : MPropOrdered m l] [mprop' : MPropOrdered m l] :
    (∀ α (c : m α) post, wlp c (mprop := mprop) post = wlp c (mprop := mprop') post) ->
    ∀ (τ : α -> Type u) (cont cont' : (a : α) -> τ a -> l),
      (∀ x, cont x = cont' x) ->
      pre (mprop := mprop) cont = pre (mprop := mprop') cont'

@[simp]
def NonDetT.finally (x : NonDetT m α) : NonDet m l α := {
  tp := x.tpc (fun _ => PUnit)
  inh := x.inh (fun _ => PUnit) (fun _ => ⟨.unit⟩)
  pre := fun t => x.pre ⊤ t
  sem := fun t => x.sem (fun _ => Pure.pure ·) t
}

def NonDetT.tp (x : NonDetT m α) := x.finally.tp

@[simp]
def NonDet.run (x : NonDet m l α) (seed : x.tp) := x.sem seed
def NonDetT.run (x : NonDetT m α) (seed : x.tp) := x.finally.run seed
@[simp]
def NonDet.seed (x : NonDet m l α) := x.inh.default
def NonDetT.seed (x : NonDetT m α) := x.finally.seed

def NonDetT.any (x : NonDetT m α) : m α := x.run x.seed

@[simp]
def NonDet.validSeed (x : NonDet m l α) (pre : l) (seed : x.tp) := pre ≤ x.pre seed
def NonDetT.validSeed (x : NonDetT m α) (pre : l) (seed : x.tp) := x.finally.validSeed pre seed

variable [MPropDetertministic m l] [LawfulMonad m]

def NonDetT.pure (x : α) : NonDetT m α := {
  tpc τ := τ x
  pre cont := cont x
  sem cont := cont x

  inh τ inh := by solve_by_elim
  pre_sem_iInf := by introv _ _ _ h; simp only [h]
  pre_sem_iSup := by introv _ _ _ h; simp only [h]
  sem_bind := by introv; simp
  pre_mono := by simp; intros; solve_by_elim
}

def NonDetT.bind (x : NonDetT m α) (f : α → NonDetT m β) : NonDetT m β := {
  tpc τ := x.tpc <| fun out => (f out).tpc τ
  sem cont := x.sem fun a ft => (f a).sem cont ft
  pre cont := x.pre fun a ft => (f a).pre cont ft

  inh τ inh := by
    simp; apply x.inh; intro a; apply (f a).inh; exact inh
  pre_sem_iInf := by
    introv _ _ _ h; simp only
    apply x.pre_sem_iInf <;> intro a <;> solve_by_elim [(f a).pre_sem_iInf, (f a).inh]
  pre_sem_iSup := by
    introv _ _ _ h; simp only
    apply x.pre_sem_iSup <;> intro a <;> solve_by_elim [(f a).pre_sem_iSup, (f a).inh]
  sem_bind := by
    introv; simp [x.sem_bind, (f _).sem_bind];
  pre_mono := by
    simp; intros mp mp' _ τ c c' _;
    apply x.pre_mono (mprop := mp) (τ := (fun a ↦ (f a).tpc τ)) (cont := fun a ft ↦
      (f a).pre (mprop := mp) c ft)
    { assumption }
    intro a; apply (f a).pre_mono (mprop := mp) <;> assumption

}

def NonDetT.pick (α : Type u) [Inhabited α] : NonDetT m α := {
  tpc τ := (a : α) × τ a
  sem cont t := cont t.1 t.2
  pre cont t := cont t.1 t.2

  inh τ inh := by
    simp; exists default; apply (inh default).default
  pre_sem_iInf := by
    introv _ _ _; simp; rintro h ⟨a, t⟩; simp
    apply le_trans'; apply h
    simp; intro t
    rw [<-le_himp_iff, <-le_himp_iff]
    refine iInf_le_of_le ⟨a, t⟩ ?_
    exact le_himp
  pre_sem_iSup := by
    introv _ _ _; simp; rintro h ⟨a, t⟩; simp
    apply le_trans; apply h
    simp; intro t
    refine le_iSup_of_le ⟨a, t⟩ ?_; simp
  sem_bind := by simp
  pre_mono := by simp; intros; ext; simp [*]
}

def NonDetT.assume  (as : Prop) : NonDetT m PUnit := {
  tpc τ := τ .unit
  sem cont t := cont .unit t
  pre cont t := ⌜as⌝ ⊓ cont .unit t

  inh τ inh := by solve_by_elim
  pre_sem_iInf := by
    introv _ _ _; simp only [join_himp]
    rw [←sup_iInf_eq, ←sup_iInf_eq];
    exact fun a ↦ sup_le_sup_left (a PUnit.unit) ⌜as⌝ᶜ
  pre_sem_iSup := by
    introv inh₁ inh₂ _ _; simp only [inf_assoc, <-inf_iSup_eq]
    apply inf_le_inf_left; solve_by_elim
  sem_bind := by simp
  pre_mono := by
    simp; intros; ext; simp [*];
    by_cases as = True
    { simp_all }
    have : as = False := by simp_all
    simp_all
}

instance : Monad (NonDetT m) where
  pure := .pure
  bind := .bind

class MonadNonDet (m : Type u → Type v) where
  pick : (τ : Type u) -> [Inhabited τ] → m τ
  assume : Prop → m PUnit

export MonadNonDet (pick assume)

instance : MonadNonDet (NonDetT m) where
  pick   := .pick
  assume := .assume

instance : MonadLift m (NonDetT m) where
  monadLift {α} c := {
    tpc τ := (a : α) -> τ a
    pre cont t := wlp c fun a => cont a (t a)
    sem cont t := c >>= fun a => cont a (t a)

    inh τ inh := by
      simp; exact ⟨fun a => inh a |>.default⟩
    pre_sem_iInf := by
      introv h _ _ _; simp only
      simp only [μ_bind_wp (m := m), <-wlp_himp, Function.comp_apply]
      rw [<-wp_iInf, <-wp_iInf]; apply wp_cons; intro y
      rw [iInf_pi (a := y) (p := fun y iy => cp₁ y iy ⇨ MProp.μ (m := m) (cs₁ y iy))]
      rw [iInf_pi (a := y) (p := fun y iy => cp₂ y iy ⇨ MProp.μ (m := m) (cs₂ y iy))]
      solve_by_elim
    pre_sem_iSup := by
      introv h _ _ _; simp only
      simp only [μ_bind_wp (m := m), wlp_join_wp, Function.comp_apply]
      rw [<-wp_iSup, <-wp_iSup]; apply wp_cons; intro y
      rw [iSup_pi (a := y) (p := fun y iy => cp₁ y iy ⊓ MProp.μ (m := m) (cs₁ y iy))]
      rw [iSup_pi (a := y) (p := fun y iy => cp₂ y iy ⊓ MProp.μ (m := m) (cs₂ y iy))]
      solve_by_elim
    sem_bind := by simp
    pre_mono := by
      intro _ _ wlpEq τ c c' cEq; simp; ext t
      simp [wlpEq, cEq]
  }

instance : LawfulMonad (NonDetT m) := by
  refine LawfulMonad.mk' _ ?_ ?_ ?_ <;> (intros; rfl)


section NonDetTSimplifications

omit [MPropDetertministic m l]
theorem lift_tpc {α : Type u} (x : m α) :
  (liftM (n := NonDetT m) x).tpc = ((a : α) -> · a) := rfl
theorem lift_pre {α : Type u} τ (x : m α) :
  (liftM (n := NonDetT m) x).pre (τ := τ)  =
  fun cont t => wlp x fun a => cont a (t a) := rfl
theorem lift_sem {α β : Type u} τ (x : m α) :
  (liftM (n := NonDetT m) x).sem (β := β) (τ := τ) = fun cont t => x >>= fun a => cont a (t a) := rfl
omit [LawfulMonad m]
theorem pick_tpc (τ : Type u) [Inhabited τ] :
  (pick (m := NonDetT m) τ).tpc = ((t : τ) × · t) := rfl
theorem pick_pre (τ : Type u) τ' [Inhabited τ] :
  (pick (m := NonDetT m) τ).pre (τ := τ') =
  (fun cont t => cont t.1 t.2) := rfl
theorem assume_tpc (as : Prop) : (assume (m := NonDetT m) as).tpc = (· .unit) := rfl
theorem assume_pre τ (as : Prop) :
  (assume (m := NonDetT m) as).pre (τ := τ) =
  fun cont t => ⌜as⌝ ⊓ cont .unit t := rfl
theorem assume_sem τ (as : Prop) :
  (assume (m := NonDetT m) as).sem (β := β) (τ := τ) =
  fun cont t => cont .unit t := rfl
theorem pick_sem (τ : Type u) [Inhabited τ] τ' :
  (pick (m := NonDetT m) τ).sem (β := β) (τ := τ') =
  fun cont t => cont t.1 t.2 := rfl

end NonDetTSimplifications

namespace Demonic

@[simp]
def NonDet.μ (x : NonDet m l UProp) : l :=  ⨅ t : x.tp, x.pre t ⇨ MProp.μ (x.sem t)

def NonDetT.μ (x : NonDetT m UProp) : l := NonDet.μ x.finally

scoped
instance : MPropOrdered (NonDetT m) l := {
  μ := NonDetT.μ
  ι := fun p => monadLift (m := m) (MProp.ι p)
  μ_surjective := by intro p; simp [NonDetT.μ, monadLift, MonadLift.monadLift]; rw [MPropOrdered.μ_surjective]; rw [@iInf_const]
  μ_top := by intro x; simp [NonDetT.μ, pure, NonDetT.pure]; apply MPropOrdered.μ_top
  μ_bot := by intro x; simp [NonDetT.μ, pure, NonDetT.pure, iInf_const]; apply MPropOrdered.μ_bot
  μ_ord_pure := by
    intro p₁ p₂ h; simp [NonDetT.μ, pure, NonDetT.pure, iInf_const]; apply MPropOrdered.μ_ord_pure
    assumption
  μ_ord_bind := by
    intro α f g
    simp [Function.comp, Pi.hasLe, Pi.partialOrder, Pi.preorder, inferInstanceAs]
    intros le x
    simp [liftM, monadLift, MonadLift.monadLift, bind, NonDetT.bind, NonDetT.pure]
    simp only [NonDetT.μ, NonDetT.finally]; dsimp
    apply x.pre_sem_iInf
    { solve_by_elim }
    { intro a; solve_by_elim [(f a).inh] }
    intro a; solve_by_elim [(g a).inh]
  }

lemma NonDetT.wp_eq (c : NonDetT m α) post :
  wp c post =
    ⨅ t : c.tp,
      c.finally.pre t ⇨ wp (c.finally.sem t) post := by
   simp [wp, liftM, monadLift, MProp.lift, MProp.μ, MPropOrdered.μ]
   simp [NonDetT.μ, bind, NonDetT.bind, MProp.ι, MPropOrdered.ι]
   simp [monadLift, MonadLift.monadLift]
   simp [c.sem_bind, MProp.μ]; apply le_antisymm
   { apply c.pre_sem_iInf <;> (try simp [iInf_const]) <;> solve_by_elim }
   apply c.pre_sem_iInf <;> (try simp [iInf_const]) <;> solve_by_elim

lemma MonadNonDet.wp_pick (τ : Type u) [Inhabited τ] (post : τ -> l) :
  wp (pick (m := NonDetT m) τ) post = ⨅ t, post t := by
    simp [NonDetT.wp_eq, pick_pre, pick_sem, wp_pure, pick_tpc]
    apply le_antisymm <;> simp <;> intro i
    { apply iInf_le_of_le ⟨i, .unit⟩; simp }
    apply iInf_le_of_le i.fst; simp

lemma MonadNonDet.wp_assume as (post : PUnit -> l) :
  wp (assume (m := NonDetT m) as) post = ⌜as⌝ ⇨ post .unit := by
    simp [NonDetT.wp_eq, pick_pre,wp_pure, assume_sem, assume_pre, assume_tpc]
    apply le_antisymm
    { apply iInf_le_of_le .unit; simp }
    simp

lemma NonDetT.wp_lift (c : m α) post :
  wp (liftM (n := NonDetT m) c) post = wp c post := by
    simp [NonDetT.wp_eq, pick_pre, wp_pure, lift_sem, lift_pre, lift_tpc]
    apply le_antisymm
    { apply iInf_le_of_le (fun _ => .unit); simp }
    simp

lemma NonDetT.run_validSeed (x : NonDetT m α) (pre : l) (post : α -> l) (seed : x.tp) :
  x.validSeed pre seed ->
  triple pre x post ->
  triple pre (x.run seed) post := by
    simp [NonDetT.validSeed, triple, NonDetT.run, NonDetT.wp_eq]
    intro v h; apply le_trans'; apply h; simp [v]

end Demonic

namespace Angelic

@[simp]
def NonDet.μ (x : NonDet m l UProp) : l :=  ⨆ t : x.tp, x.pre t ⊓ MProp.μ (x.sem t)

def NonDetT.μ (x : NonDetT m UProp) : l := NonDet.μ x.finally

scoped
instance : MPropOrdered (NonDetT m) l := {
  μ := NonDetT.μ
  ι := fun p => monadLift (m := m) (MProp.ι p)
  μ_surjective := by intro p; simp [NonDetT.μ, monadLift, MonadLift.monadLift]; rw [MPropOrdered.μ_surjective]; rw [@iSup_const]
  μ_top := by intro x; simp [NonDetT.μ, pure, NonDetT.pure, iSup_const]; apply MPropOrdered.μ_top
  μ_bot := by intro x; simp [NonDetT.μ, pure, NonDetT.pure]; apply MPropOrdered.μ_bot
  μ_ord_pure := by
    intro p₁ p₂ h; simp [NonDetT.μ, pure, NonDetT.pure, iSup_const]; apply MPropOrdered.μ_ord_pure
    assumption
  μ_ord_bind := by
    intro α f g
    simp [Function.comp, Pi.hasLe, Pi.partialOrder, Pi.preorder, inferInstanceAs]
    intros le x
    simp [liftM, monadLift, MonadLift.monadLift, bind, NonDetT.bind, NonDetT.pure]
    simp only [NonDetT.μ, NonDetT.finally]; dsimp
    apply x.pre_sem_iSup
    { solve_by_elim }
    { intro a; solve_by_elim [(f a).inh] }
    intro a; solve_by_elim [(g a).inh]
  }

lemma NonDetT.wp_eq (c : NonDetT m α) post :
  wp c post =
    ⨆ t : c.tp,
      c.finally.pre t ⊓ wp (c.finally.sem t) post := by
   simp [wp, liftM, monadLift, MProp.lift, MProp.μ, MPropOrdered.μ]
   simp [NonDetT.μ, bind, NonDetT.bind, MProp.ι, MPropOrdered.ι]
   simp [monadLift, MonadLift.monadLift]
   simp [c.sem_bind, MProp.μ]; apply le_antisymm
   { apply c.pre_sem_iSup <;> (try simp [iSup_const]) <;> solve_by_elim }
   apply c.pre_sem_iSup <;> (try simp [iSup_const]) <;> solve_by_elim

lemma MonadNonDet.wp_pick (τ : Type u) [Inhabited τ] (post : τ -> l) :
  wp (pick (m := NonDetT m) τ) post = ⨆ t, post t := by
    simp [NonDetT.wp_eq, pick_pre, pick_sem, wp_pure, pick_tpc]
    apply le_antisymm <;> simp <;> intro i
    { apply le_iSup_of_le i.fst; simp }
    apply le_iSup_of_le ⟨i, .unit⟩; simp

lemma MonadNonDet.wp_assume as (post : PUnit -> l) :
  wp (assume (m := NonDetT m) as) post = ⌜as⌝ ⊓ post .unit := by
    simp [NonDetT.wp_eq, pick_pre,wp_pure, assume_sem, assume_pre, assume_tpc]
    apply le_antisymm
    { exact iSup_const_le }
    apply le_iSup_of_le .unit; simp

lemma NonDetT.wp_lift (c : m α) post :
  wp (liftM (n := NonDetT m) c) post = wp c post := by
    simp [NonDetT.wp_eq, pick_pre, wp_pure, lift_sem, lift_pre, lift_tpc]
    apply le_antisymm
    { exact iSup_const_le }
    apply le_iSup_of_le (fun _ => .unit); simp

lemma NonDetT.run_validSeed (x : NonDetT m α) (pre : l) (post : α -> l) (seed : x.tp) :
  triple pre (x.run seed) post ->
  x.validSeed pre seed ->
  triple pre x post := by
    simp [NonDetT.validSeed, triple, NonDetT.run, NonDetT.wp_eq]
    intro v h; refine le_iSup_of_le seed ?_; simp [*]

end Angelic
section ExceptT

@[always_inline]
instance (ε) [MonadExceptOf ε m] [Inhabited ε] : MonadExceptOf ε (NonDetT m) where
  throw e  := liftM (m := m) (throw e)
  /- TODO: fix me not sure how to implement it -/
  tryCatch := fun _x c =>
    have: Inhabited (NonDetT m _) := ⟨c default⟩
    panic! "`try-catch` for nondetermenistic monad is not implemented"

variable {ε : Type u}


end ExceptT

def ite.fst {α β} {p : Prop} [Decidable p] (x : if p then α else β) (h : p) : α := by
  rw [if_pos h] at x; exact x


def ite.snd {α β} {p : Prop} [Decidable p] (x : if p then α else β) (h : ¬p) : β := by
  rw [if_neg h] at x; exact x

def bite.fst {α β: Type u} {p : Prop} [instD : Decidable p] : (x : bif p then α else β) -> (h : p) -> α := by
  rcases instD with (h|h) <;> dsimp [decide]
  { exact fun _ f => by contradiction  }
  exact fun x _ => x
def bite.snd {α β : Type u} {p : Prop} [instD : Decidable p] : (x : bif p then α else β) -> (h : ¬p) -> β := by
  rcases instD with (h|h) <;> dsimp [decide]
  { exact fun x _ => x }
  exact fun _ f => by contradiction



private lemma iInf_bif_pos {α β : Type u} (cnd : Prop) [instD : Decidable cnd] (h : cnd)
  (f : α -> l) : ⨅ x : bif cnd then α else β, f (bite.fst x h) = ⨅ x : α, f x := by
  apply le_antisymm
  { simp; intro i; apply iInf_le_of_le (by simp_all; assumption);
    cases instD <;> simp [bite.fst]; contradiction }
  simp; intro i; apply iInf_le_of_le (by simp [h] at i; assumption)
  cases instD <;> simp [bite.fst]; contradiction

private lemma iInf_bif_neg {α β : Type u} (cnd : Prop) [instD : Decidable cnd] (h : ¬cnd)
  (f : β -> l) : ⨅ x : bif cnd then α else β, f (bite.snd x h) = ⨅ x : β, f x := by
  apply le_antisymm
  { simp; intro i; apply iInf_le_of_le (by simp_all; assumption)
    cases instD <;> simp [bite.snd]; contradiction }
  simp; intro i; apply iInf_le_of_le (by simp [h] at i; assumption);
  cases instD <;> simp [bite.snd]; contradiction

private lemma iSup_bif_neg {α β : Type u} (cnd : Prop) [instD : Decidable cnd] (h : ¬cnd)
  (f : β -> l) : ⨆ x : bif cnd then α else β, f (bite.snd x h) = ⨆ x : β, f x := by
  apply le_antisymm
  { simp; intro i; apply le_iSup_of_le (by simp [h] at i; assumption);
    cases instD <;> simp [bite.snd]; contradiction }
  simp; intro i; apply le_iSup_of_le (by simp_all; assumption);
  cases instD <;> simp [bite.snd]; contradiction

private lemma iSup_bif_pos {α β : Type u} (cnd : Prop) [instD : Decidable cnd] (h : cnd)
  (f : α -> l) : ⨆ x : bif cnd then α else β, f (bite.fst x h) = ⨆ x : α, f x := by
  apply le_antisymm
  { simp; intro i; apply le_iSup_of_le (by simp [h] at i; assumption);
    cases instD <;> simp [bite.fst]; contradiction  }
  simp; intro i; apply le_iSup_of_le  (by simp_all; assumption)
  cases instD <;> simp [bite.fst]; contradiction

def NonDetT.ite {α : Type u} (cnd : Prop) [instD : Decidable cnd] (thn : NonDetT m α) (els : NonDetT m α) : NonDetT m α := {
  tpc τ := bif cnd then thn.tpc τ else els.tpc τ
  pre {τ} _ cont t := if h : cnd then thn.pre cont (bite.fst t h) else els.pre cont (bite.snd t h)
  sem {τ β} cont t := if h : cnd then thn.sem cont (bite.fst t h) else els.sem cont (bite.snd t h)

  inh τ inh := by
    simp; cases (decide cnd) <;> simp <;> solve_by_elim [thn.inh, els.inh]
  pre_sem_iInf := by
    dsimp; split_ifs with h <;> introv <;> intros
    { repeat rw [iInf_bif_pos (instD := instD) (f := fun t => thn.pre _ t ⇨ MPropOrdered.μ (thn.sem _ t))]
      apply thn.pre_sem_iInf <;> assumption }
    repeat rw [iInf_bif_neg (instD := instD) (f := fun t => els.pre _ t ⇨ MPropOrdered.μ (els.sem _ t))]
    apply els.pre_sem_iInf <;> assumption
  pre_sem_iSup := by
    dsimp; split_ifs with h <;> introv <;> intros
    { repeat rw [iSup_bif_pos (instD := instD) (f := fun t => thn.pre _ t ⊓ MPropOrdered.μ (thn.sem _ t))]
      apply thn.pre_sem_iSup <;> assumption }
    repeat rw [iSup_bif_neg (instD := instD) (f := fun t => els.pre _ t ⊓ MPropOrdered.μ (els.sem _ t))]
    apply els.pre_sem_iSup <;> assumption
  sem_bind     := by
    simp; split_ifs <;> intros <;> solve_by_elim [thn.sem_bind, els.sem_bind]
  pre_mono     := by
    simp; split_ifs <;> intros
    { ext; rw [@thn.pre_mono] <;> try simp [*] }
    ext; rw [@els.pre_mono] <;> try simp [*]
}

omit [MPropDetertministic m l] [LawfulMonad m] in
@[simp↑ high]
lemma NonDetT.ite_eq {α : Type u} (x : NonDetT m α) (y : NonDetT m α) (cond : Prop) [dec : Decidable cond] :
  (if cond then x else y) = NonDetT.ite cond x y := by
    split_ifs with h
    { have : cond = True := by simp_all
      cases this;
      simp [ite, decide]
      cases dec <;> simp_all
      rcases x with ⟨⟨⟩⟩; simp [bite.fst] }
    have : cond = False := by simp_all
    cases this;
    simp [ite, decide]
    cases dec <;> simp_all
    rcases y with ⟨⟨⟩⟩; simp [bite.snd]
    contradiction
section
open Demonic

private lemma meet_himp (x x' y z : l) :
  x = x' ->
  (x ⇨ y) ⊓ (x' ⇨ z) = x ⇨ (y ⊓ z) := by
  rintro rfl
  simp [himp_eq]; rw [@sup_inf_right]

private lemma le_coml_sup (x y z : l) :
  y <= x ⊔ z -> xᶜ <= yᶜ ⊔ z := by
  intro h;
  rw [sup_comm, <-himp_eq]; simp
  rw [inf_comm, <-le_himp_iff, himp_eq]; simp
  rwa [sup_comm]


lemma NonDetT.wp_tot_part ε (c : NonDetT (ExceptT ε m) α) post :
  [totl| wp c ⊤] ⊓ [part| wp c post] = [totl| wp c post] := by
  open PartialCorrectness in rw [@NonDetT.wp_eq]
  open TotalCorrectness in repeat rw [@NonDetT.wp_eq]
  unfold NonDetT.tp
  simp [<-iInf_inf_eq, meet_himp]
  open TotalCorrectness in
  conv =>
    enter [1,1]; ext; rw [meet_himp]; rfl
    erw [@c.pre_mono (cont := ⊤) (τ := fun _ => PUnit)]; rfl
    tactic =>
      introv; simp [wlp, wp_part_eq, wp_tot_eq]
      apply le_antisymm <;> simp
      { constructor
        { apply le_coml_sup; rw [<-wp_or]; apply wp_cons
          rintro (_|_) <;> simp }
        refine le_sup_of_le_right ?_; apply wp_cons
        rintro (_|_) <;> simp }
      constructor
      { apply le_coml_sup; rw [<-wp_or]; apply wp_cons
        rintro (_|_) <;> simp }
      rw [sup_comm, <-himp_eq]; simp [<-wp_and]
      apply wp_cons; rintro (_|_) <;> simp
    tactic => simp
  simp [_root_.wp_tot_part]

set_option quotPrecheck false in
notation "[totl😇|" t "]" => open TotalCorrectness Angelic in t
set_option quotPrecheck false in
notation "[part😈|" t "]" => open PartialCorrectness Demonic in t

lemma NonDetT.iwp_part_wp_tot_eq ε (c : NonDetT (ExceptT ε m) α) post
  (wp_bot : ∀ α (c : m α), wp c ⊥ = ⊥)
  (wp_top : ∀ α (c : m α), wp c ⊤ = ⊤) :
  [part😈| iwp c post] = [totl😇| wp c post] := by
    simp [iwp, NonDetT.wp_eq, Angelic.NonDetT.wp_eq, compl_iInf, -compl_himp, himp_eq]
    simp (disch := assumption) [wp_tot_eq_iwp_part]
    simp [inf_comm]; congr; ext; congr 1
    erw [@c.pre_mono (τ := fun _ => PUnit)] <;> try simp
    introv; simp [wlp, wp_part_eq, wp_tot_eq]
    apply le_antisymm <;> simp
    { constructor
      { apply le_coml_sup; rw [<-wp_or]; apply wp_cons
        rintro (_|_) <;> simp }
      rw [sup_comm, <-himp_eq]; simp [<-wp_and]
      apply wp_cons; rintro (_|_) <;> simp }
    constructor
    { apply le_coml_sup; rw [<-wp_or]; apply wp_cons
      rintro (_|_) <;> simp }
    refine le_sup_of_le_right ?_; apply wp_cons
    rintro (_|_) <;> simp






end


end NonDetermenisticTransformer
