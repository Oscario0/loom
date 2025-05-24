import Mathlib.Logic.Function.Basic
import Mathlib.Order.CompleteBooleanAlgebra
import Mathlib.Order.Lattice
import Mathlib.Order.Basic

import LoL.MonadAlgebras.WP
import LoL.MonadAlgebras.WLP
universe u v w

section NonDetermenisticTransformer


inductive NonDetDevT (m : Type u -> Type v) : (α : Type u) -> Type _ where
  | pure {α} (ret : α) : NonDetDevT m α
  | vis {α} {β} (x : m β) (f : β → NonDetDevT m α) : NonDetDevT m α
  | pickCont {α} (τ : Type u) (p : τ -> Prop) (f : τ → NonDetDevT m α) : NonDetDevT m α
  | repeatCont {α} {β} (init : β) (f : β -> NonDetDevT m (ForInStep β)) (cont : β -> NonDetDevT m α) : NonDetDevT m α

variable {m : Type u -> Type v} {α β : Type u} [Monad m]

def NonDetDevT.bind (x : NonDetDevT m α) (f : α → NonDetDevT m β) : NonDetDevT m β :=
  match x with
  | pure ret => f ret
  | vis x f' => vis x fun y => bind (f' y) f
  | pickCont τ p f' => pickCont τ p fun t => bind (f' t) f
  | repeatCont init f' cont => repeatCont init f' fun t => bind (cont t) f

instance : Monad (NonDetDevT m) where
  pure := NonDetDevT.pure
  bind := NonDetDevT.bind

instance [LawfulMonad m] : LawfulMonad (NonDetDevT m) := by
  refine LawfulMonad.mk' _ ?_ ?_ ?_
  { introv; induction x
    <;> simp [Functor.map, NonDetDevT.bind]
    <;> solve_by_elim [funext] }
  { introv; simp [bind, NonDetDevT.bind] }
  introv; induction x
  <;> simp [bind, NonDetDevT.bind]
  <;> solve_by_elim [funext]

variable [CompleteBooleanAlgebra l] [MPropOrdered m l]

lemma meet_himp (x x' y z : l) :
  x = x' ->
  (x ⇨ y) ⊓ (x' ⇨ z) = x ⇨ (y ⊓ z) := by
  rintro rfl
  simp [himp_eq]; rw [@sup_inf_right]

def NonDetDevT.pick (τ : Type u) : NonDetDevT m τ :=
  NonDetDevT.pickCont _ (fun _ => True) pure
def NonDetDevT.assume (as : Prop) : NonDetDevT m PUnit :=
  NonDetDevT.pickCont PUnit (fun _ => as) fun _ => pure .unit
def NonDetDevT.pickSuchThat (τ : Type u) (p : τ → Prop) : NonDetDevT m τ :=
  NonDetDevT.pickCont τ p pure
def NonDetDevT.repeat (init : α) (f : α -> NonDetDevT m (ForInStep α)) : NonDetDevT m α :=
  NonDetDevT.repeatCont init f pure

class MonadNonDetDev (m : Type u → Type v) where
  pick : (τ : Type u) →  m τ
  pickSuchThat : (τ : Type u) → (τ → Prop) → m τ
  assume : Prop → m PUnit.{u+1}
  rep {α : Type u} : α → (α → m (ForInStep α)) → m α

export MonadNonDetDev (pick assume pickSuchThat rep)


instance : MonadNonDetDev (NonDetDevT m) where
  pick   := .pick
  assume := .assume
  pickSuchThat := .pickSuchThat
  rep := .repeat

def sp (x : m α) (pre : l) : α -> l := (sInf fun post => pre <= wp x post)

lemma le_wp_sp_le (x : m α) [LawfulMonad m] [MPropDetertministic m l] :
  post ≠ ⊤ ->
   (sp x pre <= post -> pre <= wp x post) := by
    intro pne
    by_cases ex:  Nonempty (Set.Elem fun post ↦ pre ≤ wp x post)
    { have : pre <= wp x (sp x pre) := by {
        unfold sp; simp [sInf]; rw [@wp_iInf]
        revert ex; simp [Set.Elem, Set.Mem, Membership.mem] }
      solve_by_elim [wp_cons, le_trans] }
    rw [@Set.not_nonempty_iff_eq_empty'] at ex
    simp [sp, ex, *]

lemma sp_le_le_wp (x : m α) :
   (pre <= wp x post -> sp x pre <= post) := by
    intro a; --refine inf_le_of_left_le ?_
    exact CompleteSemilatticeInf.sInf_le (fun post ↦ pre ≤ wp x post) post a


namespace Demonic

noncomputable
def   NonDetDevT.wp : {α : Type u} -> NonDetDevT m α -> Cont l α
  | _, .pure ret => pure ret
  | _, .vis x f => fun post => _root_.wp x fun a => wp (f a) post
  | _, .pickCont _ p f => fun post => ⨅ a, ⌜p a⌝ ⇨ wp (f a) post
  | _, .repeatCont init f cont => fun post => ⨆ (inv : ForInStep _ -> l),
    ⌜ ∀ b, (inv (ForInStep.yield b)) <= wp (f b) inv⌝ ⊓
    spec (inv (.yield init)) (fun b => inv (.done b)) (fun b => wp (cont b) post)

omit [MPropOrdered m l] in
lemma spec_mono {α : Type u} (pre : l) (post : α -> l) (f g : α -> l) :
  (∀ a, f a <= g a) ->
  spec pre post f <= spec pre post g := by
    unfold spec; intro
    refine inf_le_inf (by rfl) ?_
    refine LE.pure_imp (post ≤ f) (post ≤ g) ?_
    intro h a; apply le_trans; apply h a; solve_by_elim

lemma NonDetDevT.wp_mono [LawfulMonad m] {α : Type u} (x : NonDetDevT m α) (f g : α -> l) :
  (∀ a, f a <= g a) ->
  NonDetDevT.wp x f <= NonDetDevT.wp x g := by
    intro h; induction x
    <;> simp [NonDetDevT.wp, pure, h, -le_himp_iff, -iSup_le_iff]
    <;> try solve_by_elim [wp_cons, iInf_le_of_le, himp_le_himp_left]
    apply iSup_mono; intro inv
    solve_by_elim [wp_cons, spec_mono, inf_le_inf_left]
lemma NonDetDevT.wp_bind [LawfulMonad m] {α β : Type u} (x : NonDetDevT m α) (f : α -> NonDetDevT m β)
  (post : β -> l):
  NonDetDevT.wp (x.bind f) post = NonDetDevT.wp x (fun x => NonDetDevT.wp (f x) post) := by
    unhygienic induction x
    <;> simp [NonDetDevT.wp, bind, pure, -le_himp_iff, -iSup_le_iff, NonDetDevT.bind]
    { simp [f_ih] }
    { simp [f_ih] }
    simp [cont_ih]




noncomputable
def NonDetDevT.μ : NonDetDevT m l -> l := fun x => NonDetDevT.wp x id

instance : MonadLift m (NonDetDevT m) where
  monadLift x := NonDetDevT.vis x pure

variable [LawfulMonad m]

noncomputable
-- scoped
instance {l : outParam (Type u)} [CompleteBooleanAlgebra l] [MPropOrdered m l] [LawfulMonad m] : MPropOrdered (NonDetDevT m) l where
  μ := NonDetDevT.μ
  μ_ord_pure := by
    intro l; simp [NonDetDevT.μ, NonDetDevT.wp]; rfl
  μ_ord_bind := by
    simp [NonDetDevT.μ, bind, NonDetDevT.wp_bind]; intros
    solve_by_elim [NonDetDevT.wp_mono]

lemma NonDetDevT.wp_eq_wp {α : Type u} (x : NonDetDevT m α) (post : α -> l) :
  _root_.wp x post = NonDetDevT.wp x post := by
    simp [_root_.wp, liftM, monadLift, MProp.lift, MPropOrdered.μ, NonDetDevT.μ]
    erw [map_eq_pure_bind, NonDetDevT.wp_bind]
    rfl


@[simp]
lemma NonDetDevT.wp_vis {β : Type u} (x : m β) (f : β → NonDetDevT m α) post :
  _root_.wp (NonDetDevT.vis x f) post = _root_.wp x fun a => _root_.wp (f a) post := by
  simp [NonDetDevT.wp_eq_wp]; rfl

lemma NonDetDevT.wp_lift (c : m α) post :
  _root_.wp (liftM (n := NonDetDevT m) c) post = _root_.wp c post := by
  simp [NonDetDevT.wp_eq_wp]; rfl

@[simp]
lemma NonDetDevT.wp_pickCont {τ : Type u} p (f : τ → NonDetDevT m α) post :
  _root_.wp (NonDetDevT.pickCont τ p f) post = ⨅ a, ⌜p a⌝ ⇨ _root_.wp (f a) post := by
  simp [NonDetDevT.wp_eq_wp]; rfl

@[simp]
lemma NonDetDevT.wp_repeatCont {α : Type u} (init : α) (f : α -> NonDetDevT m (ForInStep α)) (cont : α -> NonDetDevT m β) post :
  _root_.wp (NonDetDevT.repeatCont init f cont) post = ⨆ (inv : ForInStep _ -> l),
    ⌜ ∀ b, (inv (ForInStep.yield b)) <= wp (f b) inv⌝ ⊓
    spec (inv (.yield init)) (fun b => inv (.done b)) (fun b => wp (cont b) post) := by
  simp [NonDetDevT.wp_eq_wp]; rfl

@[simp]
lemma NonDetDevT.wp_pure (x : α) post :
  _root_.wp (NonDetDevT.pure (m := m) x) post = post x := by erw [_root_.wp_pure]

lemma MonadNonDetDev.wp_pick {τ : Type u} post :
  _root_.wp (MonadNonDetDev.pick (m := NonDetDevT m) τ) post = iInf post := by
  simp [MonadNonDetDev.pick, NonDetDevT.pick]

lemma MonadNonDetDev.wp_assume {as : Prop} post : _root_.wp (MonadNonDetDev.assume (m := NonDetDevT m) as) post = ⌜as⌝ ⇨ post .unit := by
  simp [MonadNonDetDev.assume, NonDetDevT.assume, iInf_const]

lemma MonadNonDetDev.wp_pickSuchThat {τ : Type u} (p : τ → Prop) post :
  _root_.wp (MonadNonDetDev.pickSuchThat (m := NonDetDevT m) τ p) post = ⨅ a, ⌜p a⌝ ⇨ post a := by
  simp [MonadNonDetDev.pickSuchThat, NonDetDevT.pickSuchThat]

lemma MonadNonDetDev.wp_repeat {α : Type u} (init : α) (f : α -> NonDetDevT m (ForInStep α)) post :
  _root_.wp (MonadNonDetDev.rep (m := NonDetDevT m) init f) post = ⨆ (inv : ForInStep _ -> l),
    ⌜ ∀ b, (inv (ForInStep.yield b)) <= wp (f b) inv⌝ ⊓
    spec (inv (.yield init)) (fun b => inv (.done b)) post := by
  simp [MonadNonDetDev.rep, NonDetDevT.repeat, NonDetDevT.wp, pure, NonDetDevT.wp_eq_wp]


instance [MonadNonDetDev m] : ForIn m Lean.Loop Unit where
  forIn {β} _ _ init f := @MonadNonDetDev.rep m _ β init (f ())

lemma MonadNonDetDev.wp_forIn {β : Type u} (init : β) (f : Unit -> β -> NonDetDevT m (ForInStep β))
  (inv : β -> l) (on_done : β -> l) :
  (∀ b, inv b <= wp (f () b) (fun | .yield b' => inv b' | .done b' => inv b' ⊓ on_done b')) ->
  triple (inv init) (forIn (m := NonDetDevT m) Lean.Loop.mk init f) (fun b => inv b ⊓ on_done b) := by
  intro hstep; simp [triple]; erw [MonadNonDetDev.wp_repeat]
  refine le_iSup_of_le (fun | .yield b' => inv b' | .done b' => inv b' ⊓ on_done b') ?_
  simp [spec, hstep]


end Demonic
