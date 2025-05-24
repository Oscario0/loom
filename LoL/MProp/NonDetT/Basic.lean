import Mathlib.Logic.Function.Basic
import Mathlib.Order.CompleteBooleanAlgebra
import Mathlib.Order.Lattice
import Mathlib.Order.Basic

import LoL.MProp.WP
import LoL.MProp.WLP

universe u v w

section NonDetermenisticTransformer


inductive NonDetT (m : Type u -> Type v) (α : Type u) where
  | pure (ret : α)
  | vis (x : m β) (f : β → NonDetT m α)
  | pickCont (τ : Type u) (p : τ -> Prop) (f : τ → NonDetT m α)

variable {m : Type u -> Type v} {α β : Type u} [Monad m]

def NonDetT.bind (x : NonDetT m α) (f : α → NonDetT m β) : NonDetT m β :=
  match x with
  | pure ret => f ret
  | vis x f' => vis x fun y => bind (f' y) f
  | pickCont τ p f' => pickCont τ p fun t => bind (f' t) f

instance : Monad (NonDetT m) where
  pure := NonDetT.pure
  bind := NonDetT.bind

instance [LawfulMonad m] : LawfulMonad (NonDetT m) := by
  refine LawfulMonad.mk' _ ?_ ?_ ?_
  { introv; induction x
    <;> simp [Functor.map, NonDetT.bind]
    <;> solve_by_elim [funext] }
  { introv; simp [bind, NonDetT.bind] }
  introv; induction x
  <;> simp [bind, NonDetT.bind]
  <;> solve_by_elim [funext]

variable [CompleteBooleanAlgebra l] [MPropOrdered m l]

lemma meet_himp (x x' y z : l) :
  x = x' ->
  (x ⇨ y) ⊓ (x' ⇨ z) = x ⇨ (y ⊓ z) := by
  rintro rfl
  simp [himp_eq]; rw [@sup_inf_right]

def NonDetT.pick (τ : Type u) : NonDetT m τ :=
  NonDetT.pickCont _ (fun _ => True) pure
def NonDetT.assume (as : Prop) : NonDetT m PUnit :=
  NonDetT.pickCont PUnit (fun _ => as) fun _ => pure .unit
def NonDetT.pickSuchThat (τ : Type u) (p : τ → Prop) : NonDetT m τ :=
  NonDetT.pickCont τ p pure

class MonadNonDet (m : Type u → Type v) where
  pick : (τ : Type u) →  m τ
  pickSuchThat : (τ : Type u) → (τ → Prop) → m τ
  assume : Prop → m PUnit.{u+1}

export MonadNonDet (pick assume pickSuchThat)


instance : MonadNonDet (NonDetT m) where
  pick   := .pick
  assume := .assume
  pickSuchThat := .pickSuchThat

def NonDetT.type : NonDetT m α -> Type u
  | pure _ => PUnit
  | vis _ f => ∀ b, (f b).type
  | pickCont τ _ f => (t : τ) × (f t).type

def NonDetT.pre : (x : NonDetT m α) -> x.type -> l
  | pure _, _ => ⊤
  | vis x f, t => wlp x fun x => (f x).pre (t x)
  | pickCont τ p f, t => ⌜p t.1⌝ ⊓ (f t.1).pre t.2

def NonDetT.run : (x : NonDetT m α) -> x.type -> m α
  | pure ret, _ => Pure.pure (f := m) ret
  | vis x f, tpc => x >>= fun a => (f a).run (tpc a)
  | pickCont _ _ f, tpc => (f tpc.1).run tpc.2

def NonDetT.validSeed [MPropOrdered m l]
  (x : NonDetT m α) (pre : l) (seed : x.type) := pre ≤ x.pre seed

def sp (x : m α) (pre : l) : α -> l := (sInf fun post => pre <= wp x post)

lemma le_wp_sp_le (x : m α) [LawfulMonad m] [MPropDetertministic m l] :
  post ≠ ⊤ ->
   (sp x pre <= post -> pre <= wp x post) := by
    intro pne
    by_cases ex:  Nonempty (Set.Elem fun post ↦ pre ≤ wp x post)
    { have : pre <= wp x (sp x pre) := by {
        unfold sp; simp [sInf]; rw [@wp_iInf]
        revert ex; simp [Set.Elem, Set.Mem, Membership.mem]
      }
      solve_by_elim [wp_cons, le_trans] }
    rw [@Set.not_nonempty_iff_eq_empty'] at ex
    simp [sp, ex, *]

lemma sp_le_le_wp (x : m α) :
   (pre <= wp x post -> sp x pre <= post) := by
    intro a; --refine inf_le_of_left_le ?_
    exact CompleteSemilatticeInf.sInf_le (fun post ↦ pre ≤ wp x post) post a


namespace Demonic

def NonDetT.μ : NonDetT m UProp -> l
  | .pure ret => ⌜ret.down⌝
  | .vis x f => wp x fun a => μ (f a)
  | .pickCont _ p f => ⨅ a, ⌜p a⌝ ⇨ μ (f a)

instance : MonadLift m (NonDetT m) where
  monadLift x := NonDetT.vis x pure

variable [LawfulMonad m]

scoped
instance {l : outParam (Type u)} [CompleteBooleanAlgebra l] [MPropOrdered m l] [LawfulMonad m] : MPropOrdered (NonDetT m) l where
  μ := NonDetT.μ
  ι p := liftM $ MPropOrdered.ι (m := m) p
  μ_surjective := by
    intro x; simp [liftM, monadLift, MonadLift.monadLift, NonDetT.μ, wp]
    simp [MProp.lift, MPropOrdered.pure]
    erw [MPropOrdered.bind (m := m)]; rotate_right
    { ext; simp; conv => enter [1];  rw [@MPropOrdered.cancel] }
    simp; rw [@MPropOrdered.cancel]
  μ_top := by intro x; simp [NonDetT.μ, MPropOrdered.μ_top]
  μ_bot := by intro x; simp [NonDetT.μ, MPropOrdered.μ_bot]
  μ_ord_pure := by
    intro p₁ p₂ h; simp [NonDetT.μ]
    solve_by_elim [MPropOrdered.μ_ord_pure]
  μ_ord_bind := by
    introv; simp [Function.comp, Pi.hasLe, Pi.partialOrder, Pi.preorder, inferInstanceAs]
    intro h x; induction x
    <;> simp [bind, MPropOrdered.bind, NonDetT.bind, NonDetT.μ, -le_himp_iff]
    <;> try solve_by_elim [wp_cons, iInf_le_of_le, himp_le_himp_left]

@[simp]
lemma NonDetT.wp_vis {β : Type u} (x : m β) (f : β → NonDetT m α) post :
  wp (NonDetT.vis x f) post = wp x fun a => wp (f a) post := by
  conv =>
    enter [1]
    simp [wp, liftM, monadLift, MProp.lift, bind, Functor.map, NonDetT.bind]
    simp [MPropOrdered.μ, NonDetT.μ]
  congr

lemma NonDetT.wp_lift (c : m α) post :
  wp (liftM (n := NonDetT m) c) post = wp c post := by
  simp [liftM, monadLift, MonadLift.monadLift, wp_pure]

@[simp]
lemma NonDetT.wp_pickCont {τ : Type u} p (f : τ → NonDetT m α) post :
  wp (NonDetT.pickCont τ p f) post = ⨅ a, ⌜p a⌝ ⇨ wp (f a) post := by
  conv =>
    enter [1]
    simp [wp, liftM, monadLift, MProp.lift, bind, Functor.map, NonDetT.bind]
    simp [MPropOrdered.μ, NonDetT.μ]
  congr

@[simp]
lemma NonDetT.wp_pure (x : α) post :
  wp (NonDetT.pure (m := m) x) post = post x := by erw [_root_.wp_pure]

lemma MonadNonDet.wp_pick {τ : Type u} post :
  wp (MonadNonDet.pick (m := NonDetT m) τ) post = iInf post := by
  simp [MonadNonDet.pick, NonDetT.pick]

lemma MonadNonDet.wp_assume {as : Prop} post : wp (MonadNonDet.assume (m := NonDetT m) as) post = ⌜as⌝ ⇨ post .unit := by
  simp [MonadNonDet.assume, NonDetT.assume, iInf_const]

lemma MonadNonDet.wp_pickSuchThat {τ : Type u} (p : τ → Prop) post :
  wp (MonadNonDet.pickSuchThat (m := NonDetT m) τ p) post = ⨅ a, ⌜p a⌝ ⇨ post a := by
  simp [MonadNonDet.pickSuchThat, NonDetT.pickSuchThat]

lemma NonDetT.run_validSeed (x : NonDetT m α) (pre : l) (post : α -> l) (seed : x.type) [MPropDetertministic m l] :
  x.validSeed pre seed ->
  triple pre x post ->
  triple pre (x.run seed) post := by
    simp [triple]; revert seed pre
    unhygienic induction x <;> simp [NonDetT.run, NonDetT.validSeed, NonDetT.pre, NonDetT.type, _root_.wp_pure, wp_bind]
    { introv vs preh;
      by_cases eqt : (fun x ↦ wp ((f x).run (seed x)) post) = ⊤
      { simp [eqt]; apply le_trans; apply preh; apply wp_cons; simp }
      apply le_wp_sp_le _ eqt
      intro i; simp; apply f_ih; simp [NonDetT.validSeed]
      apply sp_le_le_wp
      { rw [<-wp_top_wlp]; simp; constructor <;> try assumption
        apply le_trans; apply preh; apply wp_cons; simp }
      solve_by_elim [sp_le_le_wp] }
    rintro pre ⟨seed, seed'⟩; simp; intro preL _ h
    apply f_ih; simp [NonDetT.validSeed, *]
    apply le_trans'; apply h; simpa

lemma NonDetT.wp_and [MPropDetertministic m l] {β} (x : NonDetT m β) post post' :
  wp x (fun x => post x ⊓ post' x) = wp x post ⊓ wp x post' := by
  unhygienic induction x <;> (try simp [f_ih]) <;> simp [_root_.wp_and, NonDetT.wp_pure, ←iInf_inf_eq, meet_himp]


end Demonic

namespace Angelic

def NonDetT.μ : NonDetT m UProp -> l
  | .pure ret => ⌜ret.down⌝
  | .vis x f => wp x fun a => μ (f a)
  | .pickCont _ p f => ⨆ a, ⌜p a⌝ ⊓ μ (f a)

instance : MonadLift m (NonDetT m) where
  monadLift x := NonDetT.vis x pure

variable [LawfulMonad m]

scoped
instance {l : outParam (Type u)} [CompleteBooleanAlgebra l] [MPropOrdered m l] [LawfulMonad m] : MPropOrdered (NonDetT m) l where
  μ := NonDetT.μ
  ι p := liftM $ MPropOrdered.ι (m := m) p
  μ_surjective := by
    intro x; simp [liftM, monadLift, MonadLift.monadLift, NonDetT.μ, wp]
    simp [MProp.lift, MPropOrdered.pure]
    erw [MPropOrdered.bind (m := m)]; rotate_right
    { ext; simp; conv => enter [1];  rw [@MPropOrdered.cancel] }
    simp; rw [@MPropOrdered.cancel]
  μ_top := by intro x; simp [NonDetT.μ, MPropOrdered.μ_top]
  μ_bot := by intro x; simp [NonDetT.μ, MPropOrdered.μ_bot]
  μ_ord_pure := by
    intro p₁ p₂ h; simp [NonDetT.μ]
    solve_by_elim [MPropOrdered.μ_ord_pure]
  μ_ord_bind := by
    introv; simp [Function.comp, Pi.hasLe, Pi.partialOrder, Pi.preorder, inferInstanceAs]
    intro h x; induction x
    <;> simp [bind, MPropOrdered.bind, NonDetT.bind, NonDetT.μ, -le_himp_iff]
    <;> try solve_by_elim [wp_cons, inf_le_inf_left, le_iSup_of_le]


@[simp]
lemma NonDetT.wp_vis {β : Type u} (x : m β) (f : β → NonDetT m α) post :
  wp (NonDetT.vis x f) post = wp x fun a => wp (f a) post := by
  conv =>
    enter [1]
    simp [wp, liftM, monadLift, MProp.lift, bind, Functor.map, NonDetT.bind]
    simp [MPropOrdered.μ, NonDetT.μ]
  congr

lemma NonDetT.wp_lift (c : m α) post :
  wp (liftM (n := NonDetT m) c) post = wp c post := by
  simp [liftM, monadLift, MonadLift.monadLift, wp_pure]

@[simp]
lemma NonDetT.wp_pickCont {τ : Type u} p (f : τ → NonDetT m α) post :
  wp (NonDetT.pickCont τ p f) post = ⨆ a, ⌜p a⌝ ⊓ wp (f a) post := by
  conv =>
    enter [1]
    simp [wp, liftM, monadLift, MProp.lift, bind, Functor.map, NonDetT.bind]
    simp [MPropOrdered.μ, NonDetT.μ]
  congr

@[simp]
lemma NonDetT.wp_pure (x : α) post :
  wp (NonDetT.pure (m := m) x) post = post x := by erw [_root_.wp_pure]

lemma MonadNonDet.wp_pick {τ : Type u} [Nonempty τ] post :
  wp (MonadNonDet.pick (m := NonDetT m) τ) post = iSup post := by
  simp [MonadNonDet.pick, NonDetT.pick]

lemma MonadNonDet.wp_assume {as : Prop} post : wp (MonadNonDet.assume (m := NonDetT m) as) post = ⌜as⌝ ⊓ post .unit := by
  simp [MonadNonDet.assume, NonDetT.assume, iSup_const]

lemma MonadNonDet.wp_pickSuchThat {τ : Type u} [Nonempty τ] (p : τ → Prop) post :
  wp (MonadNonDet.pickSuchThat (m := NonDetT m) τ p) post = ⨆ a, ⌜p a⌝ ⊓ post a := by
  simp [MonadNonDet.pickSuchThat, NonDetT.pickSuchThat]

def sp (x : m α) (pre : l) : α -> l := (sInf fun post => pre <= wp x post)

lemma le_wp_sp_le (x : m α) [MPropDetertministic m l] :
  post ≠ ⊤ ->
   (sp x pre <= post -> pre <= wp x post) := by
    intro pne
    by_cases ex:  Nonempty (Set.Elem fun post ↦ pre ≤ wp x post)
    { have : pre <= wp x (sp x pre) := by {
        unfold sp; simp [sInf]; rw [@wp_iInf]
        revert ex; simp [Set.Elem, Set.Mem, Membership.mem]
      }
      solve_by_elim [wp_cons, le_trans] }
    rw [@Set.not_nonempty_iff_eq_empty'] at ex
    simp [sp, ex, *]

omit [LawfulMonad m] in
lemma sp_le_le_wp (x : m α) :
   (pre <= wp x post -> sp x pre <= post) := by
    intro a; --refine inf_le_of_left_le ?_
    exact CompleteSemilatticeInf.sInf_le (fun post ↦ pre ≤ wp x post) post a

lemma NonDetT.run_validSeed (x : NonDetT m α) (pre : l) (post : α -> l) (seed : x.type) [MPropDetertministic m l] :
  triple pre (x.run seed) post ->
  x.validSeed pre seed ->
  triple pre x post := by
    simp [triple]; revert seed pre
    unhygienic induction x <;> simp [NonDetT.run, NonDetT.validSeed, NonDetT.pre, NonDetT.type, _root_.wp_pure, wp_bind]
    { introv preh vs;
      by_cases eqt : (fun x ↦ wp (f x) post) = ⊤
      { simp [eqt]; apply le_trans; apply preh; apply wp_cons; simp }
      apply le_wp_sp_le _ eqt
      intro i; simp; apply f_ih
      { revert i; solve_by_elim [sp_le_le_wp] }
      simp [NonDetT.validSeed]; apply sp_le_le_wp
      rw [<-wp_top_wlp]; simp; constructor <;> try assumption
      apply le_trans; apply preh; apply wp_cons; simp }
    rintro pre ⟨seed, seed'⟩; simp; intro preL _ h
    refine le_iSup_of_le seed ?_; simp; solve_by_elim

end Angelic


section variable [LawfulMonad m] [MPropDetertministic m l]


open Demonic in
lemma NonDetT.wp_tot_part ε (c : NonDetT (ExceptT ε m) α) post :
  [totl| wp c post] = [totl| wp c ⊤] ⊓ [part| wp c post] := by
  unhygienic induction c <;> simp
  { conv => enter [2,1,2]; ext; rw [<-inf_top_eq (a := [totl| wp (f _) _])]
    open TotalCorrectness in rw [wp_and]
    rw [inf_assoc]; erw [_root_.wp_tot_part]
    open TotalCorrectness in simp [<-wp_and, f_ih] }
  rw [← @iInf_inf_eq]; congr; ext x
  rw [f_ih, meet_himp]
  by_cases p x = True; simp [*]
  have : p x = False := by aesop
  simp [*]

set_option quotPrecheck false in
notation "[totlD|" t "]" => open TotalCorrectness Angelic in t
set_option quotPrecheck false in
notation "[partA|" t "]" => open PartialCorrectness Demonic in t

lemma NonDetT.iwp_part_wp_tot ε (c : NonDetT (ExceptT ε m) α) post
  (wp_bot : ∀ α (c : m α), wp c ⊥ = ⊥)
  (wp_top : ∀ α (c : m α), wp c ⊤ = ⊤) :
  [partA| wp c post] = [totlD| iwp c post] := by
    unhygienic induction c <;> simp
    { simp (disch := assumption) [wp_tot_eq_iwp_part, *]; rfl }
    simp [compl_iSup, f_ih, himp_eq, sup_comm];
    congr; ext x; congr 2
    by_cases p x = True; simp [*]
    have : p x = False := by aesop
    simp [*]

open Demonic in
lemma NonDetT.wp_tot_wp_handler ε [Inhabited ε] (c : NonDetT (ExceptT ε m) α) :
  [totl| wp c ⊤] =
    ⨅ (ex : ε), [handler (· ≠ ex)| wp c ⊤] := by
  unhygienic induction c <;> simp
  { conv => enter [2,1]; ext ex; rw [wp_except_handler_eq]
    rw [<-wp_iInf]
    rw [wp_except_handler_eq]; congr; ext ⟨a⟩ <;> simp
    { apply le_antisymm; simp
      refine iInf_le_of_le a ?_; simp }
    apply f_ih }
  rw [@iInf_comm]; congr; ext a
  simp [f_ih, himp_eq]; rw [@iInf_sup_eq]; congr; ext x; congr 1
  by_cases p a = True; simp [*]
  have : p a = False := by aesop
  simp [*]


#exit

open Lean

def NonDetT.stuck : NonDetT m α := pickCont PEmpty (·.elim)


lemma empty_f {α : Type*} (t : PEmpty) (f : PEmpty -> α) : f t = t.elim := by
  cases t
@[simp]
lemma NonDetT.stuck_bind : NonDetT.stuck.bind f = NonDetT.stuck := by
  simp [NonDetT.bind, NonDetT.stuck]; ext ⟨⟩

@[simp]
lemma NonDetT.stuckE : NonDetT.pickCont PEmpty f = NonDetT.stuck := by
  simp [NonDetT.bind, NonDetT.stuck]; ext ⟨⟩

inductive NonDetT.stucks : NonDetT m α → Prop
  | vis x f : (∀ y, f y |>.stucks) → (vis x f).stucks
  | pickCont τ f : (∀ x, f x |>.stucks) → (pickCont τ f).stucks
  | pickEmpty : (pickCont PEmpty f).stucks

def NonDetT.rel (x y : NonDetT m α) : Prop :=
  x = y ∨ (x.stucks ∧ y.stucks)


attribute [local simp] NonDetT.rel in
instance : Equivalence (NonDetT.rel (α := α) (m := m)) where
  refl := by simp
  symm := by aesop
  trans := by aesop

instance NonDetT.Setoid : Setoid (NonDetT m α) where
  r := NonDetT.rel
  iseqv := by apply instEquivalenceNonDetTRel

lemma bind_eq {x y : NonDetT m α} {f g : α → NonDetT m β} :
  x ≈ y ->
  (∀ a, f a ≈ g a) ->
  x.bind f ≈ y.bind g := by
  rintro (rfl|⟨xst, yst⟩)
  { unhygienic induction x <;> simp [NonDetT.bind]
    { solve_by_elim }
    intro eq
    by_cases eq' : (∀ a, f a = g a)
    { left; simp; ext; congr; solve_by_elim [funext] }
    { right
      specialize f_ih _ eq
       } }

  -- revert y f g <;> unhygienic induction x
  -- { rintro ⟨⟩ <;> simp [HasEquiv.Equiv, Setoid.r, NonDetT.rel, NonDetT.bind] <;>
  --   introv h <;> cases h <;> subst_vars <;> try solve_by_elim
  --   rename_i h <;> rcases h with ⟨⟨⟩,_⟩ }
  -- { rintro ⟨⟩ <;> simp [HasEquiv.Equiv, Setoid.r, NonDetT.rel, NonDetT.bind]
  --   { rintro _ _ h ⟨⟩ }
  --   { rintro _ _ ⟨⟨rfl, ⟨eqs₁, eqs₂⟩⟩⟩ feq
  --     simp at eqs₁ eqs₂ <;> subst_eqs
  --     simp [HasEquiv.Equiv, Setoid.r, NonDetT.rel, NonDetT.bind] at f_ih
  --     simp;  } }

  --    }


#exit

inductive NonDetT.notStuck : NonDetT m α → Prop
  | pure x : (pure x).notStuck
  | vis x f : (∀ y, f y |>.notStuck) → (vis x f).notStuck
  | pickCont τ f (t₀ : τ) : (∀ x, f x |>.notStuck) → (pickCont τ f).notStuck

inductive NonDetT.rel : NonDetT m α → NonDetT m α → Prop
  | bot : ∀ x, x = stuck ∨ x.notStuck -> stuck.rel x
  | pure : ∀ x, (pure x).rel (pure x)
  | vis : ∀ x f₁ f₂, (∀ y, (f₁ y).rel (f₂ y)) → (vis x f₁).rel (vis x f₂)
  | pickCont : ∀ (τ : Type u) (f₁ f₂ : τ → NonDetT m α),
      (∀ x, (f₁ x).rel (f₂ x)) → (pickCont τ f₁).rel (pickCont τ f₂)

omit [Monad m] [LawfulMonad m] in
lemma NonDetT.rel_notStuck (x y : NonDetT m α) :
  x.notStuck → x.rel y → x = y := by
  intro h; revert y; induction h
  { rintro (⟨⟩ | ⟨⟩ | ⟨⟩ ) <;> try rintro ⟨⟩; try simp }
  { rintro (⟨⟩ | ⟨⟩ | ⟨⟩ ) <;> try rintro ⟨⟩; try simp
    solve_by_elim [funext] }
  rintro (⟨⟩ | ⟨⟩ | ⟨⟩ ) <;> try rintro ⟨⟩; try simp; contradiction
  congr; solve_by_elim [funext]




instance : Order.PartialOrder (NonDetT m α) where
  rel := NonDetT.rel
  rel_refl := by
    intro x; induction x <;> try constructor <;> solve_by_elim
  rel_trans := by
    introv h; revert z
    induction h <;> intros <;> (try constructor) <;> try assumption
    { rename_i h; cases h <;> try solve_by_elim
      { rename_i h; rcases h with ⟨_,_⟩
        rename_i h; rcases h
        right; constructor; intro y
        rename_i h h';
        have := NonDetT.rel_notStuck _ _ (h' y) (h y); simp [<-this, h'] }
      rename_i h; rcases h with ⟨_,_⟩; simp
      rename_i h; rcases h
      right; constructor; assumption; intro y
      rename_i h _ h';
      have := NonDetT.rel_notStuck _ _ (h' y) (h y); simp [<-this, h'] }
    { rename_i h; cases h; solve_by_elim }
    { rename_i h; rcases h <;> (try simp) <;> solve_by_elim }

  rel_antisymm := by
    introv h; induction h <;> try simp
    { intros h; cases h <;> simp }
    { intros h; cases h; ext; solve_by_elim }
    intros h; cases h <;> ext <;> solve_by_elim [empty_f]

open Classical in
noncomputable instance : Order.CCPO (NonDetT m α) where
  csup cs :=
    if h : ∃ x, cs x ∧ x.notStuck then h.choose else .stuck
  csup_spec := by
    simp; introv cc; split_ifs with h
    { constructor
      { rcases h.choose_spec with ⟨ch, chh⟩  } }

noncomputable instance : Order.MonoBind (NonDetT m) where
  bind_mono_left h := by
    induction h
    { simp [bind]; solve_by_elim }
    { simp [bind, NonDetT.bind]; exact Order.PartialOrder.rel_of_eq rfl }
    { simp [bind, NonDetT.bind]; constructor; solve_by_elim }
    simp [bind, NonDetT.bind]; constructor; solve_by_elim
  bind_mono_right h := by
    rename_i x f₁ f₂
    induction x <;> simp [bind, NonDetT.bind] <;> try solve_by_elim


def Loop.repeat {β : Type u} {m : Type u → Type v} [Monad m] (_ : Loop) (init : β) (f : Unit → β → NonDetT m (ForInStep β)) :
  NonDetT m β :=
  let rec @[specialize] loop (b : β) : NonDetT m β := do
    match ← f () b with
      | ForInStep.done b  => pure b
      | ForInStep.yield b => loop b
  partial_fixpoint
  loop init


end NonDetermenisticTransformer
