import Mathlib.Order.CompleteBooleanAlgebra

import LoL.MProp.EffectObservations
import LoL.MProp.WP
import LoL.MProp.Instances

universe u v w

variable {m : Type u -> Type v} [Monad m] [LawfulMonad m] {α : Type u} {l : Type u}
variable [inst: CompleteBooleanAlgebra l] [mprop: MPropOrdered m l]

instance : SemilatticeInf l := inst.toSemilatticeInf

omit [LawfulMonad m] in
@[simp]
lemma trueE : ⌜True⌝ = ⊤ := by
  apply le_antisymm; exact OrderTop.le_top ⌜True⌝
  apply MPropOrdered.μ_top

omit [LawfulMonad m] in
@[simp]
lemma falseE : ⌜False⌝ = ⊥ := by
  apply le_antisymm; apply MPropOrdered.μ_bot
  simp

@[local simp]
private lemma compl_fun {α} (x y : α -> l) :
  (fun a => x a ⊔ y a)ᶜ = (fun a => (x a)ᶜ ⊓ (y a)ᶜ) := by simp [compl]

@[local simp]
private lemma compl_fun' {α} (x y : α -> l) :
  (fun a => x a ⊓ y a)ᶜ = (fun a => (x a)ᶜ ⊔ (y a)ᶜ) := by simp [compl]

@[local simp]
private lemma compl_fun'' {α} (x : α -> l) :
  (fun a => (x a)ᶜ) = xᶜ := by simp [compl]


@[local simp]
private lemma compl_fun_true {α} :
  (fun (_ : α) => ⊤)ᶜ = fun _ => (⊥ : l) := by simp [compl]

def wlp (c : m α) (post : α -> l) : l := (wp c postᶜ)ᶜ ⊔ wp c post

@[simp]
lemma wlp_true (c : m α) : wlp c (fun _ => ⊤) = ⊤ := by
  simp [wlp]; rw [@eq_top_iff, sup_comm, <-himp_eq]; simp
  apply wp_cons; simp

@[simp]
lemma wlp_pure (x : α) (post : α -> l) :
  wlp (pure (f := m) x) post = post x := by
    simp [wlp, wp_pure, triple_pure]

omit [LawfulMonad m] in
lemma wp_wlp (c : m α) (post : α -> l) :
  wp c post <= wlp c post := by
    simp [wlp, wp]

section Determenism
variable [MPropDetertministic m l]

lemma wlp_and (c : m α) (post₁ post₂ : α -> l) :
  wlp c (fun x => post₁ x ⊓ post₂ x) = wlp c post₁ ⊓ wlp c post₂ := by
  simp [wlp]; apply le_antisymm
  { simp [wp_or, wp_and]; repeat' constructor
    { apply le_sup_of_le_left; apply inf_le_of_left_le; rfl }
    { apply le_sup_of_le_right; apply inf_le_of_left_le; rfl }
    { apply le_sup_of_le_left; apply inf_le_of_right_le; rfl }
    apply le_sup_of_le_right; apply inf_le_of_right_le; rfl }
  rw (occs := .pos [3]) [sup_comm]; rw [<-himp_eq]; simp
  rw [inf_inf_distrib_right]
  conv =>
    enter [1,1]
    rw [inf_sup_right, <-wp_and];
    simp [inf_sup_left]; rw [wp_or, inf_sup_left]; simp
    erw [wp_and, <-inf_sup_right]
  conv =>
    enter [1,2]
    rw [inf_sup_right, <-wp_and];
    simp [inf_sup_left]; rw [wp_or, inf_sup_left]; simp
    erw [wp_and, <-inf_sup_right]
  rw (occs := .pos [3]) [inf_comm]
  rw [inf_assoc]
  rw (occs := .pos [2]) [<-inf_assoc]
  rw (occs := .pos [3]) [inf_comm]
  repeat rw [<-inf_assoc]
  rw [inf_sup_right, <-wp_and]; simp
  apply inf_le_of_left_le
  apply inf_le_of_left_le
  apply wp_cons; simp

lemma wlp_bind {β} (x : m α) (f : α -> m β) (post : β -> l) :
  wlp (x >>= f) post = wlp x (fun x => wlp (f x) post) := by
  simp [wlp, wp_bind]; apply le_antisymm
  { simp [wp_and, wp_or]; constructor
    { repeat apply le_sup_of_le_left; simp }
    repeat apply le_sup_of_le_right; simp }
  simp [wp_and, wp_or]; constructor
  { rw [<-compl_compl (x := wp x fun a ↦ wp (f a) post)]
    rw [<-himp_eq, le_himp_iff, ← compl_sup, <-wp_or]
    simp; apply wp_cons; simp }
  rw [sup_comm]; simp [<-himp_eq, <-wp_and]
  apply wp_cons; simp

lemma wlp_himp (c : m α) (post post' : α -> l) :
  wp c (fun x => post' x ⇨ post x) = wlp c post' ⇨ wp c post := by
    rw [himp_eq, wlp]; simp [himp_eq, wp_or]
    apply le_antisymm <;> simp
    { rw [<-compl_compl (x := wp c post'ᶜ ⊓ (wp c post')ᶜ)]
      rw [<-himp_eq]; simp; rw [@inf_sup_left]; simp [<-wp_and]
      apply wp_cons; simp }
    rw [<-le_himp_iff, himp_eq]; simp
    refine le_sup_of_le_left ?_
    refine le_sup_of_le_right ?_
    simp

lemma wp_top_wlp (c : m α) (post : α -> l) :
  wp c ⊤ ⊓ wlp c post = wp c post := by
  apply le_antisymm
  { rw [inf_comm, ← @le_himp_iff', <-wlp_himp]; simp; rfl }
  simp; constructor
  { apply wp_cons; simp }
  apply wp_wlp

section ExceptT

abbrev noFailure (m : Type u -> Type v) (l : Type u)
  [Monad m] [MProp m l] [CompleteLattice l] := ∀ α (c : m α), wp c ⊤ = ⊤

variable {ε : Type u}

-- open PartialCorrectness

omit [MPropDetertministic m l] in
lemma wp_except_part_eq (c : ExceptTPart ε m α) post :
  wp c post = wp (m := m) c (fun | .ok x => post x | .error _ => ⊤) := by
    simp [wp, liftM, monadLift, MProp.lift]
    simp [instMPropOrderedExceptTPartOfLawfulMonad, MPropExcept, bind, ExceptT.bind, ExceptT.mk]
    unfold ExceptT.bindCont; simp;
    apply MPropOrdered.bind; ext a; cases a <;> simp [Except.getD]
    rw [MPropOrdered.μ_surjective]; apply trueE

-- open TotalCorrectness

omit [MPropDetertministic m l] in
lemma wp_except_tot_eq (c : ExceptTTot ε m α) post :
  wp c post = wp (m := m) c (fun | .ok x => post x | .error _ => ⊥) := by
    simp [wp, liftM, monadLift, MProp.lift]
    simp [instMPropOrderedExceptTTotOfLawfulMonad, MPropExcept, bind, ExceptT.bind, ExceptT.mk]
    unfold ExceptT.bindCont; simp;
    apply MPropOrdered.bind; ext a; cases a <;> simp [Except.getD]
    rw [MPropOrdered.μ_surjective]; apply falseE

variable (wp_bot : noFailure m l)
include wp_bot

lemma wp_compl (c : m α) post :
  (wp c postᶜ)ᶜ <= wp c post := by
    refine compl_le_iff_compl_le.mp ?_
    rw [← @codisjoint_iff_compl_le_right]; intro b
    rw [<-wp_bot (c := c)]; intros; apply le_trans
    apply wp_cons; intro a; apply BooleanAlgebra.top_le_sup_compl (x := post)
    erw [wp_or]; simp_all

lemma wp_part_eq_wlp (c : ExceptTTot ε m α) (post : α -> l) :
  wp c.toPart post = wlp c post := by
    simp [wlp, wp_except_tot_eq, wp_except_part_eq]
    apply le_antisymm <;> try simp
    { rw [sup_comm, <-himp_eq]; simp; erw [<-wp_and]
      apply wp_cons; rintro (_|_) <;> simp }
    constructor
    { apply le_trans'; apply wp_compl; assumption
      simp; apply wp_cons; rintro (_|_) <;> simp }
    apply wp_cons; rintro (_|_) <;> simp

end ExceptT

end Determenism
