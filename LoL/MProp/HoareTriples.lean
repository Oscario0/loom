import Mathlib.Order.CompleteBooleanAlgebra

import LoL.MProp.EffectObservations
import LoL.MProp.Instances

universe u v w

variable {m : Type u -> Type v} [Monad m] [LawfulMonad m] {α : Type u} {l : Type u}

section
variable  [Preorder l]
section
variable [MProp m l]

def wp (c : m α) (post : α -> l) : l := liftM (n := Cont l) c post
def triple (pre : l) (c : m α) (post : α -> l) : Prop :=
  pre ≤ wp c post

abbrev mtriple (pre : m PProp) (c : m α) (post : α -> m PProp) : Prop :=
  triple (MProp.μ pre) c (MProp.μ ∘ post)

omit [Preorder l] in
lemma wp_pure (x : α) (post : α -> l) : wp (m := m) (pure x) post = post x := by
  simp [wp, liftM, lift_pure]
  rfl

lemma triple_pure (pre : l) (x : α) (post : α -> l) :
  triple pre (pure (f := m) x) post <-> pre ≤ (post x)
  := by
    rw [triple, wp]; simp [liftM, lift_pure]; rfl

lemma mtriple_pure (pre : m PProp) (x : α) (post : α -> m PProp) :
  mtriple pre (pure x) post <->
  MProp.μ pre ≤ MProp.μ (post x)
  := by exact triple_pure (MProp.μ pre) x (MProp.μ ∘ post)
end

variable [MPropOrdered m l]

lemma wp_bind {β} (x : m α) (f : α -> m β) (post : β -> l) :
    wp (x >>= f) post = wp x (fun x => wp (f x) post) := by
    simp [wp, liftM]; rw [lift_bind]; rfl

lemma wp_cons (x : m α) (post post' : α -> l) :
  (∀ y, post y ≤ post' y) ->
  wp x post ≤ wp x post' := by
    intros h; simp [wp]; apply Cont.monotone_lift; intros y
    apply h

lemma triple_bind {β} (pre : l) (x : m α) (cut : α -> l)
  (f : α -> m β) (post : β -> l) :
  triple pre x cut ->
  (∀ y, triple (cut y) (f y) post) ->
  triple pre (x >>= f) post := by
    intros; simp [triple, wp_bind]
    solve_by_elim [le_trans', wp_cons]

lemma mtriple_bind {β} (pre : m PProp) (x : m α) (cut : α -> m PProp)
  (f : α -> m β) (post : β -> m PProp) :
  mtriple pre x cut ->
  (∀ y, mtriple (cut y) (f y) post) ->
  mtriple pre (x >>= f) post := by apply triple_bind

theorem Triple.forIn_list {α β}
  {xs : List α} {init : β} {f : α → β → m (ForInStep β)}
  (inv : List α → β → m PProp)
  (hstep : ∀ hd tl b,
    mtriple
      (inv (hd :: tl) b)
      (f hd b)
      (fun | .yield b' => inv tl b' | .done b' => inv [] b')) :
  mtriple (inv xs init) (forIn xs init f) (inv []) := by
    induction xs generalizing init
    { simp; rw [mtriple_pure] }
    simp only [List.forIn_cons]
    apply mtriple_bind; apply hstep; intros y
    cases y <;> simp <;> solve_by_elim [(mtriple_pure ..).mpr, le_refl]
end

section
variable [SemilatticeInf l] [MPropPartialOrder m l]

def spec (pre : l) (post : α -> l) : Cont l α :=
  fun p => pre ⊓ MProp.pure (m := m) (post ≤ p)

def mspec (pre : m PProp) (post : α -> m PProp) : Cont l α :=
  spec (m := m) (MProp.μ pre) (MProp.μ ∘ post)

lemma triple_spec (pre : l) (c : m α) (post : α -> l) :
  spec (m := m) pre post <= wp c <->
  triple pre c post := by
    constructor
    { intro h; unfold triple
      specialize h post; apply le_trans'; apply h
      unfold spec; simp
      apply MPropPartialOrder.μ_top }
    intro t p; unfold spec
    by_cases h: post ≤ p
    { apply inf_le_of_left_le; apply le_trans; apply t
      solve_by_elim [Cont.monotone_lift (x := c)] }
    apply inf_le_of_right_le; apply le_trans'; apply MPropPartialOrder.μ_bot (m := m)
    apply MPropPartialOrder.μ_ord_pure; solve_by_elim

lemma mtriple_mspec (pre : m PProp) (c : m α) (post : α -> m PProp) :
  mspec pre post ≤ wp c <-> mtriple pre c post := by apply triple_spec

class abbrev MonadLogic (m : Type u -> Type v) (l : Type u) [Monad m] := Logic l, MPropPartialOrder m l
end

section
variable [inst: CompleteBooleanAlgebra l]

variable [MPropPartialOrder m l]

omit [LawfulMonad m] in
@[simp]
lemma trueE : ⌜True⌝ = ⊤ := by
  apply le_antisymm; exact OrderTop.le_top ⌜True⌝
  apply MPropPartialOrder.μ_top

omit [LawfulMonad m] in
@[simp]
lemma falseE : ⌜False⌝ = ⊥ := by
  apply le_antisymm; apply MPropPartialOrder.μ_bot
  simp

def failPre (c : m α) : l := sSup {pre | ¬ triple pre c ⊤}

-- @[simp]
lemma failPre_bind {β} x (f : α -> m β) :
  failPre (x >>= f) <= failPre x ⊔ wp x (fun x => failPre (f x)) := by
    simp [failPre, triple, wp_bind]
    intro pre htr
    by_cases hpre : pre <= wp x ⊤
    { refine le_sup_of_le_right ?_
      apply le_trans; apply hpre; apply wp_cons; intros
      apply CompleteLattice.le_sSup; simp
      intro  }

@[simp]
lemma failPre_bind' {β} x (f : α -> m β) : failPre x <= failPre (x >>= f) := by
  simp [failPre, triple, wp_bind]
  intro pre hpre;
  refine CompleteLattice.le_sSup {pre | ¬pre ≤ wp x fun x ↦ wp (f x) ⊤} pre ?_
  simp; revert hpre; contrapose!
  solve_by_elim [le_trans', wp_cons, le_top]

-- partial weakest precondition
def wlp (c : m α) (post : α -> l) : l :=
  wp c post ⊔ failPre c

def ptriple (pre : l) (c : m α) (post : α -> l) : Prop :=
  pre ≤ wlp c post

omit [LawfulMonad m] in
@[simp]
lemma wlp_true (c : m α) : wlp c (fun _ => ⌜True⌝) = ⌜True⌝ := by
  simp [wlp]; apply le_antisymm; simp
  simp only [failPre, triple]
  by_cases h : ⊤ <= wp c ⊤
  { solve_by_elim [le_sup_of_le_left] }
  apply le_sup_of_le_right
  exact CompleteLattice.le_sSup {pre | ¬pre ≤ wp c ⊤} ⊤ h

-- partial weakest precondition
@[simp]
lemma wlp_pure (x : α) (post : α -> l) :
  wlp (pure (f := m) x) post = post x := by
    simp [wlp, failPre, wp_pure, triple_pure]


lemma wlp_bind {β} (x : m α) (f : α -> m β) (post : β -> l) :
  wlp (x >>= f) post = wlp x (fun x => wlp (f x) post) := by
  simp [wlp, wp_bind]; apply le_antisymm
  { simp; constructor
    { refine le_sup_of_le_left ?_
      apply wp_cons <;> simp }

    refine le_sup_of_le_right ?_
    apply MProp.pure_imp; intros
    solve_by_elim [le_sup_of_le_right, MProp.pure_imp] }
  simp; constructor
  { by_cases h : ∀ (a : β), ⌜True⌝ ≤ post a = False
    { simp [*]; refine le_sup_of_le_left ?_
      apply wp_cons <;> simp; intros
      apply MPropPartialOrder.μ_bot }
    simp_all; refine le_sup_of_le_right ?_
    apply MPropPartialOrder.μ_top }


end
