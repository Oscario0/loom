import Mathlib.Logic.Function.Basic
import Mathlib.Order.CompleteBooleanAlgebra
import Mathlib.Order.Lattice
import Mathlib.Order.Basic
import Mathlib.Data.W.Basic

import LoL.MonadAlgebras.WP
import LoL.MonadAlgebras.WLP
import LoL.MonadAlgebras.NonDetT.Basic
import Lol.Meta

universe u v w

open Demonic
open TotalCorrectness

variable {m : Type u -> Type v} {α β : Type u} [Monad m]

variable {l} [CompleteBooleanAlgebra l] [MPropOrdered m l] [LawfulMonad m] [MPropDetertministic m l]

inductive AccFrom (p : Nat -> Prop) : Nat -> Prop
    | now : p i -> AccFrom p i
    | later : ¬ p i -> AccFrom p (i + 1) -> AccFrom p i


def findNat (p : Nat -> Prop) [DecidablePred p] : Option Nat :=
  let rec aux i :=
    if p i then
      some i
    else
      aux (i + 1)
  partial_fixpoint
  aux 0

lemma AccFrom_findNat (p : Nat -> Prop) [DecidablePred p] (i : Nat) :
  AccFrom p i -> (findNat.aux p i).isSome := by
  intros h; unhygienic induction h <;> (unfold findNat.aux; aesop)

lemma AccFrom_of_p (p : Nat -> Prop) [DecidablePred p] (i : Nat) :
  p i -> ∀ j ≤ i, AccFrom p j := by
  intro pi j h
  unhygienic induction h using Nat.decreasingInduction <;> try solve_by_elim
  by_cases p k; solve_by_elim
  apply AccFrom.later <;> solve_by_elim

lemma exists_findNat (p : Nat -> Prop) [DecidablePred p] :
  (∃ x, p x) ↔ (findNat p).isSome := by
  constructor
  { rintro ⟨x, px⟩
    apply AccFrom_findNat; apply AccFrom_of_p <;> aesop }
  simp [Option.isSome_iff_exists]; intro i eq; exists i; revert eq
  unfold findNat; generalize 0 = m;
  apply findNat.aux.partial_correctness; aesop

lemma findNat_none (p : Nat -> Prop) [DecidablePred p] :
  (findNat p).isNone -> ∀ i, ¬ p i := by
  simp; rw [<-Option.not_isSome_iff_eq_none, <-exists_findNat]; simp

lemma p_findNat_some (p : Nat -> Prop) [DecidablePred p] (i : Nat) :
  p i -> ∃ j, p j ∧ j <= i ∧ findNat p = some j := by
  intro pi; exists i; simp [pi]
  sorry

lemma findNat_some_p (p : Nat -> Prop) [DecidablePred p] (i : Nat) :
  findNat p = some i -> p i := by
  simp [findNat]; generalize 0 = m;
  apply findNat.aux.partial_correctness; aesop


def find [Encodable α] (p : α -> Prop) [DecidablePred p] : Option α :=
  findNat (fun x => (Encodable.decode x).any (p ·)) |>.bind Encodable.decode

lemma find_none (p : α -> Prop) [DecidablePred p] [Encodable α] :
  (find p).isNone -> ∀ x, ¬ p x := by
  simp [find]; intro h a pa
  have := p_findNat_some (fun x => (Encodable.decode x).any (p ·)) (Encodable.encode a) ?_
  { rcases this with ⟨j, pj, hj, eq⟩; simp [eq] at h;
    simp [h] at pj }
  simpa

lemma find_some_p (p : α -> Prop) [DecidablePred p] [Encodable α] (x : α) :
  find p = some x -> p x := by
  simp [find, Option.bind]; split; simp
  have := findNat_some_p _ _ (by assumption)
  intro eq; rw [eq] at this; simp at this; exact this

inductive ExtractNonDet {m α} : NonDetT m α -> Type _ where
  | pure : ∀ (x : α), ExtractNonDet (NonDetT.pure x)
  | vis {β} (x : m β) (f : β → NonDetT m α) :
      (∀ y, ExtractNonDet (f y)) → ExtractNonDet (.vis x f)
  | pickSuchThat (τ : Type u) (p : τ -> Prop) (f : τ → NonDetT m α) {_ : Encodable τ}
    {_ : DecidablePred p} : (∀ x, ExtractNonDet (f x)) → ExtractNonDet (.pickCont τ p f)
  | assume (p : PUnit -> Prop) (f : PUnit → NonDetT m α) :
    (∀ x, ExtractNonDet (f x)) → ExtractNonDet (.pickCont PUnit p f)

def NonDetT.extract : (s : NonDetT m α) -> (ex : ExtractNonDet s := by solve_by_elim) -> ExceptT PUnit m α
  | .pure x, _ => Pure.pure x
  | .vis x f, .vis _ _ _ => liftM x >>= (fun x => extract (f x))
  | .pickCont _ p f, .pickSuchThat _ _ _ _ =>
    match find p with
    | none => throw .unit
    | some x =>  extract (f x)
  | .pickCont _ _ f, .assume _ _ _ => extract (f .unit)

noncomputable
abbrev NonDetT.prop : (s : NonDetT m α) -> Cont l α
  | .pure x => Pure.pure x
  | .vis x f => fun post => wlp x fun y => NonDetT.prop (f y) post
  | .pickCont _ p f => fun post =>
    (⨅ t, ⌜p t⌝ ⇨ NonDetT.prop (f t) post) ⊓ (⨆ t, ⌜p t⌝)

lemma NonDetT.extract_refines_wp (s : NonDetT m α) (inst : ExtractNonDet s) :
  wp s post ⊓ s.prop ⊤ <= wp s.extract post := by
  unhygienic induction inst
  { simp [wp_pure, NonDetT.extract] }
  { simp [NonDetT.wp_vis, NonDetT.prop]; rw [inf_comm, wlp_join_wp]
    simp [NonDetT.extract, wp_bind, ExceptT.wp_lift]
    apply wp_cons; aesop (add norm inf_comm) }
  { simp [NonDetT.wp_pickCont, NonDetT.prop, NonDetT.extract]; split
    { have := find_none p (by simpa);
      have : (∀ x, p x = False) := by simpa
      simp [this] }
    rw [<-inf_assoc]; refine inf_le_of_left_le ?_
    rw [← @iInf_inf_eq]; simp [meet_himp _ _ _ _ rfl]
    rename_i y _
    refine iInf_le_of_le y ?_
    have := find_some_p _ _ (by assumption)
    simp [this]; simp_all only }
  simp [NonDetT.wp_pickCont, NonDetT.prop, NonDetT.extract]
  have: ∀ a : PUnit.{u + 1}, a = .unit := by aesop
  simp [this, iInf_const, iSup_const]; apply le_trans'; apply a_ih
  simp; constructor
  { rw [<-inf_assoc, <-le_himp_iff]; exact inf_le_left }
  refine inf_le_of_right_le ?_; exact inf_le_left

lemma NonDetT.extract_refines (pre : l) (s : NonDetT m α) (inst : ExtractNonDet s) :
  triple pre s post ->
  pre <= s.prop ⊤ ->
  triple pre s.extract post := by
  intro tr imp; apply le_trans'; apply NonDetT.extract_refines_wp
  simp; aesop

def ExtractNonDet.bind : (ExtractNonDet x) -> (∀ y, ExtractNonDet (f y)) -> ExtractNonDet (x >>= f)
  | .pure x, inst => by
    dsimp [Bind.bind, NonDetT.bind]; exact (inst x)
  | .vis x f inst, inst' => by
    dsimp [Bind.bind, NonDetT.bind]; constructor
    intro y; apply ExtractNonDet.bind <;> solve_by_elim
  | .pickSuchThat _ p f inst, inst' => by
    dsimp [Bind.bind, NonDetT.bind]; constructor
    assumption; assumption; intro y; apply ExtractNonDet.bind <;> solve_by_elim
  | .assume _ f inst, inst' => by
    dsimp [Bind.bind, NonDetT.bind]; apply ExtractNonDet.assume
    intro y; apply ExtractNonDet.bind <;> solve_by_elim

def ExtractNonDet.pure' : ExtractNonDet (Pure.pure (f := NonDetT m) x) := by
  dsimp [Pure.pure, NonDetT.pure]; constructor

def ExtractNonDet.liftM (x : m α) :
  ExtractNonDet (liftM (n := NonDetT m) x) := by
    dsimp [_root_.liftM, monadLift, MonadLift.monadLift]; constructor
    intro y; apply ExtractNonDet.pure'

def ExtractNonDet.assume' {p : Prop} : ExtractNonDet (MonadNonDet.assume (m :=  NonDetT m) p) := by
  dsimp [MonadNonDet.assume, NonDetT.assume]; apply ExtractNonDet.assume
  intro y; apply ExtractNonDet.pure

def ExtractNonDet.pickSuchThat' {τ : Type u} (p : τ -> Prop) [Encodable τ] [DecidablePred p] :
  ExtractNonDet (MonadNonDet.pickSuchThat (m := NonDetT m) τ p) := by
    dsimp [MonadNonDet.pickSuchThat, NonDetT.pickSuchThat]; constructor
    assumption; assumption; intro y; apply ExtractNonDet.pure

def ExtractNonDet.if {p : Prop} {dec : Decidable p} {x y : NonDetT m α}
  (_ : ExtractNonDet x) (_ : ExtractNonDet y) :
  ExtractNonDet (if p then x else y) := by
    match dec with
    | .isTrue h => dsimp [ite]; assumption
    | .isFalse h => dsimp [ite]; assumption

def ExtractNonDet.ForIn_list {xs : List α} {init : β} {f : α → β → NonDetT m (ForInStep β)}
  (_ : ∀ a b, ExtractNonDet (f a b)) :
  ExtractNonDet (forIn xs init f) := by
    unhygienic induction xs generalizing init
    { dsimp [forIn]; apply ExtractNonDet.pure }
    { simp only [List.forIn_cons]
      apply ExtractNonDet.bind; solve_by_elim
      rintro (_|_)
      { dsimp; apply ExtractNonDet.pure }
      dsimp; apply tail_ih }

macro "extract_step" : tactic =>
  `(tactic|
    first
      | eapply ExtractNonDet.ForIn_list
      | eapply ExtractNonDet.bind
      | eapply ExtractNonDet.pure'
      | eapply ExtractNonDet.liftM
      | eapply ExtractNonDet.assume'
      | eapply ExtractNonDet.pickSuchThat'
      | eapply ExtractNonDet.if)

macro "extract_tactic" : tactic =>
  `(tactic| repeat' (intros; extract_step; try dsimp))

structure Extractable (x : NonDetT m α) where
  cond : Cont l α
  prop : ∀ post, cond post <= x.prop post

omit [LawfulMonad m] [MPropDetertministic m l] in
lemma NonDetT.prop_bind (x : NonDetT m α) (f : α -> NonDetT m β) :
  (x >>= f).prop = fun post => x.prop (fun a => (f a).prop post) := by
  unhygienic induction x
  { rfl }
  { simp [Bind.bind, NonDetT.bind, NonDetT.prop];
    ext post; congr!; erw [f_ih] }
  simp [Bind.bind, NonDetT.bind, NonDetT.prop];
  ext post; congr!; erw [f_ih]

omit [MPropDetertministic m l] in
lemma NonDetT.prop_mono (x : NonDetT m α) post post' :
  post <= post' -> x.prop post <= x.prop post' := by
  intro postLe; unhygienic induction x <;> simp only [NonDetT.prop]
  { solve_by_elim }
  { solve_by_elim [wlp_cons] }
  apply inf_le_inf_right; apply iInf_mono; intro
  exact himp_le_himp_left (f_ih _)

def Extractable.bind (x : NonDetT m α) (f : α -> NonDetT m β)
  (ex : Extractable x) (exf : ∀ a, Extractable (f a)) :
  Extractable (x >>= f) := by
    exists fun post => ex.cond (fun a => (exf a).cond post)
    intro post; rw [NonDetT.prop_bind]
    simp [Bind.bind, NonDetT.bind, NonDetT.prop]
    apply le_trans'; apply NonDetT.prop_mono
    { intro a; apply (exf a).prop }
    apply ex.prop

def Extractable.pure (x : α) : Extractable (pure (f := NonDetT m) x) := by
  exists fun post => post x
  intro post; simp [NonDetT.prop, Pure.pure]

def Extractable.liftM (x : m α) : Extractable (liftM (n := NonDetT m) x) := by
  exists wlp x
  intro post; simp [_root_.liftM, NonDetT.prop]; apply wlp_cons; rfl

noncomputable
def Extractable.assume (p : Prop) :
  Extractable (MonadNonDet.assume (m := NonDetT m) p) := by
  exists fun post => ⌜ p ⌝ ⊓ post .unit
  intro post; simp [NonDetT.prop, MonadNonDet.assume, NonDetT.assume, Pure.pure, iSup_const]

noncomputable
def Extractable.pickSuchThat (τ : Type u) (p : τ -> Prop) [Encodable τ] [DecidablePred p] :
  Extractable (MonadNonDet.pickSuchThat (m := NonDetT m) τ p) := by
    exists fun post => (⨅ t, ⌜ p t ⌝ ⇨ post t) ⊓ (⨆ t, ⌜ p t ⌝)
    intro post; simp [NonDetT.prop, MonadNonDet.pickSuchThat, NonDetT.pickSuchThat, Pure.pure, iInf_const]

noncomputable
def Extractable.forIn (xs : List α) (init : β) (f : α -> β -> NonDetT m (ForInStep β))
  (ex: ∀ a b, Extractable (f a b)):
  Extractable (forIn xs init f) := by
    exists fun post => ⌜⊤ <= post ∧ ∀ a b, ⊤ <= (ex a b).cond ⊤⌝
    intro post; dsimp
    by_cases h : (⊤ <= post ∧ ∀ a b, ⊤ <= (ex a b).cond ⊤) = False
    { rw [h]; simp }
    have : (⊤ <= post ∧ ∀ a b, ⊤ <= (ex a b).cond ⊤) = True := by aesop
    simp at h
    rw [this]; simp only [trueE]
    induction xs generalizing init
    { simp [Pure.pure, NonDetT.prop, h] }
    simp only [List.forIn_cons, NonDetT.prop_bind]
    apply le_trans'; apply (ex _ _).prop
    rw [<-h.right]; apply le_of_eq; congr
    ext (_|_)
    { simp [Pure.pure, NonDetT.prop, h] }
    simp_all

noncomputable
def Extractable.forIn_range (m : Type -> Type v) (l : Type) {β : Type} [CompleteBooleanAlgebra l] [Monad m] [MPropOrdered m l] (xs : Std.Range) (init : β) (f : ℕ -> β -> NonDetT m (ForInStep β))
  (ex: ∀ a b, Extractable (f a b)):
  Extractable (ForIn.forIn xs init f) := by
    unfold instForInOfForIn'; simp; solve_by_elim [forIn]

omit [LawfulMonad m] [MPropDetertministic m l] in
lemma Extractable.intro (x : NonDetT m α) (ex : Extractable x) :
  pre <= ex.cond post ->
  pre <= x.prop post := by
    solve_by_elim [ex.prop, le_trans']

macro "extractable_step" : tactic =>
  `(tactic|
    first
      | eapply Extractable.forIn
      | eapply Extractable.bind
      | eapply Extractable.pure
      | eapply Extractable.liftM
      | eapply Extractable.assume
      | eapply Extractable.pickSuchThat)

macro "extractable_tactic" : tactic =>
  `(tactic| repeat' (intros; extractable_step; try dsimp))


syntax "let" ident ":|" term : doElem
syntax "while_some" ident ":|" termBeforeDo "do" doSeq : doElem
macro_rules
  | `(doElem| let $x:ident :| $t) => `(doElem| let $x:ident <- pickSuchThat _ (fun $x => $t))
  | `(doElem| while_some $x:ident :| $t do $seq:doSeq) =>
    match seq with
    | `(doSeq| $[$seq:doElem]*)
    | `(doSeq| $[$seq:doElem;]*)
    | `(doSeq| { $[$seq:doElem]* }) =>
      `(doElem|
        while ∃ $x:ident, $t do
          let $x :| $t
          $[$seq:doElem]*)
    | _ => Lean.Macro.throwError "while_some expects a sequence of do-elements"

abbrev foo (n : ℕ) : NonDetT (StateT ℕ Id) ℕ := do
  for i in List.range n do
    let x :| x > i
    modify (· + x)
  get


#print foo

abbrev fooEx : ExtractNonDet (foo n) := by extract_tactic
abbrev fooExable : Extractable (foo n) := by extractable_tactic



-- #synth MPropOrdered (NonDetT (StateT ℕ Id)) (ℕ -> Prop)

open Classical

attribute [-simp] top_le_iff
example (n : ℕ) :
  ⊤ <= (foo n).prop (fun _ => ⊤) := by
  -- apply Extractable.intro (foo n) fooExable
  -- simp [fooExable, Extractable.forIn, Extractable.bind, Extractable.pure, Extractable.liftM, Extractable.assume, Extractable.pickSuchThat, wlp_true]
  sorry


#exit


def refines (pre : l) (x : m α) (nx : NonDetT m α) :=
  ∀ post : α -> l, triple pre nx post -> triple pre x post

lemma refines_validSeed (pre : l) (nx : NonDetT m α) (seed : nx.type) :
  nx.validSeed pre seed -> refines pre (nx.run seed) nx := by
  solve_by_elim [NonDetT.run_validSeed]

def refinesOn (pre : Cont l β) (x : β -> m α) (nx : β -> NonDetT m α) : Prop :=
  pre.monotone ->
  (∀ post post', pre (fun x => post x ⊓ post' x) = pre post ⊓ pre post') ->
  pre ⊤ = ⊤ ->
  ∀ post : β -> α -> l, pre (fun b => wp (nx b) (post b)) <= pre (fun b => wp (x b) (post b))


abbrev refinesOnPre (pre : l) (x : m α) (nx : NonDetT m α) :=
  refinesOn (fun post : PUnit -> _ => pre ⇨ post .unit) (fun _ => x) (fun _ => nx)

omit [MPropDetertministic m l] in
lemma refinesOn_himp (pre : l) (x : m α) (nx : NonDetT m α) :
  refinesOnPre pre x nx -> refines pre x nx := by
  intro ref post; simp [triple]; intro tr
  simp [refinesOn] at ref; apply le_trans'; apply ref _ (post := fun _ => post)
  { simp [meet_himp] }
  { introv h; apply le_trans'; apply h; simp }
  simp [*]

structure ExtractNonDet (pre : Cont l β) (nx : β -> NonDetT m α) where
  val : β -> m α
  refines : refinesOn pre val nx

def Extract.bind (nx : β -> NonDetT m γ) (nf : β -> γ -> NonDetT m α):
  (ex : ExtractNonDet pre nx) ->
  ExtractNonDet (pre >>= fun b post => wlp (ex.val b) fun g => post (b, g)) (fun bg => nf bg.1 bg.2) ->
  ExtractNonDet pre (fun b => nx b >>= nf b) := by
    rintro ⟨val, ref⟩ ⟨valf, reff⟩; simp [refinesOn] at ref reff
    simp [Bind.bind] at reff
    exists (fun b => val b >>= fun g => valf (b, g))
    introv prem preand pret; simp; simp [wp_bind]
    apply le_trans; apply ref <;> try solve_by_elim
    conv => enter [1,1]; ext; rw [<-wp_top_wlp]
    conv => enter [2,1]; ext; rw [<-wp_top_wlp]
    simp [preand]; refine inf_le_of_right_le ?_
    apply reff (post := fun bg a => post bg.1 a)
    { introv fm; solve_by_elim [wlp_cons] }
    { intro; simp [wlp_and, preand] }
    solve_by_elim


def Extract.lift_bind (x : β -> m γ) (nf : β -> γ -> NonDetT m α):
  ExtractNonDet (pre >>= fun b post => wlp (x b) fun g => post (b, g)) (fun bg => nf bg.1 bg.2) ->
  ExtractNonDet pre (fun b => liftM (x b) >>= nf b) := by
    intro h; apply Extract.bind; rotate_left
    { exists x; introv _ _ _; simp [NonDetT.wp_lift] }
    solve_by_elim

#check Lean.Order.fix

def Extract.pickSuchThat_bind (pre : Cont l β) (τ : Type u) (p : β -> τ -> Prop) (nf : β -> τ -> NonDetT m α)
   (x : β -> τ) :
  ⊤ <= pre (fun b => ⌜ p b (x b) ⌝) ->
  -- Extract (pre >>= fun b post => wlp (x b) fun g => post (b, g)) (fun bg => nf bg.1 bg.2) ->
  ExtractNonDet pre (fun b => nf b (x b)) ->
  ExtractNonDet pre (fun b => pickSuchThat (m := NonDetT m) τ (p b) >>= nf b) := by
    rintro h ⟨val, ref⟩;
    apply Extract.bind; rotate_left
    { exists (fun b => pure (x b))
      simp [refinesOn, MonadNonDet.wp_pickSuchThat, wp_pure]; introv prem preand _
      rw [@top_le_iff] at h
      rw [<-inf_top_eq (a := pre _), <-h, <-preand]
      apply prem; intro a; refine le_himp_iff.mp ?_
      exact iInf_le_iff.mpr fun b a_1 ↦ a_1 (x a) }
    simp; exists fun x => val x.1; introv prem prea pret; simp
    simp [Bind.bind] at prem prea pret; apply ref
    { intro f f' _; apply (prem (f ·.1) (f' ·.1)); solve_by_elim }
    { intro f f'; apply (prea (f ·.1) (f' ·.1)) }
    solve_by_elim
