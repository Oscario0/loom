import Mathlib.Logic.Function.Basic
import Mathlib.Order.CompleteBooleanAlgebra
import Mathlib.Order.Lattice
import Mathlib.Order.Basic
import Mathlib.Data.W.Basic
import Mathlib.Data.FinEnum

import LoL.MonadAlgebras.WP
import LoL.MonadAlgebras.WLP
import LoL.MonadAlgebras.NonDetDevT.Basic
import Lol.Meta

universe u v w

open Demonic

open Lean.Order

-- instance [Monad m] [inst : ∀ α, Lean.Order.PartialOrder (m α)] : Lean.Order.PartialOrder (ExceptT ε m α) := inst _
instance [Monad m] [inst : ∀ α, Lean.Order.CCPO (m α)] : Lean.Order.CCPO (ExceptT ε m α) := inst _
instance [Monad m] [∀ α, Lean.Order.CCPO (m α)] [MonoBind m] : Lean.Order.MonoBind (ExceptT ε m) where
  bind_mono_left h₁₂ := by
    apply MonoBind.bind_mono_left (m := m)
    exact h₁₂
  bind_mono_right h₁₂ := by
    apply MonoBind.bind_mono_right (m := m)
    intro x
    cases x
    · apply PartialOrder.rel_refl
    · apply h₁₂

instance [Monad m] [inst : ∀ α, Lean.Order.CCPO (m α)] : Lean.Order.CCPO (StateT ε m α) := by
  unfold StateT
  infer_instance
instance [Monad m] [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] : Lean.Order.MonoBind (StateT ε m) where
  bind_mono_left h₁₂ := by
    intro; simp [bind, StateT.bind]
    apply MonoBind.bind_mono_left (m := m)
    apply h₁₂
  bind_mono_right h₁₂ := by
    intro; simp [bind, StateT.bind]
    apply MonoBind.bind_mono_right (m := m)
    intro x
    apply h₁₂

instance [Monad m] [inst : ∀ α, Lean.Order.CCPO (m α)] : Lean.Order.CCPO (ReaderT ε m α) := by
  unfold ReaderT
  infer_instance
instance [Monad m] [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] : Lean.Order.MonoBind (ReaderT ε m) where
  bind_mono_left h₁₂ := by
    intro; simp [bind, ReaderT.bind]
    apply MonoBind.bind_mono_left (m := m)
    apply h₁₂
  bind_mono_right h₁₂ := by
    intro; simp [bind, ReaderT.bind]
    apply MonoBind.bind_mono_right (m := m)
    intro x
    apply h₁₂



@[specialize, inline]
def Loop.forIn.loop {m : Type u -> Type v} [Monad m] [∀ α, CCPO (m α)] [MonoBind m]  (f : Unit → β → m (ForInStep β)) (b : β) : m β := do
    match ← f () b with
      | ForInStep.done b  => pure b
      | ForInStep.yield b => loop f b
  partial_fixpoint

@[inline]
def Loop.forIn {m : Type u -> Type v} [Monad m] [∀ α, CCPO (m α)] [MonoBind m] {β : Type u}
  (_ : Lean.Loop) (init : β) (f : Unit → β → m (ForInStep β)) : m β :=
  Loop.forIn.loop f init

@[instance high]
instance [md : Monad m] [ccpo : ∀ α, CCPO (m α)] [mono : MonoBind m] : ForIn m Lean.Loop Unit where
  forIn l := @Loop.forIn m md ccpo mono _ l

variable {m : Type u -> Type v} {α β : Type u} [Monad m] [∀ α, CCPO (m α)] [MonoBind m]
variable {l} [CompleteBooleanAlgebra l] [MPropOrdered m l] [LawfulMonad m] [MPropDetertministic m l]

class LawfulCCPO (m : Type u -> Type v) [Monad m] [∀ α, CCPO (m α)] [MonoBind m]
  [MPropOrdered m l] where
  -- ord_agree (x y : m l) : y ⊑ x -> MPropOrdered.μ x <= MPropOrdered.μ y
  wp_csup {α : Type u} (xc : m α -> Prop) (post : α -> l) :
    chain xc ->
    ⨅ x : { x // xc x } , wp x.val post <= wp (CCPO.csup xc) post


-- lemma csup_uniq [CCPO α] (xc : α -> Prop) (xcc : chain xc) xcsup :
--   (∀ x, xcsup ⊑ x <-> (∀ y, xc y -> y ⊑ x)) -> xcsup = CCPO.csup xc := by
--     intro hcsup
--     apply PartialOrder.rel_antisymm
--     { simp [hcsup]; solve_by_elim [le_csup] }
--     apply csup_le xcc; simp [<-hcsup]; exact PartialOrder.rel_of_eq rfl

-- omit [LawfulMonad m] [MPropDetertministic m l] in
-- lemma LawfulCCPO.csup_bind [LawfulCCPO m] (xc : Set (m α)) (f : α -> m l) :
--   chain xc ->
--     MPropOrdered.μ (CCPO.csup xc >>= f) = MPropOrdered.μ (CCPO.csup ((bind · f) '' xc)) := by
--     intro h
--     apply le_antisymm
--     {
--       apply LawfulCCPO.ord_agree; apply csup_le
--       { intro x y;
--         simp [<-Set.mem_def (s := ((fun x ↦ x >>= f) '' xc))]
--         rintro x xin rfl y yin rfl
--         cases (h x y xin yin)
--         { left; solve_by_elim [MonoBind.bind_mono_left] }
--         right; solve_by_elim [MonoBind.bind_mono_left] }
--       intro yl; simp [<-Set.mem_def (s := ((fun x ↦ x >>= f) '' xc))]
--       rintro x xin rfl; solve_by_elim [MonoBind.bind_mono_left, le_csup] }
--     {  }


-- omit [LawfulMonad m] [MPropDetertministic m l] in
-- lemma LawfulCCPO.csup_bind' [LawfulCCPO m] (xc : Set (m α)) (f : α -> m l) :
--   chain xc ->
--     CCPO.csup xc >>= f = CCPO.csup ((bind · f) '' xc) := by
--   intro cl
--   apply csup_uniq
--   { intro x y; simp [<-Set.mem_def (s := ((fun x ↦ x >>= f) '' xc))]
--     rintro x xin rfl y yin rfl
--     cases (cl x y xin yin)
--     { left; solve_by_elim [MonoBind.bind_mono_left] }
--     right; solve_by_elim [MonoBind.bind_mono_left] }
--   intro x; simp [<-Set.mem_def (s := ((fun x ↦ x >>= f) '' xc))]; constructor
--   { intro xle y yin;
--     apply PartialOrder.rel_trans; rotate_left; apply xle
--     solve_by_elim [MonoBind.bind_mono_left, le_csup] }

--   apply csup_le
--   { intro x y;
--     simp [<-Set.mem_def (s := ((fun x ↦ x >>= f) '' xc))]
--     rintro x xin rfl y yin rfl
--     cases (h x y xin yin)
--     { left; solve_by_elim [MonoBind.bind_mono_left] }
--     right; solve_by_elim [MonoBind.bind_mono_left] }
--   intro yl; simp [<-Set.mem_def (s := ((fun x ↦ x >>= f) '' xc))]
--   rintro x xin rfl; solve_by_elim [MonoBind.bind_mono_left, le_csup]

-- omit [MPropDetertministic m l] in
-- lemma LawfulCCPO.wp_csup [LawfulCCPO m] (xc : m α -> Prop) post :
--   chain xc ->
--   ⨅ x : { x // xc x } , wp x.val post <= wp (CCPO.csup xc) post := by
--     intro cl
--     simp [wp, liftM, monadLift, MProp.lift]
--     rewrite [map_eq_pure_bind]
--     apply le_trans'; apply LawfulCCPO.μ_csup
--     refine iInf_mono' ?_
--     simp [<-Set.mem_def (s := ((fun x ↦ post <$> x) '' xc))]
--     aesop

omit [MPropDetertministic m l] in
lemma repeat_inv [LawfulCCPO m] (f : Unit -> β -> m (ForInStep β))
  (inv : ForInStep β -> l)
  init :
   (∀ b, triple (inv (.yield b)) (f () b) (inv)) ->
   triple (inv (.yield init)) (Loop.forIn.loop f init) (fun b => inv (.done b)) := by
  intro hstep
  revert init
  apply Loop.forIn.loop.fixpoint_induct (f := f) (motive :=
    fun loop => ∀ init, triple (inv (.yield init)) (loop init) (fun b =>inv (.done b)))
  { apply Lean.Order.admissible_pi_apply
      (P := fun init loop => triple (inv (.yield init)) (loop) (fun b =>inv (.done b)))
    simp [admissible, triple]; intro init loops cl h
    apply le_trans';  apply LawfulCCPO.wp_csup; solve_by_elim
    simp; solve_by_elim }
  intro loop ih init; simp [triple, wp_bind]; apply le_trans; apply hstep
  apply wp_cons; rintro (_|_); simp [wp_pure]
  apply ih

instance : MPropOrdered Option Prop where
  μ := (·.getD True)
  μ_ord_pure := by simp
  μ_ord_bind {α} f g := by
    rintro h (_|x) <;> simp
    solve_by_elim

instance : LawfulCCPO Option where
  wp_csup {α} chain := by
    intro post hchain
    simp [CCPO.csup, flat_csup]
    split_ifs with ch
    { intro h; apply h;
      rcases Classical.choose_spec ch
      solve_by_elim }
    solve_by_elim

instance (hd : ε -> _) [IsHandler hd] [LawfulCCPO m] : LawfulCCPO (ExceptT ε m) where
  wp_csup {α} chain := by
    intro post hchain
    simp [wp_except_handler_eq]
    apply LawfulCCPO.wp_csup (m := m)
    solve_by_elim

omit [(α : Type u) → CCPO (m α)] [MonoBind m] [MPropDetertministic m l] in
lemma wp_statet (x : StateT σ m α) :
  wp x post = fun s => wp (x s) (fun xs => post xs.1 xs.2) := by
    simp [wp, monadLift, liftM, MProp.lift, Functor.map, MPropOrdered.μ, StateT.map]

omit [(α : Type u) → CCPO (m α)] [MonoBind m] [MPropDetertministic m l] in
lemma wp_readert (x : ReaderT σ m α) :
  wp x post = fun s => wp (x s) (post · s) := by
    simp [wp, monadLift, liftM, MProp.lift, Functor.map, MPropOrdered.μ]


instance [LawfulCCPO m] : LawfulCCPO (StateT σ m) where
  wp_csup {α} chain := by
    intro post hchain
    simp [instCCPOStateTOfMonad_loL, CCPO.csup, wp_statet]
    rw [@Pi.le_def]; simp; unfold fun_csup; intro s
    apply le_trans'
    apply LawfulCCPO.wp_csup (m := m)
    { simp [Lean.Order.chain]; rintro x y f cf rfl g cg rfl
      cases (hchain f g cf cg)
      { left; solve_by_elim }
      right; solve_by_elim }
    refine iInf_mono' ?_; aesop

instance [LawfulCCPO m] : LawfulCCPO (ReaderT σ m) where
  wp_csup {α} chain := by
    intro post hchain
    simp [instCCPOReaderTOfMonad_loL, CCPO.csup, wp_readert]
    rw [@Pi.le_def]; simp; unfold fun_csup; intro s
    apply le_trans'
    apply LawfulCCPO.wp_csup (m := m)
    { simp [Lean.Order.chain]; rintro x y f cf rfl g cg rfl
      cases (hchain f g cf cg)
      { left; solve_by_elim }
      right; solve_by_elim }
    refine iInf_mono' ?_; aesop


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

lemma findNat_aux_some_le (p : Nat -> Prop) [DecidablePred p] (i : Nat) :
  findNat.aux p i = some j -> ∀ k, i <= k -> k < j -> ¬ p k := by
  apply findNat.aux.partial_correctness
  intro aux ih i r; split
  { rintro ⟨⟩ ph; omega }
  intro h; have:= ih _ _ h;
  intros k _ _ pk; apply this k <;> try omega
  by_cases h : k = i; aesop; omega


lemma findNat_some_p (p : Nat -> Prop) [DecidablePred p] (i : Nat) :
  findNat p = some i -> p i := by
  simp [findNat]; generalize 0 = m;
  apply findNat.aux.partial_correctness; aesop


lemma p_findNat_some (p : Nat -> Prop) [DecidablePred p] (i : Nat) :
  p i -> ∃ j, p j ∧ j <= i ∧ findNat p = some j := by
  intro pi;
  have : (findNat p).isSome := by
    false_or_by_contra; rename_i h
    simp [<-Option.isNone_iff_eq_none] at h
    have h := findNat_none _ h
    aesop
  revert this; simp [Option.isSome_iff_exists]
  intro x h
  have := findNat_aux_some_le p 0 h
  exists x; repeat' constructor
  { solve_by_elim [findNat_some_p] }
  { have h := fun h₁ h₂ => this _ h₁ h₂ pi
    simp at h; exact h }
  solve_by_elim

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

class Findable {α : Type u} (p : α -> Prop) where
  find : Option α
  find_none : find.isNone -> ∀ x, ¬ p x
  find_some_p : find = some x -> p x

instance {p : α -> Prop} [Encodable α] [DecidablePred p] : Findable p where
  find := find p
  find_none := find_none p
  find_some_p := find_some_p p _

@[instance high]
instance {p : α -> Prop} [FinEnum α] [DecidablePred p] : Findable p where
  find := FinEnum.toList α |>.find? p
  find_none := by simp [List.find?, Fintype.complete]
  find_some_p := by intro x h; have := List.find?_some h; aesop

inductive ExtractNonDet {m} : {α : Type u} -> NonDetDevT m α -> Type _ where
  | pure {α} : ∀ (x : α), ExtractNonDet (NonDetDevT.pure x)
  | vis {α} {β} (x : m β) (f : β → NonDetDevT m α) :
      (∀ y, ExtractNonDet (f y)) → ExtractNonDet (.vis x f)
  | pickSuchThat {α} (τ : Type u) (p : τ -> Prop) (f : τ → NonDetDevT m α)
    {_ : Findable p}
     : (∀ x, ExtractNonDet (f x)) → ExtractNonDet (.pickCont τ p f)
  | assume {α} (p : PUnit -> Prop) (f : PUnit → NonDetDevT m α) :
    (∀ x, ExtractNonDet (f x)) → ExtractNonDet (.pickCont PUnit p f)
  | repeatCont {α} {β} init (f : β -> NonDetDevT m (ForInStep β)) (cont : β -> NonDetDevT m α) :
     (∀ x, ExtractNonDet (f x)) →
     (∀ x, ExtractNonDet (cont x)) →
     ExtractNonDet (.repeatCont init f cont)

def NonDetDevT.extract [∀ α, CCPO (m α)] [MonoBind m]
  : {α : Type u} -> (s : NonDetDevT m α) -> (ex : ExtractNonDet s := by solve_by_elim) -> ExceptT PUnit m α
  | _, .pure x, _ => Pure.pure x
  | _, .vis x f, .vis _ _ _ => liftM x >>= (fun x => extract (f x))
  | _, .pickCont _ p f, .pickSuchThat _ _ _ _ =>
    match Findable.find p with
    | none => throw .unit
    | some x =>  extract (f x)
  | _, .pickCont _ _ f, .assume _ _ _ => extract (f .unit)
  | _, .repeatCont init f cont, .repeatCont _ _ _ _ _ =>
    forIn Lean.Loop.mk init (fun _ x => extract (f x)) >>= (fun x => extract (cont x))

noncomputable
abbrev NonDetDevT.prop : {α : Type u} -> (s : NonDetDevT m α) -> Cont l α
  | _, .pure x => Pure.pure x
  | _, .vis x f => fun post => wlp x fun y => NonDetDevT.prop (f y) post
  | _, .pickCont _ p f => fun post =>
    (⨅ t, ⌜p t⌝ ⇨ NonDetDevT.prop (f t) post) ⊓ (⨆ t, ⌜p t⌝)
  | _, .repeatCont _ f cont =>
    fun post => ⌜ ∀ b, ⊤ <= (f b).prop ⊤ ∧ ⊤ <= (cont b).prop post ⌝

open TotalCorrectness

@[local simp]
lemma pure_intro_l (x : l) :
  (x ⊓ ⌜ p ⌝ <= y) = (p -> x <= y) := by
  by_cases h : p <;> simp [h]

@[local simp]
lemma pure_intro_r (x : l) :
  (⌜ p ⌝ ⊓ x <= y) = (p -> x <= y) := by
  by_cases h : p <;> simp [h]

attribute [simp] LE.pure_intro


lemma NonDetDevT.extract_refines_wp [LawfulCCPO m] (s : NonDetDevT m α) (inst : ExtractNonDet s) :
  wp s post ⊓ s.prop ⊤ <= wp s.extract post := by
  unhygienic induction inst
  { simp [wp_pure, NonDetDevT.extract] }
  { simp [NonDetDevT.wp_vis, NonDetDevT.prop]; rw [inf_comm, wlp_join_wp]
    simp [NonDetDevT.extract, wp_bind, ExceptT.wp_lift]
    apply wp_cons; aesop (add norm inf_comm) }
  { simp [NonDetDevT.wp_pickCont, NonDetDevT.prop, NonDetDevT.extract]; split
    { have := Findable.find_none (p := p) (by simpa);
      have : (∀ x, p x = False) := by simpa
      simp [this] }
    rw [<-inf_assoc]; refine inf_le_of_left_le ?_
    rw [← @iInf_inf_eq]; simp [meet_himp _ _ _ _ rfl]
    rename_i y _
    refine iInf_le_of_le y ?_
    have := Findable.find_some_p (p := p) (by assumption)
    simp [this]; simp_all only }
  { simp [NonDetDevT.wp_pickCont, NonDetDevT.prop, NonDetDevT.extract]
    have: ∀ a : PUnit.{u + 1}, a = .unit := by aesop
    simp [this, iInf_const, iSup_const]; apply le_trans'; apply a_ih
    simp; constructor
    { rw [<-inf_assoc, <-le_himp_iff]; exact inf_le_left }
    refine inf_le_of_right_le ?_; exact inf_le_left }
  rw [NonDetDevT.wp_repeatCont, NonDetDevT.extract, wp_bind, NonDetDevT.prop]
  simp; intro hprop inv hinv; apply le_trans'; apply wp_cons; rotate_right
  { apply (triple_spec ..).mpr; apply repeat_inv
    intro b; apply le_trans'; apply a_ih; simp [hprop]
    simp [NonDetDevT.wp_eq_wp, hinv] }
  intro b; apply le_trans'; apply a_ih_1; simp [hprop]
  simp [NonDetDevT.wp_eq_wp]

lemma NonDetDevT.extract_refines [LawfulCCPO m] (pre : l) (s : NonDetDevT m α) (inst : ExtractNonDet s) :
  triple pre s post ->
  pre <= s.prop ⊤ ->
  triple pre s.extract post := by
  intro tr imp; apply le_trans'; apply NonDetDevT.extract_refines_wp
  simp; aesop

def ExtractNonDet.bind : (ExtractNonDet x) -> (∀ y, ExtractNonDet (f y)) -> ExtractNonDet (x >>= f)
  | .pure x, inst => by
    dsimp [Bind.bind, NonDetDevT.bind]; exact (inst x)
  | .vis x f inst, inst' => by
    dsimp [Bind.bind, NonDetDevT.bind]; constructor
    intro y; apply ExtractNonDet.bind <;> solve_by_elim
  | .pickSuchThat _ p f inst, inst' => by
    dsimp [Bind.bind, NonDetDevT.bind]; constructor
    assumption; intro y; apply ExtractNonDet.bind <;> solve_by_elim
  | .assume _ f inst, inst' => by
    dsimp [Bind.bind, NonDetDevT.bind]; apply ExtractNonDet.assume
    intro y; apply ExtractNonDet.bind <;> solve_by_elim
  | .repeatCont init f cont inst₁ inst₂, inst' => by
    dsimp [Bind.bind, NonDetDevT.bind]; constructor; assumption
    intro y; apply ExtractNonDet.bind <;> solve_by_elim

def ExtractNonDet.pure' : ExtractNonDet (Pure.pure (f := NonDetDevT m) x) := by
  dsimp [Pure.pure, NonDetDevT.pure]; constructor

def ExtractNonDet.liftM (x : m α) :
  ExtractNonDet (liftM (n := NonDetDevT m) x) := by
    dsimp [_root_.liftM, monadLift, MonadLift.monadLift]; constructor
    intro y; apply ExtractNonDet.pure'

def ExtractNonDet.assume' {p : Prop} : ExtractNonDet (MonadNonDetDev.assume (m :=  NonDetDevT m) p) := by
  dsimp [MonadNonDetDev.assume, NonDetDevT.assume]; apply ExtractNonDet.assume
  intro y; apply ExtractNonDet.pure

def ExtractNonDet.pickSuchThat' {τ : Type u} (p : τ -> Prop) [Findable p] :
  ExtractNonDet (MonadNonDetDev.pickSuchThat (m := NonDetDevT m) τ p) := by
    dsimp [MonadNonDetDev.pickSuchThat, NonDetDevT.pickSuchThat]; constructor
    assumption; intro y; apply ExtractNonDet.pure

def ExtractNonDet.if {p : Prop} {dec : Decidable p} {x y : NonDetDevT m α}
  (_ : ExtractNonDet x) (_ : ExtractNonDet y) :
  ExtractNonDet (if p then x else y) := by
    match dec with
    | .isTrue h => dsimp [ite]; assumption
    | .isFalse h => dsimp [ite]; assumption

def ExtractNonDet.ForIn_list {xs : List α} {init : β} {f : α → β → NonDetDevT m (ForInStep β)}
  (_ : ∀ a b, ExtractNonDet (f a b)) :
  ExtractNonDet (forIn xs init f) := by
    unhygienic induction xs generalizing init
    { dsimp [forIn]; apply ExtractNonDet.pure }
    { simp only [List.forIn_cons]
      apply ExtractNonDet.bind; solve_by_elim
      rintro (_|_)
      { dsimp; apply ExtractNonDet.pure }
      dsimp; apply tail_ih }


def ExtractNonDet.forIn {β : Type u} (init : β) (f : Unit -> β -> NonDetDevT m (ForInStep β)) :
  (∀ b, ExtractNonDet (f () b)) ->
  ExtractNonDet (forIn Lean.Loop.mk init f) := by
    intro ex
    apply (ExtractNonDet.repeatCont _ _ _ ex)
    intro; (expose_names; exact pure x)


macro "extract_step" : tactic =>
  `(tactic|
    first
      | eapply ExtractNonDet.forIn
      | eapply ExtractNonDet.ForIn_list
      | eapply ExtractNonDet.bind
      | eapply ExtractNonDet.pure'
      | eapply ExtractNonDet.liftM
      | eapply ExtractNonDet.assume'
      | eapply ExtractNonDet.pickSuchThat'
      | eapply ExtractNonDet.if)

macro "extract_tactic" : tactic =>
  `(tactic| repeat' (intros; extract_step; try dsimp))

structure Extractable (x : NonDetDevT m α) where
  cond : Cont l α
  prop : ∀ post, cond post <= x.prop post

omit [LawfulMonad m] [MPropDetertministic m l] [(α : Type u) → CCPO (m α)] [MonoBind m] in
lemma NonDetDevT.prop_bind (x : NonDetDevT m α) (f : α -> NonDetDevT m β) :
  (x >>= f).prop = fun post => x.prop (fun a => (f a).prop post) := by
  unhygienic induction x
  { rfl }
  { simp [Bind.bind, NonDetDevT.bind, NonDetDevT.prop];
    ext post; congr!; erw [f_ih] }
  { simp [Bind.bind, NonDetDevT.bind, NonDetDevT.prop];
    ext post; congr!; erw [f_ih] }
  { simp [Bind.bind, NonDetDevT.bind, NonDetDevT.prop];
    ext post; congr!; erw [cont_ih] }

omit [MPropDetertministic m l] [(α : Type u) → CCPO (m α)] [MonoBind m] in
lemma NonDetDevT.prop_mono (x : NonDetDevT m α) post post' :
  post <= post' -> x.prop post <= x.prop post' := by
  intro postLe; unhygienic induction x <;> simp only [NonDetDevT.prop]
  { solve_by_elim }
  { solve_by_elim [wlp_cons] }
  { apply inf_le_inf_right; apply iInf_mono; intro
    aesop }
  apply LE.pure_imp; intro h b; specialize h b
  revert h; simp only [and_imp]; intro h₁ h₂; simp only [h₁, true_and]
  solve_by_elim [le_trans]


def Extractable.bind (x : NonDetDevT m α) (f : α -> NonDetDevT m β)
  (ex : Extractable x) (exf : ∀ a, Extractable (f a)) :
  Extractable (x >>= f) := by
    exists fun post => ex.cond (fun a => (exf a).cond post)
    intro post; rw [NonDetDevT.prop_bind]
    simp [Bind.bind, NonDetDevT.bind, NonDetDevT.prop]
    apply le_trans'; apply NonDetDevT.prop_mono
    { intro a; apply (exf a).prop }
    apply ex.prop

def Extractable.pure (x : α) : Extractable (pure (f := NonDetDevT m) x) := by
  exists fun post => post x
  intro post; simp [NonDetDevT.prop, Pure.pure]

def Extractable.liftM (x : m α) : Extractable (liftM (n := NonDetDevT m) x) := by
  exists wlp x
  intro post; simp [_root_.liftM, NonDetDevT.prop]; apply wlp_cons; rfl

noncomputable
def Extractable.assume (p : Prop) :
  Extractable (MonadNonDetDev.assume (m := NonDetDevT m) p) := by
  exists fun post => ⌜ p ⌝ ⊓ post .unit
  intro post; simp [NonDetDevT.prop, MonadNonDetDev.assume, NonDetDevT.assume, Pure.pure, iSup_const]

noncomputable
def Extractable.pickSuchThat (τ : Type u) (p : τ -> Prop) [Encodable τ] [DecidablePred p] :
  Extractable (MonadNonDetDev.pickSuchThat (m := NonDetDevT m) τ p) := by
    exists fun post => (⨅ t, ⌜ p t ⌝ ⇨ post t) ⊓ (⨆ t, ⌜ p t ⌝)
    intro post; simp [NonDetDevT.prop, MonadNonDetDev.pickSuchThat, NonDetDevT.pickSuchThat, Pure.pure, iInf_const]

noncomputable
def Extractable.forIn (xs : List α) (init : β) (f : α -> β -> NonDetDevT m (ForInStep β))
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
    { simp [Pure.pure, NonDetDevT.prop, h] }
    simp only [List.forIn_cons, NonDetDevT.prop_bind]
    apply le_trans'; apply (ex _ _).prop
    rw [<-h.right]; apply le_of_eq; congr
    ext (_|_)
    { simp [Pure.pure, NonDetDevT.prop, h] }
    simp_all

noncomputable
def Extractable.forIn_range (m : Type -> Type v) (l : Type) {β : Type} [CompleteBooleanAlgebra l] [Monad m] [MPropOrdered m l] (xs : Std.Range) (init : β) (f : ℕ -> β -> NonDetDevT m (ForInStep β))
  (ex: ∀ a b, Extractable (f a b)):
  Extractable (ForIn.forIn xs init f) := by
    unfold instForInOfForIn'; simp; solve_by_elim [forIn]

noncomputable
def Extractable.forIn'   (f : Unit -> β -> NonDetDevT m (ForInStep β))
  (ex : ∀ a, Extractable (f () a)) :
  Extractable (ForIn.forIn Lean.Loop.mk init f) := by
    exists fun post => ⌜⊤ <= post ∧ ∀ a, ⊤ <= (ex a).cond ⊤⌝
    simp [ForIn.forIn, NonDetDevT.prop, rep, NonDetDevT.repeat, Pure.pure]
    intro posth
    have h : ∀ (b : β), (f () b).prop ⊤ = ⊤ := by {
      intro b; refine eq_top_iff.mpr ?_
      apply le_trans'; apply (ex b).prop; simp
      simp [posth] }
    simp [h]

noncomputable
def Extractable.if_some {τ} {p : τ -> Prop}
  [Encodable τ]
  [DecidablePred p]
  {dec : Decidable $ ∃ x, p x} {x : τ -> NonDetDevT m α} {y : NonDetDevT m α}
  (_ : ∀ t, Extractable (x t)) (_ : Extractable y) :
  Extractable (if ∃ x, p x then MonadNonDetDev.pickSuchThat τ p >>= x else y) := by
    split_ifs with h
    { apply Extractable.bind;
      { exists fun post => (⨅ t, ⌜ p t ⌝ ⇨ post t)
        intro post; simp [MonadNonDetDev.pickSuchThat, NonDetDevT.prop, NonDetDevT.pickSuchThat, Pure.pure]
        rcases h with ⟨t, h⟩
        refine le_iSup_of_le t ?_; simp [h] }
      apply_assumption }
    apply_assumption


omit [LawfulMonad m] [MPropDetertministic m l] [(α : Type u) → CCPO (m α)] [MonoBind m]in
lemma Extractable.intro (x : NonDetDevT m α) (ex : Extractable x) :
  pre <= ex.cond post ->
  pre <= x.prop post := by
    solve_by_elim [ex.prop, le_trans']

macro "extractable_step" : tactic =>
  `(tactic|
    first
      | eapply Extractable.if_some
      | eapply Extractable.forIn
      | eapply Extractable.bind
      | eapply Extractable.pure
      | eapply Extractable.liftM
      | eapply Extractable.assume
      | eapply Extractable.pickSuchThat)

macro "extractable_tactic" : tactic =>
  `(tactic| repeat' (intros; extractable_step; try dsimp))


def NonDetDevT.run [∀ α, CCPO (m α)] [MonoBind m] [LawfulCCPO m]
  (x : NonDetDevT m α) (ex : ExtractNonDet x := by extract_tactic) : ExceptT PUnit m α :=
  x.extract
