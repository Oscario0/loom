import Mathlib.Logic.Function.Basic
import Mathlib.Order.CompleteBooleanAlgebra
import Mathlib.Order.Lattice
import Mathlib.Order.Basic
import Mathlib.Data.W.Basic
import Mathlib.Data.FinEnum

import Loom.MonadAlgebras.WP.Gen
import Loom.MonadAlgebras.WP.Liberal
import Loom.MonadAlgebras.NonDetT.Basic
import Loom.MonadAlgebras.NonDetT.Findable

universe u v w

open Lean.Order

variable [Monad m] [CCPOBot m] [CompleteBooleanAlgebra l] [MAlgOrdered m l] [LawfulMonad m]
variable [∀ α, CCPO (m α)] [MonoBind m]

def NonDetT.run {α : Type u} :  NonDetT m α -> m α
  | .pure x => Pure.pure x
  | .vis x f => liftM x >>= (fun x => (f x).run)
  | @NonDetT.pickCont _ _ _ p _ f =>
    match Findable.find (p := p) () with
    | none => CCPOBot.compBot
    | some x =>  (f x).run
  | .repeatCont init f cont =>
    forIn Lean.Loop.mk init (fun _ x => (f x).run) >>= (fun x => (cont x).run)


namespace PartialCorrectness.DemonicChoice

variable [MAlgPartial m] [CCPOBotLawful m]

lemma ExtractNonDet.extract_refines_wp (s : NonDetT m α) :
  wp s post <= wp s.run post := by
  unhygienic induction s
  { simp [wp_pure, NonDetT.run] }
  { simp [NonDetT.wp_vis, NonDetT.run, wp_bind]
    apply wp_cons; aesop (add norm inf_comm) }
  { simp [NonDetT.wp_pickCont, NonDetT.run]; split
    { have := Findable.find_none (p := p) (by simpa);
      have : (∀ x, p x = False) := by simpa
      simp [this]
      simp [CCPOBotLawful.prop, wp_bot] }
    rename_i y _
    refine iInf_le_of_le y ?_
    have := Findable.find_some_p (p := p) (by assumption)
    simp [this]; apply f_ih }
  rw [NonDetT.wp_repeatCont, NonDetT.run, wp_bind]
  simp; intro inv hinv; apply le_trans'; apply wp_cons; rotate_right
  { apply (triple_spec ..).mpr; apply repeat_inv
    intro b; apply le_trans'; apply f_ih
    simp [NonDetT.wp_eq_wp, hinv] }
  intro b; apply le_trans'; apply cont_ih
  simp [NonDetT.wp_eq_wp]

lemma ExtractNonDet.extract_refines (pre : l) (s : NonDetT m α) :
  triple pre s post ->
  triple pre s.run post := by
  intro tr; apply le_trans'; apply ExtractNonDet.extract_refines_wp
  aesop

end PartialCorrectness.DemonicChoice

namespace TotalCorrectness.DemonicChoice

lemma ExtractNonDet.extract_refines_wp (s : NonDetT m α) :
  wp s post <= wp s.run post := by
  unhygienic induction s
  { simp [wp_pure, NonDetT.run] }
  { simp [NonDetT.wp_vis, NonDetT.run, wp_bind]
    apply wp_cons; aesop (add norm inf_comm) }
  { simp [NonDetT.wp_pickCont, NonDetT.run]; split
    { have := Findable.find_none (p := p) (by simpa);
      have : (∀ x, p x = False) := by simpa
      simp [this] }
    intro _ _
    rename_i y _ _ _
    refine iInf_le_of_le y ?_
    have := Findable.find_some_p (p := p) (by assumption)
    simp [this]; apply f_ih }
  rw [NonDetT.wp_repeatCont, NonDetT.run, wp_bind]
  simp; intro inv wf hinv; apply le_trans'; apply wp_cons; rotate_right
  { apply (triple_spec ..).mpr; apply repeat_inv
    intro b; apply le_trans'; apply f_ih
    simp [NonDetT.wp_eq_wp]
    apply hinv }
  intro b; apply le_trans'; apply cont_ih
  simp [NonDetT.wp_eq_wp]

lemma ExtractNonDet.extract_refines (pre : l) (s : NonDetT m α) :
  triple pre s post ->
  triple pre s.run post := by
  intro tr; apply le_trans'; apply ExtractNonDet.extract_refines_wp
  aesop

end TotalCorrectness.DemonicChoice

-- inductive ExtractNonDet (findable : {τ : Type u} -> (τ -> Prop) -> Type u) {m} : {α : Type u} -> NonDetT m α -> Type _ where
--   | pure {α} : ∀ (x : α), ExtractNonDet findable (NonDetT.pure x)
--   | vis {α} {β} (x : m β) (f : β → NonDetT m α) :
--       (∀ y, ExtractNonDet findable (f y)) → ExtractNonDet findable (.vis x f)
--   | pickSuchThat {α} (τ : Type u) (p : τ -> Prop) (f : τ → NonDetT m α)
--     {_ : findable p}
--      : (∀ x, ExtractNonDet findable (f x)) → ExtractNonDet findable (.pickCont τ p f)
--   | assume {α} (p : PUnit -> Prop) (f : PUnit → NonDetT m α) :
--     (∀ x, ExtractNonDet findable (f x)) → ExtractNonDet findable (.pickCont PUnit p f)
--   | repeatCont {α} {β} init (f : β -> NonDetT m (ForInStep β)) (cont : β -> NonDetT m α) :
--      (∀ x, ExtractNonDet findable (f x)) →
--      (∀ x, ExtractNonDet findable (cont x)) →
--      ExtractNonDet findable (.repeatCont init f cont)

-- set_option linter.unusedVariables false in
-- def ExtractNonDet.bind {findable : {τ : Type u} -> (τ -> Prop) -> Type u} :
--   (_ : ExtractNonDet findable x) -> (_ : ∀ y, ExtractNonDet findable (f y)) -> ExtractNonDet findable (x >>= f)
--   | .pure x, inst => by
--     dsimp [Bind.bind, NonDetT.bind]; exact (inst x)
--   | .vis x f inst, inst' => by
--     dsimp [Bind.bind, NonDetT.bind]; constructor
--     intro y; apply ExtractNonDet.bind <;> solve_by_elim
--   | .pickSuchThat _ p f inst, inst' => by
--     dsimp [Bind.bind, NonDetT.bind]; constructor
--     assumption; intro y; apply ExtractNonDet.bind <;> solve_by_elim
--   | .assume _ f inst, inst' => by
--     dsimp [Bind.bind, NonDetT.bind]; apply ExtractNonDet.assume
--     intro y; apply ExtractNonDet.bind <;> solve_by_elim
--   | .repeatCont init f cont inst₁ inst₂, inst' => by
--     dsimp [Bind.bind, NonDetT.bind]; constructor; assumption
--     intro y; apply ExtractNonDet.bind <;> solve_by_elim

-- instance ExtractNonDet.pure' : ExtractNonDet findable (Pure.pure (f := NonDetT m) x) := by
--   dsimp [Pure.pure, NonDetT.pure]; constructor

-- instance ExtractNonDet.liftM (x : m α) :
--   ExtractNonDet findable (liftM (n := NonDetT m) x) := by
--     dsimp [_root_.liftM, monadLift, MonadLift.monadLift]; constructor
--     intro y; apply ExtractNonDet.pure'

-- instance ExtractNonDet.assume' {p : Prop} : ExtractNonDet findable (MonadNonDet.assume (m :=  NonDetT m) p) := by
--   dsimp [MonadNonDet.assume, NonDetT.assume]; apply ExtractNonDet.assume
--   intro y; apply ExtractNonDet.pure

-- instance ExtractNonDet.pickSuchThat' {τ : Type u} (p : τ -> Prop) [Findable p] :
--   ExtractNonDet Findable (MonadNonDet.pickSuchThat (m := NonDetT m) τ p) := by
--     dsimp [MonadNonDet.pickSuchThat, NonDetT.pickSuchThat]; constructor
--     assumption; intro y; apply ExtractNonDet.pure

-- instance ExtractNonDet.pickSuchThat_weak {τ : Type u} (p : τ -> Prop) [WeakFindable p] :
--   ExtractNonDet WeakFindable (MonadNonDet.pickSuchThat (m := NonDetT m) τ p) := by
--     dsimp [MonadNonDet.pickSuchThat, NonDetT.pickSuchThat]; constructor
--     assumption; intro y; apply ExtractNonDet.pure


-- instance ExtractNonDet.if {p : Prop} {dec : Decidable p} {x y : NonDetT m α}
--   (_ : ExtractNonDet findable x) (_ : ExtractNonDet findable y) :
--   ExtractNonDet findable (if p then x else y) := by
--     match dec with
--     | .isTrue h => dsimp [ite]; assumption
--     | .isFalse h => dsimp [ite]; assumption

-- instance ExtractNonDet.ForIn_list {xs : List α} {init : β} {f : α → β → NonDetT m (ForInStep β)}
--   (_ : ∀ a b, ExtractNonDet findable (f a b)) :
--   ExtractNonDet findable (forIn xs init f) := by
--     unhygienic induction xs generalizing init
--     { dsimp [forIn]; apply ExtractNonDet.pure }
--     { simp only [List.forIn_cons]
--       apply ExtractNonDet.bind; solve_by_elim
--       rintro (_|_)
--       { dsimp; apply ExtractNonDet.pure }
--       dsimp; apply tail_ih }


-- instance ExtractNonDet.forIn {β : Type u} (init : β) (f : Unit -> β -> NonDetT m (ForInStep β)) :
--   (∀ b, ExtractNonDet findable (f () b)) ->
--   ExtractNonDet findable (forIn Lean.Loop.mk init f) := by
--     intro ex
--     apply (ExtractNonDet.repeatCont _ _ _ ex); intro;
--     apply ExtractNonDet.pure

-- variable [Monad m] [∀ α, CCPO (m α)] [MonoBind m] [CCPOBot m] [CompleteBooleanAlgebra l] [MAlgOrdered m l] [MAlgDet m l] [LawfulMonad m]

-- @[simp, inline]
-- def NonDetT.extractGen {findable : {τ : Type u} -> (τ -> Prop) -> Type u}
--   (findOf : ∀ {τ : Type u} (p : τ -> Prop), findable p -> Unit -> Option τ)
--   : {α : Type u} -> (s : NonDetT m α) -> (ex : ExtractNonDet findable s := by solve_by_elim) -> m α
--   | _, .pure x, _ => Pure.pure x
--   | _, .vis x f, .vis _ _ _ => x >>= (fun x => extractGen findOf (f x))
--   | _, .pickCont _ p f, .pickSuchThat _ _ _ _ =>
--     match findOf p ‹_› () with
--     | none => CCPOBot.compBot
--     | some x =>  extractGen findOf (f x)
--   | _, .pickCont _ _ f, .assume _ _ _ => extractGen findOf (f .unit)
--   | _, .repeatCont init f cont, .repeatCont _ _ _ _ _ =>
--     forIn Lean.Loop.mk init (fun _ x => extractGen findOf (f x)) >>= (fun x => extractGen findOf (cont x))

-- @[inline]
-- def NonDetT.extract {α : Type u} (s : NonDetT m α) (ex : ExtractNonDet Findable s := by solve_by_elim) : m α :=
--   NonDetT.extractGen Findable.find s

-- def NonDetT.extractWeak {α : Type u} (s : NonDetT m α) (ex : ExtractNonDet WeakFindable s := by solve_by_elim) : m α :=
--   NonDetT.extractGen WeakFindable.find s

-- macro "extract_step" : tactic =>
--   `(tactic|
--     first
--       | eapply ExtractNonDet.forIn
--       | eapply ExtractNonDet.ForIn_list
--       | eapply ExtractNonDet.bind
--       | eapply ExtractNonDet.pure'
--       | eapply ExtractNonDet.liftM
--       | eapply ExtractNonDet.assume'
--       | eapply ExtractNonDet.pickSuchThat'
--       | eapply ExtractNonDet.pickSuchThat_weak
--       | split)

-- macro "extract_tactic" : tactic =>
--   `(tactic| repeat' (intros; extract_step <;> try dsimp))

-- @[inline]
-- def NonDetT.run {α : Type u} (s : NonDetT m α) (ex : ExtractNonDet Findable s := by extract_tactic) : m α :=
--   NonDetT.extract s ex

-- def NonDetT.runWeak {α : Type u} (s : NonDetT m α) (ex : ExtractNonDet WeakFindable s := by extract_tactic) : m α :=
--   NonDetT.extractWeak s ex

-- noncomputable
-- abbrev NonDetT.prop : {α : Type u} -> (s : NonDetT m α) -> Cont l α
--   | _, .pure x => Pure.pure x
--   | _, .vis x f => fun post => wlp x fun y => NonDetT.prop (f y) post
--   | _, .pickCont _ p f => fun post =>
--     (⨅ t, ⌜p t⌝ ⇨ NonDetT.prop (f t) post) ⊓ (⨆ t, ⌜p t⌝)
--   | _, .repeatCont _ f cont =>
--     fun post => ⌜ ∀ b, ⊤ <= (f b).prop ⊤ ∧ ⊤ <= (cont b).prop post ⌝

-- structure Extractable (x : NonDetT m α) where
--   cond : Cont l α
--   prop : ∀ post, cond post <= x.prop post

-- omit [CCPOBot m] [MonoBind m] [∀ α, CCPO (m α)] [LawfulMonad m] [MAlgDet m l] in
-- lemma NonDetT.prop_bind (x : NonDetT m α) (f : α -> NonDetT m β) :
--   (x >>= f).prop = fun post => x.prop (fun a => (f a).prop post) := by
--   unhygienic induction x
--   { rfl }
--   { simp [Bind.bind, NonDetT.bind, NonDetT.prop];
--     ext post; congr!; erw [f_ih] }
--   { simp [Bind.bind, NonDetT.bind, NonDetT.prop];
--     ext post; congr!; erw [f_ih] }
--   { simp [Bind.bind, NonDetT.bind, NonDetT.prop];
--     ext post; congr!; erw [cont_ih] }

-- omit [CCPOBot m] [MonoBind m] [∀ α, CCPO (m α)] [MAlgDet m l] in
-- lemma NonDetT.prop_mono (x : NonDetT m α) post post' :
--   post <= post' -> x.prop post <= x.prop post' := by
--   intro postLe; unhygienic induction x <;> simp only [NonDetT.prop]
--   { solve_by_elim }
--   { solve_by_elim [wlp_cons] }
--   { apply inf_le_inf_right; apply iInf_mono; intro
--     aesop }
--   apply LE.pure_imp; intro h b; specialize h b
--   revert h; simp only [and_imp]; intro h₁ h₂; simp only [h₁, true_and]
--   solve_by_elim [le_trans]


-- def Extractable.bind (x : NonDetT m α) (f : α -> NonDetT m β)
--   (ex : Extractable x) (exf : ∀ a, Extractable (f a)) :
--   Extractable (x >>= f) := by
--     exists fun post => ex.cond (fun a => (exf a).cond post)
--     intro post; rw [NonDetT.prop_bind]
--     simp
--     apply le_trans'; apply NonDetT.prop_mono
--     { intro a; apply (exf a).prop }
--     apply ex.prop

-- def Extractable.pure (x : α) : Extractable (pure (f := NonDetT m) x) := by
--   exists fun post => post x
--   intro post; simp [NonDetT.prop, Pure.pure]

-- def Extractable.liftM (x : m α) : Extractable (liftM (n := NonDetT m) x) := by
--   exists wlp x
--   intro post; simp [NonDetT.prop]; apply wlp_cons; rfl

-- noncomputable
-- def Extractable.assume (p : Prop) :
--   Extractable (MonadNonDet.assume (m := NonDetT m) p) := by
--   exists fun post => ⌜ p ⌝ ⊓ post .unit
--   intro post; simp [NonDetT.prop, MonadNonDet.assume, NonDetT.assume, Pure.pure, iSup_const]

-- noncomputable
-- def Extractable.pickSuchThat (τ : Type u) (p : τ -> Prop) [Encodable τ] [DecidablePred p] :
--   Extractable (MonadNonDet.pickSuchThat (m := NonDetT m) τ p) := by
--     exists fun post => (⨅ t, ⌜ p t ⌝ ⇨ post t) ⊓ (⨆ t, ⌜ p t ⌝)
--     intro post; simp [NonDetT.prop, MonadNonDet.pickSuchThat, NonDetT.pickSuchThat, Pure.pure]

-- noncomputable
-- def Extractable.forIn (xs : List α) (init : β) (f : α -> β -> NonDetT m (ForInStep β))
--   (ex: ∀ a b, Extractable (f a b)):
--   Extractable (forIn xs init f) := by
--     exists fun post => ⌜⊤ <= post ∧ ∀ a b, ⊤ <= (ex a b).cond ⊤⌝
--     intro post; dsimp
--     by_cases h : (⊤ <= post ∧ ∀ a b, ⊤ <= (ex a b).cond ⊤) = False
--     { rw [h]; simp }
--     have : (⊤ <= post ∧ ∀ a b, ⊤ <= (ex a b).cond ⊤) = True := by aesop
--     simp at h
--     rw [this]; simp only [trueE]
--     induction xs generalizing init
--     { simp [Pure.pure, NonDetT.prop, h] }
--     simp only [List.forIn_cons, NonDetT.prop_bind]
--     apply le_trans'; apply (ex _ _).prop
--     rw [<-h.right]; apply le_of_eq; congr
--     ext (_|_)
--     { simp [Pure.pure, NonDetT.prop, h] }
--     simp_all

-- noncomputable
-- def Extractable.forIn_range (m : Type -> Type v) (l : Type) {β : Type} [CompleteBooleanAlgebra l] [Monad m] [MAlgOrdered m l] (xs : Std.Range) (init : β) (f : ℕ -> β -> NonDetT m (ForInStep β))
--   (ex: ∀ a b, Extractable (f a b)):
--   Extractable (ForIn.forIn xs init f) := by
--     unfold instForInOfForIn'; simp; solve_by_elim [forIn]

-- noncomputable
-- def Extractable.forIn'   (f : Unit -> β -> NonDetT m (ForInStep β))
--   (ex : ∀ a, Extractable (f () a)) :
--   Extractable (ForIn.forIn Lean.Loop.mk init f) := by
--     exists fun post => ⌜⊤ <= post ∧ ∀ a, ⊤ <= (ex a).cond ⊤⌝
--     simp [ForIn.forIn, NonDetT.prop, rep, NonDetT.repeat, Pure.pure]
--     intro posth
--     have h : ∀ (b : β), (f () b).prop ⊤ = ⊤ := by {
--       intro b; refine eq_top_iff.mpr ?_
--       apply le_trans'; apply (ex b).prop; simp
--       simp [posth] }
--     simp [h]

-- noncomputable
-- def Extractable.if_some {τ} {p : τ -> Prop}
--   [Encodable τ]
--   [DecidablePred p]
--   {dec : Decidable $ ∃ x, p x} {x : τ -> NonDetT m α} {y : NonDetT m α}
--   (_ : ∀ t, Extractable (x t)) (_ : Extractable y) :
--   Extractable (if ∃ x, p x then MonadNonDet.pickSuchThat τ p >>= x else y) := by
--     split_ifs with h
--     { apply Extractable.bind
--       { exists fun post => (⨅ t, ⌜ p t ⌝ ⇨ post t)
--         intro post; simp [MonadNonDet.pickSuchThat, NonDetT.prop, NonDetT.pickSuchThat, Pure.pure]
--         rcases h with ⟨t, h⟩
--         refine le_iSup_of_le t ?_; simp [h] }
--       apply_assumption }
--     apply_assumption


-- omit [LawfulMonad m] [MAlgDet m l] [CCPOBot m] [∀ α, CCPO (m α)] in
-- lemma Extractable.intro (x : NonDetT m α) (ex : Extractable x) :
--   pre <= ex.cond post ->
--   pre <= x.prop post := by
--     solve_by_elim [ex.prop, le_trans']

-- macro "extractable_step" : tactic =>
--   `(tactic|
--     first
--       | eapply Extractable.if_some
--       | eapply Extractable.forIn
--       | eapply Extractable.bind
--       | eapply Extractable.pure
--       | eapply Extractable.liftM
--       | eapply Extractable.assume
--       | eapply Extractable.pickSuchThat)

-- macro "extractable_tactic" : tactic =>
--   `(tactic| repeat' (intros; extractable_step; try dsimp))

-- namespace TotalCorrectness.DemonicChoice

-- lemma ExtractNonDet.extract_refines_wp (s : NonDetT m α) (inst : ExtractNonDet Findable s) :
--   wp s post ⊓ s.prop ⊤ <= wp s.extract post := by
--   unhygienic induction inst
--   { simp [wp_pure, NonDetT.extract] }
--   { simp [NonDetT.wp_vis, NonDetT.prop]; rw [inf_comm, wlp_join_wp]
--     simp [NonDetT.extract, wp_bind]
--     apply wp_cons; aesop (add norm inf_comm) }
--   { simp [NonDetT.wp_pickCont, NonDetT.prop, NonDetT.extract]; split
--     { have := Findable.find_none (p := p) (by simpa);
--       have : (∀ x, p x = False) := by simpa
--       simp [this] }
--     rw [<-inf_assoc]; refine inf_le_of_left_le ?_
--     rw [← @iInf_inf_eq]; simp [meet_himp _ _ _ _ rfl]
--     rename_i y _
--     refine iInf_le_of_le y ?_
--     have := Findable.find_some_p (p := p) (by assumption)
--     simp [this]; apply a_ih }
--   { simp [NonDetT.wp_pickCont, NonDetT.prop, NonDetT.extract]
--     have: ∀ a : PUnit.{u_1 + 1}, a = .unit := by aesop
--     simp [this, iInf_const, iSup_const]; apply le_trans'; apply a_ih
--     simp; constructor
--     { rw [<-inf_assoc, <-le_himp_iff]; exact inf_le_left }
--     refine inf_le_of_right_le ?_; exact inf_le_left }
--   rw [NonDetT.wp_repeatCont, NonDetT.extract, NonDetT.extractGen, wp_bind, NonDetT.prop]
--   simp; intro hprop inv wf hinv; apply le_trans'; apply wp_cons; rotate_right
--   { apply (triple_spec ..).mpr; apply repeat_inv
--     intro b; apply le_trans'; apply a_ih; simp [hprop]
--     simp [NonDetT.wp_eq_wp]
--     apply hinv }
--   intro b; apply le_trans'; apply a_ih_1; simp [hprop]
--   simp [NonDetT.wp_eq_wp]

-- lemma ExtractNonDet.extract_refines (pre : l) (s : NonDetT m α) (inst : ExtractNonDet Findable s) :
--   triple pre s post ->
--   pre <= s.prop ⊤ ->
--   triple pre s.extract post := by
--   intro tr imp; apply le_trans'; apply ExtractNonDet.extract_refines_wp
--   simp; aesop

-- end TotalCorrectness.DemonicChoice

-- namespace PartialCorrectness.DemonicChoice

-- variable [CCPOBotLawful m] [MAlgPartial m]

-- lemma ExtractNonDet.extract_refines_wp (s : NonDetT m α) (inst : ExtractNonDet WeakFindable s) :
--   wp s post ⊓ s.prop ⊤ <= wp s.extractWeak post := by
--   unhygienic induction inst
--   { simp [wp_pure, NonDetT.extractWeak] }
--   { simp [NonDetT.wp_vis, NonDetT.prop]; rw [inf_comm, wlp_join_wp]
--     simp [NonDetT.extractWeak, wp_bind]
--     apply wp_cons; aesop (add norm inf_comm) }
--   { simp [NonDetT.wp_pickCont, NonDetT.prop, NonDetT.extractWeak]; split
--     simp [CCPOBotLawful.prop, wp_bot]
--     rw [<-inf_assoc]; refine inf_le_of_left_le ?_
--     rw [← @iInf_inf_eq]; simp [meet_himp _ _ _ _ rfl]
--     rename_i y _
--     refine iInf_le_of_le y ?_
--     have := WeakFindable.find_some_p (p := p) (by assumption)
--     simp [this]; apply a_ih }
--   { simp [NonDetT.wp_pickCont, NonDetT.prop, NonDetT.extractWeak]
--     have: ∀ a : PUnit.{u_1 + 1}, a = .unit := by aesop
--     simp [this, iInf_const, iSup_const]; apply le_trans'; apply a_ih
--     simp; constructor
--     { rw [<-inf_assoc, <-le_himp_iff]; exact inf_le_left }
--     refine inf_le_of_right_le ?_; exact inf_le_left }
--   rw [NonDetT.wp_repeatCont, NonDetT.extractWeak, NonDetT.extractGen, wp_bind, NonDetT.prop]
--   simp; intro hprop inv hinv; apply le_trans'; apply wp_cons; rotate_right
--   { apply (triple_spec ..).mpr; apply repeat_inv
--     intro b; apply le_trans'; apply a_ih; simp [hprop]
--     simp [NonDetT.wp_eq_wp, hinv] }
--   intro b; apply le_trans'; apply a_ih_1; simp [hprop]
--   simp [NonDetT.wp_eq_wp]

-- /- Theorem 6.1 for PartialCorrectness: triple on NonDetT monad implies triple on extracted monad -/
-- set_option linter.unusedSectionVars false in
-- lemma ExtractNonDet.extract_refines (pre : l) (s : NonDetT m α) (inst : ExtractNonDet WeakFindable s) :
--   triple pre s post ->
--   pre <= s.prop ⊤ ->
--   triple pre s.extractWeak post := by
--   intro tr imp; apply le_trans'; apply ExtractNonDet.extract_refines_wp
--   simp; aesop

-- noncomputable
-- def _root_.ExtractNonDet.prop {α : Type u} (s : NonDetT m α) :  ExtractNonDet WeakFindable s -> l
--   | .pure x => ⊤
--   | .vis x f ex => wlp x fun y => (ex y).prop
--   | .pickSuchThat _ p f ex => (⨅ t, ⌜p t⌝ ⇨ (ex t).prop)
--   | .assume p _ ex => ⌜p .unit⌝ ⊓ (ex .unit).prop
--   | .repeatCont _ f cont ex ex' => ⌜ ∀ b, ⊤ <= (ex b).prop ∧ ⊤ <= (ex' b).prop⌝

-- set_option linter.unusedSectionVars false in
-- lemma ExtractNonDet.extract_refines_wp_weak (s : NonDetT m α) (inst : ExtractNonDet WeakFindable s) :
--   wp s post ⊓ inst.prop <= wp s.extractWeak post := by
--   unhygienic induction inst
--   { simp [wp_pure, NonDetT.extractWeak] }
--   { simp [NonDetT.wp_vis, ExtractNonDet.prop]; rw [inf_comm, wlp_join_wp]
--     simp [NonDetT.extractWeak, wp_bind]
--     apply wp_cons; aesop (add norm inf_comm) }
--   { simp [NonDetT.wp_pickCont, ExtractNonDet.prop, NonDetT.extractWeak]; split
--     simp [CCPOBotLawful.prop, wp_bot]
--     rw [← @iInf_inf_eq]; simp [meet_himp _ _ _ _ rfl]
--     rename_i y _
--     refine iInf_le_of_le y ?_
--     have := WeakFindable.find_some_p (p := p) (by assumption)
--     simp [this]; apply a_ih }
--   { simp [NonDetT.wp_pickCont, ExtractNonDet.prop, NonDetT.extractWeak]
--     have: ∀ a : PUnit.{u_1 + 1}, a = .unit := by aesop
--     simp [this, iInf_const]; apply le_trans'; apply a_ih
--     simp; constructor
--     { rw [<-inf_assoc]; apply inf_le_of_left_le; rw [<-le_himp_iff] }
--     rw [<-inf_assoc]; exact inf_le_right }
--   rw [NonDetT.wp_repeatCont, NonDetT.extractWeak, NonDetT.extractGen, wp_bind, ExtractNonDet.prop]
--   simp; intro hprop inv hinv; apply le_trans'; apply wp_cons; rotate_right
--   { apply (triple_spec ..).mpr; apply repeat_inv
--     intro b; apply le_trans'; apply a_ih; simp [hprop]
--     simp [NonDetT.wp_eq_wp, hinv] }
--   intro b; apply le_trans'; apply a_ih_1; simp [hprop]
--   simp [NonDetT.wp_eq_wp]

-- /- Theorem 6.1 for PartialCorrectness: triple on NonDetT monad implies triple on extracted monad -/
-- set_option linter.unusedSectionVars false in
-- lemma ExtractNonDet.extract_refines_triple_weak (pre : l) (s : NonDetT m α) (inst : ExtractNonDet WeakFindable s) :
--   triple pre s post ->
--   pre <= inst.prop ->
--   triple pre s.extractWeak post := by
--   intro tr imp; apply le_trans'; apply ExtractNonDet.extract_refines_wp_weak
--   simp; aesop


-- end PartialCorrectness.DemonicChoice
