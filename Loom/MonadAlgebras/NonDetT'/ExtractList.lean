import Loom.MonadAlgebras.NonDetT'.ExtractListBasic

/-
Let's infer what to do from the first principle.
For now just assume the result type is `mr α`.

In `pickCont`, by using a list, we will have
- `List τ`
- recursion and map, we have `List mr α`

Then one natural thing to do is some `flatMap`-like operation
to get `mr α`.

... So, there is nothing directly related to `ListT` here
-/

/-
But it is also good to keep track of the choices made,
so we can use `mr (α × List κ)`. To add the choice, we
need to "operate" inside the monad, so we need `mr` to be a monad.
- Wait, if the trace is at the position with `α`, then it is possible
  to get lost (e.g., when `α` does not appear in the result).

  So maybe `κ` should be outside the `α`? Parameterized by `mr`?

OK, this should be considered as a failed attempt.

-/

theorem iSup_list_map {l : Type w} [CompleteLattice l] {α : Type u} {β : Type v} (post : β → l) (f : α → β) (xs : List α) :
  ⨆ y ∈ xs.map f, post y = ⨆ x ∈ xs, post (f x) := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.mem_cons, iSup_or, iSup_sup_eq, ih]
    simp

section initial_idea

-- this shows
-- (1) the key might be the flatmap-like operation
-- (2) this operation might be done in a modular fashion

-- going not fancy
-- class MonadRepFun (m m' : Type u → Type v) (s : Type w) where
--   eq : ∀ {α}, m α ≃ (s → m' α)

-- def MonadRepFun.flatMap [inst : MonadRepFun m m' s] (l : List (m (List α))) : m (List α) := by
--   let a := l.map inst.eq.toFun
--   apply inst.eq.invFun
--   intro st
--   let b := a.map (· st)

end initial_idea

def pointwiseInf {l : Type v} [CompleteLattice l] {α : Type u} (post : α → l) : List α → l :=
  fun xs => ⨅ a ∈ xs, post a

noncomputable
def pointwiseInf' {l : Type v} [CompleteBooleanAlgebra l] {α : Type u} (post : α → l) : List α → l :=
  fun xs => ⨅ a, ⌜ a ∈ xs ⌝ ⇨ post a

theorem pointwiseInf_alt {l : Type v} [CompleteBooleanAlgebra l] {α : Type u} (post : α → l) lis :
  pointwiseInf post lis = pointwiseInf' post lis := by
  unfold pointwiseInf pointwiseInf'
  apply iInf_congr ; intro a
  by_cases h : a ∈ lis <;> simp [h]

def pointwiseSup {l : Type v} [CompleteLattice l] {α : Type u} (post : α → l) : List α → l :=
  fun xs => ⨆ a ∈ xs, post a

theorem pointwiseSup_append {l : Type v} [CompleteLattice l] {α : Type u} (post : α → l) (xs ys : List α) :
  pointwiseSup post (xs ++ ys) = pointwiseSup post xs ⊔ pointwiseSup post ys := by
  simp [pointwiseSup, iSup_or, iSup_sup_eq]

noncomputable
def pointwiseSup' {l : Type v} [CompleteBooleanAlgebra l] {α : Type u} (post : α → l) : List α → l :=
  fun xs => ⨆ a, ⌜ a ∈ xs ⌝ ⊓ post a

theorem pointwiseSup_alt {l : Type v} [CompleteBooleanAlgebra l] {α : Type u} (post : α → l) lis :
  pointwiseSup post lis = pointwiseSup' post lis := by
  unfold pointwiseSup pointwiseSup'
  apply iSup_congr ; intro a
  by_cases h : a ∈ lis <;> simp [h]

section what_do_we_want

abbrev VeilExecM (ε ρ σ α : Type u) :=
  ReaderT ρ (StateT σ (ExceptT ε DivM)) α
  -- ρ → σ → DivM (Except ε (α × σ))
-- #simp [VeilExecM, ReaderT, StateT, ExceptT] (fun ε ρ σ α => VeilExecM ε ρ σ α)
-- to be applied to `α`
abbrev VeilMultiExecM_ κ ε ρ σ α := ρ → σ → List (List κ × DivM (Except ε (α × σ)))

def NonDetT.extractGenList_VeilM {findable} {α : Type u}
  (findOf : ∀ {τ : Type u} (p : τ → Prop), ExtCandidates findable κ p → Unit → List τ)
  : (s : NonDetT (VeilExecM ε ρ σ) α) → (ex : ExtractNonDet (ExtCandidates findable κ) s := by solve_by_elim) →
  VeilMultiExecM_ κ ε ρ σ α
  | .pure x, _ => fun _ s => [([], DivM.res (Except.ok (x, s)))]
  | .vis x f, .vis _ _ _ =>
    fun r s =>
      match x r s with
      | DivM.res (Except.ok (y, s')) =>
        extractGenList_VeilM findOf (f y) (by rename_i a ; exact a y) r s'
      -- the following two cannot be merged into one case, due to return type mismatch
      | DivM.div => [([], DivM.div)]
      | DivM.res (Except.error e) => [([], DivM.res (Except.error e))]
  | .pickCont _ p f, .pickSuchThat _ _ _ _ =>
    fun r s =>
      findOf p ‹_› () |>.flatMap fun x =>
        let tmp := extractGenList_VeilM findOf (f x) (by rename_i a ; exact a x) r s
        let x := ExtCandidates.rep _ _ (self := ‹_›) x
        tmp.map fun (ks, y) => (x :: ks, y)

-- to prove what?
-- a state is a possible post state (w.r.t. two state transition) iff
-- it is in the result of execution;
-- (optional) and there exists a extractnondet that corresponds to the
-- prefix and gives the result (should be a corollary of some more general theorem)

-- if exception is in the result list, then (from wp only?)
-- if divergence is in the result list, then ...?

end what_do_we_want

section carrying_monad

-- failed. Guess it is not possible to do this in a "modular" way.

-- def CarryT (κ : Type w) (m : Type u → Type v) (α : Type u) :=
  -- List κ × m α
  -- carrying a constant seems not feasible
  -- (κ → κ) × m α
  -- this does not make sense ... `bind` cannot be defined
  -- κ → κ × m α
  -- `bind` cannot be defined

-- instance CarryT.monadT (m : Type u → Type v) [Monad m] (κ : Type w) :
--   Monad (CarryT κ m) where
--   pure := fun x k => (k, pure x)
--   bind := fun mx f k =>
--     let (k', mx) := mx k
--     let my := mx >>= (fun a => f a |>.snd)
--     (ks, my)

-- #check instLawfulMonadStateRefT'

-- instance CarryT.lawfulMonadT (m : Type u → Type v) [Monad m] [LawfulMonad m] (κ : Type w) :
--   LawfulMonad (CarryT κ m) where
--   bind_pure_comp := by rintro α β f ⟨ks, mx⟩ ; simp [pure, bind, Functor.map]
--   bind_map       := by rintro α β ⟨ks, mf⟩ ⟨ks', mx⟩ ; simp [pure, bind, Functor.map, Seq.seq]
--   pure_bind      := by intros; apply ext; intros; simp
--   bind_assoc     := by intros; apply ext; intros; simp

end carrying_monad

-- NOTE: this should be some special kind of monad morphism

-- is `MonadLift` a good way to represent "going from one monad to another"?
-- or, maybe use something else?
class MonadFlatMapGo (m : Type u → Type v) (n : Type u → Type w) where
  go : {α : Type u} → m α → n α

-- TODO well ... is this something generalizable to monad morphism?

class LawfulMonadFlatMapGo (m : Type u → Type v) (n : Type u → Type w)
  [inst : MonadFlatMapGo m n]
  [Monad m]
  [Monad n]
  (l : Type u)
  -- [CompleteBooleanAlgebra l]
  [CompleteLattice l]
  [MAlgOrdered m l]
  [MAlgOrdered n l]
  (p : l → l → Prop)  -- what about equality? `≤` is just one direction, so maybe parameterize it with `p`
  where
  -- must be relating the results before and after `go`;
  -- a wrong formulation is about all `b : n α`
  go_sound : ∀ α (a : m α) post,
    p (wp a post) (wp (inst.go a) post)

instance
  [inst : MonadFlatMapGo m n]
  [Monad m]
  [Monad n]
  (l : Type u)
  -- [CompleteBooleanAlgebra l]
  [CompleteLattice l]
  [MAlgOrdered m l]
  [MAlgOrdered n l]
  [inst : LawfulMonadFlatMapGo m n l Eq] : LawfulMonadFlatMapGo m n l LE.le where
  go_sound := by
    intro α a post
    rw [inst.go_sound α a post]

instance
  [inst : MonadFlatMapGo m n]
  [Monad m]
  [Monad n]
  (l : Type u)
  -- [CompleteBooleanAlgebra l]
  [CompleteLattice l]
  [MAlgOrdered m l]
  [MAlgOrdered n l]
  [inst : LawfulMonadFlatMapGo m n l Eq] : LawfulMonadFlatMapGo m n l GE.ge where
  go_sound := by
    intro α a post
    rw [inst.go_sound α a post]

abbrev relLift (p : l → l → Prop) : (α → l) → (α → l) → Prop :=
  fun f g => ∀ a, p (f a) (g a)

instance
  [MonadFlatMapGo m n]
  [Monad m]
  [Monad n]
  [CompleteLattice l]
  [MAlgOrdered m (a → l)]
  [MAlgOrdered n (a → l)]
  [inst : LawfulMonadFlatMapGo m n (a → l) (relLift Eq)]
  : LawfulMonadFlatMapGo m n (a → l) Eq where
  go_sound := by introv ; ext a ; apply inst.go_sound

variable [CompleteLattice l] (l1 l2 : Nat → l) in
#check (rfl : (l1 ≤ l2) =
  -- (∀ x, l1 x ≤ l2 x))
  relLift (· ≤ ·) l1 l2)

instance [inst : MonadFlatMapGo m n] : MonadFlatMapGo (ExceptT ε m) (ExceptT ε n) where
  go := inst.go

-- CHECK now I guess this is unrelated to `MonadFlatMapGo`, but generic for monad morphism
instance
  [Monad m]
  [Monad n]
  [LawfulMonad m]
  [LawfulMonad n]
  (l : Type u)
  [CompleteLattice l]
  [MAlgOrdered m l]
  [MAlgOrdered n l]
  (p : l → l → Prop)
  [inst : MonadFlatMapGo m n]
  [instl : LawfulMonadFlatMapGo m n l p]
  {hd : ε → Prop}
  [IsHandler hd]
  : LawfulMonadFlatMapGo (ExceptT ε m) (ExceptT ε n) l p where
  go_sound := by
    intro α a post
    have tmp := instl.go_sound _ a
      (fun e => match e with
        | Except.ok x    => post x
        | Except.error e => ⌜hd e⌝ )
    simp [wp, liftM, monadLift] at tmp ⊢
    simp [MAlg.lift, Functor.map, ExceptT.map, ExceptT.mk] at tmp ⊢
    repeat rw [map_eq_pure_bind] at tmp
    simp only [OfHd, MAlgExcept, map_bind]
    -- not easy to rewrite
    have tmp1 : ∀ (a : Except ε α),
      ((pure
        (match a with
        | Except.ok x => post x
        | Except.error e => ⌜hd e⌝)) : m l) =
      (((Except.getD fun x ↦ ⌜hd x⌝) <$>
        match a with
        | Except.ok a => pure (Except.ok (post a))
        | Except.error e => pure (Except.error e)) : m l) := by
      intro a ; cases a <;> simp [Except.getD]
    conv at tmp => lhs ; rhs ; rhs ; intro x ; rw [tmp1]
    clear tmp1
    have tmp2 : ∀ (a : Except ε α),
      ((pure
        (match a with
        | Except.ok x => post x
        | Except.error e => ⌜hd e⌝)) : n l) =
      (((Except.getD fun x ↦ ⌜hd x⌝) <$>
        match a with
        | Except.ok a => pure (Except.ok (post a))
        | Except.error e => pure (Except.error e)) : n l) := by
      intro a ; cases a <;> simp [Except.getD]
    conv at tmp => rhs ; rhs ; rhs ; intro x ; rw [tmp2]
    clear tmp2
    exact tmp

instance [inst : MonadFlatMapGo m n] : MonadFlatMapGo (ReaderT ρ m) (ReaderT ρ n) where
  go := fun a r => inst.go (a r)

instance
  [Monad m]
  [Monad n]
  [LawfulMonad m]
  [LawfulMonad n]
  (l : Type u)
  [CompleteLattice l]
  [MAlgOrdered m l]
  [MAlgOrdered n l]
  (p : l → l → Prop)
  [inst : MonadFlatMapGo m n]
  [instl : LawfulMonadFlatMapGo m n l p]
  : LawfulMonadFlatMapGo (ReaderT ρ m) (ReaderT ρ n) (ρ → l) (relLift p) where
  go_sound := by
    intro α a post r
    have tmp := instl.go_sound _ (a r) (fun a => post a r)
    simp [wp, liftM, monadLift] at tmp ⊢
    simp [MAlg.lift] at tmp ⊢
    simp [MAlgOrdered.μ, Functor.map]
    exact tmp

instance [inst : MonadFlatMapGo m n] : MonadFlatMapGo (StateT σ m) (StateT σ n) where
  go := fun a s => inst.go (a s)

instance
  [Monad m]
  [Monad n]
  [LawfulMonad m]
  [LawfulMonad n]
  (l : Type u)
  [CompleteLattice l]
  [MAlgOrdered m l]
  [MAlgOrdered n l]
  (p : l → l → Prop)
  [inst : MonadFlatMapGo m n]
  [instl : LawfulMonadFlatMapGo m n l p]
  : LawfulMonadFlatMapGo (StateT σ m) (StateT σ n) (σ → l) (relLift p) where
  go_sound := by
    intro α a post s
    have tmp := instl.go_sound _ (a s) (fun (a, s) => post a s)
    simp [wp, liftM, monadLift] at tmp ⊢
    simp [MAlg.lift] at tmp ⊢
    simp [MAlgOrdered.μ, Functor.map, StateT.map]
    exact tmp

-- TODO maybe also need one way to get the log?
class MonadPersistentLog (κ : Type w) (m : Type u → Type v) where
  log : κ → m PUnit

-- using `MonadLiftT` reports error, so anyway
instance
  -- (κ : Type w) (m : Type u → Type v)
  [inst : MonadPersistentLog κ m]
  [lft : MonadLift m n] :
  MonadPersistentLog κ n where
  log := (lft.monadLift <| inst.log ·)

-- no effect can be observed from the log action
class LawfulMonadPersistentLog (κ : Type w) (m : Type u → Type v)
  [inst : MonadPersistentLog κ m]
  [Monad m]
  -- [LawfulMonad m]
  (l : Type u)
  [CompleteLattice l]
  [MAlgOrdered m l]
  where
  log_sound : ∀ (k : κ) (post : PUnit → l),
    -- wp (inst.log k >>= f) post = wp (f PUnit.unit) post
    wp (inst.log k) post = post PUnit.unit

-- TODO we should be able to derive `LawfulMonadPersistentLog` systematically,
-- through some kind of lawful lifts, but it seems not very easy to do so ...?
-- #print
-- instance
--   [Monad m]
--   [Monad n]
--   [CompleteLattice l]
--   [MAlgOrdered m l]
--   [MAlgOrdered n l]
--   [inst : MonadPersistentLog κ m]
--   [lft : MonadLift m n]
--   [insta : LawfulMonadPersistentLog κ m l]
--   : LawfulMonadPersistentLog κ n l where

section monads_with_persistency

-- Ahe point is: sometimes, when the thing to be carried over is inside `m`,
-- then it might get lost when the value with type `m α` does not depend on `α`!
-- This includes `DivM`.
-- And there is no way to remedy in a modular way.
-- So one possible way to go is to augment them with "persistent" results.

def PeDivM (κ : Type w) (α : Type u) := κ × DivM α

def PeDivM.prepend {κ : Type w} [Monoid κ] {α : Type u} (k : κ) (x : PeDivM κ α) : PeDivM κ α :=
  (k * x.1, x.2)

theorem PeDivM.prepend_snd_same {κ : Type w} [Monoid κ] {α : Type u} (k : κ) (x : PeDivM κ α) :
  (x.prepend k).2 = x.2 := by simp [PeDivM.prepend]

-- more suitable to be inserted
def PeDivM.log {κ : Type w} (k : κ) : PeDivM κ PUnit :=
  (k, DivM.res PUnit.unit)

instance [Monoid κ] : Monad (PeDivM κ) where
  pure := fun x => (1, DivM.res x)
  bind := fun (k1, mx) f =>
    match mx with
    | DivM.res x => f x |>.prepend k1
    | DivM.div => (k1, DivM.div)

example {κ : Type w} [Monoid κ] {α : Type u} (k : κ) (x : PeDivM κ α) :
  x.prepend k = (PeDivM.log k) >>= (fun _ => x) := by
  dsimp [PeDivM.prepend, bind, PeDivM.log]

-- instance [Monoid κ] : MonadLift DivM (PeDivM κ) where
--   monadLift := fun x => (1, x)

instance [Monoid κ] : MonadFlatMapGo DivM (PeDivM κ) where
  go := fun x => (1, x)

instance : MonadPersistentLog κ (PeDivM κ) where
  log := PeDivM.log

instance [Monoid κ] : LawfulMonad (PeDivM κ) := by
  refine LawfulMonad.mk' _ ?_ ?_ ?_
  · introv ; simp [Functor.map, PeDivM.prepend] ; (repeat' split) <;> simp
  · introv ; simp [bind, pure, PeDivM.prepend]
  · introv ; simp [bind, pure, PeDivM.prepend] ; rcases x with ⟨k1, x | _⟩ <;> simp
    rcases f x with ⟨k2, y | _⟩ <;> simp
    rcases g y with ⟨k3, z | _⟩ <;> simp
    all_goals (congr! 1 ; ac_rfl)

theorem PeDivM.bind_snd {κ : Type w} {α β : Type u} [Monoid κ] (mx : PeDivM κ α) (f : α → PeDivM κ β) :
  (mx >>= f).2 = mx.2 >>= (Prod.snd ∘ f) := by
  rcases mx with ⟨k1, x | _⟩ <;> simp [bind, prepend]

-- only depends on the second component
instance [Monoid κ]
  [CompleteLattice l]
  [inst : MAlgOrdered DivM l] : MAlgOrdered (PeDivM κ) l where
  μ := inst.μ ∘ Prod.snd
  μ_ord_pure := by intro ll ; apply MAlgOrdered.μ_ord_pure
  μ_ord_bind {α} f g := by
    intro h x ; simp [Function.comp] ; repeat rw [PeDivM.bind_snd]
    apply MAlgOrdered.μ_ord_bind ; exact h

instance
  [Monoid κ]
  [CompleteLattice l]
  [inst : MAlgOrdered DivM l]
   : LawfulMonadFlatMapGo DivM (PeDivM κ) l Eq where
  go_sound := by
    intro α a post
    simp [wp, liftM, monadLift, MAlg.lift, Functor.map]
    rcases a with a | _ <;> simp [PeDivM.prepend, MAlgOrdered.μ]

/-
Another point where the original ListT m is interesting is that it is a composite of
two monads (m and the list monad). This leads us to the study of distributive laws.
There is a canonical distributive law when m is commutative — then ListT m is a monad.
-/

end monads_with_persistency

section test_for_StateT_failed

/-
-- class MonadFlatMap (m : Type u → Type v) where
--   op : ∀ {α}, List (m (List α)) → m (List α)

-- -- the list can be smaller than it should be; here similarly, exhibiting less behavior is allowed
-- class LawfulMonadFlatMap (m : Type u → Type /- v -/ u) (l : Type u) [Monad m] [inst : MonadFlatMap m] [CompleteBooleanAlgebra l] [MAlgOrdered m l] where
--   sound : ∀ (xs : List (m (List α))) (post : α → l),
--     -- TODO not very sure about the direction
--     -- (pointwiseSup (wp · (pointwiseInf post)) xs) ≤ wp (inst.op xs) (pointwiseInf post)
--     wp (inst.op xs) (pointwiseInf post) ≤ (pointwiseSup (wp · (pointwiseInf post)) xs)

section test

variable (σ : Type u) [Monad m] [MonadFlatMap m]

instance : MonadFlatMap (StateT σ m) where
  op := fun {α} xs s =>
    letI tmp := xs.map (· s)
    letI tmp := tmp.map ((fun (as, b) => as.map (Prod.mk · b)) <$> ·)
    letI tmp := MonadFlatMap.op tmp
    sorry

end test

-- well, `m (List α)` does not work, for example with `StateT σ m`,
-- we can only keep one copy of the state, not multiple copies.
-- so it should not be `m (List α)`, but some more general type `m' α` ...?

-- it seems that we cannot directly use `StateT σ m`, but it has to be something else
-/

end test_for_StateT_failed

abbrev ListT (m : Type u → Type v) (α : Type u) := m (List α)

-- ... well, this looks not bad, but might not actually be the way to go
class MonadFlatMap (m' : Type u → Type v) where
  op : ∀ {α}, List (ListT m' α) → ListT m' α

-- this is too general
-- or maybe the shape works, but we always pass the `ListT` version to the
-- type of `MonadFlatMap`
class MonadFlatMap' (m' : Type u → Type v) where
  op : ∀ {α}, List (m' α) → m' α

class LawfulMonadFlatMapSup (m : Type u → Type v) (l : Type u)
  [Monad m]
  [inst : MonadFlatMap' m]
  [CompleteLattice l]
  [MAlgOrdered m l]
  (p : l → l → Prop)
  where
  sound : ∀ (xs : List (m α)) (post : α → l),
    p (⨆ a ∈ xs, wp a post) (wp (inst.op xs) post)

instance
  [Monad m]
  [MonadFlatMap' m]
  [CompleteLattice l]
  [MAlgOrdered m (a → l)]
  [inst : LawfulMonadFlatMapSup m (a → l) (relLift Eq)]
  : LawfulMonadFlatMapSup m (a → l) Eq where
  sound := by introv ; ext a ; apply inst.sound

instance
  [inst : MonadFlatMap' m]
  [Monad m]
  (l : Type u)
  -- [CompleteBooleanAlgebra l]
  [CompleteLattice l]
  [MAlgOrdered m l]
  [inst : LawfulMonadFlatMapSup m l Eq] : LawfulMonadFlatMapSup m l LE.le where
  sound := by
    intro α a post
    rw [inst.sound a post]

instance
  [inst : MonadFlatMap' m]
  [Monad m]
  (l : Type u)
  -- [CompleteBooleanAlgebra l]
  [CompleteLattice l]
  [MAlgOrdered m l]
  [inst : LawfulMonadFlatMapSup m l Eq] : LawfulMonadFlatMapSup m l GE.ge where
  sound := by
    intro α a post
    rw [inst.sound a post]

-- just a marker
class MonadFlatMapRel (m : Type u → Type v) (m' : Type u → Type v)
  [MonadFlatMap' (ListT m')] where
  -- op : ∀ {α}, List (m' (List α)) → m' (List α)

-- sanity check
instance : MonadFlatMap' (ListT Id) where
  op := List.flatten

section for_ReaderT

/-
-- for this simple representable(?) thing ...
-- emm, so what is the principle? in general, wrap `m` with `ListT`, and produce the same thing?

variable [inst : MonadFlatMap' (ListT m')]

-- the wrapping position does not matter much for `ReaderT`
example : (ListT (ReaderT ρ m')) = (ReaderT ρ (ListT m')) := rfl

instance : MonadFlatMap' (ListT (ReaderT ρ m')) where
  op := fun l r => inst.op <| l.map (· r)
-/

-- by the thing above, it does not quite matter how `m'` looks like,
-- and it seems that here `m'` cannot be too constrained with certain shape ...

variable [inst : MonadFlatMap' m']

instance : MonadFlatMap' (ReaderT ρ m') where
  op := fun l r => inst.op <| l.map (· r)

instance --{m : Type u → Type v) (l : Type u)
  [Monad m]
  [LawfulMonad m]
  [inst : MonadFlatMap' m]
  [CompleteLattice l]
  [MAlgOrdered m l]
  (p : l → l → Prop)
  [instl : LawfulMonadFlatMapSup m l p]
  : LawfulMonadFlatMapSup (ReaderT ρ m) (ρ → l) (relLift p)
  where
  sound := by
    intro α xs post r
    simp [MonadFlatMap'.op]
    have tmp := instl.sound (List.map (· r) xs) (fun a => post a r)
    rw [iSup_list_map] at tmp
    simp [wp, liftM, monadLift] at tmp ⊢
    simp [MAlg.lift, Functor.map, MAlgOrdered.μ] at tmp ⊢
    exact tmp

end for_ReaderT

section test_for_StateT_1

variable (σ : Type u) [Monad m'] [inst : MonadFlatMap' (ListT m')] -- [MonadFlatMapRel m m']

-- instance : MonadFlatMap (StateT σ m) (fun a => StateT σ m (List (a × σ))) where
--   op := fun xs s =>
--     letI tmp := xs.map (· s)
--     letI tmp := tmp.map (Prod.fst <$> ·)
--     letI tmp := inst.op tmp
--     (fun a => Prod.mk a s) <$> tmp

-- instance : Monad (fun a => StateT σ m (List (a × σ))) where
--   pure := fun x s => pure ([(x, s)], s)
--   bind := fun m f s => do
--     let (res, s') ← m s
      -- sorry

-- instance : MonadFlatMap (StateT σ m) (fun a => StateT (List σ) m (List a)) where
--   op := fun xs s => inst.op <| xs.map (· s)

-- instance : Monad (fun a => StateT (List σ) m (List a)) where
--   pure := fun x s => pure ([x], s)
--   bind := fun m f s => sorry
--     -- let (res, s') ← m s
--     --   sorry

/-
`σ → List α` might be more efficient, but not so convenient to use
instance : MonadFlatMap (StateT σ m) (fun a => StateT (List σ) m (σ → a)) where
  op := fun xs s =>
    letI tmp := xs.map (· s)
    letI tmp := tmp.map ((fun (a, b) => b.map (fun x => (a x, x))) <$> ·)
    letI tmp := inst.op tmp
    -- (fun a => Prod.mk a s) <$> tmp
    sorry

instance : Monad (fun a => StateT (List σ) m (σ → a)) where
  pure := fun x s => pure (fun _ => x, s)
  bind := fun x f s => do
    let (res, s') ← x s
    let res' := s'.map res
    let sub := res'.map (f · s')
    MonadFlatMap.op m sub

instance : MonadLift (StateT σ m) (fun a => StateT (List σ) m (σ → a)) where
  monadLift := fun x y => do
    let res := y.map x
    let tmp := MonadFlatMap.op m res
    sorry
-/

abbrev StateMulT σ m α := StateT (List σ) m (List α)

theorem StateMulT.eq_StateT_Listσ_ListT : StateMulT σ m = ListT (StateT (List σ) m) := rfl

/-
if `m'` is `Id` ...
`StateMulT σ Id = ListT (StateT (List σ) Id) = StateT (List σ) Id (List α) = (List σ) → (List α) × (List σ)`
flatmap would be
`List ((List σ) → (List α) × (List σ)) → ((List σ) → (List α) × (List σ))`

-/

instance possibility1 : MonadFlatMap' (StateMulT σ m') where
  op := fun xs s =>
    let tmp := xs.map (· s)
    -- needs some kind of way to operate inside the monad, otherwise no way to go here
    -- meaning, `m'` has to be a monad
    let tmp := tmp.map (Function.uncurry List.zip <$> ·)
    let tmp := inst.op (α := _ × _) tmp
    List.unzip <$> tmp

-- instance possibility2 [Monad (ListT m')] : MonadFlatMap' (StateMulT σ m') where
--   op := fun xs s =>
--     let tmp := xs.map (· s)
--     let tmp := tmp.map (Function.uncurry List.zip <$> ·)
--     let tmp := inst.op (α := _ × _) tmp
--     List.unzip <$> tmp

instance : MonadFlatMapRel (StateT σ m) (StateT (List σ) m') where

instance : Monad (StateMulT σ m') where
  pure := fun x s => pure ([x], s)
  bind := fun x f s => do
    let (res, s') ← x s
    -- let res' := res.flatten
    let sub := res.map (f · s')
    -- repeating?
    let tmp := sub.map (Function.uncurry List.zip <$> ·)
    let tmp := inst.op tmp
    List.unzip <$> tmp

variable [Monad m] [MonadLiftT m m']

-- set_option synthInstance.checkSynthOrder false in
-- maybe actually `T`? `MonadLift` will complain
instance isb : MonadLiftT (StateT σ m) (StateMulT σ m') where
  monadLift := fun x y =>
    let res := y.map x
    -- let tmp := res.map
    -- TODO is this idea applicable ... to the failed attempts above?
    let tmp := res.map (fun x => ([·]) <$> (liftM (n := m') x))
    -- repeating?
    let tmp := inst.op tmp
    List.unzip <$> tmp

def increment (m : Nat) : StateT Nat Id Nat := do
  let n ← get
  set (n + m)
  pure n

#eval (
  let a := (isb (m' := Id) Nat).monadLift (increment 2)
  a [1, 2, 3]
)

end test_for_StateT_1

section test_for_monad_inside_list

-- well it is clear that `List` is a monad, how about `List (m α)`?
abbrev TsilT (m : Type u → Type v) (α : Type u) := List (m α)

-- the "core" might be important here: `m α → (α → TsilT m β) → TsilT m β`
-- TODO how to use it in other places? one place: for `⨅`
class TsilTCore (m : Type u → Type v) where
  op : ∀ {α β}, m α → (α → TsilT m β) → TsilT m β

-- NOTE: this function should be essentially the same as `ExceptT.bindCont`,
-- where the pure is the one of `TsilT m`, namely `fun x => [instm.pure x]`.
-- does this observation help?

-- this might indicate that the monad constructed using `TsilTCore`, and
-- the one constructed by exploiting the fact that `ExceptT` and `TsilT`
-- commute, are the same.
-- TODO can we prove this?
#print ExceptT.bindCont
def ExceptT.TsilTCore.go {ε : Type u} {m : Type u → Type v}
  [inst : Pure m]
  {α β : Type u}
  (f : α → TsilT (ExceptT ε m) β) : Except ε α → TsilT (ExceptT ε m) β
  | Except.ok a    => f a
  | Except.error e => [inst.pure (Except.error e)]

instance
  [Pure m]
  [inst : TsilTCore m]
  : TsilTCore (ExceptT ε m) where
  op := fun x f => inst.op x (ExceptT.TsilTCore.go f)

-- CHECK any relation with laws on monad morphism?
class LawfulTsilTCore (m : Type u → Type v)
  [Monad m]
  [TsilTCore m]
  where
  op_single : ∀ {α β} (x : m α) (f : α → m β),
    TsilTCore.op x (fun a => [f a]) = [x >>= f]
  pure_op : ∀ {α β} (x : α) (f : α → TsilT m β), TsilTCore.op (pure x) f = f x
  op_assoc : ∀ {α β γ} (x : m α) (f : α → TsilT m β) (g : β → TsilT m γ),
    List.flatMap (TsilTCore.op · g) (TsilTCore.op x f) =
    TsilTCore.op x (fun a => List.flatMap (TsilTCore.op · g) (f a))

-- TODO how is this related to other laws?
class LawfulTsilTCore' (m : Type u → Type v)
  [Monad m]
  [TsilTCore m]
  where
  -- this is too strong!!! not derivable even for `PeDivM`!!!
  -- op_map_commute : ∀ {α β γ} (x : m α) (f : α → TsilT m β) (h : m β → m γ),
  --   List.map h (TsilTCore.op x f) = TsilTCore.op x (fun a => List.map h (f a))
  op_fmap_commute : ∀ {α β γ} (x : m α) (f : α → TsilT m β) (h : β → γ),
    List.map (h <$> ·) (TsilTCore.op x f) = TsilTCore.op x (fun a => List.map (h <$> ·) (f a))

class LawfulTsilTCoreMAlgSup (m : Type u → Type v) (l : Type u)
  [Monad m]
  [TsilTCore m]
  [CompleteLattice l]
  [MAlgOrdered m l]
  where
  sup : ∀ (f g : α → TsilT m l),
    (pointwiseSup MAlgOrdered.μ ∘ f ≤ pointwiseSup MAlgOrdered.μ ∘ g) →
    ∀ (x : m α),
      pointwiseSup MAlgOrdered.μ (TsilTCore.op x f) ≤ pointwiseSup MAlgOrdered.μ (TsilTCore.op x g)

instance [Pure m] [TsilTCore m] : Monad (TsilT m) where
  pure := fun x => [pure x]
  bind := fun xs f => xs.flatMap fun mx => TsilTCore.op mx f

instance
  [Monad m]
  [TsilTCore m]
  [inst : LawfulTsilTCore m]
  : LawfulTsilTCore (ExceptT ε m) where
  op_single := by
    introv
    simp +unfoldPartialApp [TsilTCore.op, bind, ExceptT.bind, ExceptT.mk, ExceptT.TsilTCore.go]
    have tmp := inst.op_single x (ExceptT.bindCont f)
    simp [ExceptT.bindCont] at tmp
    -- kind of awkward ...
    rw [← tmp] ; congr! 1 ; ext a ; rcases a with e | a <;> simp
  pure_op := by
    introv
    simp [TsilTCore.op, pure, ExceptT.pure, ExceptT.mk, LawfulTsilTCore.pure_op, ExceptT.TsilTCore.go]
  op_assoc := by
    introv
    simp [TsilTCore.op, bind, ExceptT.bind, ExceptT.mk]
    have tmp := inst.op_assoc x (ExceptT.TsilTCore.go f) (ExceptT.TsilTCore.go g)
    trans ; apply tmp
    congr! 1 ; funext a-- ; rcases a with e | a <;> simp [ExceptT.TsilTCore.go]
    unfold ExceptT.TsilTCore.go ; dsimp
    rcases a with e | a <;> simp [LawfulTsilTCore.pure_op]
    rfl

instance-- {m : Type u → Type v} {l ε : Type u}
  [monad_m : Monad m]
  [LawfulMonad m]
  [TsilTCore m]
  [CompleteLattice l]
  [MAlgOrdered m l]
  {hd : ε → Prop}
  [IsHandler hd]
  [inst : LawfulTsilTCoreMAlgSup m l]
  [LawfulTsilTCore' m]
  : LawfulTsilTCoreMAlgSup (ExceptT ε m) l where
  sup := by
    introv ; intro h x
    have tmp := @inst.sup (Except ε α)
    simp [TsilTCore.op, OfHd, MAlgExcept, MAlgOrdered.μ] at h ⊢

    -- TODO this is messy
    -- CHECK is this idea used anywhere else?
    -- generalize heq : (fun (e : ExceptT ε m l) => MAlgOrdered.μ ((Except.getD fun x ↦ ⌜hd x⌝) <$> e)) = ff at h ⊢
    simp only [pointwiseSup] at tmp ⊢
    -- NOTE: the requirement of `LawfulTsilTCore'` comes from observation here
    -- unfold ExceptT.TsilTCore.go
    -- let f' : Except ε α → TsilT m l := fun
    --   | Except.ok a    =>
    --     List.map (fun e => ((Except.getD fun x ↦ ⌜hd x⌝) <$> e))
    --     (f a)
    --   | Except.error e =>
    --     List.map (fun e => ((Except.getD fun x ↦ ⌜hd x⌝) <$> e))
    --     [pure (Except.error e)]
    --     -- [pure (⌜hd e⌝)]
    specialize tmp
      (fun a => List.map (fun e => ((Except.getD fun x ↦ ⌜hd x⌝) <$> e)) (ExceptT.TsilTCore.go f a))
      (fun a => List.map (fun e => ((Except.getD fun x ↦ ⌜hd x⌝) <$> e)) (ExceptT.TsilTCore.go g a))
    simp only [← LawfulTsilTCore'.op_fmap_commute, iSup_list_map] at tmp
    apply tmp ; clear tmp
    -- rintro (e | a)
    intro i ; simp only [Function.comp, pointwiseSup, iSup_list_map]
    rcases i with e | a
    · simp [ExceptT.TsilTCore.go]
    · dsimp only [ExceptT.TsilTCore.go] ; apply h

theorem TsilTCore.bind_cons {α β : Type u}
  [Monad m]
  [TsilTCore m]
  (mx : m α) (mxs : TsilT m α) (f : α → TsilT m β) :
  letI tmp : TsilT m α := (mx :: mxs)
  (tmp >>= f) = (TsilTCore.op mx f) ++ (mxs >>= f) := by simp [bind]

theorem TsilTCore.bind_append {α β : Type u}
  [Monad m]
  [TsilTCore m]
  (mx1 mx2 : TsilT m α) (f : α → TsilT m β) :
  ((mx1 ++ mx2) >>= f) = (mx1 >>= f) ++ (mx2 >>= f) := by simp [bind]

-- TODO is this required?
instance [Monad m] [LawfulMonad m] [TsilTCore m]
  [LawfulTsilTCore m]
   : LawfulMonad (TsilT m) := by
  refine LawfulMonad.mk' _ ?_ ?_ ?_
  · introv ; simp [Functor.map, pure]
    induction x with
    | nil => simp
    | cons y xs ih => simp [ih] ; rw [LawfulTsilTCore.op_single] ; simp
  · introv ; simp [bind, pure] ; apply LawfulTsilTCore.pure_op
  · introv ; simp [bind, pure] ; rw [List.flatMap_assoc]
    apply List.flatMap_congr ; intro x _ ; apply LawfulTsilTCore.op_assoc

-- no, not clear at all
-- def TsilT.bind_good (m : Type u → Type v) : Prop :=
--   sorry

-- the flatten is very trivial in this case
instance : MonadFlatMap' (TsilT m') where
  op := List.flatten

-- NOTE: the following are attempts to derive `LawfulMonadFlatMapSup`
-- for `TsilT m`, but not for `ExceptT ε ...` since there might not be instance
-- about `MonadFlatMap'` for `ExceptT` at the top layer

namespace AngelicChoice

scoped instance
  [Monad m]
  [TsilTCore m]
  [CompleteLattice l]
  [inst : MAlgOrdered m l]
  [LawfulTsilTCoreMAlgSup m l]
  : MAlgOrdered (TsilT m) l where
  μ := pointwiseSup MAlgOrdered.μ
  μ_ord_pure := by intro ll ; simp [pointwiseSup, pure] ; apply MAlgOrdered.μ_ord_pure
  μ_ord_bind := by
    introv ; intro h xs
    induction xs with
    | nil => simp [pointwiseSup, bind]
    | cons x xs ih =>
      simp only [TsilTCore.bind_cons, pointwiseSup_append]
      apply sup_le_sup <;> try assumption
      -- simp only [bind, pointwiseSup, List.flatMap_singleton]
      apply LawfulTsilTCoreMAlgSup.sup ; assumption

scoped instance --{m : Type u → Type v) (l : Type u)
  testtesttest
  [Monad m]
  [TsilTCore m]
  [CompleteLattice l]
  [inst : MAlgOrdered m l]
  [LawfulTsilTCoreMAlgSup m l]
  -- [LawfulMonad m]
  -- [LawfulMonad (TsilT m)]
  -- [CompleteLattice l]
  -- [MAlgOrdered m l]
  -- [MAlgOrdered (TsilT m) l]
  -- [TsilT.wp_iSup m l]
  : LawfulMonadFlatMapSup (TsilT m) l Eq
  where
  sound := by
    introv ; simp [MonadFlatMap'.op, wp, liftM, monadLift, MAlg.lift, Functor.map, MAlgOrdered.μ]
    simp only [pointwiseSup]
    -- this is troublesome!!!
    -- TODO having `iSup_list_flatMap` would be nice
    rw [List.flatten_eq_flatMap, List.flatMap_assoc] ; simp only [id]
    conv => rhs ; rhs ; intro a ; rw [List.mem_flatMap, iSup_exists] ; rhs ; intro i ; rw [iSup_and]
    rw [iSup_comm (ι := m l)]
    conv => rhs ; rhs ; intro a ; rw [iSup_comm (ι := m l)]

end AngelicChoice

-- CHECK maybe this restriction can be put on `wp` rather than monad algebra ...
-- or reverse?
-- class MAlgOrderedTsilTSup (m : Type u → Type v) (l : Type u)
--   [Monad (TsilT m)]
--   [CompleteLattice l]
--   [inst : MAlgOrdered (TsilT m) l]
--   where
--   μ_sup :

class TsilT.wp_iSup (m : Type u → Type v) (l : Type u)
  [Monad m]
  [Monad (TsilT m)]
  [CompleteLattice l]
  [inst : MAlgOrdered m l]
  [instl : MAlgOrdered (TsilT m) l]
  where
  sup : ∀ {α : Type u} (a : TsilT m α) (post : α → l),
    (⨆ x ∈ a, wp x post) = (wp a post)

-- TODO this may not be the best way to go
instance --{m : Type u → Type v) (l : Type u)
  [Monad m]
  [Monad (TsilT m)]
  [LawfulMonad m]
  [LawfulMonad (TsilT m)]
  [CompleteLattice l]
  [MAlgOrdered m l]
  [MAlgOrdered (TsilT m) l]
  [TsilT.wp_iSup m l]
  : LawfulMonadFlatMapSup (TsilT m) l Eq
  where
  sound := by
    introv ; simp [MonadFlatMap'.op] ; rw [← TsilT.wp_iSup.sup]
    conv => lhs ; rhs ; intro a ; rhs ; intro x ; rw [← TsilT.wp_iSup.sup]
    simp only [List.mem_flatten, iSup_exists, iSup_and]
    rw [iSup_comm (ι := m α)]
    conv => rhs ; rhs ; intro a ; rw [iSup_comm (ι := m α)]

-- well ... to account for the logging construct
instance : MonadLift m' (TsilT m') where
  monadLift := fun x => [x]

instance {m'} : MonadFlatMapGo m' (TsilT m') where
  go := fun x => [x]

-- TODO this is ad-hoc, maybe adding some kind of transitivity would be better
instance [inst : MonadFlatMapGo m m'] : MonadFlatMapGo m (TsilT m') where
  go := fun x => [inst.go x]
/-
class LawfulTsilT (m : Type u → Type v) [inst : Monad m] [inst' : Monad (TsilT m)] where
  pure_good : ∀ (x : α), inst'.pure x = [inst.pure x]
  -- CHECK any relationship with monotinicity?
  -- FIXME: the `(∀ a, f a ∈ f' a)` might be too strong
  bind_good : ∀ (mx : m α) (f : α → m β) (mx' : List (m α)) (f' : α → List (m β)),
    mx ∈ mx' → (∀ a, f a ∈ f' a) → inst.bind mx f ∈ (@id (List (m β)) (inst'.bind mx' f'))
  bind_good' : ∀ (mx' : List (m α)) (f' : α → List (m β)) (my : m β),
    my ∈ (@id (List (m β)) (inst'.bind mx' f')) →
    ∃ mx ∈ mx', ∃ f : α → m β, (∀ a, f a ∈ f' a) ∧ inst.bind mx f = my

-- also aligns with some requirements of monad morphism
class LawfulTsilTSmall (m : Type u → Type v) [inst : Monad m] [inst' : Monad (TsilT m)] where
  pure_good : ∀ (x : α), inst'.pure x = [inst.pure x]
-/
-- #print ExceptT.bindCont
-- #print ExceptT.bind
-- instance ExceptT.TsilT_middle [inst : Monad (TsilT m)] : Monad (TsilT (ExceptT ε m)) where
--   pure := fun x => inst.pure (Except.ok x)
--   bind := sorry -- fun xs f =>
variable (ε : Type u) (m : Type u → Type v) (α : Type u) in
-- this is interesting
#check (rfl : ExceptT ε (TsilT m) α = List (m (Except ε α)))
variable (ε : Type u) (m : Type u → Type v) (α : Type u) in
#check (rfl : (TsilT (ExceptT ε m)) α = List (m (Except ε α)))

/-
-- NOTE: this is replaced by the `TsilTCore` approach
instance [Monoid κ] : Monad (TsilT (PeDivM κ)) where
  pure := fun x => [pure x]
  bind := fun xs f =>
    xs.flatMap fun (k1, mx) =>
      match mx with
      | DivM.div => [(k1, DivM.div)]
      -- TODO give this a definition
      -- TODO an optimization: if `k1 = 1`, then no need to prepend
      | DivM.res x => f x |>.map (PeDivM.prepend k1)

theorem TsilT.PeDivM.bind_append [Monoid κ] {α β : Type u} (mx1 mx2 : TsilT (PeDivM κ) α) (f : α → TsilT (PeDivM κ) β) :
  ((mx1 ++ mx2) >>= f) = (mx1 >>= f) ++ (mx2 >>= f) := by simp [bind]

instance [Monoid κ] : LawfulMonad (TsilT (PeDivM κ)) := by
  refine LawfulMonad.mk' _ ?_ ?_ ?_
  · introv ; simp [Functor.map, pure]
    induction x with
    | nil => simp
    | cons y xs ih => simp [ih] ; rcases y with ⟨k1, y | _⟩ <;> simp [PeDivM.prepend]
  · introv ; simp [bind, pure] ; rw [List.map_id''] ; intro ; simp [PeDivM.prepend]
  · introv ; simp [bind, pure] ; rw [List.flatMap_assoc]
    apply List.flatMap_congr ; rintro ⟨k1, x | _⟩ _ <;> simp
    rw [List.map_flatMap, List.flatMap_map]
    apply List.flatMap_congr ; rintro ⟨k2, y | _⟩ _ <;> simp [PeDivM.prepend]
    intros ; ac_rfl
-/

instance [Monoid κ] : TsilTCore (PeDivM κ) where
  op := fun (k1, mx) f =>
    match mx with
    | DivM.div => [(k1, DivM.div)]
    -- TODO give this a definition
    -- TODO an optimization: if `k1 = 1`, then no need to prepend
    | DivM.res x => f x |>.map (PeDivM.prepend k1)

instance [Monoid κ] : LawfulTsilTCore (PeDivM κ) where
  op_single := by
    introv ; simp [TsilTCore.op, bind]
    rcases x with ⟨k1, x | _⟩ <;> rfl
  pure_op := by
    introv ; simp [TsilTCore.op, pure]
    apply List.map_id'' ; rintro ⟨k1, x⟩ ; simp [PeDivM.prepend]
  op_assoc := by
    introv ; simp [TsilTCore.op, bind]
    rcases x with ⟨k1, x | _⟩ <;> try rfl
    dsimp
    rw [List.map_flatMap, List.flatMap_map]
    apply List.flatMap_congr ; rintro ⟨k2, y | _⟩ _ <;> simp [PeDivM.prepend]
    intros ; ac_rfl

instance [Monoid κ] : LawfulTsilTCore' (PeDivM κ) where
  op_fmap_commute := by
    introv ; simp [TsilTCore.op]
    rcases x with ⟨k1, x | _⟩ <;> simp [Functor.map]
    rintro ⟨k2, y | _⟩ _ <;> simp [PeDivM.prepend]

instance
  [Monoid κ]
  [CompleteLattice l]
  [inst : MAlgOrdered DivM l]  -- only rely on the second component
  : LawfulTsilTCoreMAlgSup (PeDivM κ) l where
  sup := by
    introv ; intro h x
    simp only [TsilTCore.op, pointwiseSup, MAlgOrdered.μ] at h ⊢
    rcases x with ⟨k1, x | _⟩ <;> try trivial
    dsimp
    repeat rw [iSup_list_map]
    apply h

/-
-- CHECK not bad, but maybe not immediately useful
-- anyway, this says we need some axiomatization about the monad algebra on `TsilT m`

instance
  [Monad m]
  [Monad n]
  [LawfulMonad m]
  [LawfulMonad n]
  (l : Type u)
  [CompleteLattice l]
  [MAlgOrdered m l]
  [MAlgOrdered n l]
  (p : l → l → Prop)
  [inst : MonadFlatMapGo m n]
  [instl : LawfulMonadFlatMapGo m n l p]
  [Monad (TsilT n)]
  [MAlgOrdered (TsilT n) l]     -- TODO needs refinement
   : LawfulMonadFlatMapGo m (TsilT n) l p where
  go_sound := by
    intro α a post
    have tmp := instl.go_sound _ a post
    simp [wp, liftM, monadLift, MAlg.lift, Functor.map, MAlgOrdered.μ, MonadFlatMapGo.go, pointwiseSup] at tmp ⊢
    have aaa : (MAlgOrdered.μ (m := TsilT n) (post <$> ([MonadFlatMapGo.go a] : TsilT n α))) =
      (MAlgOrdered.μ (m := n) (post <$> MonadFlatMapGo.go a)) := by
      sorry
    rw [aaa] ; assumption
-/

namespace AngelicChoice

-- the general `MAlgOrdered` instance is not obvious??
-- scoped instance (m : Type u -> Type v)
--   [CompleteLattice l]
--   [Monad m] [LawfulMonad m] [inst : MAlgOrdered m l]
--   [Monad (TsilT m)] [LawfulMonad (TsilT m)] [LawfulTsilTSmall m]
--   : MAlgOrdered (TsilT m) l where
--   μ := pointwiseSup inst.μ
--   μ_ord_pure := by intro ll ; simp [pointwiseSup, LawfulTsilTSmall.pure_good] ; apply MAlgOrdered.μ_ord_pure
--   μ_ord_bind {α} f g := by
--     intro h x

--     -- unfold Function.comp at h
--     -- apply Function.
--     sorry

-- NOTE: this is not very related to whether we want demonic or angelic choice,
-- but more about defining the monad algebra for `TsilT m`, where `m` is concrete
-- (since as mentioned above, the general case is not obvious)

/-
-- NOTE: this is replaced by the `TsilTCore` approach
scoped instance [Monoid κ]
  [CompleteLattice l]
  -- [inst : MAlgOrdered (PeDivM κ) l]
  [inst : MAlgOrdered DivM l]   -- only rely on the second component
  : MAlgOrdered (TsilT (PeDivM κ)) l where
  μ := pointwiseSup MAlgOrdered.μ
  μ_ord_pure := by intro ll ; simp [pointwiseSup, pure] ; apply MAlgOrdered.μ_ord_pure
  μ_ord_bind {α} f g := by
    intro h xs ; induction xs with
    | nil => simp [pointwiseSup, bind]
    | cons x xs ih =>
      have tmp := TsilT.PeDivM.bind_append [x] xs f ; simp at tmp ; rw [tmp] ; clear tmp
      have tmp := TsilT.PeDivM.bind_append [x] xs g ; simp at tmp ; rw [tmp] ; clear tmp
      repeat rw [pointwiseSup_append]
      apply sup_le_sup <;> try assumption
      rcases x with ⟨k1, x | _⟩ <;> simp [bind, MAlgOrdered.μ]
      unfold pointwiseSup
      repeat rw [iSup_list_map]
      unfold Function.comp
      conv => lhs ; rhs ; intro x_1 ; rhs ; intro x ; rw [PeDivM.prepend_snd_same]
      conv => rhs ; rhs ; intro x_1 ; rhs ; intro x ; rw [PeDivM.prepend_snd_same]
      apply h

      -- unfold Function.comp at h

      -- unfold
      -- -- apply iSup_mem
      -- simp

      -- simp [ih]
      -- apply?


      -- simp [bind]

      -- · rw [List.flatMap_cons, List.flatMap_nil, List.map_id'']
      --   apply iSup_le ; intro z ; simp
      --   apply inst.μ_ord_bind ; intro a ; apply h
      -- · rw [List.flatMap_cons, List.flatMap_nil, List.map_id'']
      --   apply iSup_le ; intro z ; simp
      --   apply inst.μ_ord_bind ; intro a ; apply h
      -- -- TODO the `ih` part
      -- apply iSup_le ; intro z ; simp
      -- rw [List.flatMap_cons, List.map_id'']
      -- apply inst.μ_ord_bind ; intro a ; apply h
      -- all_goals

theorem TsilT.PeDivM.wp_cons
  [Monoid κ]
  [CompleteLattice l]
  [inst : MAlgOrdered DivM l]
  {α : Type u} (x : PeDivM κ α) (xs : TsilT (PeDivM κ) α) (post : α → l) :
  (wp (m := TsilT (PeDivM κ)) (x :: xs) post) = (wp x post ⊔ wp xs post) := by
  simp [wp, liftM, monadLift, MAlg.lift, Functor.map, MAlgOrdered.μ, pointwiseSup,
    iSup_or, iSup_sup_eq]
  rcases x with ⟨k1, x | _⟩ <;> simp [PeDivM.prepend, pure]
-/

scoped instance
  [Monad m]
  [LawfulMonad m]
  [TsilTCore m]
  [CompleteLattice l]
  [inst : MAlgOrdered m l]
  [LawfulTsilTCore m]
  [LawfulTsilTCoreMAlgSup m l]
   : LawfulMonadFlatMapGo m (TsilT m) l Eq where
  go_sound := by
    introv
    simp [wp, liftM, monadLift, MAlg.lift, Functor.map, MAlgOrdered.μ, MonadFlatMapGo.go, pointwiseSup, TsilTCore.op]
    unfold Function.comp ; simp [LawfulTsilTCore.op_single]

#check LawfulMonadFlatMapGo
-- TODO the proper way to do this is to have a transitivity for `LawfulMonadFlatMapGo`
scoped instance
  [Monad m]
  [Monad m']
  [LawfulMonad m']
  [TsilTCore m']
  [CompleteLattice l]
  [inst : MAlgOrdered m l]
  [inst : MAlgOrdered m' l]
  [LawfulTsilTCore m']
  [LawfulTsilTCoreMAlgSup m' l]
  [MonadFlatMapGo m m']
  {p : l → l → Prop}
  [LawfulMonadFlatMapGo m m' l p]
   : LawfulMonadFlatMapGo m (TsilT m') l p where
  go_sound := by
    introv
    simp [wp, liftM, monadLift, MAlg.lift, Functor.map, MAlgOrdered.μ, MonadFlatMapGo.go, pointwiseSup, TsilTCore.op]
    unfold Function.comp ; simp [LawfulTsilTCore.op_single]
    apply LawfulMonadFlatMapGo.go_sound

/-
-- NOTE: this is replaced by the `TsilTCore` approach
scoped instance
  [Monoid κ]
  [CompleteLattice l]
  [inst : MAlgOrdered DivM l]
   : LawfulMonadFlatMapGo DivM (TsilT (PeDivM κ)) l Eq where
  go_sound := by
    intro α a post
    simp [wp, liftM, monadLift, MAlg.lift, Functor.map, MAlgOrdered.μ, MonadFlatMapGo.go, pointwiseSup, TsilTCore.op]
    rcases a with a | _ <;> simp [PeDivM.prepend, pure]
-/

/-
-- NOTE: this is replaced by the `TsilTCore` approach
scoped instance
  [Monoid κ]
  [CompleteLattice l]
  [inst : MAlgOrdered DivM l]
  : TsilT.wp_iSup (PeDivM κ) l where
  sup := by
    introv
    induction a with
    | nil => simp [wp, liftM, monadLift, MAlg.lift, Functor.map, MAlgOrdered.μ, pointwiseSup]
    | cons y xs ih =>
      simp [TsilT.PeDivM.wp_cons, iSup_or, iSup_sup_eq, ih]
      -- TODO this looks familiar. parallel <-> relational reasoning?
      -- `wp (y :: xs) post`, nesting WP?
      -- oh, maybe not, this is __parallel without sharing__

      -- simp [wp, liftM, monadLift, MAlg.lift, Functor.map, MAlgOrdered.μ, pointwiseSup]


      --  ; rcases y with ⟨k1, y | _⟩ <;> simp [PeDivM.prepend]
    -- TODO any easier way to prove?

    -- simp [wp, liftM, monadLift, MAlg.lift, MAlgOrdered.μ, Functor.map, MAlgOrdered.μ, pointwiseSup]

    -- simp only [Functor.map]
    -- unfold pointwiseSup

    -- rcases a with a | _ <;> simp [PeDivM.prepend, pure]
-/
end AngelicChoice

-- HMM is there any other way to go, without using this equality? I don’t know
-- instance (priority := 2000)
--   [inst : Monad (ExceptT ε (TsilT m))]
--   : Monad (TsilT (ExceptT ε m)) := inst

-- instance (priority := 2000)
--   [inst : Monad (ExceptT ε (TsilT m))]
--   [inst2 : @LawfulMonad (ExceptT ε (TsilT m)) inst]
--   : LawfulMonad (TsilT (ExceptT ε m)) := inst2

-- instance (priority := 2000)
--   [i1 : Monad (ExceptT ε (TsilT m))]
--   [i2 : CompleteLattice l]
--   [inst : @MAlgOrdered (ExceptT ε (TsilT m)) l i1 i2]
--     : MAlgOrdered (TsilT (ExceptT ε m)) l := inst

/-
-- NOTE: this is replaced by the `TsilTCore` approach
class TsilTEmptyBindEmpty (m : Type u → Type v)
  [inst : Monad (TsilT m)] where
  empty_bind_empty : ∀ α β (f : α → TsilT m β), inst.bind [] f = []

class TsilTEmptyMAlgBot (m : Type u → Type v) (l : Type u)
  [inst : Monad (TsilT m)]
  [CompleteLattice l]
  [instl : MAlgOrdered (TsilT m) l] where
  bot : instl.μ [] = ⊥

instance
  [Monad m]
  [Monad (TsilT m)]
  [LawfulMonad m]
  [LawfulMonad (TsilT m)]
  [CompleteLattice l]
  [inst : MAlgOrdered m l]
  [instl : MAlgOrdered (TsilT m) l]
  {hd : ε → Prop}
  [IsHandler hd]
  -- [TsilTEmptyBindEmpty m]
  -- [TsilTEmptyMAlgBot m l]
  [instt : TsilT.wp_iSup m l]
  : TsilT.wp_iSup (ExceptT ε m) l where
  sup := by
    introv
    have tmp := @instt.sup
    simp [wp, liftM, monadLift, MAlg.lift, Functor.map, MAlgOrdered.μ, pointwiseSup,
        ExceptT.map, ExceptT.mk]
    simp only [OfHd, MAlgExcept, MAlgOrdered.μ]


    induction a with
    | nil =>
      simp [wp, liftM, monadLift, MAlg.lift, Functor.map, MAlgOrdered.μ, pointwiseSup,
        ExceptT.map, ExceptT.mk, TsilTEmptyBindEmpty.empty_bind_empty]
      simp only [OfHd, MAlgExcept, MAlgOrdered.μ]
      rw [map_eq_pure_bind, TsilTEmptyBindEmpty.empty_bind_empty, TsilTEmptyMAlgBot.bot]
    | cons y xs ih =>
      simp [wp, liftM, monadLift, MAlg.lift, Functor.map, MAlgOrdered.μ, pointwiseSup,
        ExceptT.map, ExceptT.mk, TsilTEmptyBindEmpty.empty_bind_empty]
      simp [TsilT.PeDivM.wp_cons, iSup_or, iSup_sup_eq, ih]
      sorry
-/

-- TODO well, this becomes bad
-- instance (priority := 2000)
--   [inst : MonadFlatMapGo m n]
--   [Monad m]
--   [i1 : Monad (ExceptT ε (TsilT n))]
--   (l : Type u)
--   [i2 : CompleteLattice l]
--   [MAlgOrdered m l]
--   [inst : @MAlgOrdered (ExceptT ε (TsilT n)) l i1 i2]
--   (p : l → l → Prop)
--   [i1 : Monad (ExceptT ε (TsilT m))]
--   [i2 : CompleteLattice l]
--   [inst : @LawfulMonadFlatMapGo (ExceptT ε (TsilT m)) l i1 i2]
--     : MAlgOrdered (TsilT (ExceptT ε m)) l := inst


-- instance [Monoid κ] : LawfulTsilT (PeDivM κ) where
--   pure_good := by introv ; rfl
--   bind_good := by
--     introv ; intro h1 h2 ; dsimp [bind]
--     eapply List.mem_flatMap_of_mem ; assumption
--     rcases mx with ⟨k1, x | _⟩ <;> simp
--     exists (f x) ; simp [h2]
--   bind_good' := by
--     introv ; intro h ; simp [bind] at h ; rcases h with ⟨mx, hmx, h⟩
--     exists mx ; constructor ; assumption
--     rcases mx with ⟨k1, x | _⟩ <;> simp at h
--     · rcases h with ⟨⟨k2, my'⟩, hmy', h⟩ ; dsimp at h ; subst my
--     sorry

end test_for_monad_inside_list

section test_for_StateT_2

-- variable (σ : Type u) [Monad m'] [inst : MonadFlatMap' (ListT m')] -- [MonadFlatMapRel m m']

-- does not have to be `List σ`

abbrev StateMulT' (σ : Type u) (m : Type u → Type v) := StateT σ (ListT m)

theorem StateMulT'.eq_StateT_σ_ListT : StateMulT' σ m α = (σ → m (List (α × σ))) := rfl

-- the same construction as `ReaderT`;
-- here use the restrictive version `MonadFlatMap' (ListT m')`
instance possibility1' [instf : MonadFlatMap' (ListT m')] :
  MonadFlatMap' (StateMulT' σ m') where
  op := fun l r =>
    letI tmp := l.map (· r)
    letI res := instf.op tmp
    res

-- CHECK an alternative way is to declare `ListT m'` as monad??
instance [inst : Monad m'] [instf : MonadFlatMap' (ListT m')] :
  Monad (StateMulT' σ m') where
  pure := fun x s => inst.pure ([(x, s)])
  bind := fun x f s =>
    inst.bind (x s) (fun l =>
      let tmp := l.map (fun (a, s) => f a s)
      instf.op tmp)

-- TODO revive this part
-- variable [Monad m] [MonadLiftT m m']

-- -- set_option synthInstance.checkSynthOrder false in
-- -- maybe actually `T`? `MonadLift` will complain
-- instance isb' : MonadLiftT (StateT σ m) (StateMulT' σ m') where
--   monadLift := fun x y => List.singleton <$> (x y)

-- viewing `m` as a certain "object" rather than a computation
-- CHECK however, `List (m α)` is not immediately a monad w.r.t. `α`?
-- it is unclear how to reuse the `bind` of `m`
-- so the following is not a monad
/-
abbrev StateMulT'' (σ : Type u) (m : Type u → Type v) := StateT σ (List <| m ·)

theorem StateMulT''.eq_StateT_σ_ListT : StateMulT'' σ m α = (σ → (List <| m (α × σ))) := rfl

-- even simpler ...
instance possibility1'' :
  MonadFlatMap' (StateMulT'' σ m') where
  op := fun l r =>
    letI tmp := l.map (· r)
    tmp.flatten
-/

end test_for_StateT_2

section test_for_StateT_3

-- the same construction as `ReaderT`
-- ... of course. or why?
instance possibility1'' [instf : MonadFlatMap' m'] :
  MonadFlatMap' (StateT σ m') where
  op := fun l r =>
    letI tmp := l.map (· r)
    letI res := instf.op tmp
    res

instance --{m : Type u → Type v) (l : Type u)
  [Monad m]
  [LawfulMonad m]
  [inst : MonadFlatMap' m]
  [CompleteLattice l]
  [MAlgOrdered m l]
  (p : l → l → Prop)
  [instl : LawfulMonadFlatMapSup m l p]
  : LawfulMonadFlatMapSup (StateT σ m) (σ → l) (relLift p)
  where
  sound := by
    intro α xs post st
    simp [MonadFlatMap'.op]
    have tmp := instl.sound (List.map (· st) xs) (fun (a, s) => post a s)
    rw [iSup_list_map] at tmp
    simp [wp, liftM, monadLift] at tmp ⊢
    simp [MAlg.lift, Functor.map, MAlgOrdered.μ, StateT.map] at tmp ⊢
    exact tmp

end test_for_StateT_3

-- TODO why this is not present?
instance : Monoid (List κ) where
  one := []
  mul := List.append
  mul_assoc := by introv ; apply List.append_assoc
  one_mul := by introv ; rfl
  mul_one := by introv ; apply List.append_nil

section what_do_we_want_again

-- NOTE: there are some attempts to switch between `ExceptT ε (TsilT m)` and `TsilT (ExceptT ε m)`
-- below; but due to the type dependence (e.g., `LawfulMonad` depends on `Monad`),
-- this switch might be troublesome.
-- so for now, let's first insist on one form, say `TsilT (ExceptT ε m)`.

-- def VeilExecM (ε : Type w) (ρ σ α : Type u) :=
--   -- ReaderT ρ (StateT σ (ExceptT ε DivM)) α
--   ρ → σ → DivM (Except ε (α × σ))
-- -- #simp [VeilExecM, ReaderT, StateT, ExceptT] (fun ε ρ σ α => VeilExecM ε ρ σ α)
-- -- to be applied to `α`
abbrev VeilMultiExecM_' κ ε ρ σ α :=
  ReaderT ρ (StateT σ (ExceptT ε (TsilT (PeDivM (List κ))))) α

abbrev VeilMultiExecM_'' κ ε ρ σ α :=
  -- NOTE: it has to be this, if we want an instance of `MonadFlatMap'`,
  -- because we cannot construct it by having an instance for `ExceptT`!!
  -- it must be inside some list.
  -- conjecture: even if `TsilT` and `ExceptT` commute, things might not work out ...?
  ReaderT ρ (StateT σ (TsilT (ExceptT ε (PeDivM (List κ))))) α
  -- ρ → σ → List (List κ × DivM (Except ε (α × σ)))
#check (rfl : VeilMultiExecM_' = VeilMultiExecM_)

variable (ε ρ σ α : Type) (κ : Type q)
-- TODO universe problem, due to `MAlg`?
#check inferInstanceAs (Monoid (List κ))
-- #check inferInstanceAs (Monad (VeilMultiExecM_' κ ε ρ σ))
set_option trace.Meta.synthInstance.answer true in
#check inferInstanceAs (MonadFlatMapGo (VeilExecM ε ρ σ) (VeilMultiExecM_' κ ε ρ σ))

set_option trace.Meta.synthInstance.answer true in
#check inferInstanceAs (MonadFlatMapGo (VeilExecM ε ρ σ) (VeilMultiExecM_'' κ ε ρ σ))

#check
  (rfl : (inferInstanceAs (MonadFlatMapGo (VeilExecM ε ρ σ) (VeilMultiExecM_' κ ε ρ σ)))
  =
  (inferInstanceAs (MonadFlatMapGo (VeilExecM ε ρ σ) (VeilMultiExecM_'' κ ε ρ σ))))

set_option trace.Meta.synthInstance.answer true in
open TotalCorrectness in
#check fun (hd : ε → Prop) =>
  let _ : IsHandler hd := ⟨⟩
  -- inferInstanceAs (LawfulMonadFlatMapGo (VeilExecM ε ρ σ) (VeilMultiExecM_' κ ε ρ σ) (ρ → σ → Prop) Eq)
  inferInstanceAs (MAlgOrdered (VeilExecM ε ρ σ) (ρ → σ → Prop))

set_option trace.Meta.synthInstance.answer true in
open AngelicChoice in
open TotalCorrectness in
#check fun (hd : ε → Prop) =>
  let _ : IsHandler hd := ⟨⟩
  inferInstanceAs (MAlgOrdered (VeilMultiExecM_' κ ε ρ σ) (ρ → σ → Prop))

set_option trace.Meta.synthInstance.answer true in
open AngelicChoice in
open TotalCorrectness in
#check fun (hd : ε → Prop) =>
  let _ : IsHandler hd := ⟨⟩
  inferInstanceAs (MAlgOrdered (VeilMultiExecM_'' κ ε ρ σ) (ρ → σ → Prop))

-- NOTE: this needs rewriting, unless given rewriting instance
-- set_option synthInstance.maxHeartbeats 1000 in
-- set_option trace.Meta.synthInstance.answer true in
-- set_option trace.Meta.synthInstance.instances true in
-- open AngelicChoice in
-- open TotalCorrectness in
-- #check fun (hd : ε → Prop) =>
--   let _ : IsHandler hd := ⟨⟩
--   inferInstanceAs (MAlgOrdered (VeilMultiExecM_'' κ ε ρ σ) (ρ → σ → Prop))

set_option trace.Meta.synthInstance.answer true in
open AngelicChoice in
open TotalCorrectness in
#check fun (hd : ε → Prop) =>
  let _ : IsHandler hd := ⟨⟩
  inferInstanceAs (LawfulMonad (VeilMultiExecM_' κ ε ρ σ))

set_option trace.Meta.synthInstance.answer true in
open AngelicChoice in
open TotalCorrectness in
#check fun (hd : ε → Prop) =>
  let _ : IsHandler hd := ⟨⟩
  inferInstanceAs (LawfulMonad (VeilMultiExecM_'' κ ε ρ σ))

set_option trace.Meta.synthInstance.answer true in
set_option trace.Meta.synthInstance.instances true in
open AngelicChoice in
open TotalCorrectness in
#check fun (hd : ε → Prop) =>
  let _ : IsHandler hd := ⟨⟩
  inferInstanceAs (LawfulMonadFlatMapGo
    -- (StateT σ (ExceptT ε DivM))
    (VeilExecM ε ρ σ)
    -- (StateT σ (ExceptT ε (TsilT (PeDivM (List κ)))))
    (VeilMultiExecM_'' κ ε ρ σ)
    -- (σ → Prop)
    (ρ → σ → Prop)
    -- (relLift <| relLift Eq)
    Eq
    )

-- NOTE: this is direct for `VeilMultiExecM_''` but not for `VeilMultiExecM_'`, see the reason above
set_option trace.Meta.synthInstance.answer true in
set_option trace.Meta.synthInstance.instances true in
#check inferInstanceAs (MonadFlatMap' (VeilMultiExecM_'' κ ε ρ σ))

-- NOTE: some of these, together with the "switching instances" above,
-- seems to introduce discrepancies in instance resolution (i.e., not canonical)
-- CHECK this also seems to indicate that even for the same monad
-- (`TsilT (ExceptT ...))` vs `ExceptT (TsilT ...)`),
-- the instances might not be interchangeable!!!

-- instance : (MonadFlatMap' (VeilMultiExecM_' κ ε ρ σ)) := by
--   have tmp := inferInstanceAs (MonadFlatMap' (VeilMultiExecM_'' κ ε ρ σ))
--   exact tmp

-- instance : (Monad (TsilT (ExceptT ε (PeDivM (List κ))))) := by
--   have tmp := inferInstanceAs (Monad (ExceptT ε (TsilT (PeDivM (List κ)))))
--   exact tmp

-- instance : (Monad (VeilMultiExecM_'' κ ε ρ σ)) := by
--   have tmp := inferInstanceAs (Monad (VeilMultiExecM_' κ ε ρ σ))
--   exact tmp

-- instance : (LawfulMonad (TsilT (ExceptT ε (PeDivM (List κ))))) := by
--   have tmp := inferInstanceAs (LawfulMonad (ExceptT ε (TsilT (PeDivM (List κ)))))
--   exact tmp

-- instance : (LawfulMonad (VeilMultiExecM_'' κ ε ρ σ)) := by
--   have tmp := inferInstanceAs (LawfulMonad (VeilMultiExecM_' κ ε ρ σ))
--   exact tmp

-- instance [inst : (MAlgOrdered (ExceptT ε (TsilT (PeDivM (List κ)))) Prop)]
--   : (MAlgOrdered (TsilT (ExceptT ε (PeDivM (List κ)))) Prop) := inst

-- instance [inst : (MAlgOrdered (VeilMultiExecM_' κ ε ρ σ) (ρ → σ → Prop))]
--   : (MAlgOrdered (VeilMultiExecM_'' κ ε ρ σ) (ρ → σ → Prop)) := inst

-- set_option synthInstance.maxSize 256 in
-- set_option synthInstance.maxHeartbeats 100000 in
-- set_option trace.Meta.synthInstance.answer true in
-- set_option trace.Meta.synthInstance.instances true in
set_option diagnostics true in
open AngelicChoice in
open TotalCorrectness in
#check fun (hd : ε → Prop) =>
  let _ : IsHandler hd := ⟨⟩
  -- inferInstanceAs
  --   (LawfulMonadFlatMapSup (TsilT (ExceptT ε (PeDivM (List κ)))) Prop Eq)
  -- let tmp : (LawfulMonadFlatMapSup (TsilT (ExceptT ε (PeDivM (List κ)))) Prop Eq) :=
  --   (@testtesttest (ExceptT ε (PeDivM (List κ))) Prop
  --   (inferInstance)
  --   (inferInstance)
  --   (inferInstance)
  --   (inferInstance)
  --   (inferInstance))
  inferInstanceAs
    (LawfulMonadFlatMapSup
      -- (TsilT (ExceptT ε (PeDivM (List κ))))
      (VeilMultiExecM_'' κ ε ρ σ)
      -- Prop
      (ρ → σ → Prop)
      -- Eq
      (relLift <| relLift Eq)
      )
  -- inferInstanceAs (type_of% (@testtesttest (ExceptT ε (PeDivM (List κ))) Prop
  --   (inferInstance)
  --   (inferInstance)
  --   (inferInstance)
  --   (inferInstance)
  --   (inferInstance)))
  -- TODO why automatic inference does not work here?
  -- inferInstanceAs (LawfulTsilTCoreMAlgSup (ExceptT ε (PeDivM (List κ))) Prop)
  -- inferInstanceAs (LawfulMonadFlatMapSup
  --   -- (StateT σ (ExceptT ε DivM))
  --   -- (VeilExecM ε ρ σ)
  --   -- (StateT σ (ExceptT ε (TsilT (PeDivM (List κ)))))
  --   -- (VeilMultiExecM_'' κ ε ρ σ)
  --   (TsilT (ExceptT ε (PeDivM (List κ))))
  --   Prop
  --   -- (σ → Prop)
  --   -- (ρ → σ → Prop)
  --   -- (relLift <| relLift Eq)
  --   Eq
  --   )

set_option trace.Meta.synthInstance.answer true in
set_option trace.Meta.synthInstance.instances true in
#check inferInstanceAs (MonadPersistentLog (List κ) (VeilMultiExecM_'' κ ε ρ σ))

-- well, this is ...
open AngelicChoice in
open TotalCorrectness in
noncomputable
instance
  {hd : ε → Prop}
  [IsHandler hd]
  : LawfulMonadPersistentLog (List κ) (VeilMultiExecM_'' κ ε ρ σ) (ρ → σ → Prop) where
  log_sound := by
    introv
    simp [wp, liftM, monadLift, MAlg.lift, Functor.map, MAlgOrdered.μ,
      StateT.map, ExceptT.map, ExceptT.mk, TsilTCore.op, PeDivM.prepend_snd_same,
      MonadPersistentLog.log, MonadLift.monadLift, StateT.lift, ExceptT.lift, PeDivM.log,
      PeDivM.prepend, ExceptT.TsilTCore.go, pure, bind, ExceptT.pure]
    ext a b
    simp [pointwiseSup, OfHd, MAlgExcept, MAlgOrdered.μ, Functor.map, PeDivM.prepend, Except.getD]
    simp [LE.pure]

-- #check inferInstanceAs (MonadLiftT (VeilExecM ε ρ σ) (VeilMultiExecM_' κ ε ρ σ))
-- TODO how to relate the original monad to the new one? `lift` might not be a very good approach
-- #check inferInstanceAs (MonadLiftT (ExceptT ε DivM) (ExceptT ε (TsilT (PeDivM (List κ)))))

end what_do_we_want_again

section test

open Lean.Order

-- like: `m' := StateT (List σ) m`

-- abbrev ArrayTraceT κ m := StateT (Array κ) m

-- variable [Monad m] /- [Lean.MonadBacktrack s m] -/ -- [MonadRepFun m m' s]
variable (m' : /- Type w → -/ Type u → Type v)
  -- [inst1 : Monad (ListT m')]
  -- [inst2 : MonadLiftT m (ListT m')]
  -- -- [inst1 : Monad (ListT (ArrayTraceT κ m'))]
  -- -- [inst2 : MonadLiftT (ArrayTraceT κ m) (ListT (ArrayTraceT κ m'))]
  -- [inst3 : MonadFlatMap' (ListT m')]
  [inst1 : Monad m']-- [inst1 : Monad (m' κ)]
  -- [inst2 : MonadLiftT m (m' κ)]
  [inst2 : MonadFlatMapGo m m']-- [inst2 : MonadFlatMapGo m (m' κ)]
  -- [inst1 : Monad (ListT (ArrayTraceT κ m'))]
  -- [inst2 : MonadLiftT (ArrayTraceT κ m) (ListT (ArrayTraceT κ m'))]
  [inst3 : MonadFlatMap' m'] -- [inst3 : MonadFlatMap' (m' κ)]
  [inst4 : MonadPersistentLog κ m']-- [inst4 : MonadPersistentLog κ (m' κ)]
-- [∀ α, CCPO (m α)] [CCPOBot m] [MonoBind m] [CompleteBooleanAlgebra l] [MPropOrdered m l] [MPropDet m l] [LawfulMonad m]

-- `((τ : Type u) × τ)` will introduce universe level inconsistency
-- so use some `κ` as the "container" type instead


/-
divergence vs. empty list of results:



-/

@[simp, inline]
def NonDetT.extractGenList {findable} {α : Type u} -- {κ}
  (findOf : ∀ {τ : Type u} (p : τ → Prop), ExtCandidates findable κ p → Unit → List τ)
  -- (represent : ∀ {τ : Type u} (p : τ → Prop), findable p → τ → κ)
  : (s : NonDetT m α) → (ex : ExtractNonDet (ExtCandidates findable κ) s) →
  -- ListT (ArrayTraceT κ m') α -- m (List α)
  -- CHECK is this `StateT` even meaningful?
  -- m' (α × List κ)
  m' α
  | .pure x, _ =>
    -- Pure.pure (x, [])
    inst1.pure x
  | .vis x f, .vis _ _ _ =>
    inst1.bind (inst2.go x) (fun y => extractGenList findOf (f y) (by rename_i a ; exact a y))
    -- inst2.monadLift x /- (StateT.lift x) -/ >>= (fun x => extractGenList findOf (f x))
  | .pickCont _ p f, .pickSuchThat _ _ _ _ =>
    let l := findOf p ‹_› ()
    -- let res : List (ListT (ArrayTraceT κ m') α) := l.map (fun x (κs : Array κ) =>
    --   let rep := represent p ‹_› x
    --   -- modify (List.cons (represent p ‹_› x))
    --   extractGenList findOf represent (f x) _ (κs.push rep))
    -- -- MonadFlatMap.op res

    --   -- modify (List.cons (represent p ‹_› x))
    --   extractGenList findOf represent (f x) _ (κs.push rep))
    let res := l.map (fun x =>
      let tmp := extractGenList findOf (f x) (by rename_i a ; exact a x)
      let x := ExtCandidates.rep findable p (self := ‹_›) x
      inst1.bind (inst4.log x) (fun _ => tmp))
    inst3.op res
  -- | .pickCont _ p f, .assume _ _ _ =>
  --   if p .unit
  --   then extractGenList findOf (f .unit)
  --   else Pure.pure []   -- dead end

def NonDetT.extractList {α : Type u} (s : NonDetT m α)
  (ex : ExtractNonDet (ExtCandidates Candidates κ) s) : m' α :=
  NonDetT.extractGenList m'
    (fun p (ec : ExtCandidates Candidates κ p) => ec.core.find)
    s ex

def NonDetT.extractPartialList {α : Type u} (s : NonDetT m α)
  (ex : ExtractNonDet (ExtCandidates PartialCandidates κ) s) : m' α :=
  NonDetT.extractGenList m'
    (fun p (ec : ExtCandidates PartialCandidates κ p) => ec.core.find)
    s ex

variable /- [∀ α, CCPO (m α)] [CCPOBot m] [MonoBind m] -/
  [Monad m]
  [CompleteBooleanAlgebra l]
  [MAlgOrdered m l]
  -- [MAlgDet m l]
  [LawfulMonad m]
  -- [LawfulMonadFlatMap m l]
  [MAlgOrdered m' l]
  [LawfulMonad m']
  [LawfulMonadPersistentLog κ m' l]

namespace AngelicChoice

theorem ExtractNonDet.extract_list_refines_wp
  [instl : LawfulMonadFlatMapGo m m' l GE.ge]
  [instl2 : LawfulMonadFlatMapSup m' l GE.ge]
  (s : NonDetT m α)
  (findOf : ∀ {τ : Type u} (p : τ → Prop), ExtCandidates findable κ p → Unit → List τ)
  (findOf_sound : ∀ {τ : Type u} (p : τ → Prop) (ec : ExtCandidates findable κ p) x,
    x ∈ findOf p ec () → p x)
  (ex : ExtractNonDet (ExtCandidates findable κ) s) :
  wp (s.extractGenList m' findOf ex) post ≤ wp s post := by
  induction ex with
  | pure x => simp [NonDetT.extractPartialList, wp_pure]
  | vis x f g ih =>
    simp [NonDetT.wp_vis, NonDetT.extractPartialList, wp_bind]
    have tmp := instl.go_sound _ x --post
    simp only [ge_iff_le] at tmp
    trans ; apply tmp ; apply wp_cons ; aesop (add norm inf_comm)
  | pickSuchThat τ p f cd ih =>
    simp [NonDetT.wp_pickCont, NonDetT.extractPartialList]
    rename_i extcd
    -- have htmp := PartialCandidates.find_then (self := extcd.core)
    -- generalize (PartialCandidates.find p (self := extcd.core) ()) = lis at htmp ⊢
    specialize findOf_sound p extcd
    generalize (findOf p extcd ()) = lis at findOf_sound ⊢
    have tmp := @instl2.sound
    simp only [ge_iff_le] at tmp
    trans ; apply tmp ; rw [iSup_list_map] ; simp only [wp_bind, LawfulMonadPersistentLog.log_sound]
    simp
    intro a hin ; trans ; apply ih
    apply le_iSup_of_le a ; simp [findOf_sound _ hin]

theorem ExtractNonDet.wp_refines_extract_list
  [instl : LawfulMonadFlatMapGo m m' l LE.le]
  [instl2 : LawfulMonadFlatMapSup m' l LE.le]
  (s : NonDetT m α)
  (findOf : ∀ {τ : Type u} (p : τ → Prop), ExtCandidates findable κ p → Unit → List τ)
  (findOf_complete : ∀ {τ : Type u} (p : τ → Prop) (ec : ExtCandidates findable κ p) x,
    p x → x ∈ findOf p ec ())
  (ex : ExtractNonDet (ExtCandidates findable κ) s) :
  wp s post ≤ wp (s.extractGenList m' findOf ex) post := by
  induction ex with
  | pure x => simp [NonDetT.extractList, wp_pure]
  | vis x f g ih =>
    simp [NonDetT.wp_vis, NonDetT.extractList, wp_bind]
    have tmp := instl.go_sound _ x --post
    trans ; (on_goal 2=> apply tmp) ; apply wp_cons ; aesop (add norm inf_comm)
  | pickSuchThat τ p f cd ih =>
    simp only [NonDetT.wp_pickCont, NonDetT.extractList, NonDetT.extractGenList]
    rename_i extcd
    -- have htmp := Candidates.find_iff (self := extcd.core)
    -- generalize (Candidates.find p (self := extcd.core) ()) = lis at htmp ⊢
    specialize findOf_complete p extcd
    generalize (findOf p extcd ()) = lis at findOf_complete ⊢
    have tmp := @instl2.sound
    trans ; (on_goal 2=> apply tmp) ; rw [iSup_list_map] ; simp only [wp_bind, LawfulMonadPersistentLog.log_sound]
    simp
    intro a hin ; trans ; apply ih
    apply le_iSup_of_le a ; simp [findOf_complete, hin]

theorem ExtractNonDet.extract_list_eq_wp
  [instl : LawfulMonadFlatMapGo m m' l Eq]
  [instl2 : LawfulMonadFlatMapSup m' l Eq]
  (s : NonDetT m α)
  (ex : ExtractNonDet (ExtCandidates Candidates κ) s) :
  wp s post = wp (s.extractList m' ex) post := by
  apply le_antisymm
  · apply ExtractNonDet.wp_refines_extract_list
    introv ; rw [Candidates.find_iff (self := ec.core)] ; exact id
  · apply ExtractNonDet.extract_list_refines_wp
    introv ; rw [Candidates.find_iff (self := ec.core)] ; exact id

end AngelicChoice

end test

section put_together

open AngelicChoice TotalCorrectness in
theorem VeilM.extract_list_eq_wp
  (s : NonDetT (VeilExecM ε ρ σ) α)
  (ex : ExtractNonDet (ExtCandidates Candidates (List κ)) s)
  (hd : ε → Prop) [IsHandler hd] :
  wp s post = wp (s.extractList (VeilMultiExecM_'' κ ε ρ σ) ex) post := by
  apply ExtractNonDet.extract_list_eq_wp

end put_together

#exit


-- wait, `m (List α)`, not `List (m α)`? but generating multiple copies of
-- the same monad is clearly not desirable

-- well, maybe partly because of the discrepancy between what we want (the state)
-- and what gets returned (the result value `α`) ...

-- it is not feasible to go from `Candidates` to `Findable`
-- TODO what was the reason again?

-- omit [Monad m] in
-- lemma LE.pure_or {l : Type u} [_root_.CompleteLattice l]
--   (p₁ p₂ : Prop) : (⌜ p₁ ∨ p₂ ⌝ : l) = (⌜ p₁ ⌝ ⊔ ⌜ p₂ ⌝) := by
--   simp [LE.pure] ; aesop

variable /- [∀ α, CCPO (m α)] [CCPOBot m] [MonoBind m] -/ [CompleteBooleanAlgebra l] [MAlgOrdered m l]
  -- [MAlgDet m l]
  [LawfulMonad m]
  [LawfulMonadFlatMap m l]

namespace AngelicChoice

-- variable [MAlgTotal m]
-- variable [Nonempty α]     -- ??

-- omit [MPropDet m l] in

-- TODO this still seems to be a relatively good attempt ... any lessons learned?

lemma ExtractNonDet.extract_refines_wp_weak__ (s : NonDetT m α)
  (inst : ExtractNonDet PartialCandidates s) :
  -- wp s.extractPartialList (fun a => ⨆ (x : { ι : α // ι ∈ a }), post x.val) ≤ wp s post := by
  wp s.extractPartialList (pointwiseInf post) ≤ wp s post := by
  induction inst with
  | pure x => simp [wp_pure, NonDetT.extractPartialList, pointwiseInf]
  | vis x f g =>
    simp [NonDetT.wp_vis, NonDetT.extractPartialList, wp_bind]
    apply wp_cons; aesop (add norm inf_comm)
  | pickSuchThat τ p f cd ih =>
    simp [NonDetT.wp_pickCont, NonDetT.extractPartialList]
    have htmp := PartialCandidates.find_then (self := by assumption)
    generalize (PartialCandidates.find p ()) = lis at htmp ⊢
    trans ; apply LawfulMonadFlatMap.sound
    unfold pointwiseSup ; simp
    intro a hin ; trans ; apply ih
    apply le_iSup_of_le a ; simp [htmp _ hin]
  | assume p f g ih =>
    simp [NonDetT.wp_pickCont, NonDetT.extractPartialList]
    apply le_iSup_of_le .unit
    split_ifs with h <;> simp [h]
    · apply ih
    · unfold pointwiseInf ; simp [wp_pure] --simp [pointwiseInf]

end AngelicChoice

-- TODO `run`??

end test

section proof

abbrev VeilM.multiChoices (act : VeilM m ρ σ α) := ExtractNonDet Candidates act

end proof

-- nextExecAll : label → VeilExecM m ρ σ (List σ)
-- nextAct r s s' ↔ s' ∈ nextExecAll.operational' r s

-- also, impossible to derive a list of `WeakFindable`, due to the `∀` thing
