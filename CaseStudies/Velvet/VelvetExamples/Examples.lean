import Auto
import Lean

import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Ring.Int.Defs

import Loom.MonadAlgebras.NonDetT.Extract
import Loom.MonadAlgebras.WP.Tactic
import Loom.MonadAlgebras.WP.DoNames'

import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil

open PartialCorrectness DemonicChoice Lean.Elab.Term.DoNames

set_option auto.smt.trust true
set_option auto.smt true
set_option auto.smt.timeout 4
set_option auto.smt.solver.name "cvc5"

attribute [solverHint] TArray.get_set TArray.size_set

section insertionSort

/-

Dafny code below for reference

method insertionSort(arr: array<int>)
  modifies arr
  ensures forall i, j :: 0 <= i < j < arr.Length ==> arr[i] <= arr[j]
  ensures multiset(arr[..]) == old(multiset(arr[..]))
{
  if arr.Length <= 1 {
    return;
  }
  var n := 1;
  while n != arr.Length
  invariant 0 <= n <= arr.Length
  invariant forall i, j :: 0 <= i < j <= n - 1 ==> arr[i] <= arr[j]
  invariant multiset(arr[..]) == old(multiset(arr[..]))
  {
    var mind := n;
    while mind != 0
    invariant 0 <= mind <= n
    invariant multiset(arr[..]) == old(multiset(arr[..]))
    invariant forall i, j :: 0 <= i < j <= n && (j != mind)==> arr[i] <= arr[j]
    {
      if arr[mind] <= arr[mind - 1] {
        arr[mind], arr[mind - 1] := arr[mind - 1], arr[mind];
      }
      mind := mind - 1;
    }
    n := n + 1;
  }
}
-/

-- set_option trace.profiler true
attribute [local solverHint] Array.multiset_swap
attribute [solverHint] Array.size_set_c Array.get_set_c

--partial correctness version of insertionSort
method insertionSort
  (mut arr: Array Int) return (u: Unit)
  require 1 ≤ arr.size
  ensures forall i j, 0 ≤ i ∧ i ≤ j ∧ j < size arr → arrNew[i]! ≤ arrNew[j]!
  ensures toMultiset arr = toMultiset arrNew
  do
    let arr₀ := arr
    let arr_size := arr.size
    let mut n := 1
    while n ≠ arr.size
    invariant arr.size = arr_size
    invariant 1 ≤ n ∧ n ≤ arr.size
    invariant forall i j, 0 ≤ i ∧ i < j ∧ j <= n - 1 → arr[i]! ≤ arr[j]!
    invariant toMultiset arr = toMultiset arr₀
    done_with n = arr.size
    do
      let mut mind := n
      while mind ≠ 0
      invariant arr.size = arr_size
      invariant mind ≤ n
      invariant forall i j, 0 ≤ i ∧ i < j ∧ j ≤ n ∧ j ≠ mind → arr[i]! ≤ arr[j]!
      invariant toMultiset arr = toMultiset arr₀
      done_with mind = 0
      do
        if arr[mind]! < arr[mind - 1]! then
          swap! arr[mind - 1]! arr[mind]!
        mind := mind - 1
      n := n + 1
    return

extract_program_for insertionSort
prove_precondition_decidable_for insertionSort
prove_postcondition_decidable_for insertionSort by
  (exact (decidable_by_nat_upperbound [(size arr), (size arr)]))
derive_tester_for insertionSort

-- doing simple testing
run_elab do
  let g : Plausible.Gen (_ × Bool) := do
    let arr ← Plausible.SampleableExt.interpSample (Array Int)
    let res := insertionSortTester arr
    pure (arr, res)
  for _ in [1: 500] do
    let res ← Plausible.Gen.run g 10
    unless res.2 do
      IO.println s!"postcondition violated for input {res.1}"
      break

set_option maxHeartbeats 1000000

prove_correct insertionSort by
  loom_solve

end insertionSort

section squareRoot

--partial correctness version of square root
method sqrt (x: ℕ) return (res: ℕ)
  require x > 8
  ensures res * res ≤ x
  ensures ∀ i, i ≤ res → i * i ≤ x
  ensures ∀ i, i * i ≤ x → i ≤ res
  do
    if x = 0 then
      return 0
    else
      let mut i := 0
      while i * i ≤ x
      invariant ∀ j, j < i → j * j ≤ x
      done_with x < i * i
      do
        i := i + 1
      return i - 1

prove_correct sqrt by
  loom_solve!

end squareRoot


section runLengthEncoding

structure Encoding where
  cnt: Nat
  c: Char
  deriving Inhabited

variable {velvetString} [arr_inst_int: TArray Char velvetString]
variable {arrEncoding} [arr_encoding_inst: TArray Encoding arrEncoding]

def get_cnt_sum (l: List Encoding) :=
  match l with
  | List.nil => 0
  | List.cons x xs => x.cnt + get_cnt_sum xs
  
lemma get_cnt_sum_hd e l : get_cnt_sum (e::l) = e.cnt + get_cnt_sum l := by
  conv  => {
    lhs
    unfold get_cnt_sum
  }


lemma get_cnt_sum_append l1 l2:  get_cnt_sum (l1 ++ l2) = get_cnt_sum l1 + get_cnt_sum l2 := by
  induction l1 with
  | nil => simp; rfl
  | cons e l1' ih =>
    simp [ih]
    repeat (rw [get_cnt_sum_hd])
    grind

method decodeStr' (encoded_str: Array Encoding) 
   return (res: Array Char)
   require (forall i, i < size encoded_str -> encoded_str[i]!.cnt > 0   )
   ensures (res.size = get_cnt_sum encoded_str.toList)
     do
       let mut decoded := Array.replicate 0 'x'
       let mut i := 0
       while i < encoded_str.size
          invariant 0 <= i ∧ i <= encoded_str.size
          invariant decoded.size = get_cnt_sum (encoded_str.extract 0 i).toList
          done_with i = encoded_str.size
          do
            let elem := encoded_str[i]!
            let elem_decoded := Array.replicate elem.cnt elem.c
            decoded :=  decoded ++ elem_decoded
            i := i + 1
       return decoded


prove_correct decodeStr' by
  unfold decodeStr'
  loom_solve
  · simp[*] at *
    have : decoded.size = get_cnt_sum (List.take i encoded_str.toList) := by trivial
    rw [this] at *
    rw [List.take_succ_eq_append_getElem]
    rw [get_cnt_sum_append]
    simp[*]
    unfold get_cnt_sum
    rfl
  · simp[*]; rfl
  · simp[*]

#eval (decodeStr' #[{cnt:= 10, c:= 'd'}, {cnt := 3, c:= 'e'}, {cnt := 5, c:= 'f'}]).run

def decodeStrLean (encoded_str: Array Encoding) : Array Char := 
  if h: encoded_str.size > 0 then (
    let elem := encoded_str[0]
    (Array.replicate  elem.cnt elem.c) ++ (decodeStrLean (encoded_str.extract 1))
  )
  else #[]

#eval (decodeStrLean #[{cnt:= 10, c:= 'd'}, {cnt := 3, c:= 'e'}, {cnt := 5, c:= 'f'}])

lemma decodeStrTriple : forall encoded_str, (forall i, i < size encoded_str -> encoded_str[i]!.cnt > 0) -> 
  ( (decodeStrLean encoded_str).size = get_cnt_sum encoded_str.toList) := by
    intros encoded_str pre
    sorry


method encodeStr (str: Array Char) return (res: Array Encoding)
  ensures (forall i, i < size res -> res[i]!.cnt > 0)
  ensures (decodeStrLean res =  str) do
    return #[]
    
end runLengthEncoding
