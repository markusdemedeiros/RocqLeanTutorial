
/-! Basics

Ported from
https://github.com/arthuraa/rocq-introduction/blob/master/handouts/basics.v
-/

namespace Basics

inductive Nat : Type where
  | O
  | S (n : Nat)
export Nat (O S)

def zero : Nat := O

def one : Nat := S zero

def two: Nat := S one

def succ (n : Nat) : Nat := S n

def plus_two (n : Nat) : Nat := succ (succ n)

def add (n m : Nat) :=
  match n with
  | O => m
  | S n' => S (add n' m)

/-- info: Basics.Nat.S (Basics.Nat.S (Basics.Nat.S (Basics.Nat.S (Basics.Nat.O)))) -/
#guard_msgs in
#eval add two two

theorem add_l_0 : ∀ (n : Nat), add O n = n := by
  intro n
  cases n
  · rfl
  · rfl

/-
(** This result is so simple that the [eauto] tactic is enough.  In general,
    [eauto] will try to prove a goal by chaining together a series of elementary
    proof steps, up to some limit. *)

Lemma add_l_0' : forall n, add O n = n.
Proof. Admitted.
-/

theorem one_not_zero : one ≠ zero := by
  rintro ⟨⟩

theorem add_Sn_neq_zero : ∀ n m, add (S n) m ≠ O := by
  rintro n m ⟨⟩

theorem add_nS_neq_zero : ∀ n m, add n (S m) ≠ O := by
  intro n
  induction n
  · simp [add]
  · simp [add]

theorem add_r_0 : ∀ n, add n O = n := by
  intro n
  induction n
  · simp [add]
  · simpa [add]

theorem add_l_S : ∀ n m, add (S n) m = S (add n m) := by
  intro n m
  rfl

theorem add_r_S : ∀ n m, add n (S m) = S (add n m) := by
  intro n
  induction n
  · intro m
    simp [add]
  · rename_i ih
    intro m
    simpa [add] using ih _

theorem add_comm : ∀ n m, add n m = add m n := by
  intro n
  induction n
  · intro m
    rw [add_r_0, add_l_0]
  · rename_i ih
    intro m
    rw [add_l_S, add_r_S]
    congr 1
    exact ih _

theorem add_eq_0 : ∀ n m, add n m = O ↔ n = O ∧ m = O := by
  intro n m
  induction n
  · simp [add_l_0]
  · simp [add_l_S]

theorem add_eq_S : ∀ n m p, add n m = S p -> ∃ k, n = S k ∨ m = S k := by
  intro n m
  induction n
  · intro p
    grind [add_l_0]
  · simp [add_l_S]

inductive List (T : Type) : Type
| nil
| cons (x : T) (xs : List T)
export List (nil cons)

def ex1 : List Nat := nil

def ex2 : List Nat := cons zero nil

def ex1' : List Nat := nil

def ex2' : List Nat := cons zero nil

def app {T} (xs ys : List T) : List T :=
  match xs with
  | nil => ys
  | cons x xs' => cons x (app xs' ys)

theorem app_nil_l : ∀ T (xs : List T), app nil xs = xs := by
  rintro T xs
  rfl

theorem app_nil_r : ∀ T (xs : List T), app xs nil = xs := by
  rintro T xs
  induction xs
  · simp [app]
  · simpa [app]

theorem app_assoc : ∀ T (xs ys zs : List T), app xs (app ys zs) = app (app xs ys) zs := by
  intro T xs
  induction xs
  · simp [app]
  · grind [app]
