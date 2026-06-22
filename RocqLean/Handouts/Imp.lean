import Std.Data.ExtTreeMap.Basic

inductive binop where
  | Add
  | Mul
  | Sub
  | Leq
deriving DecidableEq
export binop (Add Mul Sub Leq)

inductive expr where
| Var (x : String)
| Num (n : Nat)
| Binop (b : binop) (e1 e2 : expr)
deriving DecidableEq
export expr (Var Num Binop)

inductive com where
| Skip
| Seq (c1 c2 : com)
| Assign (x : String) (e : expr)
| If (e : expr) (c1 c2 : com)
| While (e : expr) (c : com)
deriving DecidableEq
export com (Skip Seq Assign If While)

def eval_binop (b : binop) :=
  match b with
  | .Add => Nat.add
  | .Mul => Nat.mul
  | .Sub => Nat.sub
  | .Leq => fun n1 n2 => if (n1 ≤ n2) then 1 else 0

-- gmap strikes again, the bane of Iris-Lean
def state : Type := Std.ExtTreeMap String Nat

inductive result (T : Type) where
  | Done (x : T)
  | Error
  | NotYet
export result (Done Error NotYet)

instance instBindResult : Bind result where
  bind
  | Done a => (· a)
  | Error => fun _ => Error
  | NotYet => fun _ => NotYet

def eval_expr (_e : expr) (_s : state) : result Nat :=
  -- Wait for lecture definition probably
  NotYet

theorem eval_expr_notyet e s : eval_expr e s ≠ NotYet :=
  sorry

def iter {T} (f : (T -> result T) -> T -> result T) (k : Nat) (x : T) : result T :=
  f (fun x' =>
      match k with
      | .zero => NotYet
      | .succ k' => iter f k' x') x

def eval_com (c : com) (k : nat) (s : state) : result state :=
  match c with
  | .Skip =>
      Done s
  | .Seq c1 c2 => do
      let s' ← eval_com c1 k s
      eval_com c2 k s'
  | .Assign x e => do
      let n ← eval_expr e s
      Done (s.insert x n)
  | .If _e _c1 _c2 =>
      NotYet
  | .While _e _c =>
      NotYet

theorem result_done_mbind : ∀ {T S} (x : T) (f : T -> result S),
    Done x >>= f = f x := by simp [bind]

theorem result_mbind_done : ∀ {T} (x : result T), x >>= Done = x := by
  rintro _ ⟨⟩ <;> simp [bind]

theorem result_mbind_assoc :
  ∀ {T S R} (g : S -> result R) (f : T -> result S) (x : result T),
    (x >>= f) >>= g =
    x >>= (fun y : T => (f y) >>= g) := by
  rintro _ _ _ g f (_|_|_) <;> simp only [bind]

theorem result_mbind_inv :
  ∀ {T S} {f : T -> result S} {x : result T} {y : S},
    x >>= f = Done y -> ∃ a, x = Done a ∧ f a = Done y := by
  rintro _ _ f (_|_|_) _ <;> simp [bind]

class SqSubsetEq (T : Type _) where
  sqle : T → T → Prop

syntax term " ⊑ " term : term
syntax term " ⊑@{" term "} " term : term
-- I wonder if you need syntax+macro_rules for notation typeclasses in general
-- or if you can get away with a macro somehow (naive def fails tc synthesis)
macro_rules
  | `($t1 ⊑ $t2) => `(SqSubsetEq.sqle $t1 $t2)
  | `($t1 ⊑@{$T} $t2) => `(SqSubsetEq.sqle (T := $T) $t1 $t2)

instance result_sqsubseteq {T} : SqSubsetEq (result T) where
  sqle x y := x = NotYet ∨ x = y

-- I bet this will change in the lecture
theorem result_sqsubseteq_NotYet :
  forall {T} (x : result T), NotYet  ⊑ x := by
  intro T x
  left
  rfl

instance instResultSqSubseteqRefl (T : Type) : Std.Refl (· ⊑@{result T} ·) where
  refl _ := .inr rfl

instance instResultSqSubseteqTrans (T : Type) :
    Trans (· ⊑@{result T} ·) (· ⊑@{result T} ·) (· ⊑@{result T} ·) where
  trans := by rintro x y z (rfl|rfl) (rfl|rfl) <;> simp [SqSubsetEq.sqle]

theorem result_bind_mono :
  forall {T S} (f g : T -> result S) (x y : result T),
    (x ⊑ y) →
    (forall a, f a ⊑ g a) →
    (x >>= f) ⊑ y >>= g := by
  sorry


/-
Lemma iter_mono :
  forall {T} (f g : (T -> result T) -> T -> result T) n m x,
    (forall (f' g' : T -> result T),
      (forall x, f' x ⊑ g' x) ->
      (forall x, f f' x ⊑ g g' x)) ->
    n <= m ->
    iter f n x ⊑ iter g m x.
Proof.
intros T f g n m x f_g n_m.
induction m as [|m IH] in n, n_m, x |- *.
- assert (n = 0) as n0. { lia. }
  rewrite n0 /=. apply f_g. done.
- destruct n as [|n]; rewrite /=.
  + apply f_g. done.
  + apply f_g. intros a. apply IH. lia.
Qed.

(** Because [iter] behaves in this way, command evaluation also yields more
    results with more iterations. *)

Lemma eval_com_mono :
  forall n m c s, n <= m -> eval_com c n s ⊑ eval_com c m s.
Proof. Admitted.

Fixpoint vars_expr e : gset string :=
  match e with
  | Var x => singleton x
  | Num n => empty
  | Binop b e1 e2 => union (vars_expr e1) (vars_expr e2)
  end.

Fixpoint vars_com c : gset string :=
  match c with
  | Skip => empty
  | Seq c1 c2 => union (vars_com c1) (vars_com c2)
  | Assign x e => union (singleton x) (vars_expr e)
  | If e c1 c2 => union (vars_expr e) (union (vars_com c1) (vars_com c2))
  | While e c => union (vars_expr e) (vars_com c)
  end.

Lemma vars_com_not_error c k s :
  subseteq (vars_com c) (dom s) ->
  eval_com c k s <> Error.
Proof. Admitted.
-/
