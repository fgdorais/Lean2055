import Batteries

namespace Lean2055

scoped notation "ℕ" => Nat
scoped notation "ℤ" => Int
scoped notation "ℚ" => Rat

scoped infix:35 (priority := high) " ∧ " => And
scoped infix:35 (priority := high) " ∨ " => Or

scoped syntax "cleanup" colGt (Lean.Parser.Tactic.location)? : tactic
macro_rules
| `(tactic| cleanup $[$loc]?) => `(tactic| try simp only [Classical.not_not] $[$loc]?)

scoped syntax "split_and" : tactic
macro_rules
| `(tactic| split_and) => `(tactic| refine And.intro ?_ ?_)

scoped syntax "split_or" colGt Lean.Parser.Tactic.location : tactic
macro_rules
| `(tactic| split_or at $h:ident) =>
  `(tactic| cases $h:term with cleanup at $h:ident
    | inl $h => ?_ | inr $h => ?_)

scoped syntax (priority := high) "left" colGt (ident)? : tactic
macro_rules
| `(tactic| left $h) =>
  `(tactic| refine Classical.or_iff_not_imp_right.2 ?_ <;> intro $h:ident <;> cleanup at $h:ident)
| `(tactic| left) => `(tactic| refine Or.inl ?_)

scoped syntax (priority := high) "right" colGt (ident)? : tactic
macro_rules
| `(tactic| right $h) =>
  `(tactic| refine Classical.or_iff_not_imp_left.2 ?_ <;> intro $h:ident <;> cleanup at $h:ident)
| `(tactic| right) => `(tactic| refine Or.inr ?_)

attribute [scoped simp ←] Nat.mul_assoc Nat.add_assoc
attribute [scoped simp] Nat.add_mul Nat.mul_add
attribute [scoped simp] Nat.mul_right_comm
attribute [scoped simp] Nat.pow_zero Nat.pow_succ

attribute [scoped simp ←] Int.mul_assoc Int.add_assoc
attribute [scoped simp] Int.add_mul Int.mul_add
attribute [scoped simp] Int.mul_right_comm
attribute [scoped simp] Int.neg_mul Int.pow_zero Int.pow_succ

scoped macro "arithmetic" : tactic => `(tactic| first | done | simp +arith)

abbrev Set (U : Type _) := U → Prop

instance (U : Type _) : Membership U (Set U) := ⟨(· ·)⟩

instance (U : Type _) : HasSubset (Set U) := ⟨fun A B => ∀ (x : U), x ∈ A → x ∈ B⟩

instance (U : Type _) : Union (Set U) := ⟨fun A B x => x ∈ A ∨ x ∈ B⟩

instance (U : Type _) : Inter (Set U) := ⟨fun A B x => x ∈ A ∧ x ∈ B⟩

instance (U : Type _) : SDiff (Set U) := ⟨fun A B x => x ∈ A ∧ x ∉ B⟩

instance (U : Type _) : EmptyCollection (Set U) := ⟨fun _ => False⟩

instance (U : Type _) : Singleton U (Set U) where
  singleton x y := y = x

instance (U : Type _) : Insert U (Set U) where
  insert a A x := x = a ∨ x ∈ A

protected theorem Subset.def {U : Type _} (A B : Set U) : A ⊆ B ↔ ∀ (x : U), x ∈ A → x ∈ B := .rfl

protected theorem Inter.def {U : Type _} (A B : Set U) (x : U) : x ∈ A ∩ B ↔ x ∈ A ∧ x ∈ B := .rfl

protected theorem Union.def {U : Type _} (A B : Set U) (x : U) : x ∈ A ∪ B ↔ x ∈ A ∨ x ∈ B := .rfl

protected theorem SDiff.def {U : Type _} (A B : Set U) (x : U) : x ∈ A \ B ↔ x ∈ A ∧ x ∉ B := .rfl

protected theorem Empty.def {U : Type _} (x : U) : x ∈ (∅ : Set U) ↔ False := .rfl

protected theorem Empty.forall {U : Type _} (P : U → Prop) : (∀ x, x ∈ (∅ : Set U) → P x) ↔ True := by
  simp [Empty.def]

protected theorem Empty.exists {U : Type _} (P : U → Prop) : (∃ x, x ∈ (∅ : Set U) ∧ P x) ↔ False := by
  simp [Empty.def]

protected theorem Singleton.def {U : Type _} (a x : U) : x ∈ (singleton a : Set U) ↔ x = a := .rfl

protected theorem Singleton.forall {U : Type _} (a : U) (P : U → Prop) :
    (∀ x, x ∈ (singleton a : Set U) → P x) ↔ P a := by
  constructor
  · intro h; exact h a rfl
  · intro | h, _, rfl => exact h

protected theorem Singleton.exists {U : Type _} (a : U) (P : U → Prop) :
    (∃ x, x ∈ (singleton a : Set U) ∧ P x) ↔ P a := by
  constructor
  · intro | ⟨_, rfl, h⟩ => exact h
  · intro h; exists a

protected theorem Insert.def {U : Type _} (A : Set U) (a x : U) : x ∈ insert a A ↔ x = a ∨ x ∈ A := .rfl

protected theorem Insert.forall {U : Type _} (A : Set U) (a : U) (P : U → Prop) :
    (∀ x, x ∈ insert a A → P x) ↔ P a ∧ (∀ x, x ∈ A → P x) := by
  constructor
  · intro h
    constructor
    · apply h
      simp [insert]
      left
      rfl
    · intro x hx
      apply h
      simp [insert]
      right
      exact hx
  · intro ⟨ha, h⟩ x hx
    simp [insert] at hx
    match hx with
    | .inl rfl => exact ha
    | .inr hx => apply h; exact hx

protected theorem Insert.exists {U : Type _} (A : Set U) (a : U) (P : U → Prop) :
    (∃ x, x ∈ insert a A ∧ P x) ↔ P a ∨ (∃ x, x ∈ A ∧ P x) := by
  constructor
  · intro ⟨x, hx, h⟩
    match hx with
    | .inl rfl => left; exact h
    | .inr hx => right; exists x
  · intro h
    match h with
    | .inl ha =>
      exists a
      constructor
      · left; rfl
      · exact ha
    | .inr ⟨x, hx, h⟩ =>
      exists x
      constructor
      · right; exact hx
      · exact h

def setOf {U : Type _} (P : U → Prop) : Set U := P

protected theorem SetOf.def {U : Type} (P : U → Prop) (x : U) : x ∈ setOf P ↔ P x := .rfl

def Dom {U V : Type _} (R : Set (U × V)) : Set U := setOf fun x : U => ∃ (y : V), (x, y) ∈ R

def Ran {U V : Type _} (R : Set (U × V)) : Set V := setOf fun y : V => ∃ (x : U), (x, y) ∈ R

macro_rules
| `(tactic| unfold Subset $[$loc:location]?) => `(tactic| simp only [Subset.def] $[$loc]?)
| `(tactic| unfold Inter $[$loc:location]?) => `(tactic| simp only [Inter.def] $[$loc]?)
| `(tactic| unfold Union $[$loc:location]?) => `(tactic| simp only [Union.def] $[$loc]?)
| `(tactic| unfold SDiff $[$loc:location]?) => `(tactic| simp only [SDiff.def] $[$loc]?)
| `(tactic| unfold Empty $[$loc:location]?) => `(tactic| simp only [Empty.def] $[$loc]?)
| `(tactic| unfold SetOf $[$loc:location]?) => `(tactic| simp only [SetOf.def] $[$loc]?)
| `(tactic| unfold Enum $[$loc:location]?) =>
  `(tactic|
      (try simp only [Insert.forall, Insert.exists,
        Singleton.forall, Singleton.exists,
        Empty.forall, Empty.exists, -eq_self] $[$loc]?) <;>
      (try simp only [Insert.def, Singleton.def, Empty.def, -eq_self] $[$loc]?))

syntax (name := setBuilder) "{" Batteries.ExtendedBinder.extBinder " | " term "}" : term

@[term_elab setBuilder]
def elabSetBuilder : Lean.Elab.Term.TermElab
  | `({ $x:ident | $p }), expectedType? => do
    Lean.Elab.Term.elabTerm (← `(setOf fun $x:ident ↦ $p)) expectedType?
  | `({ $x:ident : $t | $p }), expectedType? => do
    Lean.Elab.Term.elabTerm (← `(setOf fun $x:ident : $t ↦ $p)) expectedType?
  | `({ $x:ident $b:binderPred | $p }), expectedType? => do
    Lean.Elab.Term.elabTerm (← `(setOf fun $x:ident ↦ satisfies_binder_pred% $x $b ∧ $p)) expectedType?
  | _, _ => Lean.Elab.throwUnsupportedSyntax

@[app_unexpander setOf]
def setOf.unexpander : Lean.PrettyPrinter.Unexpander
  | `($_ fun $x:ident ↦ $p) => `({ $x:ident | $p })
  | `($_ fun ($x:ident : $ty:term) ↦ $p) => `({ $x:ident : $ty:term | $p })
  | _ => throw ()
