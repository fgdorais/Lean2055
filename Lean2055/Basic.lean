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

protected theorem Subset.def {U : Type _} (A B : Set U) : A ⊆ B ↔ ∀ (x : U), x ∈ A → x ∈ B := .rfl

protected theorem Inter.def {U : Type _} (A B : Set U) (x : U) : x ∈ A ∩ B ↔ x ∈ A ∧ x ∈ B := .rfl

protected theorem Union.def {U : Type _} (A B : Set U) (x : U) : x ∈ A ∪ B ↔ x ∈ A ∨ x ∈ B := .rfl

protected theorem SDiff.def {U : Type _} (A B : Set U) (x : U) : x ∈ A \ B ↔ x ∈ A ∧ x ∉ B := .rfl

protected theorem Empty.def {U : Type _} (x : U) : x ∈ (∅ : Set U) ↔ False := .rfl

macro_rules
| `(tactic| unfold Subset $[$loc:location]?) => `(tactic| simp only [Subset.def] $[$loc]?)
| `(tactic| unfold Inter $[$loc:location]?) => `(tactic| simp only [Inter.def] $[$loc]?)
| `(tactic| unfold Union $[$loc:location]?) => `(tactic| simp only [Union.def] $[$loc]?)
| `(tactic| unfold SDiff $[$loc:location]?) => `(tactic| simp only [SDiff.def] $[$loc]?)
| `(tactic| unfold Empty $[$loc:location]?) => `(tactic| simp only [Empty.def] $[$loc]?)
