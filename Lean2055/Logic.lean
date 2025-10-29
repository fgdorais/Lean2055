/- Copyright 2025 François G. Dorais -/
import Lean2055.Basic
import Lean2055.TruthTable

namespace Lean2055

scoped infix:15 " ≡ " => Eq

/-! # Common Logical Equivalences -/

/-! ## Commutative Laws -/

theorem and_comm (A B : Prop) : A ∧ B ≡ B ∧ A := by truth_table [A, B]

theorem or_comm (A B : Prop) : A ∨ B ≡ B ∨ A := by truth_table [A, B]

/-! ## Associative Laws -/

theorem and_assoc (A B C : Prop) : (A ∧ B) ∧ C ≡ A ∧ (B ∧ C) := by truth_table [A, B, C]

theorem or_assoc (A B C : Prop) : (A ∨ B) ∨ C ≡ A ∨ (B ∨ C) := by truth_table [A, B, C]

/-! ## Idempotent Laws -/

theorem and_idem (A : Prop) : A ∧ A ≡ A := by truth_table [A]

theorem or_idem (A : Prop) : A ∨ A ≡ A := by truth_table [A]

/-! ## Absorption Laws -/

theorem or_absorb_left (A B : Prop) : A ∨ (A ∧ B) ≡ A := by truth_table [A, B]

theorem and_absorb_left (A B : Prop) : A ∧ (A ∨ B) ≡ A := by truth_table [A, B]

theorem or_absorb_right (A B : Prop) : (A ∧ B) ∨ B ≡ B := by truth_table [A, B]

theorem and_absorb_right (A B : Prop) : (A ∨ B) ∧ B ≡ B := by truth_table [A, B]

/-! ## Distributive Laws -/

theorem and_distrib_left (A B C : Prop) : A ∧ (B ∨ C) ≡ (A ∧ B) ∨ (A ∧ C) := by truth_table [A, B, C]

theorem or_distrib_left (A B C : Prop) : A ∨ (B ∧ C) ≡ (A ∨ B) ∧ (A ∨ C) := by truth_table [A, B, C]

theorem and_distrib_right (A B C : Prop) : (A ∨ B) ∧ C ≡ (A ∧ C) ∨ (B ∧ C) := by truth_table [A, B, C]

theorem or_distrib_right (A B C : Prop) : (A ∧ B) ∨ C ≡ (A ∨ C) ∧ (B ∨ C) := by truth_table [A, B, C]

/-! ## DeMorgan Laws -/

theorem and_deMorgan (A B : Prop) : ¬(A ∧ B) ≡ ¬A ∨ ¬B := by truth_table [A, B]

theorem or_deMorgan (A B : Prop) : ¬(A ∨ B) ≡ ¬A ∧ ¬B := by truth_table [A, B]

theorem forall_deMorgan {U : Type _} (A : U → Prop) : ¬(∀ (x : U), A x) ≡ ∃ (x : U), ¬ A x := propext <| Classical.not_forall ..

theorem exists_deMorgan {U : Type _} (A : U → Prop) : ¬(∃ (x : U), A x) ≡ ∀ (x : U), ¬ A x := propext <| not_exists ..

/-! ## Implication Laws -/

theorem not_or (A B : Prop) : ¬A ∨ B ≡ A → B := by truth_table [A, B]

theorem and_not (A B : Prop) : A ∧ ¬B ≡ ¬(A → B) := by truth_table [A, B]

theorem not_imp_not (A B : Prop) : ¬A → ¬B ≡ B → A := by truth_table [A, B]

theorem not_imp (A B : Prop) : ¬A → B ≡ ¬B → A := by truth_table [A, B]

theorem imp_not (A B : Prop) : A → ¬B ≡ B → ¬A := by truth_table [A, B]

theorem imp_and_imp (A B : Prop) : (A → B) ∧ (B → A) ≡ A ↔ B := by truth_table [A, B]

theorem imp_self (A : Prop) : A → A ≡ True := by truth_table [A]

/-! ## Tautology Laws -/

theorem and_true (A : Prop) : A ∧ True ≡ A := by truth_table [A]

theorem or_true (A : Prop) : A ∨ True ≡ True := by truth_table [A]

theorem true_and (A : Prop) : True ∧ A ≡ A := by truth_table [A]

theorem true_or (A : Prop) : True ∨ A ≡ True := by truth_table [A]

theorem true_imp (A : Prop) : True → A ≡ A := by truth_table [A]

theorem imp_true (A : Prop) : A → True ≡ True := by truth_table [A]

/-! ## Contradiction Laws -/

theorem and_false (A : Prop) : A ∧ False ≡ False := by truth_table [A]

theorem or_false (A : Prop) : A ∨ False ≡ A := by truth_table [A]

theorem false_and (A : Prop) : False ∧ A ≡ False := by truth_table [A]

theorem false_or (A : Prop) : False ∨ A ≡ A := by truth_table [A]

theorem false_imp (A : Prop) : False → A ≡ True := by truth_table [A]

theorem imp_false (A : Prop) : A → False ≡ ¬A := by truth_table [A]

/-! ## Negation Laws -/

theorem not_true : ¬True ≡ False := by truth_table []

theorem not_false : ¬False ≡ True := by truth_table []

theorem not_not (A : Prop) : ¬¬A ≡ A := by truth_table [A]

theorem and_not_self (A : Prop) : A ∧ ¬A ≡ False := by truth_table [A]

theorem or_not_self (A : Prop) : A ∨ ¬A ≡ True := by truth_table [A]

theorem not_and_self (A : Prop) : ¬A ∧ A ≡ False := by truth_table [A]

theorem not_or_self (A : Prop) : ¬A ∨ A ≡ True := by truth_table [A]
