import Batteries

namespace Lean2055

scoped notation "ℕ" => Nat
scoped notation "ℤ" => Int
scoped notation "ℚ" => Rat

attribute [scoped simp ←] Nat.mul_assoc Nat.add_assoc
attribute [scoped simp] Nat.add_mul Nat.mul_add
attribute [scoped simp] Nat.mul_right_comm
attribute [scoped simp] Nat.pow_zero Nat.pow_succ

attribute [scoped simp ←] Int.mul_assoc Int.add_assoc
attribute [scoped simp] Int.add_mul Int.mul_add
attribute [scoped simp] Int.mul_right_comm
attribute [scoped simp] Int.neg_mul Int.pow_zero Int.pow_succ

scoped macro "arithmetic" : tactic => `(tactic| first | done | simp +arith)
