/- Copyright 2025 François G. Dorais -/
import Lean2055.Basic

namespace Lean2055

scoped syntax "truth_table" colGt "["term,*"]" : tactic

macro_rules
  | `(tactic| truth_table []) =>
    `(tactic| simp [*])
  | `(tactic| truth_table [$p]) =>
    `(tactic| cases Classical.propComplete $p <;> truth_table [])
  | `(tactic| truth_table [$p, $ps,*]) =>
    `(tactic| cases Classical.propComplete $p <;> truth_table [$ps,*])
