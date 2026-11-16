/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini

Only the permanent-bound definition is extracted from CountingCone.Defs.
The unrelated Steiner-system definitions are not needed in this project.
-/
module

public import Mathlib

@[expose] public section

namespace STS

def vdWPC : Prop :=
  ∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ), M ∈ doublyStochastic ℝ (Fin n) →
    (Nat.factorial n : ℝ) / (n : ℝ) ^ n ≤ M.permanent

end STS
