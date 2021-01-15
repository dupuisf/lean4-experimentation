/-
Copyright (c) 2021 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/

/-
This is a test to see if we can register as an instance the fact that `semimodule 𝕜 E` implies `semimodule ℝ E`
for `is_R_or_C 𝕜` in Lean 4. It looks like we can.
-/

class Smul (α : Type u) (β : Type v) where
    smul : α → β → β

infixl:80 "•" => Smul.smul

instance : Smul Nat Int where
    smul := fun x y => (x : Int) * y

instance SmulSelf {α : Type u} [Mul α] : Smul α α where
    smul := fun x y => x * y

class is_N_or_Z (𝕜 : Type u) [Add 𝕜] [Mul 𝕜] where
    ofNat : Nat → 𝕜
    neg : 𝕜 → 𝕜

instance : is_N_or_Z Nat where
    ofNat := id
    neg := id

instance : is_N_or_Z Int where
    ofNat := Coe.coe
    neg := Int.neg

variables {𝕜 : Type u} [Add 𝕜] [Mul 𝕜] [is_N_or_Z 𝕜]

instance (n : Nat) : OfNat 𝕜 n where
    ofNat := (is_N_or_Z.ofNat n)

instance SmulNK : Smul Nat 𝕜 where
    smul := fun r x => (is_N_or_Z.ofNat r) * x

--#check (show Smul Nat Nat from inferInstance)

variables {E : Type u} [Smul 𝕜 E]
  
instance SmulTrans : Smul Nat E where
    smul := fun r x => ((is_N_or_Z.ofNat r) : 𝕜) • x

#check (show Smul Nat E from inferInstance)  -- also fine in Lean 3
#check (show Smul Nat Nat from inferInstance)  -- In Lean 3: breakage ("maximum class-instance resolution depth blabla")