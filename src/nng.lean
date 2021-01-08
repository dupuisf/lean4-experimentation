/-
Natural number game on hard mode
-/

/- definition.lean -/

inductive mynat where
| zero : mynat
| succ (n : mynat) : mynat

notation "ℕ" => mynat  -- The one benefit of playing this game in Lean 4

namespace mynat

def FromNat (n : Nat) : ℕ := match n with
| Nat.zero      => mynat.zero
| Nat.succ k    => mynat.succ $ FromNat k

instance : OfNat ℕ n where
    ofNat := FromNat n

theorem OneEqSuccZero : (1 : ℕ) = succ 0 := rfl

theorem ZeroNeSucc (m : ℕ) : (0 : ℕ) ≠ succ m := fun h => by cases h

theorem SuccInj {m n : ℕ} (h : succ m = succ n) : m = n := by cases h; rfl

/- add.lean -/

def add : ℕ → ℕ → ℕ
| m, 0          => m
| m, (succ n)   => succ (add m n)

instance : Add ℕ where
    add := mynat.add

theorem AddZero (m : ℕ) : m + 0 = m := rfl
theorem AddZero' (m : ℕ) : m + zero = m := rfl

theorem AddSucc (m n : ℕ) : m + succ n = succ (m + n) := rfl

/- mul.lean -/

def mul : ℕ → ℕ → ℕ
| m, zero   => zero
| m, succ n => mul m n + m

instance : Mul ℕ := ⟨mynat.mul⟩

theorem MulZero (m : ℕ) : m * 0 = 0 := rfl
theorem MulZero' (m : ℕ) : m * zero = zero := rfl

theorem MulSucc (m n : ℕ) : m * (succ n) = m * n + m := rfl

/- pow.lean -/

def pow : ℕ → ℕ → ℕ
| m, zero   => 1
| m, succ n => pow m n * m

instance : Pow ℕ := ⟨mynat.pow⟩

theorem PowZero (m : ℕ) : m ^ 0 = 1 := rfl
theorem PowZero' (m : ℕ) : m ^ zero = 1 := rfl

theorem PowSucc (m n : ℕ) : m ^ (succ n) = m ^ n * m := rfl

/- le.lean -/

def le (a b : ℕ) := ∃ (c : ℕ), b = a + c

instance : HasLessEq ℕ := ⟨mynat.le⟩

theorem LeIffExistsAdd (a b : ℕ) : a ≤ b ↔ ∃ (c : ℕ), b = a + c := Iff.rfl

/- lt.lean (?) -/

def lt (a b : ℕ) := a ≤ b ∧ ¬ (b ≤ a)

instance : HasLess ℕ := ⟨mynat.lt⟩

/- Tutorial world -/
theorem example1 (x y z : ℕ) : x * y + z = x * y + z := rfl

theorem example2 (x y : ℕ) (h : y = x + 7) : 2 * y = 2 * (x + 7) := by rw h

theorem example3 (a b : ℕ) (h : succ a = b) : succ (succ a) = succ b := by rw h

theorem AddSuccZero (a : ℕ) : a + succ 0 = succ a := AddSucc a 0

/- Addition world -/

theorem ZeroAdd (n : ℕ) : 0 + n = n := match n with
| zero      => rfl
| succ k    => by rw [AddSucc, ZeroAdd]

theorem ZeroAdd' (n : ℕ) : zero + n = n := ZeroAdd n

theorem AddAssoc (a b c : ℕ) : (a + b) + c = a + (b + c) := match c with
| zero      => rfl
| succ k    => by rw [AddSucc, AddSucc, AddAssoc, AddSucc]

theorem SuccAdd (a b : ℕ) : succ a + b = succ (a + b) := match b with
| zero      => by rw [AddZero', AddZero']
| succ k    => by rw [AddSucc, AddSucc, SuccAdd]

theorem AddComm (a b : ℕ) : a + b = b + a := match b with
| zero      => by rw [AddZero', ZeroAdd']
| succ k    => by rw [AddSucc, SuccAdd, AddComm]

theorem SuccEqAddOne (n : ℕ) : succ n = n + 1 := rfl

theorem AddRightComm (a b c : ℕ) : a + b + c = a + c + b := by rw [AddAssoc, AddComm b c, AddAssoc]

/- Multiplication world -/

theorem ZeroMul (m : ℕ) : 0 * m = 0 := match m with
| zero      => rfl
| succ k    => by rw [MulSucc, AddZero, ZeroMul]
theorem ZeroMul' (m : ℕ) : zero * m = zero := ZeroMul m

theorem MulOne (m : ℕ) : m * 1 = m := match m with
| zero      => rfl
| succ k    => by rw [OneEqSuccZero, MulSucc, MulZero, ZeroAdd]


theorem OneMul (m : ℕ) : 1 * m = m := match m with
| zero      => rfl
| succ k    => by rw [MulSucc, OneMul, SuccEqAddOne] 

theorem MulAdd (t a b: ℕ) : t * (a + b) = t * a + t * b := match a with
| zero      => by rw [ZeroAdd', MulZero', ZeroAdd']
| succ k    => by rw [SuccAdd, MulSucc, MulSucc, MulAdd, AddAssoc, AddComm (t*b) t, AddAssoc]

theorem MulAssoc (a b c : ℕ) : (a * b) * c = a * (b * c) := match c with
| zero      => rfl
| succ k    => by rw [MulSucc, MulSucc, MulAdd, MulAssoc]

theorem SuccMul (a b : ℕ) : succ a * b = a * b + b := match b with
| zero      => rfl
| succ k    => by rw [MulSucc, MulSucc, SuccMul, AddAssoc, AddSucc, AddComm k a, ←AddSucc, AddAssoc]

theorem AddMul (a b t : ℕ) : (a + b) * t = a * t + b * t := match t with
| zero      => rfl
| succ k    => by rw [MulSucc, MulSucc, MulSucc, AddMul, AddAssoc, AddComm (b*k) (a+b), AddComm (b*k) b, AddAssoc a b (b*k), AddAssoc]

theorem MulComm (a b : ℕ) : a * b = b * a := match b with
| zero      => by rw [MulZero', ZeroMul']
| succ k    => by rw [MulSucc, SuccMul, MulComm]

theorem MulLeftComm (a b c : ℕ) : a * (b * c) = b * (a * c) := by rw [←MulAssoc a b c, MulComm a b, MulAssoc]

/- Power world -/

theorem ZeroPowZero : (0 : ℕ) ^ (0 : ℕ) = 1 := PowZero 0

theorem ZeroPowSucc (m : ℕ) : (0 : ℕ) ^ (succ m) = 0 := by rw [PowSucc, MulZero]

theorem PowOne (a : ℕ) : a ^ (1 : ℕ) = a := by rw [OneEqSuccZero, PowSucc, PowZero, OneMul]

theorem OnePow (m : ℕ) : (1 : ℕ) ^ m = 1 := match m with
| zero      => rfl
| succ k    => by rw [PowSucc, MulOne, OnePow]

theorem PowAdd (a m n : ℕ) : a ^ (m + n) = a ^ m * a ^ n := match n with
| zero      => by rw [AddZero', PowZero', MulOne]
| succ k    => by rw [PowSucc, AddSucc, PowSucc, ←MulAssoc, PowAdd]

theorem MulPow (a b n : ℕ) : (a * b) ^ n = a ^ n * b ^ n := match n with
| zero      => rfl
| succ k    => by rw [PowSucc, PowSucc, PowSucc, MulPow, MulAssoc, ←MulAssoc (b^k) a b, MulComm (b^k) a, MulAssoc (a^k) a, MulAssoc a]

theorem PowPow (a m n : ℕ) : (a ^ m) ^ n = a ^ (m * n) := match n with
| zero      => rfl
| succ k    => by rw [PowSucc, PowPow, ←PowAdd, MulSucc]

theorem PowTwoEqMulSelf (a : ℕ) : a^(2 : ℕ) = a * a := by { have h₁ : (2 : ℕ) = 1 + 1 := rfl; simp [h₁, PowAdd, PowOne] }

theorem TwoMulEqAddSelf (a : ℕ) : (2 : ℕ) * a = a + a := by { have h₁ : (2 : ℕ) = 1 + 1 := rfl; simp [h₁, AddMul, OneMul] }

theorem AddSquared (a b : ℕ) : (a + b) ^ 2 = a ^ 2 + b ^ 2 + 2 * a * b := by 
    rw [PowTwoEqMulSelf, PowTwoEqMulSelf, PowTwoEqMulSelf, AddMul, MulAdd, TwoMulEqAddSelf, AddMul, MulAdd]
    rw [AddAssoc, AddComm (a*b), AddComm (b*a), MulComm b a, AddAssoc (b*b), AddAssoc]

/- Advanced Addition World -/

theorem SuccInj' {a b : ℕ} (hs : succ a = succ b) : a = b := SuccInj hs

theorem SuccSuccInj {a b : ℕ} (h : succ (succ a) = succ (succ b)) : a = b := SuccInj $ SuccInj h

theorem SuccEqSuccOfEq {a b : ℕ} : a = b → succ a = succ b := fun h => by rw [h]

theorem EqIffSuccEqSucc (a b : ℕ) : succ a = succ b ↔ a = b := Iff.intro (fun h => SuccInj' h) (fun h => SuccEqSuccOfEq h)

theorem AddRightCancel (a t b : ℕ) : a + t = b + t → a = b := fun h => by induction t with
| zero        => rw [AddZero', AddZero'] at h; exact h
| succ k ih   => rw [AddSucc, AddSucc] at h; exact ih $ SuccInj' h

theorem AddLeftCancel (t a b : ℕ) : t + a = t + b → a = b := fun h => by induction t with
| zero          => rw [ZeroAdd', ZeroAdd'] at h;  exact h
| succ k ih     => rw [SuccAdd, SuccAdd] at h; exact ih $ SuccInj h 

theorem AddRightCancelIff (t a b: ℕ) : a + t = b + t ↔ a = b := Iff.intro (AddRightCancel a t b) (fun h => by rw [h])

theorem EqZeroOfAddRightEqSelf {a b : ℕ} : a + b = a → b = 0 := fun h => by
    have h' : a + b = a + 0 := by rw [AddZero, h]
    exact AddLeftCancel a b 0 h'

theorem SuccNeZero (a : ℕ) : succ a ≠ 0 := (ZeroNeSucc a).symm

theorem AddLeftEqZero {a b : ℕ} (H : a + b = 0) : b = 0 := by cases b with
| zero      => rfl
| succ b'   => rw [AddSucc] at H; exact False.elim $ SuccNeZero _ H

theorem AddRightEqZero {a b : ℕ} : a + b = 0 → a = 0 := fun H => by cases a with
| zero      => rfl
| succ b'   => rw [SuccAdd] at H; exact False.elim $ SuccNeZero _ H

theorem AddOneEqSucc (d : ℕ) : d + 1 = succ d := rfl

theorem NeSuccSelf (n : ℕ) : n ≠ succ n := by induction n with
| zero      => exact mynat.noConfusion
| succ k ih => intro h; exact ih $ SuccInj' h


/- Advanced Multiplication World -/

theorem EqSuccOfNonzero {a : ℕ} : a ≠ 0 → ∃ a' : ℕ, a = succ a' := match a with
| zero        => fun ha => False.elim (ha rfl)
| succ k      => fun _ => ⟨k, rfl⟩

theorem MulPos {a b : ℕ} : a ≠ 0 → b ≠ 0 → a * b ≠ 0 := match a with
| zero      => fun ha _ _ => ha rfl
| succ a'   => match b with
    | zero      => fun _ hb _ => hb rfl
    | succ b'   => fun _ _ hab => mynat.noConfusion hab

-- This doesn't work with `match ... with` for some reason
theorem EqZeroOrEqZeroOfMulEqZero {a b : ℕ} (h : a*b = 0) : a = 0 ∨ b = 0 := by cases a with
| zero      => exact Or.inl rfl
| succ a'   => cases b with
    | zero      => exact Or.inr rfl
    | succ b'   => exact False.elim $ MulPos (SuccNeZero a') (SuccNeZero b') h

theorem MulEqZeroIff (a b : ℕ) : a * b = 0 ↔ a = 0 ∨ b = 0 := Iff.intro EqZeroOrEqZeroOfMulEqZero $ fun h => by cases h with
| Or.inl ha => rw [ha, ZeroMul]
| Or.inr hb => rw [hb, MulZero]

theorem MulLeftCancel (a b c : ℕ) (ha : a ≠ 0) : a * b = a * c → b = c := sorry

/- Inequality world -/

theorem OneAddLeSelf (x : ℕ) : x ≤ (1 : ℕ) + x := by { rw [LeIffExistsAdd]; exact ⟨1, AddComm 1 x⟩ }

theorem LeRefl (x : ℕ) : x ≤ x := by { rw [LeIffExistsAdd]; exact ⟨0, AddZero x⟩ }

theorem LeSucc (a b : ℕ) : a ≤ b → a ≤ (succ b) := fun h => by
    rw [LeIffExistsAdd] at h
    cases h with | Exists.intro x hx => { rw [hx, LeIffExistsAdd]; exact ⟨succ x, by rw [AddSucc]⟩ }

theorem ZeroLe (a : ℕ) : 0 ≤ a := by
    induction a with
    | zero     => exact LeRefl 0
    | succ k   => { apply LeSucc; assumption }

theorem LeTrans (a b c : ℕ) (hab : a ≤ b) (hbc : b ≤ c) : a ≤ c := by
    rw [LeIffExistsAdd] at hab
    rw [LeIffExistsAdd] at hbc
    cases hab with | Exists.intro x hx =>
    cases hbc with | Exists.intro y hy =>
        rw [hy, hx, AddAssoc]
        exact (LeIffExistsAdd _ _).mpr ⟨x+y, rfl⟩

theorem LeAntisymm (a b : ℕ) (hab : a ≤ b) (hba : b ≤ a) : a = b := by
    rw [LeIffExistsAdd] at hab
    rw [LeIffExistsAdd] at hba
    cases hab with | Exists.intro x hx =>
    cases hba with | Exists.intro y hy =>
    rw [hx, AddAssoc] at hy
    have h := EqZeroOfAddRightEqSelf hy.symm
    have hx' : x = 0 := AddRightEqZero h
    rw [hx', AddZero] at hx
    exact hx.symm

theorem LeZero (a : ℕ) (h : a ≤ 0) : a = 0 := by cases a with
| zero      => rfl
| succ k    => exact LeAntisymm _ _ h $ ZeroLe _

theorem SuccLeSucc (a b : ℕ) (h : a ≤ b) : succ a ≤ succ b := by
    rw [LeIffExistsAdd] at h
    cases h with | Exists.intro c hc =>
    rw [hc, LeIffExistsAdd]
    exact ⟨c, by rw [SuccAdd]⟩

theorem LeTotal (a b : ℕ) : a ≤ b ∨ b ≤ a := match a, b with
| zero,     zero        => Or.inl $ ZeroLe _
| succ a',  zero        => Or.inr $ ZeroLe _
| zero,     succ b'     => Or.inl $ ZeroLe _
| succ a',  succ b'     => by cases LeTotal a' b' with
    | Or.inl H => exact Or.inl $ SuccLeSucc a' b' H
    | Or.inr H => exact Or.inr $ SuccLeSucc b' a' H 

theorem LeSuccSelf (a : ℕ) : a ≤ succ a := LeSucc _ _ $ LeRefl _

theorem AddLeAddRight {a b : ℕ} : a ≤ b → ∀ t, (a + t) ≤ (b + t) := fun h t => by induction t with
| zero          => simp [AddZero', h]
| succ t' ht    => simp [AddSucc, SuccLeSucc _ _ ht]

theorem LeOfSuccLeSucc (a b : ℕ) : succ a ≤ succ b → a ≤ b := fun h => by
    rw [LeIffExistsAdd] at h;
    rw [LeIffExistsAdd];
    cases h with | Exists.intro x hx =>
    refine ⟨x, ?_⟩
    rw [SuccAdd] at hx
    exact SuccInj hx
    
theorem NotSuccLeSelf (a : ℕ) : ¬ (succ a ≤ a) := fun h => NeSuccSelf _ (LeAntisymm _ _ h (LeSucc a a $ LeRefl a)).symm

theorem AddLeAddLeft {a b : ℕ} (h : a ≤ b) (t : ℕ) : t + a ≤ t + b := by induction t with
| zero          => simp [ZeroAdd', h]
| succ k hk     => rw [SuccAdd, SuccAdd]; exact SuccLeSucc _ _ hk

theorem LtAuxOne (a b : ℕ) : a ≤ b ∧ ¬ (b ≤ a) → succ a ≤ b := sorry

theorem LtAuxTwo (a b : ℕ) : succ a ≤ b → a ≤ b ∧ ¬ (b ≤ a) := sorry

theorem LtIffSuccLe (a b : ℕ) : a < b ↔ succ a ≤ b := sorry
