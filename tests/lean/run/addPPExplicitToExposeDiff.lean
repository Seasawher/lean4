/-!
# Tests of `addPPExplicitToExposeDiff`
-/
set_option pp.mvars false

/-!
Basic example.
-/
/--
error: type mismatch
  rfl
has type
  ?_ = ?_ : Prop
but is expected to have type
  1 = 2 : Prop
-/
#guard_msgs in example : 1 = 2 := by
  exact rfl


/-!
Error message shouldn't fake a higher-order unification. This next one used to give
```
  type mismatch
    test n2 ?_
  has type
    (fun x ↦ x * 2) (g2 n2) = n2 : Prop
  but is expected to have type
    (fun x ↦ x * 2) (g2 n2) = n2 : Prop
```
It now doesn't for the stronger reason that we don't let `addPPExplicitToExposeDiff` have side effects,
but still it avoids doing incorrect higher-order unifications in its reasoning.
-/

theorem test {f g : Nat → Nat} (n : Nat) (hfg : ∀ a, f (g a) = a) :
    f (g n) = n := hfg n

/--
error: type mismatch
  test n2 ?_
has type
  ?_ (?_ n2) = n2 : Prop
but is expected to have type
  (fun x => x * 2) (g2 n2) = n2 : Prop
-/
#guard_msgs in
example {g2 : Nat → Nat} (n2 : Nat) : (fun x => x * 2) (g2 n2) = n2 := by
  with_reducible refine test n2 ?_


/-!
Exposes an implicit argument because the explicit arguments can be unified.
-/
def f {a : Nat} (b : Nat) : Prop := a + b = 0
/--
error: type mismatch
  sorry
has type
  @f 0 ?_ : Prop
but is expected to have type
  @f 1 2 : Prop
-/
#guard_msgs in
example : @f 1 2 := by
  exact (sorry : @f 0 _)

/-!
Add type ascriptions for numerals if they have different types.
-/
/--
error: type mismatch
  Eq.refl 0
has type
  (0 : Int) = 0 : Prop
but is expected to have type
  (0 : Nat) = 0 : Prop
-/
#guard_msgs in example : 0 = (0 : Nat) := by
  exact Eq.refl (0 : Int)

-- Even if the numerals are different.
/--
error: type mismatch
  Eq.refl 1
has type
  (1 : Int) = 1 : Prop
but is expected to have type
  (0 : Nat) = 0 : Prop
-/
#guard_msgs in example : 0 = (0 : Nat) := by
  exact Eq.refl (1 : Int)

-- Even for numerals that are functions
section
local instance {α : Type _} [OfNat β n] : OfNat (α → β) n where
  ofNat := fun _ => OfNat.ofNat n
/--
error: type mismatch
  Eq.refl (0 1)
has type
  (0 : Nat → Int) 1 = 0 1 : Prop
but is expected to have type
  (0 : Nat → Nat) 1 = 0 1 : Prop
-/
#guard_msgs in example : (0 : Nat → Nat) 1 = (0 : Nat → Nat) 1 := by
  exact Eq.refl ((0 : Nat → Int) 1)
end
