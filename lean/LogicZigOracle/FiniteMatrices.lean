/-!
Lean oracle definitions for the finite logical matrices implemented by
`src/logic/manyvalued.zig`.

This file deliberately uses only Lean's kernel and core library. Every theorem
is closed by an explicit proof term or kernel-reduced computation.
-/

namespace LogicZigOracle.FiniteMatrices

inductive Tri where
  | false_ | middle | true_
  deriving DecidableEq, Repr

def triNot : Tri → Tri
  | .false_ => .true_
  | .middle => .middle
  | .true_ => .false_

def triAnd : Tri → Tri → Tri
  | .false_, _ => .false_
  | _, .false_ => .false_
  | .middle, _ => .middle
  | _, .middle => .middle
  | .true_, .true_ => .true_

def triOr : Tri → Tri → Tri
  | .true_, _ => .true_
  | _, .true_ => .true_
  | .middle, _ => .middle
  | _, .middle => .middle
  | .false_, .false_ => .false_

def materialImp (a b : Tri) : Tri := triOr (triNot a) b

def k3Designated : Tri → Bool
  | .true_ => true
  | _ => false

def lpDesignated : Tri → Bool
  | .false_ => false
  | _ => true

theorem k3_excluded_middle_counterexample :
    k3Designated (triOr .middle (triNot .middle)) = false := rfl

theorem k3_reflexive_material_implication_counterexample :
    k3Designated (materialImp .middle .middle) = false := rfl

theorem lp_excluded_middle_designated :
    lpDesignated (triOr .middle (triNot .middle)) = true := rfl

theorem lp_explosion_counterexample :
    lpDesignated .middle = true ∧
    lpDesignated (triNot .middle) = true ∧
    lpDesignated .false_ = false := by
  exact ⟨rfl, rfl, rfl⟩

def triOfBool : Bool → Tri
  | false => .false_
  | true => .true_

theorem tri_not_preserves_boolean (a : Bool) :
    triNot (triOfBool a) = triOfBool (!a) := by
  cases a <;> rfl

theorem tri_and_preserves_boolean (a b : Bool) :
    triAnd (triOfBool a) (triOfBool b) = triOfBool (a && b) := by
  cases a <;> cases b <;> rfl

theorem tri_or_preserves_boolean (a b : Bool) :
    triOr (triOfBool a) (triOfBool b) = triOfBool (a || b) := by
  cases a <;> cases b <;> rfl

structure Fde where
  truth : Bool
  falsity : Bool
  deriving DecidableEq, Repr

def fdeFalse : Fde := ⟨false, true⟩
def fdeNeither : Fde := ⟨false, false⟩
def fdeBoth : Fde := ⟨true, true⟩
def fdeTrue : Fde := ⟨true, false⟩

def fdeNot (a : Fde) : Fde := ⟨a.falsity, a.truth⟩
def fdeAnd (a b : Fde) : Fde := ⟨a.truth && b.truth, a.falsity || b.falsity⟩
def fdeOr (a b : Fde) : Fde := ⟨a.truth || b.truth, a.falsity && b.falsity⟩
def fdeDesignated (a : Fde) : Bool := a.truth

theorem fde_neither_excluded_middle_counterexample :
    fdeDesignated (fdeOr fdeNeither (fdeNot fdeNeither)) = false := rfl

theorem fde_explosion_counterexample :
    fdeDesignated fdeBoth = true ∧
    fdeDesignated (fdeNot fdeBoth) = true ∧
    fdeDesignated fdeFalse = false := by
  exact ⟨rfl, rfl, rfl⟩

inductive L3 where
  | zero | half | one
  deriving DecidableEq, Repr

def l3Not : L3 → L3
  | .zero => .one
  | .half => .half
  | .one => .zero

def l3Imp : L3 → L3 → L3
  | .zero, _ => .one
  | .half, .zero => .half
  | .half, _ => .one
  | .one, b => b

def l3Or : L3 → L3 → L3
  | .one, _ => .one
  | _, .one => .one
  | .half, _ => .half
  | _, .half => .half
  | .zero, .zero => .zero

def l3Designated : L3 → Bool
  | .one => true
  | _ => false

theorem l3_reflexive_implication_designated (a : L3) :
    l3Designated (l3Imp a a) = true := by
  cases a <;> rfl

theorem l3_excluded_middle_counterexample :
    l3Designated (l3Or .half (l3Not .half)) = false := rfl

end LogicZigOracle.FiniteMatrices
