-- This is an abstract approach to simple row theory, which does not examine the internal structure of rows.

module

@[expose] public section

namespace Abstract

inductive Row where
-- There are countably many rows.
| mk : Nat -> Row
deriving Nonempty


deriving instance Nonempty for Row

noncomputable
opaque empty : Row
notation "{}" => empty


opaque disjoint : Row -> Row -> Prop

infix:90 " ⊥ " => disjoint

variable (a b c d : Row)


-- Might be better off including the well-definedness constraint as a precondition to theorems, a la denominator ≠ 0?
noncomputable
opaque concat (a b : Row) : Row

infixl:110 " ++ " => concat

axiom disjoint.implies_def : ∀ {a b : Row}, {_: a ⊥ b} -> Σ c, PLift (a ++ b = c)

-- Axioms
-- The axioms given here define simple row theory as a
-- *Partial Commutative Monoid*
-- https://ncatlab.org/nlab/show/effect+algebra#definition

@[simp]
axiom disjoint.zero : ∀ {a : Row}, {} ⊥ a
@[symm]
axiom disjoint.symm : ∀ {a b: Row}, a ⊥ b -> b ⊥ a

axiom concat.zero : ∀ {a : Row}, {} ++ a = a
axiom concat.symm : ∀ {a b : Row}, {_:a ⊥ b} -> a ++ b = b ++ a

-- Associativity is rephrased from the nlab version
-- y⊥z and x⊥(y∨z) implies x⊥y and (x∨y)⊥z and x∨(y∨z)=(x∨y)∨z.
axiom disjoint.assoc : ∀ {x y z : Row}, y ⊥ z -> x ⊥ (y ++ z) -> (x ++ y) ⊥ z
axiom disjoint.elim : ∀ {x y z : Row}, y ⊥ z -> x ⊥ (y ++ z) -> x ⊥ y
axiom concat.assoc : ∀ {x y z : Row}, y ⊥ z -> x ++ (y ++ z) = (x ++ y) ++ z

theorem disjoint.elim' : ∀ {x y z : Row}, x ⊥ y -> (x ++ y) ⊥ z -> y ⊥ z := by
  intro x y z h1 h2
  replace h2 := symm h2
  rw [concat.symm] at h2
  replace h1 := symm h1
  replace h2 := elim h1 h2
  apply h2.symm
  apply h1

theorem disjoint.elim_inner : ∀ {x y z : Row}, y ⊥ z -> x ⊥ (y ++ z) -> x ⊥ z := by
  intro x y z h1 h2
  replace h1 := disjoint.symm h1
  rw [concat.symm] at h2
  apply disjoint.elim h1 h2
  apply h1.symm

theorem disjoint.elim_inner' : ∀ {x y z : Row}, x ⊥ y -> (x ++ y) ⊥ z -> y ⊥ z := by
  intro x y z h1 h2
  replace h1 := disjoint.symm h1
  apply disjoint.elim' h1.symm h2


theorem disjoint.assoc' : ∀ {x y z : Row}, x ⊥ y -> (x ++ y) ⊥ z -> x ⊥ (y ++ z) := by
  intro x y z h1 h2
  have lem1 : y ⊥ z := by
    apply disjoint.elim_inner' h1 h2
  have lem2 : (z ++ y) ⊥ x := by
    rw [@concat.symm _ _ h1] at h2
    replace h2 := symm h2
    replace h1 := symm h1
    apply (disjoint.assoc h1 h2)
  replace lem2 := symm lem2
  rw [@concat.symm _ _ lem1.symm] at lem2
  exact lem2


-- Adding these two axioms makes SRT a
-- *Generalized Effect Algebra"
axiom cancellation : ∀ {a b c},
  a ⊥ b -> a ⊥ c -> (a ++ b) = (a ++ c) -> b = c
axiom positivity : ∀ a b, a ⊥ b -> (a ++ b) = {} -> a = {} ∧ b = {}

theorem positivityl : ∀ {a b}, a ⊥ b -> (a ++ b) = {} -> a = {} :=
  λ h1 h2 => (positivity _ _ h1 h2).left

theorem positivityr : ∀ {a b}, a ⊥ b -> (a ++ b) = {} -> b = {} :=
  λ h1 h2 => (positivity _ _ h1 h2).right

theorem positivity_a_eq_b : ∀ {a b}, a ⊥ b -> (a ++ b) = {} -> a = b :=
  λ h1 h2 => by
    rw [(positivity _ _ h1 h2).left, (positivity _ _ h1 h2).right]
    

@[simp]
theorem disjoint.zero_right : ∀ {a : Row}, a ⊥ {} := disjoint.zero.symm

@[simp]
theorem concat.zero_right : ∀ {a : Row}, a ++ {} = a :=
  λ {a} =>
  by
    rw [symm]
    apply zero
    apply disjoint.zero.symm

theorem concat.id_is_zero : ∀ {a b : Row}, a ⊥ b -> a ++ b = a -> b = {} :=
  λ {a b} h1 h2 =>
    by
      apply @cancellation a b {} h1 disjoint.zero_right
      rw [h2, concat.zero_right]

-- Consider lifting this to Sigma type so we can access the witness
def le (a c : Row): Prop := ∃ b, a ⊥ b ∧ (a ++ b) = c

instance : LE Row where
  le := le

@[refl]
theorem le.refl : ∀ {a : Row}, a ≤ a := ⟨{}, disjoint.zero.symm, concat.zero_right⟩

theorem le.bottom : ∀ {a : Row}, {} ≤ a := ⟨_, disjoint.zero, concat.zero⟩

theorem le.trans : ∀ {a b c : Row}, a ≤ b -> b ≤ c -> a ≤ c :=
  λ {a b c} a_b b_c =>
    match a_b, b_c with
    | ⟨ab', ab_disj, hab⟩, ⟨bc', bc_disj, hbc⟩ => by
      simp [(.≤.),le]
      exists ab' ++ bc'
      apply And.intro <;> rw [<-hab] at *
      apply @disjoint.assoc' _ _ _ ab_disj bc_disj
      rw [concat.assoc]
      apply hbc
      apply disjoint.elim' ab_disj bc_disj


theorem le.antisymm : ∀ {a b : Row}, a ≤ b -> b ≤ a -> a = b :=
  λ {a b} ha hb =>
    match ha, hb with
    | ⟨a',ha1, ha2⟩, ⟨b',hb1, hb2⟩ =>
      by
        rw [<-ha2] at hb2 hb1
        have lem1 : a' ⊥ b' := by
          apply disjoint.elim' ha1 hb1
        rw [<-concat.assoc lem1] at hb2
        have lem2 : (a' ++ b') = {} :=
          by
            apply concat.id_is_zero (disjoint.assoc' ha1 hb1) hb2
        have lem3 : a' = {} :=
          by
            apply positivityl lem1 lem2
        rw [lem3] at ha2
        simp at ha2
        exact ha2

instance : Std.IsPartialOrder Row where
  le_refl := λ _ => le.refl
  le_antisymm := λ _ _ => le.antisymm
  le_trans := λ _ _ _ => le.trans
