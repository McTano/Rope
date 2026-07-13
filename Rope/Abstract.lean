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

infixl:90 " ⊥ " => disjoint



-- redefine as 3-place Prop pred?
opaque concat_to : Row -> Row -> Row -> Prop

notation:90 a:100 " + " b:100 " ~ " c:100 => concat_to a b c

variable (a b c d : Row)

#check a + b ~ c

-- Axioms
-- The axioms given here define simple row theory as a
-- *Partial Commutative Monoid*
-- https://ncatlab.org/nlab/show/effect+algebra#definition
axiom disjoint.implies_def : ∀ {a b : Row}, a ⊥ b -> Σ c, PLift (a + b ~ c)
@[simp]
axiom concat_to.def_implies_disjoint : ∀ {a b c : Row}, (a + b ~ c) -> a ⊥ b

axiom disjoint.zero : ∀ {a : Row}, {} ⊥ a
axiom disjoint.symm : ∀ {a : Row}, a ⊥ b -> b ⊥ a

axiom concat_to.zero : ∀ {a : Row}, {} + a ~ a
axiom concat_to.symm : ∀ {a b : Row}, a + b ~ c -> b + a ~ c
-- Associativity is rephrased from the nlab version
-- y⊥z and x⊥(y∨z) implies x⊥y and (x∨y)⊥z and x∨(y∨z)=(x∨y)∨z.
-- TODO define a version of this over the concat function
axiom concat_to.associativity : forall {x y z yz xy xyz: Row},
  y + z ~ yz -> x + yz ~ xyz
             -> x ⊥ y ∧
               (x + y ~ xy ->
                        xy ⊥ z ∧ xy + z ~ xyz)

theorem zero_right : ∀ {a : Row}, a ⊥ {} := disjoint.zero.symm

axiom concat_to.unique :
  a + b ~ c ∧ a + b ~ c' -> c = c'

-- axiom concat_to.

axiom concat_to.idr : ∀ {a : Row}, a + {} ~ a
-- axiom concat_to.assoc :  ∀ {a b c: Row}, (h: a ⊥ b) -> x ⊥ (@concat a b h)

-- Might be better off including the well-definedness constraint as a precondition to theorems, a la denominator ≠ 0?
noncomputable
def concat (a b : Row) : {_: a ⊥ b} -> Row :=
  λ {h} => (h.implies_def).fst

infixl:90 " ++ " => concat

-- It's annoying that I can't say (a ++ b), even when I know that a ⊥ b is disjoint.
theorem concat.denotation : ∀ {a b: Row}, (h : a ⊥ b) -> ∃ c, ((a + b ~ c) ∧ (@concat a b h) = c) :=
  λ h =>
    ⟨h.implies_def.fst, And.intro h.implies_def.snd.down rfl⟩

theorem concat.rel : ∀ {a b : Row}, (h: a ⊥ b) -> (a + b ~ (@concat a b h)) := by
  intro a b h
  unfold concat
  apply h.implies_def.snd.down

theorem concat.denotation2 : ∀ {a b c : Row}, (h : a + b ~ c) -> (@concat a b h.def_implies_disjoint) = c :=
  λ h => concat_to.unique _ _ _ (And.intro (concat.rel h.def_implies_disjoint) h)

-- Consider lifting this to Sigma type so we can access the witness
def le (a c : Row): Prop := ∃ b, a + b ~ c

instance : LE Row where
  le := le

#check {} ≤ {}

theorem le.refl : ∀ {a : Row}, a ≤ a := ⟨{}, .idr⟩

theorem le.bottom : ∀ {a : Row}, {} ≤ a := ⟨_, .zero⟩
theorem le.trans : ∀ {a b c : Row}, a ≤ b -> b ≤ c -> a ≤ c :=
  λ {a b c} a_b b_c =>
    match a_b, b_c with
    | ⟨ab', hab⟩, ⟨bc', hbc⟩ => by
      simp [(.≤.),le] at *
      -- have lem : ab' ⊥ bc' := sorry
      -- exists (@concat ab' bc' lem)
      have lem_ab_disj : a ⊥ ab' := hab.def_implies_disjoint
      have lem' : b = (@concat a ab' lem_ab_disj) := by
        apply (concat_to.unique a ab')
        apply And.intro hab
        apply concat.rel
      have lem_bc_disj : b ⊥ bc' := hbc.def_implies_disjoint
      have lem'' : c = (@concat b bc' lem_bc_disj) := by
        apply (concat_to.unique b bc')
        apply And.intro hbc
        apply concat.rel
      rw [lem'] at hbc
      rw [lem''] at hbc
      sorry
theorem le.antisymm : ∀ {a b : Row}, a ≤ b -> b ≤ a -> a = b := by sorry


instance : Std.IsPartialOrder Row where
  le_refl := λ _ => le.refl
  le_antisymm := λ _ _ => le.antisymm
  le_trans := λ _ _ _ => le.trans
