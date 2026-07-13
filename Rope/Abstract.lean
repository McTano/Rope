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

axiom disjoint.implies_def : ∀ {a b : Row}, a ⊥ b -> Σ c, PLift (a + b ~ c)

-- Might be better off including the well-definedness constraint as a precondition to theorems, a la denominator ≠ 0?
noncomputable
def concat (a b : Row) : {_: a ⊥ b} -> Row :=
  λ {h} => (h.implies_def).fst

infixl:90 " ++ " => concat

notation:90 a:100 " ++ " b:100 "(" h ")" => @concat a b h

-- Axioms
-- The axioms given here define simple row theory as a
-- *Partial Commutative Monoid*
-- https://ncatlab.org/nlab/show/effect+algebra#definition
@[simp]
axiom concat_to.def_implies_disjoint : ∀ {a b c : Row}, (a + b ~ c) -> a ⊥ b

axiom disjoint.zero : ∀ {a : Row}, {} ⊥ a
axiom disjoint.symm : ∀ {a : Row}, a ⊥ b -> b ⊥ a

axiom concat_to.zero : ∀ {a : Row}, {} + a ~ a
axiom concat_to.symm : ∀ {a b : Row}, a + b ~ c -> b + a ~ c
-- helpers for associativity are necessary to access the disjointness proofs implied by the earlier arguments
@[simp]
axiom concat_to.assoc_helper1 : forall {x y z : Row},
  (hyz: y ⊥ z) ->
  (hxyz: x ⊥ (@concat y z hyz))
  -> x ⊥ y

@[simp]
axiom concat_to.assoc_helper2 : forall {x y z : Row},
  (hxy: x ⊥ y) ->
  ((@concat x y hxy) ⊥ z)

-- proof irrelevance of x ⊥ y for cat
@[simp, grind =]
theorem concat.unique : forall {x y : Row} {h h' : x ⊥ y},
  @concat x y h = @concat x y h' := by
  intro x y h h'
  rfl

-- Associativity is rephrased from the nlab version
-- y⊥z and x⊥(y∨z) implies x⊥y and (x∨y)⊥z and x∨(y∨z)=(x∨y)∨z.
@[simp]
axiom concat_to.assoc : forall {x y z : Row},
  (hyz: y ⊥ z) ->
  (hxyz: x ⊥ (@concat y z hyz)) ->
  (x + (@concat y z hyz) ~ (@concat (@concat x y (assoc_helper1 _ hxyz)) z (assoc_helper2 (assoc_helper1 _ hxyz))))

-- Associativity is rephrased from the nlab version
-- y⊥z and x⊥(y∨z) implies x⊥y and (x∨y)⊥z and x∨(y∨z)=(x∨y)∨z.
theorem concat.ah1 : forall {x y z : Row},
  {hyz: y ⊥ z} -> 
  x ⊥ (@concat y z hyz) ->
  (x ⊥ y)
  := by
    sorry

theorem concat.ah2 : forall {x y z : Row},
  (hyz: y ⊥ z) -> 
  (hxyz: x ⊥ (@concat y z hyz)) ->
  (@concat x y (ah1 hxyz)) ⊥ z
  := by sorry
  
-- x∨(y∨z)=(x∨y)∨z
theorem concat.assoc : forall {x y z yz xy xyz : Row},
  (hyz: y ⊥ z) ->
  (hxyz: x ⊥ (@concat y z _)) ->
  (@concat x
           (@concat y z _)
           hxyz) = (@concat
                          (@concat x y (ah1 hxyz)) z
                      (concat.ah2 hyz hxyz))
   := by sorry


theorem zero_right : ∀ {a : Row}, a ⊥ {} := disjoint.zero.symm

axiom concat_to.unique :
  a + b ~ c ∧ a + b ~ c' -> c = c'

-- axiom concat_to.

axiom concat_to.idr : ∀ {a : Row}, a + {} ~ a
-- axiom concat_to.assoc :  ∀ {a b c: Row}, (h: a ⊥ b) -> x ⊥ (@concat a b h)

-- It's annoying that I can't say (a ++ b) or synthesize h when it appears as a previous argument
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
