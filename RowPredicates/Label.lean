module


@[expose] public section

namespace Label

inductive Label : Type where
  | label (s : String)  : Label
  | LVar (name: String) : Label

inductive Label.concrete : Label -> Prop where
 | literal : Label.concrete (.label s)


def Label.syntactic_match (l l': Label) : Bool :=
  match l, l' with
      | .LVar s, .LVar s' =>  s == s'
      | .label s, .label s' => s == s'
      | _, _ => false

deriving instance Ord for Label

-- This actually only makes sense for concrete labels,
-- I'm still not totally sure whether LVar should be a case of Label or of Term
-- We do need boolean equality for labels, but i guess in the literal case it would
-- actually be easy enough to match on and compare the string contents
-- instance : BEq Label where
--   beq := λ (.label a) (.label b) => a == b

-- instance : LawfulBEq Label where
--   rfl := instBEqLabel.rfl
--   eq_of_beq := λ {a b} h => by
--     cases a
--     cases b
--     simp [(·==·)] at h
--     rw [h]
