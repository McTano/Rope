module


@[expose] public section

namespace Label

inductive Label : Type where
  | label (s : String)  : Label
  | LVar (name: String) : Label

inductive Label.concrete : Label -> Prop where
 | literal : Label.concrete (.label s)

deriving instance BEq, DecidableEq, Ord, ReflBEq, LawfulBEq for Label

-- Boolean equality of labels is purely syntactic
