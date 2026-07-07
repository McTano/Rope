module

@[expose] public section

namespace Label

inductive Label : Type where
  | explicit (s : String)  : Label
  | lVar (name: String) : Label

inductive Label.concrete : Label -> Prop where
 | literal : Label.concrete (.explicit s)

-- Equality of labels is purely syntactic
deriving instance BEq, DecidableEq, Ord, ReflBEq, LawfulBEq for Label
