module

@[expose] public section

namespace Label

inductive Label : Type where
  -- NOTE: I like the idea of first class labels but making them positional would match Rosi and might be easier to work with. Probably stuff like concatenating labels won't come up anyways
  | explicit (s : String)  : Label
  | lVar (name: String) : Label

inductive Label.concrete : Label -> Prop where
 | literal : Label.concrete (.explicit s)

-- Equality of labels is purely syntactic, explicit labels are equal if they are equal as strings, likewise for lVars
deriving instance BEq, DecidableEq, Hashable, Ord, ReflBEq, LawfulBEq for Label
