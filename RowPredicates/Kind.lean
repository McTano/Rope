module

@[expose] public section

namespace Kind

inductive Kind : Type where
  | KTy : Kind
  | KRow : Kind
  | KLabel : Kind
