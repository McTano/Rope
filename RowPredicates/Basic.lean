--------------
-- TODOs
--------------

inductive Label : Type where
  | label : String -> Label
  -- LVar : String/Number -> Label

deriving instance BEq, DecidableEq for Label

-- Idea: redefine Row as a finset of fields.
-- Or just as a dictionary.
-- Would need to map fields to their labels to compare label sets
mutual
-- Pre-Row?
inductive Row : Type where
  | empty : Row                                               -- (Identity for Concat)
  | extend : Row -> Label -> Ty -> Row
  -- | concat : Row -> Row -> Ty
  -- | RVar : String -> Row
  -- Complement/RowMinus : x: Row -> y: Row -> Disjoint x y -> Row

inductive Ty : Type where
  | Pi : Row -> Ty
  | Sigma : Row -> Ty
  | TVar : String -> Ty
  -- | TFun : Ty -> Ty
  -- | Exact : Label -> Ty
end


-- declare_syntax_cat label
-- syntax "{" ident "}" : label

-- #check_failure *(* (Label.Label "hello") @@ (@ "l") *)*

-- def l : Label := hello

-- declare_syntax_cat labeledField
-- syntax label " := " term : labeledField




def field (s: String) (t: Ty) : Row :=
  .extend .empty (.label s) t

notation "*" l => Label.label l

-- -- TODO(mctano) : Improve this notation
-- maybe make it use concat, once defined, to enforce disjointness constraints,
notation "{}" => Row.empty
notation l " : " t ", " tail => Row.extend tail (Label.label l) t
notation "@@" t => Ty.TVar t

-- #check ("hello" : @@"goodbye", "2" : @@"hello", "3rd" : @@"oopsie", {})



inductive Lacks : Row -> Label -> Prop where
  | empty : {l : Label} -> Lacks .empty l
  | extend : (r: Row) -> (l : Label) -> (l' : Label) -> (Lacks r l) -> l ≠ l' -> {t : Ty} -> (Lacks (.extend r l' t) l)

inductive In : Label -> Row ->  Prop where
  | label l {t} r' : In l (Row.extend r' l t)
  | ind l {t} r' l' : In l r' -> In l (Row.extend r' l' t)


def decide_in (l : Label) (r : Row) : (In l r) ∨ (Lacks r l) :=
  match r with
  | .empty => .inr .empty
  | .extend r' l' t' => 
                        dite (l = l')
                          (λ h_eq => .inl (by rw [<- h_eq]; exact In.label l r'))
                          (λ h_neq => match decide_in l r' with
                                      | .inl h => Or.inl (In.ind l r' l' h)
                                      | .inr h => Or.inr (Lacks.extend _ _ _ h h_neq))

inductive Disjoint : Row -> Row -> Prop where
  | empty : Disjoint .empty .empty
  | extendL : (r1 : Row) -> (r2 : Row) -> (l :Label) -> {t : Ty} -> Disjoint r1 r2
      -> Lacks r2 l -> Disjoint (.extend r1 l t) r2
  | extendR : (r1 : Row) -> (r2 : Row) -> (l :Label) -> {t : Ty} -> Disjoint r1 r2
    -> Lacks r1 l -> Disjoint r1 (.extend r2 l t)

theorem disjoint_symm {r1 r2 : Row} (h: Disjoint r1 r2) : Disjoint r2 r1 :=
  match h with
  | .empty => .empty
  | .extendL r1 r2 l h_disj h_lack1 => by apply Disjoint.extendR _ _ _ (disjoint_symm h_disj) h_lack1
  | .extendR r1 r2 l h_disj h_lack1  => by apply Disjoint.extendL _ _ _ (disjoint_symm h_disj) h_lack1

theorem emptyRowDisjointL {r: Row} :  Disjoint .empty r :=
  match r with
  | .empty => .empty
  | .extend r' _ _ => Disjoint.extendR .empty r' _ emptyRowDisjointL Lacks.empty

theorem emptyRowDisjointR {r: Row} : Disjoint r .empty := by
  apply disjoint_symm
  exact emptyRowDisjointL

inductive WellFormed : Row -> Prop where
  | empty : WellFormed .empty
  | extend : (r: Row) -> (l: Label) -> (t: Ty) -> WellFormed r -> Lacks r l -> (WellFormed (.extend r l t))

theorem lacks_extend_lacks {r: Row} {l1 l2: Label} {t: Ty} (h_lack: Lacks (r.extend l2 t) l1) : Lacks r l1 :=
  match h_lack with
  | .extend _ _ _ h _ => h

theorem lacks_implies_neq' {r1 : Row} {l1 l2 : Label} {t1: Ty} (h: Lacks (r1.extend l1 t1) l2): l2 ≠ l1 :=
  match h with
  | .extend _  _ _ _ h_neq => (λ h_eq => h_neq h_eq)

theorem lacks_implies_neq {r1 : Row} {l1 l2 : Label} {t1: Ty} (h: Lacks (r1.extend l1 t1) l2): l1 ≠ l2 :=
  by symm
     apply lacks_implies_neq' h


theorem disjoint_extend_implies_neq {r1 r2 : Row} {l1 l2 : Label} {t1 t2: Ty} (h : Disjoint (r1.extend l1 t1) (r2.extend l2 t2)): l1 ≠ l2 :=
  match h with
  | .extendL _ _ _ _ hl => lacks_implies_neq' hl
  | .extendR _ _ _ _ hl => lacks_implies_neq hl

theorem disjoint_extend_injectL {r1 r2 : Row} {l1 t1} (h : Disjoint (r1.extend l1 t1) r2) : Disjoint r1 r2 :=
  match h with
  | .extendL _ _ _ h' _ => h'
  | .extendR _ r2' _ h' h'' => by apply Disjoint.extendR _ _ _ (disjoint_extend_injectL h') (lacks_extend_lacks h'')

theorem disjoint_extend_injectR {r1 r2 : Row} {l1 t1} (h : Disjoint r1 (r2.extend l1 t1)) : Disjoint r1 r2 :=
  match h with
  | .extendL r1' _ _ h' h'' => by apply Disjoint.extendL _ _ _ (disjoint_extend_injectR h') (lacks_extend_lacks h'')
  | .extendR _ _ _ h' _ => h'

theorem disjoint_extend_inject (r1 r2 : Row) {l1 l2 : Label} {t1 t2 : Ty} (h : Disjoint (r1.extend l1 t1) (r2.extend l2 t2)) : Disjoint r1 r2 :=
  disjoint_extend_injectL (disjoint_extend_injectR h)

  -- match h with
  -- | .empty => .empty
  -- | .extendL r1' r2' l' _ h' h'' => by apply Lacks.extend _ _ _
  --                                   apply
  --                                   sorry
  --                                   sorry
  -- | .extendR _ _ _ _ e _ => sorry
  -- | .empty => sorry

-- def concat (r1 : Row) (r2 : Row) (h1: WellFormed r1) (h2: WellFormed r2) (h_disj: Disjoint r1 r2) : Row :=
--   match r1 with
--     | .empty => r2
--     | r1 => match r2 with
--             | .empty => r1
--             | .extend r2' l t =>
--               let h1' := by
--                 apply WellFormed.extend _  _  _ h1
                
                
                
--                 sorry    
--               let h2' := by sorry
--               let h3' := by sorry
--               concat (.extend r1 l t) r2' h1' h2' h3'
  -- | .empty .empty => .empty


-- This is missing the commutativity of row entries.
-- Look at how set inclusion, subset, and equality are defined.
inductive ContainedIn : Row -> Row -> Prop where
  | refl : {r: Row} -> ContainedIn r r
  | extend : (r1: Row) -> (r2: Row) -> (l : Label) -> (t : Ty) -> ContainedIn r1 r2 -> ContainedIn r1 (.extend r2 l t)

theorem contain_extend {r1 r2 : Row} {l : Label} {t : Ty} (h: ContainedIn (.extend r1 l t) r2) : ContainedIn r1 r2 :=
  match h with
  | .refl => ContainedIn.extend _ _ _ _ .refl
  | .extend _ _ _ _ h' => ContainedIn.extend _ _ _ _ (contain_extend h')
                                 

theorem contain_trans {r1 r2 r3 : Row} (h1: ContainedIn r1 r2) (h2: ContainedIn r2 r3) : ContainedIn r1 r3 := 
  match h1 with
  | .refl => h2
  | .extend _ r' l t h' => contain_trans h' (contain_extend h2)

theorem empty_contain_trivial {r: Row} : ContainedIn .empty r :=
  match r with
  | .empty => .refl
  | .extend _ _ _ => contain_trans empty_contain_trivial (contain_extend .refl)

theorem contain_empty_refl_only {r : Row} (h: ContainedIn r .empty) : r = .empty := by
  cases r
  case _ => eq_refl
  case _ => contradiction

-- inductive Row.Subset : Row -> Row -> Prop where


inductive Row.Equiv : Row -> Row -> Prop where
  | refl {r : Row} : Equiv r r
  | extend (r1 r2: Row) l t : Equiv r1 r2 -> Equiv (extend r1 l t) (extend r2 l t)



-- This can't be defined until I define equality for rows.
-- I probably also need to figure out how to encode the disjointness constraint for extending rows.
-- theorem contain_antisymm {r1 r2: Row} (h1 : ContainedIn r1 r2) (h2: ContainedIn r2 r1) : r1 = r2 := by
--   induction r2 generalizing r1
--   case _ => apply contain_empty_refl_only h1
--   case _ r' t h1' ih => sorry




-- define Predicate (TBD which should be atomic)
  -- ContainedIn : Row -> Row -> Predicate
  -- Equal : Row -> Row -> Predicate
  -- LabelOf : Label -> Row -> Predicate                                               -- I want this as a way to assert field presence/absence without introducing a type variable.
  -- Disjoint : Row -> Row -> Predicate
  -- Not : Predicate -> Predicate (alternative to having a negative judgement form.)
  
  -- Derived:
  -- NotLabelOf : Label -> Row -> Predicate                                            -- defined as (Not . LabelOf)



-- define Kind system
  -- R[k]
  -- Type
  -- Label
  -- KFun : Kind -> Kind -> Kind

-- define Predicate Derivation Rules
  -- Do we want a negative judgement form? Could just make predicates negatable.
  -- May need to divide these into terminating/non-terminating rulesets.


--------------
-- TODOs
--------------

-- relate Row Predicate Calculus to Monoids
-- Determine equivalent logical system under Curry-Howard-Correspondence.
-- find the simplest system that can express everything we need.
-- see what proofs that gets us for free.
-- prove properties of ruleset:
  -- Soundness
  -- Prove that the calculus is undecidable?
  -- Give a best-effort Decision Procedure (DP).
    -- Could use bounded recursion to run a not-necessarily terminating process for a finite time.
  -- Prove Soundness of DP.
  -- Prove something about how the DP approaches or approximates Completeness, or that it works under certain conditions.
