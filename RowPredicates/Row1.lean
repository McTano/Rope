module


public import Std.Data.HashSet
public import RowPredicates.Label

@[expose] public section

-- first (actually kind of second) attempt at defining rows
namespace Row

open Label

instance : HasEquiv Label where
  Equiv l1 l2 := l1 = l2

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
notation l " : " t ", " tail => Row.extend tail l t
notation "@@" t => Ty.TVar t

-- #check ("hello" : @@"goodbye", "2" : @@"hello", "3rd" : @@"oopsie", {})

inductive Lacks : Row -> Label -> Prop where
  | empty : {l : Label} -> Lacks .empty l
  | extend : (r: Row) -> (l : Label) -> (l' : Label) -> (Lacks r l) -> l ≠ l' -> {t : Ty} -> (Lacks (.extend r l' t) l)

inductive In : Label -> Row ->  Prop where
  | label l {t} r' : In l (Row.extend r' l t)
  | ind l {t} r' l' : In l r' -> In l (Row.extend r' l' t)

infix:90 " ∈ " => In


def decide_in (l : Label) (r : Row) : (l ∈ r) ∨ (Lacks r l) :=
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

inductive WF : Row -> Prop where
  | empty : WF .empty
  | extend : (r: Row) -> (l: Label) -> (t: Ty) -> WF r -> Lacks r l -> (WF (.extend r l t))

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

-- def concat (r1 : Row) (r2 : Row) (h1: WF r1) (h2: WF r2) (h_disj: Disjoint r1 r2) : Row :=
--   match r1 with
--     | .empty => r2
--     | r1 => match r2 with
--             | .empty => r1
--             | .extend r2' l t =>
--               let h1' := by
--                 apply WF.extend _  _  _ h1
                
                
                
--                 sorry    
--               let h2' := by sorry
--               let h3' := by sorry
--               concat (.extend r1 l t) r2' h1' h2' h3'
  -- | .empty .empty => .empty


-- needs commutativity
-- inductive ContainedIn : Row -> Row -> Prop where
--   | refl : {r: Row} -> ContainedIn r r
--   | extend : (r1: Row) -> (r2: Row) -> (l : Label) -> (t : Ty) -> ContainedIn r1 r2 -> ContainedIn r1 (.extend r2 l t)

def typeAt (r: Row) (l: Label) : Option Ty :=
  match r with
  | .empty => .none
  | .extend r' l' t =>
    if (l = l')
    then .some t
    else typeAt r' l

def contained_in (r1 r2: Row) : Prop :=
  forall (l1 : Label), (typeAt r1 l1) = (typeAt r2 l1)
  
instance : LE Row where
  le := contained_in

def contained_in_trans {r1 r2 r3 : Row} (h_1_2: contained_in r1 r2) (h_2_3: contained_in r2 r3): contained_in r1 r3 := by
  intro l;
  rw [h_1_2, h_2_3]

instance : Std.IsPreorder Row where
  le_refl := λ x =>
    by intro l
       rfl
  le_trans := λ _ _ _ => contained_in_trans

-- needs equiv defined
-- do i need a different one if i'm using equiv?
-- instance : Std.IsPartialOrder Row where
--   le_refl := sorry
--   le_antisymm := sorry
--   le_trans := sorry

-- theorem contain_extend {r1 r2 : Row} {l : Label} {t : Ty} (h: ContainedIn (.extend r1 l t) r2) : ContainedIn r1 r2 :=
--   match h with
--   | .refl => ContainedIn.extend _ _ _ _ .refl
--   | .extend _ _ _ _ h' => ContainedIn.extend _ _ _ _ (contain_extend h')


-- theorem contain_trans {r1 r2 r3 : Row} (h1: ContainedIn r1 r2) (h2: ContainedIn r2 r3) : ContainedIn r1 r3 := 
--   match h1 with
--   | .refl => h2
--   | .extend _ r' l t h' => contain_trans h' (contain_extend h2)

-- theorem empty_contain_trivial {r: Row} : ContainedIn .empty r :=
--   match r with
--   | .empty => .refl
--   | .extend _ _ _ => contain_trans empty_contain_trivial (contain_extend .refl)

-- theorem contain_empty_refl_only {r : Row} (h: ContainedIn r .empty) : r = .empty := by
--   cases r
--   case _ => eq_refl
--   case _ => contradiction




-- inductive Row.Subset : Row -> Row -> Prop where

-- TODO(mctano) prove that equiv x y <=> (x < y & y < x)
-- inductive equiv : Row -> Row -> Prop where
--   | refl {r : Row} : equiv r r
--   | extend (r1 r2: Row) (l: Label) (t: Ty) (h_equiv: equiv r1 r2) (lack1: Lacks r1 l) {wf1: WF r1} {wf2: WF r2} : equiv (.extend r1 l t) (.extend r2 l t)
--   | permute (r1: Row) l1 t1 l2 t2 {wf1: WF r1} : equiv (l1 : t1, l2 : t2, r1) (l2 : t2, l1 : t1, r1)
  -- | permuteL (rL: Row) (rR: Row) l1 t1 l2 t2 (lackL1: Lacks rL l1) (lackL2 : Lacks rL l2) (l_neq : l1 ≠ l2) {wfL : WF rL} {wfR : WF rR} : equiv (l1 : t1, l2 : t2, rL) rR -> equiv (l2 : t2, l1 : t1, rL) rR 
  -- | permuteR (rL: Row) (rR: Row) l1 t1 l2 t2 (lackR1: Lacks rR l1) (lackR2 : Lacks rR l2) (l_neq : l1 ≠ l2) {wfL : WF rL} {wfR : WF rR} : equiv rL (l1 : t1, l2 : t2, rR) -> equiv rL (l2 : t2, l1 : t1, rR) 

def equiv (r1 r2 : Row) : Prop :=  contained_in r1 r2 ∧ contained_in r2 r1

instance : HasEquiv Row where
  Equiv := Row.equiv

def same_labels (r1 r2: Row) : Prop :=
  forall l, In l r1 <-> In l r2

def same_labels_refl  {r: Row} : same_labels r r := 
  λ _ => Iff.rfl

def label_in_empty {l : Label} : ¬ In l {} :=
  λ h => by contradiction

open Std

-- instance : HasEquiv (HashSet Label) where
--   Equiv := HashSet.Equiv

-- instance :  (HashSet Label) where
--   r := HashSet.equiv
--   iseqv := {
--     refl := .refl
--     symm := by
--       intro s1 s2 e
--       induction e
--       case mk h =>
--         induction h
--         case mk h' =>
--           induction h'
--           apply inner'
          
--     trans := sorry
-- }




def labels (r : Row) : HashSet Label :=
  match r with
  | .empty => ∅
  | .extend r l _ => insert l (labels r)

theorem emptyLabels : labels {} = ∅ := rfl

-- theorem equiv_eq_labels {r1 r2 : Row} {wf1 : WF r1} {wf2 : WF r2} : (h: r1 ≈ r2) -> labels r1 = labels r2 := by
--   induction wf1 generalizing r2
  
--   cases wf2 <;> intro h

theorem equiv_refl {r : Row } : r ≈ r := by
  apply And.intro <;> intro l <;> rfl
  

theorem equiv_symm {r1 r2 : Row} (h: r1 ≈ r2) : r2 ≈ r1 := by
  cases h
  case intro left right =>
    apply And.intro right left

theorem equiv_trans {r1 r2 r3 : Row} (h_1_2 : r1 ≈ r2) (h_2_3 : r2 ≈ r3) : r1 ≈ r3 := by
  apply And.intro
  case left =>
    apply contained_in_trans h_1_2.left h_2_3.left
  case right =>
    apply contained_in_trans h_2_3.right h_1_2.right

instance : Setoid Row where
  r := equiv
  iseqv := {
    refl := λ _ => equiv_refl
    trans := equiv_trans
    symm := equiv_symm
  }



  -- cases wf2
--   case empty => sorry
--   case extend r' l1' t1' wf' lack ih => 
--     intro h
--     cases wf2
--     case empty => 

--     sorry
  -- induction wf1 generalizing r2
  -- case empty =>
  --   cases r2 <;> intro h
  --   case empty => rfl
  --   case extend r' l t =>
  --     cases h
  -- case extend r l t wf lack ih =>
  --   cases r2
  --   case empty =>
  --     intro h
  --     contradiction
  --   case extend r2 l2 t2 =>
  --     intro h
  --     by_cases h_eq : l = l2 <;> unfold labels
  --     case pos =>
  --       rw [h_eq] at h
  --       rw [h_eq] at *
  --       cases h
  --       case refl => rfl
  --       case extend wf' lack' wf2' heqv =>
  --         rw [ih heqv]
  --         assumption
  --       case permute a b c d e => 
  --         rw [ih]
          

    -- sorry
      


  
  


-- def empty_extend_not_equiv {r l t} : ¬ equiv (.extend r l t) {} := by
--   intro h
--   -- cases r
  -- case empty => contradiction
  -- case extend r' l' t' =>
  --   apply empty_extend_not_equiv _
    -- sorry
  -- cases h
  -- case permuteL rL l1 t1 lack1 lack2 h_neq h_eqv =>


    -- sorry
    -- sorry

-- theorem equiv_implies_same_labels (r1 r2: Row) (h_equiv : equiv r1 r2) : same_labels r1 r2 :=
--   λ l =>
--   match r1 with
--   | .empty => by
--     cases h_equiv <;> 
--   | .extend r' l' t' => by
--     apply equiv_implies_same_labels _ r2 h_equiv

    -- apply Iff.intro
    -- intro h
    -- rw [equiv_implies_same_labels _ r2 h_equiv] at h
    -- apply 



  -- match h_equiv with
  -- | .refl => same_labels_refl
  -- | .extend r1' r2' l _ h_eqv _ => by
  --   intro l
  --   apply Iff.intro
  --   case mp => 
  --     intro h
  --     cases h
  --     case label => apply In.label
  --     case ind ih =>
  --       apply In.ind
  --       rw [equiv_implies_same_labels r1' r2'] at ih
  --       exact ih
  --       exact h_eqv
  -- | .permuteL _ _ _ _ _ _ _ _ _ _ => by

    
                    
  


-- theorem equiv_lacks_same {l: Label} (r1 : Row) (r2 : Row) (h_eqv : equiv r1 r2)  (lack1 : Lacks r1 l) : Lacks r2 l := by
  -- induction h_eqv
  -- case refl => exact lack1
  -- case extend r1 r2 l' t _ lack_i ih => 
  --   apply Lacks.extend
  --   apply ih (lacks_extend_lacks lack1)
  --   apply lacks_implies_neq' lack1
  -- case permuteL rL rR l1 t1 l2 t2 lackL1 lackL2 l_neq h_eqv' ih =>
  --   have lem1 : Lacks (l1 : t1, rL) l := lacks_extend_lacks lack1
  --   have lem2 : Lacks rL l := lacks_extend_lacks lem1
  --   apply ih
  --   apply Lacks.extend
  --   apply Lacks.extend
  --   apply lem2
  --   symm
  --   apply lacks_implies_neq lack1
  --   symm
  --   apply lacks_implies_neq lem1
  -- case permuteR rL rR l1 t1 l2 t2 lackR1 lackR2 l_neq h_eqv' ih =>
  --   have lem1 : Lacks (l1 : t1, l2 : t2, rR) l := (ih lack1)
  --   have lem2 : Lacks (l2 : t2, rR) l := lacks_extend_lacks lem1
  --   have lem3 : Lacks rR l := lacks_extend_lacks lem2
  --   apply Lacks.extend
  --   apply Lacks.extend
  --   apply lem3
  --   symm
  --   apply lacks_implies_neq
  --   apply lem1
  --   symm
  --   apply lacks_implies_neq lem2



-- theorem extend_not_empty (r: Row) (h_eq: equiv (l : t, r) {}) : False := by


-- theorem eqv_trans {r1 r2 r3 : Row} (eq_1_2 : equiv r1 r2) (eq_2_3 : equiv r2 r3): equiv r1 r3 :=
--   match eq_1_2 with
--   | .refl => eq_2_3
--   | .extend r1' r2' l t h_eqv lack =>
--     match eq_2_3 with
--     | .refl => by
--         apply equiv.extend _ _ _ _ h_eqv lack         
--     | .extend r3_a r3_b l' t' h_eqv' lack' => by
--          apply equiv.extend r1' r3_b _ _
--          apply eqv_trans (r1 := r1') h_eqv h_eqv'
--     | .permuteL r3L r3R lx tx ly ty lackL1 lackL2 h_neq h3_eqv => by  
--       cases r3R
--       case empty => 
--       case extend => sorry
--       -- equiv (l1 ; t1, r2) {} -> False
--       -- have lem1 : equiv (ly : ty, r3L) (ly : ty, lx : tx, r3R) :=
--       --   apply equiv.extend _ _ _ _
--       -- have lem2 : equiv (ly : ty, lx : tx, r3R) (lx : tx, ly : ty, r3R) :=
--       --   equiv.permute _ _ _ _ _ _ equiv.refl
--       -- have lem4 : equiv r1' (ly : ty, r3R) :=
--       --   eqv_trans h lem1
--       -- have lem5 : equiv (lx : tx, r1') (lx : tx, ly : ty, r3R) :=
--       --   equiv.extend _ _ _ _ lem4
--       by 
--       have lem1 : equiv (ly : ty, lx : tx, r3L) r3R := by
--         apply equiv.permuteL _ _ _ _ _ _ (by grind) (by grind) h3
--       have lem2 : equiv (ly : ty, r1') (ly : ty, lx : tx, r3L) := by
--         apply equiv.extend _ _ _ _ h_eqv lack
      

      
--       sorry
--     | .permuteR _ _ _ _ _ _ _ _ _ => by
      


--       sorry
--   | .permuteL r1' r2' l1 t1 l2 t2 lack1 lack2 h_eq =>
--     by 
--       -- have lem : equiv (l1 : t1, l2 : t2, r1') (l2 : t2, l1 : t1, r2')
--       --   := equiv.permute _ _ _ _ _ _ h_eq
--       -- apply eqv_trans lem eq_2_3
--       sorry
--   | .permuteR r1' r2' l1 t1 l2 t2 lack1 lack2 h_eq =>
--     by 
--       -- have lem : equiv (l1 : t1, l2 : t2, r1') (l2 : t2, l1 : t1, r2')
--       --   := equiv.permute _ _ _ _ _ _ h_eq
--       -- apply eqv_trans lem eq_2_3
--       sorry
--   termination_by structural r1
                             


-- This can't be defined until I define equality for rows.
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

end Row