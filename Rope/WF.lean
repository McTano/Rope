module
public import Rope.Pre
public import Rope.Label

@[expose] public section

namespace WF

open Label

-- TODO add WF_Pred
-- Interdefined Well-formedness rules for Pre.Row and Pre.Ty
mutual
inductive WF_Row : (inner: Pre.Row) -> Prop where
  | empty : WF_Row .empty
  -- rVars bound at the top level can be treated as free, but they will need to be bound for polymorphic functions
  | rVar : WF_Row (.rVar s)
  | extend : WF_Row r -> r.lack l -> (WF_Ty t) -> WF_Row (.extend r l t)

-- TODO Binders for type and row variables. I think both should be defined in Ty.
inductive WF_Ty : (inner: Pre.Ty) -> Prop where
  -- Unit type?
  -- For now, all TVars are free and double as atomic types and provide a base case for WF_Ty,
  | TVar : WF_Ty (.TVar s)
  | TFun : WF_Ty arg -> WF_Ty ret -> WF_Ty (.TFun arg ret)
  | Singleton : WF_Ty (.Singleton l)
  | Pi : WF_Row r -> WF_Ty (.Pi r)
  | Sigma : WF_Row r -> WF_Ty (.Sigma r)
  | Qual : WF_Pred p -> WF_Ty t -> WF_Ty (.Qual p t)

inductive WF_Pred : (inner :Pre.Pred) -> Prop where
  | Contain : WF_Row x -> WF_Row y -> WF_Pred (.Contain x y)
  | Combine : WF_Row x -> WF_Row y -> WF_Row z -> WF_Pred (.Combine x y z)
  | TyEq : WF_Ty t1 -> WF_Ty t2 -> WF_Pred (.TyEq t1 t2)
end

theorem WF.unique_labels {r : Pre.Row} (wf : WF_Row r) : r.unique_labels :=
  match wf with
  | .empty => .empty
  | .rVar => .rVar
  | .extend r_wf r_lack_l ty_wf => Pre.Row.unique_labels.extend (WF.unique_labels r_wf) r_lack_l

-- WF.Row bundles Pre.Row with a well-formedness invariant
-- TODO See if I can refactor this to make reasoning over these less awkward.
  -- Is there anything else I can do to reduce friction when inducting over the inner row?
  -- Would defining a custom a custom induction principle or well-foundedness measure help
structure Row : Type where
  inner : Pre.Row
  wf : WF_Row inner

structure Ty : Type where
  inner : Pre.Ty
  wf : WF_Ty inner

structure Pred : Type where
  inner : Pre.Pred
  wf : WF_Pred inner


def Row.unique_labels : Row -> Prop
  | .mk inner _ => inner.unique_labels

-- A row lacks a label iff the inner (well-formed) pre-row lacks that label
def Row.lack : Row -> Label -> Prop
  | ⟨inner, _⟩, l => inner.lack l

def Row.disjoint : Row -> Row -> Prop
  | ⟨innerL, _⟩, ⟨innerR, _⟩ => innerL.disjoint innerR

def Row.concrete : Row -> Prop
  | ⟨inner, _⟩ => inner.concrete

@[match_pattern]
def Row.empty : Row := ⟨.empty, .empty⟩

@[match_pattern]
def Row.rVar (name : String) : Row :=
  ⟨.rVar name, .rVar⟩

-- TODO I keep getting inaccessible pattern errors when trying to match on this. What makes this pattern different from WF.Ty.TFun, which works fine?
@[match_pattern]
def Row.extend (r: Row) (l : Label) (t : Ty) (h: r.lack l) : Row  :=
    ⟨Pre.Row.extend r.inner l t.inner, WF_Row.extend r.wf h t.wf⟩

@[match_pattern]
def Ty.TVar (s : String) : Ty :=
  ⟨Pre.Ty.TVar s, WF_Ty.TVar⟩

@[match_pattern]
def Ty.TFun (t1 t2 : Ty) : Ty :=
  ⟨Pre.Ty.TFun t1.inner t2.inner, WF_Ty.TFun t1.wf t2.wf⟩

@[match_pattern]
def Ty.Singleton (l : Label) : Ty :=
  ⟨
    Pre.Ty.Singleton l,
    WF_Ty.Singleton
  ⟩

@[match_pattern]
def Ty.Pi (r : Row) : Ty :=
  ⟨
    Pre.Ty.Pi r.inner,
    WF_Ty.Pi r.wf
  ⟩

@[match_pattern]
def Ty.Sigma (r : Row) : Ty :=
  ⟨
    Pre.Ty.Sigma r.inner,
    WF_Ty.Sigma r.wf
  ⟩

@[match_pattern]
def Ty.Qual (p : Pred) (t : Ty) : Ty :=
  ⟨.Qual p.inner t.inner, WF_Ty.Qual p.wf t.wf⟩

@[match_pattern]
def Pred.Contain (x y : Row) : Pred :=
  ⟨Pre.Pred.Contain x.inner y.inner, WF_Pred.Contain x.wf y.wf⟩

@[match_pattern]
def Pred.Combine (x y z : Row) : Pred :=
  ⟨.Combine x.inner y.inner z.inner, WF_Pred.Combine x.wf y.wf z.wf⟩

@[match_pattern]
def Pred.TyEq (t1 t2 : Ty) : Pred :=
  ⟨.TyEq t1.inner t2.inner, WF_Pred.TyEq t1.wf t2.wf⟩


def Row.has_label (r : Row) (l : Label): Prop :=
  r.inner.has_label l


def Row.type_at (r : Row) (l : Label): Option Ty :=
  match r with
  | ⟨.empty, _⟩ => .none
  | ⟨.rVar _, _⟩ => .none
  | ⟨.extend r' l' t, wf⟩ =>
     if l = l'
      then .some ⟨t, (match wf with | .extend _ _ wft => wft)⟩
      else type_at ⟨r', (match wf with | .extend wfr _ _ => wfr)⟩ l

theorem Row.type_at_is_some {r : Row} {l: Label} (h : r.has_label l) : (Option.isSome (r.type_at l) = true) :=
  match r with
  | ⟨inner, wf⟩ =>
    match inner with
    | .empty => by contradiction
    | .extend r' l' t' =>
        by
          by_cases (l = l')
          case _ h_pos => simp [type_at, h_pos]
          case _ h_neg =>
            cases h;
            contradiction
            simp [type_at, h_neg]
            case extend h =>
              apply Row.type_at_is_some
              simp [has_label,h]

def Row.type_at! (r: Row) (l: Label) (has_l : has_label r l) : Ty :=
  (r.type_at l).get (Row.type_at_is_some has_l)

theorem lacks_extend_lacks {r: Pre.Row} {l1 l2: Label} {t: Pre.Ty} (h_lack: Pre.Row.lack (r.extend l2 t) l1) : Pre.Row.lack r l1 :=
  match h_lack with
  | .extend h' _ => h'

-- TODO Add Preds
-- Well-formed rows are equivalent iff they are equal up to reordering of fields.
-- Equivalence under a context/substitution will be defined later.
mutual
inductive Row.le : Row -> Row -> Prop where
  | empty {r : Row} : Row.le .empty r
  | rVar {s : String} : Row.le (.rVar s) (.rVar s)
  | extendR {a b : Row} {l : Label} {t : Ty} : (a_le_b: Row.le a b) -> (b_lack : b.lack l) ->  Row.le a (@Row.extend b l t b_lack)
  | extend2 {a b : Row} {l : Label} {ta tb : Ty} :
    Row.le a b -> (a_lack : a.lack l) -> (b_lack : b.lack l) -> Ty.Equiv ta tb -> Row.le (@Row.extend a l ta a_lack) (@.extend b l tb b_lack)

-- Types are equivalent iff they are equal up to equivalence of in all subtree
inductive Ty.Equiv : Ty  -> Ty  -> Prop where
  | TVar : Ty.Equiv (Ty.TVar s) (Ty.TVar s)
  | Singleton : Ty.Equiv (Ty.Singleton l) (Ty.Singleton l)
  | Pi : a.le b -> b.le a -> Ty.Equiv (Ty.Pi a) (Ty.Pi b)
  | Sigma : a.le b -> b.le a -> Ty.Equiv (Ty.Sigma a) (Ty.Sigma b)
  | TFun : Ty.Equiv a1 a2 -> Ty.Equiv r1 r2 -> Ty.Equiv (Ty.TFun a1 r1) (Ty.TFun a2 r2)
  | Qual : Pred.Equiv p1 p2 -> Ty.Equiv t1 t2 -> Ty.Equiv (.Qual p1 t1) (.Qual p2 t2)

inductive Pred.Equiv : Pred -> Pred -> Prop where
  | Contain {x1 x2 y1 y2 : Row} : Row.le x1 x2 -> Row.le x2 x1 -> Row.le y1 y2 -> Row.le y2 y1 -> (Pred.Contain x1 y1).Equiv (Pred.Contain x2 y2)
    -- Garrett-style 3-place concatenation predicate
    -- x + y ~ z
  | Combine {x1 x2 y1 y2 z1 z2: Row} :
    Row.le x1 x2 -> Row.le x2 x1 -> 
    Row.le y1 y2 -> Row.le y2 y1 -> 
    Row.le z1 z2 -> Row.le z2 z1 ->
    Pred.Equiv (.Combine x1 y1 z1) (.Combine x2 y2 z2)
  | TyEq {a1 a2 b1 b2 : Ty} : (Ty.Equiv a1 a2) -> (Ty.Equiv b1 b2) ->  Pred.Equiv (.TyEq a1 b1) (.TyEq a2 b2)
end

instance : LE Row where
  le := Row.le

-- Rows are equivalent iff they are LE each other
def Row.Equiv (a b : WF.Row) : Prop := a ≤ b ∧ b ≤ a

-- TODO Ideas for deciding le and equiv
-- sort row and compare in order
-- convert row to a hashmap
-- Redefine a WF row to always be sorted, then define le inductively over the sorted row

-- def Row.ble (a b : Row) : Bool := sorry

-- theorem Row.ble_decides_le : ∀ r1 r2: Row, r1.ble r2 = true <-> r1 ≤ r2 := by sorry

-- instance : DecidableLE Row := by
--   intro a b
--   by_cases (a.ble b)
--   case pos h =>
--     apply Decidable.isTrue
--     exact (Row.ble_decides_le a b).mp h
--   case neg h =>
--     sorry

theorem Row.le.empty_bottom (r : Row) : .empty ≤ r :=
  match r with
  | Row.empty => .empty
  -- This is why we need the .empty rule
  | Row.rVar _ => .empty
  | ⟨.extend _ _ _, WF_Row.extend _ _ _⟩ => .empty

theorem Row.le.empty_is_refl {r : Row} : r ≤ .empty <-> r = .empty :=
  Iff.intro (
    λ h =>
      match h with
      | Row.le.empty => rfl 
  ) (
    λ h => by rw [h]; exact .empty)


theorem Row.le.rVar_is_refl_or_empty {r : Row} {s : String} : r ≤ .rVar s <-> (r = .rVar s) ∨ (r = .empty) :=
  Iff.intro (
    λ h =>
      match r with
      | .empty => Or.inr rfl
      | .rVar _ => Or.inl (by cases h; rfl)
      | ⟨.extend r' l t, _⟩ => by contradiction
  ) (
    λ h  =>
      match h with
      | .inl e => by subst e; exact .rVar
      | .inr e => by subst e; exact .empty
  )

theorem Row.le_inner_has_label {a b : Row} {l : Label } (h_le : a ≤ b) (h_has : a.inner.has_label l) : b.inner.has_label l :=
    match h_le with
    | .empty => by contradiction
    | Row.le.extendR a'_le_b b_lack => by
      apply Pre.Row.has_label.extend
      apply Row.le_inner_has_label a'_le_b h_has
    | @Row.le.extend2 a' b' l' _ _ a'_le_b' a_lack b_lack _ => by
      by_cases (l = l')
      case _ pos =>
        subst pos
        apply Pre.Row.has_label.first
      case _ neg =>
        cases h_has
        case first => 
          apply Pre.Row.has_label.first
        case extend h =>
          apply Pre.Row.has_label.extend
          apply le_inner_has_label a'_le_b' h

theorem Row.lift_lack {r : Pre.Row} {l : Label} {wfr : WF_Row r} (h : r.lack l) : lack ⟨r, wfr⟩ l := h

mutual
theorem Row.le.refl : ∀ {x : Row}, x ≤ x
  | Row.empty => .empty
  | .rVar _ => .rVar
  | ⟨Pre.Row.extend r l t, .extend wfr r_lack wft⟩ => by
    apply @Row.le.extend2 ⟨r,wfr⟩ ⟨r,wfr⟩ l ⟨t, wft⟩ ⟨t, wft⟩ .refl r_lack r_lack .refl

theorem Ty.Equiv.refl : ∀ {x : Ty}, Ty.Equiv x x
| .TVar _ => .TVar
| .Singleton _ => .Singleton
| ⟨.TFun arg ret, WF_Ty.TFun wf_a wf_r⟩ =>
  @Ty.Equiv.TFun ⟨arg,wf_a⟩ ⟨arg,wf_a⟩ ⟨ret, wf_r⟩ ⟨ret, wf_r⟩ .refl .refl
| ⟨.Pi r, WF_Ty.Pi wf_r⟩ =>
  @Ty.Equiv.Pi ⟨r, wf_r⟩ ⟨r, wf_r⟩ .refl .refl
| ⟨.Sigma r, WF_Ty.Sigma wf_r⟩ =>
  @Ty.Equiv.Sigma ⟨r, wf_r⟩ ⟨r, wf_r⟩ .refl .refl
| ⟨.Qual p t, .Qual wf_p wf_t⟩ => @Ty.Equiv.Qual ⟨p, wf_p⟩ ⟨p, wf_p⟩ ⟨t, wf_t⟩ ⟨t, wf_t⟩ .refl .refl

theorem Pred.Equiv.refl : ∀ {p : Pred}, Pred.Equiv p p
    | ⟨.Contain x y,.Contain wf_x wf_y⟩ => @Pred.Equiv.Contain ⟨x, wf_x⟩ ⟨x, wf_x⟩ ⟨y, wf_y⟩ ⟨y, wf_y⟩ .refl .refl .refl .refl
    | ⟨.Combine x y z, .Combine wf_x wf_y wf_z⟩ =>
      @Pred.Equiv.Combine ⟨x, wf_x⟩ ⟨x, wf_x⟩ ⟨y, wf_y⟩ ⟨y, wf_y⟩ ⟨z, wf_z⟩ ⟨z, wf_z⟩ .refl .refl .refl .refl .refl .refl
    | ⟨.TyEq t1 t2, .TyEq wf_t1 wf_t2⟩ => @Pred.Equiv.TyEq ⟨t1, wf_t1⟩ ⟨t1, wf_t1⟩ ⟨t2, wf_t2⟩ ⟨t2, wf_t2⟩ .refl .refl
end


theorem Row.Equiv.refl : ∀ {r: Row}, r.Equiv r :=
  (.intro .refl .refl)

theorem Row.Equiv.symm : ∀ {x y : Row}, x.Equiv y → y.Equiv x :=
  λ h =>
    match h with
    | (And.intro l r) => (And.intro r l)

mutual
theorem Ty.Equiv.symm : ∀ {x y : Ty}, x.Equiv y → y.Equiv x :=
  λ h =>
    match h with
    | .TVar => Ty.Equiv.TVar
    | .Singleton => .Singleton
    | .TFun h1 h2 => .TFun (Ty.Equiv.symm h1) (Ty.Equiv.symm h2)
    | .Pi hl hr => .Pi hr hl
    | .Sigma hl hr => .Sigma hr hl
    | .Qual h1 h2 => .Qual (Pred.Equiv.symm h1) (Ty.Equiv.symm h2)

theorem Pred.Equiv.symm : ∀ {p q : Pred}, p.Equiv q → q.Equiv p :=
  λ h =>
    match h with
    | .Contain a b c d => .Contain b a d c
    | .Combine a b c d e f => .Combine b a d c f e
    | .TyEq a b => .TyEq a.symm b.symm
end

theorem Row.le.extend_le {a b : Pre.Row} {wfa : WF_Row a} {wfb : WF_Row b} {l : Label} {t : Pre.Ty} {wft : WF_Ty t} {a_lack : a.lack l} (h : Row.mk (a.extend l t) (wfa.extend a_lack wft) ≤ ⟨b,wfb⟩) : Row.mk a wfa ≤ ⟨b,wfb⟩ :=
  by
    cases h;
    case extendR b_lack a_le_b => exact le.extendR (extend_le (wft := wft) (a_lack := a_lack) a_le_b) b_lack
    case extend2 _ _ _ _ _ _ => apply le.extendR <;> assumption

mutual
theorem Row.le.trans {a b c : Pre.Row} {wfa : WF_Row a} {wfb : WF_Row b} {wfc : WF_Row c}
  (h_a_b : (Row.mk a wfa) ≤ (Row.mk b wfb)) (h_b_c : (Row.mk b wfb) ≤ (Row.mk c wfc)) : (Row.mk a wfa) ≤ (Row.mk c wfc) :=
  match h_a_b with
  | .empty => .empty
  | .rVar => h_b_c
  | @Row.le.extendR ⟨_, _⟩ ⟨b',wfb'⟩ _ ⟨t,wft⟩ a_le_b' b'_lack_l' =>
    match h_b_c with
    | @Row.le.extend2 _ _ _ _ _ b'_le_c' hlack black t_eq' => Row.le.extendR (Row.le.trans a_le_b' b'_le_c') black
    | @Row.le.extendR _ b2 _ _  b'_le_c' black => by
      apply Row.le.extendR _ black
      simp at b'_le_c'
      apply Row.le.trans _ b'_le_c'
      apply @Row.le.extendR ⟨a,wfa⟩ ⟨b',wfb'⟩ _ ⟨t,wft⟩ a_le_b' b'_lack_l'
  | @Row.le.extend2 ⟨a', wfa'⟩ ⟨b',wfb'⟩ l ⟨ta,_⟩ ⟨tb, wftb⟩ a'_le_b' a_lack b_lack t_eq =>
    match h_b_c with
    | @Row.le.extend2 _ ⟨b'', wfb''⟩ _ _ _ hle hlack black t_eq' =>
      by 
        exact @Row.le.extend2 ⟨a', wfa'⟩ ⟨b'',wfb''⟩ l _ _ (@Row.le.trans a' _ b'' _ _ _ a'_le_b' hle) a_lack black (Ty.Equiv.trans t_eq t_eq')
    | @Row.le.extendR ⟨_,_⟩ ⟨c',wfc'⟩ l' _ b_le_c' c_lack_l' => by
        simp at *
        have lem1 : Row.mk (a'.extend l ta) wfa ≤ ⟨b'.extend l tb, wfb⟩ := by
          exact Row.le.extend2 a'_le_b' a_lack b_lack t_eq
        have lem2 : Row.mk b' wfb' ≤ ⟨b'.extend l tb, wfb⟩ := by
          apply Row.le.extendR .refl  (t := ⟨tb, wftb⟩) b_lack
        have b'_le_c' : Row.mk b' wfb' ≤ ⟨c', wfc'⟩ := by
          apply Row.le.extend_le <;> assumption
        have lem3 : Row.mk a' wfa' ≤ ⟨c', wfc'⟩ := by
          apply Row.le.trans a'_le_b' b'_le_c'
        apply @Row.le.extendR _ ⟨c',wfc'⟩ l' _ _ c_lack_l'
        apply @Row.le.trans _ _ _ _ _ _ lem1 b_le_c'

theorem Ty.Equiv.trans {x y z : Pre.Ty} {wfx : WF_Ty x} {wfy : WF_Ty y} {wfz : WF_Ty z} :
  (Ty.mk x wfx).Equiv (Ty.mk y wfy) → (Ty.mk y wfy).Equiv (Ty.mk z wfz) → (Ty.mk x wfx).Equiv (Ty.mk z wfz) :=
  λ h1 h2 =>
    match x, y, z with
    | .TVar x', .TVar y', .TVar z' =>
      by cases h1 ; cases h2; apply Ty.Equiv.refl
    | .Singleton x', .Singleton y', .Singleton z' =>
      by cases h1 ; cases h2; apply Ty.Equiv.refl
    | .TFun _ _, _, _ =>
        match h1, h2 with
        | @Ty.Equiv.TFun ⟨_,_⟩ ⟨_,_⟩ ⟨_,_⟩ ⟨_,_⟩ h1a h1r, Ty.Equiv.TFun h2a h2r =>
          Ty.Equiv.TFun (Ty.Equiv.trans h1a h2a) (Ty.Equiv.trans h1r h2r)
    | .Pi _, _, _ =>
      have h1_symm := h1.symm
      have h2_symm := h2.symm
      match h1, h2 with
      | @Ty.Equiv.Pi _ ⟨b', wfb'⟩ h_xy h_yx, Ty.Equiv.Pi h_yz h_zy
          => Ty.Equiv.Pi
            (Row.le.trans h_xy h_yz)
            (Row.le.trans h_zy h_yx)
    | .Sigma _, _, _ =>
      match h1, h2 with
      | @Ty.Equiv.Sigma _ ⟨_, _⟩ h_xy h_yx,Ty.Equiv.Sigma h_yz h_zy 
        => Ty.Equiv.Sigma 
          (Row.le.trans h_xy h_yz)
          (Row.le.trans h_zy h_yx)
    | .Qual _ _, _, _ =>
      match h1, h2 with
      | @Ty.Equiv.Qual ⟨p1,_⟩ ⟨p2, _⟩ ⟨t1,_⟩ ⟨t2, _⟩ h_pxy h_txy, Ty.Equiv.Qual h_pyz h_tyz
        => Ty.Equiv.Qual
          (Pred.Equiv.trans h_pxy h_pyz)
          (Ty.Equiv.trans h_txy h_tyz)

theorem Pred.Equiv.trans {x y z : Pre.Pred} {wf_x : WF_Pred x} {wf_y : WF_Pred y} {wf_z : WF_Pred z} :
  (Pred.mk x wf_x).Equiv (Pred.mk y wf_y) → (Pred.mk y wf_y).Equiv (Pred.mk z wf_z) → (Pred.mk x wf_x).Equiv (Pred.mk z wf_z)
:=
  λ h1 h2 =>
    match y with
    | .Contain _ _ =>
      match h1, h2 with
      | @Pred.Equiv.Contain ⟨_, _⟩ ⟨_, _⟩ ⟨_, _⟩ ⟨_, _⟩ ha_xy ha_yx hb_xy hb_yx,
         Pred.Equiv.Contain ha_yz ha_zy hb_yz hb_zy =>
          .Contain
            (Row.le.trans ha_xy ha_yz)
            (Row.le.trans ha_zy ha_yx)
            (Row.le.trans hb_xy hb_yz)
            (Row.le.trans hb_zy hb_yx)
    | .Combine _ _ _ =>
      match h1, h2 with
      | @Pred.Equiv.Combine ⟨_, _⟩ ⟨_, _⟩ ⟨_, _⟩ ⟨_, _⟩ ⟨_, _⟩ ⟨_, _⟩ ha_xy ha_yx hb_xy hb_yx hc_xy hc_yx,
         Pred.Equiv.Combine ha_yz ha_zy hb_yz hb_zy hc_yz hc_zy =>
          .Combine
            (Row.le.trans ha_xy ha_yz)
            (Row.le.trans ha_zy ha_yx)
            (Row.le.trans hb_xy hb_yz)
            (Row.le.trans hb_zy hb_yx)
            (Row.le.trans hc_xy hc_yz)
            (Row.le.trans hc_zy hc_yx)
    | .TyEq _ _ =>
      match h1, h2 with
      | @Pred.Equiv.TyEq _ ⟨_,_⟩ _ ⟨_,_⟩ ha_xy hb_xy,
         Pred.Equiv.TyEq ha_yz hb_yz =>
          .TyEq
            (Ty.Equiv.trans ha_xy ha_yz)
            (Ty.Equiv.trans hb_xy hb_yz)
end


theorem Row.Equiv.trans {x y z: Row} (h_x_y : x.Equiv y) (h_y_z : y.Equiv z) : x.Equiv z :=
  And.intro (Row.le.trans h_x_y.left h_y_z.left) (Row.le.trans h_y_z.right h_x_y.right)

instance : Std.IsPreorder Row := ⟨λ _ => Row.le.refl, λ _ _ _ => Row.le.trans⟩


-- This definition of equivalence is syntactic, up to reordering of fields
-- Equivalence of rows with respect to a context or substitution will be defined over quotients of well-formed rows and types
instance Ty.instSetoid : Setoid Ty where
  r := Ty.Equiv
  iseqv := ⟨λ _ => .refl, .symm, .trans⟩

instance Row.instSetoid : Setoid Row where
  r := Row.Equiv
  iseqv := ⟨λ _ => .refl, .symm, .trans⟩

instance Pred.instSetoid : Setoid Pred where
  r := Pred.Equiv
  iseqv := ⟨λ _ => .refl, .symm, .trans⟩
