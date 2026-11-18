import Dogwood.Frontend.Cedarify
import Dogwood.Thm.Lowering

/-!
# Cedarify's rules are the specification's lowering, up to the leaves' names

The specification lowers a rule by replacing its `k`-th leaf with the context attribute
`leafAttr k` (`Dogwood.Spec.Expr.lowerFrom`). `Expr.lowerVia r` lowers the same way, with the
reference `r k` in place of the `k`-th leaf's attribute; `lowerFrom` is `lowerVia` with the
specification's references (`lowerFrom_eq_lowerVia`).

Cedarify produces each rule twice: as the crate's Cedar policy, and in the specification's form
with its leaves inline, together with, for each leaf of the latter, the crate's reference that
stands for it: `context.<key>__temporal_<n>` or `context.providers.<key>_p_<n>` of the field it
hoisted. The crate's policies are exactly `Policies.lowerVia` of the specification's form with
those references (`cedarifyFull_lowered`), so they are the specification's lowering
(`PolicySet.lowered`) with `context.leafAttr j` renamed to the crate's `j`-th reference
(`cedarifyFull_lowered_rename`). Each reference is the crate's reference to a hoisted field, of
the leaf's kind; and when the leaves have a form in the specification (`cedarifyWithSpec`), that
field's leaf is the specification's leaf (`cedarifyWithSpec_leaves`).

A rule's leaf may stand for one hoisted field twice: `e has a.b` with a reserved word in its path
is `e has a && e.a has b` (otherwise it is one extended `has`), and `e is T in x` is
`e is T && e in x`, so a leaf of `e` occurs twice in the specification's form, with two
attributes, and once in the crate's, read twice. The renaming is then not injective.
-/

namespace Dogwood.Spec

open Cedar.Spec (Attr)

/-! ## Lowering with given references -/

mutual

/-- Lower an expression whose first leaf is the `k`-th, replacing the `j`-th leaf with `r j`
(`Expr.lowerFrom` with any references). -/
def Expr.lowerVia (r : Nat → Cedar.Spec.Expr) : Nat → Expr → Cedar.Spec.Expr × Nat
  | k, .lit p => (.lit p, k)
  | k, .var v => (.var v, k)
  | k, .ite a b c =>
    let ra := Expr.lowerVia r k a
    let rb := Expr.lowerVia r ra.2 b
    let rc := Expr.lowerVia r rb.2 c
    (.ite ra.1 rb.1 rc.1, rc.2)
  | k, .and a b =>
    let ra := Expr.lowerVia r k a
    let rb := Expr.lowerVia r ra.2 b
    (.and ra.1 rb.1, rb.2)
  | k, .or a b =>
    let ra := Expr.lowerVia r k a
    let rb := Expr.lowerVia r ra.2 b
    (.or ra.1 rb.1, rb.2)
  | k, .unaryApp op a =>
    let ra := Expr.lowerVia r k a
    (.unaryApp op ra.1, ra.2)
  | k, .binaryApp op a b =>
    let ra := Expr.lowerVia r k a
    let rb := Expr.lowerVia r ra.2 b
    (.binaryApp op ra.1 rb.1, rb.2)
  | k, .getAttr a x =>
    let ra := Expr.lowerVia r k a
    (.getAttr ra.1 x, ra.2)
  | k, .hasAttr a x =>
    let ra := Expr.lowerVia r k a
    (.hasAttr ra.1 x, ra.2)
  | k, .extHasAttr a x xs =>
    let ra := Expr.lowerVia r k a
    (.extHasAttr ra.1 x xs, ra.2)
  | k, .set xs =>
    let rs := Expr.lowerListVia r k xs
    (.set rs.1, rs.2)
  | k, .record axs =>
    let rs := Expr.lowerRecordVia r k axs
    (.record rs.1, rs.2)
  | k, .call f xs =>
    let rs := Expr.lowerListVia r k xs
    (.call f rs.1, rs.2)
  | k, .temporal _ => (r k, k + 1)
  | k, .provider _ => (r k, k + 1)

def Expr.lowerListVia (r : Nat → Cedar.Spec.Expr) : Nat → List Expr → List Cedar.Spec.Expr × Nat
  | k, [] => ([], k)
  | k, x :: xs =>
    let rx := Expr.lowerVia r k x
    let rs := Expr.lowerListVia r rx.2 xs
    (rx.1 :: rs.1, rs.2)

def Expr.lowerRecordVia (r : Nat → Cedar.Spec.Expr) :
    Nat → List (Attr × Expr) → List (Attr × Cedar.Spec.Expr) × Nat
  | k, [] => ([], k)
  | k, (a, x) :: axs =>
    let rx := Expr.lowerVia r k x
    let rs := Expr.lowerRecordVia r rx.2 axs
    ((a, rx.1) :: rs.1, rs.2)

end

/-- `Conditions.lowerFrom`, with the references `r`. -/
def Conditions.lowerVia (r : Nat → Cedar.Spec.Expr) : Nat → Conditions → Cedar.Spec.Conditions × Nat
  | k, [] => ([], k)
  | k, c :: cs =>
    let rc := c.body.lowerVia r k
    let rs := Conditions.lowerVia r rc.2 cs
    (⟨c.kind, rc.1⟩ :: rs.1, rs.2)

/-- `Policy.lowerFrom`, with the references `r`. -/
def Policy.lowerVia (r : Nat → Cedar.Spec.Expr) (k : Nat) (p : Policy) : Cedar.Spec.Policy × Nat :=
  let rc := Conditions.lowerVia r k p.condition
  ({ id := p.id, effect := p.effect, principalScope := p.principalScope,
     actionScope := p.actionScope, resourceScope := p.resourceScope, condition := rc.1 }, rc.2)

/-- `Policies.lowerFrom`, with the references `r`. -/
def Policies.lowerVia (r : Nat → Cedar.Spec.Expr) : Nat → Policies → Cedar.Spec.Policies × Nat
  | k, [] => ([], k)
  | k, p :: ps =>
    let rp := p.lowerVia r k
    let rs := Policies.lowerVia r rp.2 ps
    (rp.1 :: rs.1, rs.2)

/-- The specification's reference to its `k`-th leaf, `context.leafAttr k`. -/
def specRef (k : Nat) : Cedar.Spec.Expr := .getAttr (.var .context) (leafAttr k)

end Dogwood.Spec

namespace Dogwood.Thm.Frontend.Cedarify

open Dogwood.Spec
open Dogwood.Frontend
open Dogwood.Frontend.Cedarify
open Cedar.Spec (Attr)

/-! ## The specification's lowering is lowering with its own references -/

mutual

theorem lowerFrom_eq_lowerVia : (x : Expr) → (k : Nat) → x.lowerFrom k = x.lowerVia specRef k
  | .lit _, _ | .var _, _ => rfl
  | .ite a b c, k => by
    simp only [Expr.lowerFrom, Expr.lowerVia, lowerFrom_eq_lowerVia a, lowerFrom_eq_lowerVia b,
      lowerFrom_eq_lowerVia c]
  | .and a b, k | .or a b, k | .binaryApp _ a b, k => by
    simp only [Expr.lowerFrom, Expr.lowerVia, lowerFrom_eq_lowerVia a, lowerFrom_eq_lowerVia b]
  | .unaryApp _ a, k | .getAttr a _, k | .hasAttr a _, k | .extHasAttr a _ _, k => by
    simp only [Expr.lowerFrom, Expr.lowerVia, lowerFrom_eq_lowerVia a]
  | .set xs, k | .call _ xs, k => by
    simp only [Expr.lowerFrom, Expr.lowerVia, lowerListFrom_eq_lowerVia xs]
  | .record axs, k => by simp only [Expr.lowerFrom, Expr.lowerVia, lowerRecordFrom_eq_lowerVia axs]
  | .temporal _, _ | .provider _, _ => rfl

theorem lowerListFrom_eq_lowerVia : (xs : List Expr) → (k : Nat) →
    Expr.lowerListFrom k xs = Expr.lowerListVia specRef k xs
  | [], _ => rfl
  | x :: xs, k => by
    simp only [Expr.lowerListFrom, Expr.lowerListVia, lowerFrom_eq_lowerVia x,
      lowerListFrom_eq_lowerVia xs]

theorem lowerRecordFrom_eq_lowerVia : (axs : List (Attr × Expr)) → (k : Nat) →
    Expr.lowerRecordFrom k axs = Expr.lowerRecordVia specRef k axs
  | [], _ => rfl
  | (_, x) :: axs, k => by
    simp only [Expr.lowerRecordFrom, Expr.lowerRecordVia, lowerFrom_eq_lowerVia x,
      lowerRecordFrom_eq_lowerVia axs]

end

theorem conditions_lowerFrom_eq_lowerVia : (cs : Conditions) → (k : Nat) →
    Conditions.lowerFrom k cs = Conditions.lowerVia specRef k cs
  | [], _ => rfl
  | c :: cs, k => by
    simp only [Conditions.lowerFrom, Conditions.lowerVia, lowerFrom_eq_lowerVia,
      conditions_lowerFrom_eq_lowerVia cs]

theorem policies_lowerFrom_eq_lowerVia : (ps : Policies) → (k : Nat) →
    Policies.lowerFrom k ps = Policies.lowerVia specRef k ps
  | [], _ => rfl
  | p :: ps, k => by
    simp only [Policies.lowerFrom, Policies.lowerVia, Policy.lowerFrom, Policy.lowerVia,
      conditions_lowerFrom_eq_lowerVia, policies_lowerFrom_eq_lowerVia ps]

/-- **The specification's lowering of a policy set** is lowering with its own references. -/
theorem lowered_eq_lowerVia (P : PolicySet) :
    P.lowered = (Policies.lowerVia specRef 0 P.policies).1 := by
  simp only [PolicySet.lowered, policies_lowerFrom_eq_lowerVia]

/-! ## Lowering to given references -/

/-- The references `r` give `R` from `k` on. -/
def RefsAt (r : Nat → Cedar.Spec.Expr) (k : Nat) (R : List Cedar.Spec.Expr) : Prop :=
  ∀ j (h : j < R.length), r (k + j) = R[j]

theorem RefsAt.left {r : Nat → Cedar.Spec.Expr} {k : Nat} {A B : List Cedar.Spec.Expr}
    (h : RefsAt r k (A ++ B)) : RefsAt r k A := by
  intro j hj
  have := h j (by simp; omega)
  rw [this, List.getElem_append_left hj]

theorem RefsAt.right {r : Nat → Cedar.Spec.Expr} {k : Nat} {A B : List Cedar.Spec.Expr}
    (h : RefsAt r k (A ++ B)) : RefsAt r (k + A.length) B := by
  intro j hj
  have := h (A.length + j) (by simp; omega)
  rw [Nat.add_assoc, this, List.getElem_append_right (by omega)]
  simp

/-- Two lists pair up, element by element, under `Q`. -/
def Zips {α β : Type} (Q : α → β → Prop) : List α → List β → Prop
  | [], [] => True
  | a :: as, b :: bs => Q a b ∧ Zips Q as bs
  | _, _ => False

theorem Zips.length_eq {α β : Type} {Q : α → β → Prop} :
    ∀ {as : List α} {bs : List β}, Zips Q as bs → as.length = bs.length
  | [], [], _ => rfl
  | _ :: _, _ :: _, h => by simp [Zips.length_eq h.2]
  | [], _ :: _, h | _ :: _, [], h => h.elim

theorem Zips.append {α β : Type} {Q : α → β → Prop} :
    ∀ {as as' : List α} {bs bs' : List β}, Zips Q as bs → Zips Q as' bs' → Zips Q (as ++ as') (bs ++ bs')
  | [], _, [], _, _, h' => h'
  | _ :: _, _, _ :: _, _, h, h' => ⟨h.1, Zips.append h.2 h'⟩
  | [], _, _ :: _, _, h, _ | _ :: _, _, [], _, h, _ => h.elim

theorem Zips.mono {α β : Type} {Q Q' : α → β → Prop} (hQ : ∀ a b, Q a b → Q' a b) :
    ∀ {as : List α} {bs : List β}, Zips Q as bs → Zips Q' as bs
  | [], [], _ => trivial
  | _ :: _, _ :: _, h => ⟨hQ _ _ h.1, Zips.mono hQ h.2⟩
  | [], _ :: _, h | _ :: _, [], h => h.elim

theorem Zips.flatten_replicate {α β : Type} {Q : α → β → Prop} {as : List α} {bs : List β}
    (h : Zips Q as bs) : ∀ n, Zips Q (List.replicate n as).flatten (List.replicate n bs).flatten
  | 0 => by simp [Zips]
  | n + 1 => by
    simp only [List.replicate_succ, List.flatten_cons]
    exact h.append (Zips.flatten_replicate h n)

theorem Zips.mem {α β : Type} {Q : α → β → Prop} :
    ∀ {as : List α} {bs : List β}, Zips Q as bs → ∀ b ∈ bs, ∃ a ∈ as, Q a b
  | [], [], _, _, hb => by simp at hb
  | a :: _, b :: _, h, b', hb => by
    rcases List.mem_cons.mp hb with rfl | hb
    · exact ⟨a, by simp, h.1⟩
    · obtain ⟨a', ha', hq⟩ := Zips.mem h.2 b' hb
      exact ⟨a', List.mem_cons_of_mem _ ha', hq⟩
  | [], _ :: _, h, _, _ | _ :: _, [], h, _, _ => h.elim

/-- The specification's form `d` lowers to the crate's expression `c` when its leaves are
replaced by the references `R`, and each leaf and its reference are related by `Q`. -/
structure LowersTo (Q : Leaf → Cedar.Spec.Expr → Prop) (d : Expr) (c : Cedar.Spec.Expr)
    (R : List Cedar.Spec.Expr) : Prop where
  lower : ∀ r k, RefsAt r k R → d.lowerVia r k = (c, k + R.length)
  leaves : Zips Q d.leaves R

/-- `LowersTo` for a list of expressions. -/
structure LowersToList (Q : Leaf → Cedar.Spec.Expr → Prop) (ds : List Expr)
    (cs : List Cedar.Spec.Expr) (R : List Cedar.Spec.Expr) : Prop where
  lower : ∀ r k, RefsAt r k R → Expr.lowerListVia r k ds = (cs, k + R.length)
  leaves : Zips Q (Expr.leavesList ds) R

/-- `LowersTo` for a record's entries. -/
structure LowersToRecord (Q : Leaf → Cedar.Spec.Expr → Prop) (ds : List (Attr × Expr))
    (cs : List (Attr × Cedar.Spec.Expr)) (R : List Cedar.Spec.Expr) : Prop where
  lower : ∀ r k, RefsAt r k R → Expr.lowerRecordVia r k ds = (cs, k + R.length)
  leaves : Zips Q (Expr.leavesRecord ds) R

variable {Q : Leaf → Cedar.Spec.Expr → Prop}

theorem LowersTo.mono {Q' : Leaf → Cedar.Spec.Expr → Prop} (hQ : ∀ a b, Q a b → Q' a b)
    {d : Expr} {c : Cedar.Spec.Expr} {R : List Cedar.Spec.Expr} (h : LowersTo Q d c R) :
    LowersTo Q' d c R :=
  ⟨h.lower, h.leaves.mono hQ⟩

theorem LowersToList.mono {Q' : Leaf → Cedar.Spec.Expr → Prop} (hQ : ∀ a b, Q a b → Q' a b)
    {ds : List Expr} {cs : List Cedar.Spec.Expr} {R : List Cedar.Spec.Expr}
    (h : LowersToList Q ds cs R) : LowersToList Q' ds cs R :=
  ⟨h.lower, h.leaves.mono hQ⟩

theorem LowersToRecord.mono {Q' : Leaf → Cedar.Spec.Expr → Prop} (hQ : ∀ a b, Q a b → Q' a b)
    {ds : List (Attr × Expr)} {cs : List (Attr × Cedar.Spec.Expr)} {R : List Cedar.Spec.Expr}
    (h : LowersToRecord Q ds cs R) : LowersToRecord Q' ds cs R :=
  ⟨h.lower, h.leaves.mono hQ⟩

theorem lowersTo_lit (p : Cedar.Spec.Prim) : LowersTo Q (.lit p) (.lit p) [] :=
  ⟨fun _ _ _ => rfl, by simp [Expr.leaves, Zips]⟩

theorem lowersTo_var (v : Cedar.Spec.Var) : LowersTo Q (.var v) (.var v) [] :=
  ⟨fun _ _ _ => rfl, by simp [Expr.leaves, Zips]⟩

theorem lowersTo_temporal {φ : Temporal.Formula} {ref : Cedar.Spec.Expr} (h : Q (.inl φ) ref) :
    LowersTo Q (.temporal φ) ref [ref] :=
  ⟨fun r k hr => by have := hr 0 (by simp); simp_all [Expr.lowerVia], by simp [Expr.leaves, Zips, h]⟩

theorem lowersTo_provider {c : Provider.Call} {ref : Cedar.Spec.Expr} (h : Q (.inr c) ref) :
    LowersTo Q (.provider c) ref [ref] :=
  ⟨fun r k hr => by have := hr 0 (by simp); simp_all [Expr.lowerVia], by simp [Expr.leaves, Zips, h]⟩

theorem LowersTo.unaryApp {d : Expr} {c : Cedar.Spec.Expr} {R : List Cedar.Spec.Expr}
    (h : LowersTo Q d c R) (op : Cedar.Spec.UnaryOp) :
    LowersTo Q (.unaryApp op d) (.unaryApp op c) R :=
  ⟨fun r k hr => by simp [Expr.lowerVia, h.lower r k hr], by simpa [Expr.leaves] using h.leaves⟩

theorem LowersTo.getAttr {d : Expr} {c : Cedar.Spec.Expr} {R : List Cedar.Spec.Expr}
    (h : LowersTo Q d c R) (a : Attr) : LowersTo Q (.getAttr d a) (.getAttr c a) R :=
  ⟨fun r k hr => by simp [Expr.lowerVia, h.lower r k hr], by simpa [Expr.leaves] using h.leaves⟩

theorem LowersTo.hasAttr {d : Expr} {c : Cedar.Spec.Expr} {R : List Cedar.Spec.Expr}
    (h : LowersTo Q d c R) (a : Attr) : LowersTo Q (.hasAttr d a) (.hasAttr c a) R :=
  ⟨fun r k hr => by simp [Expr.lowerVia, h.lower r k hr], by simpa [Expr.leaves] using h.leaves⟩

theorem LowersTo.extHasAttr {d : Expr} {c : Cedar.Spec.Expr} {R : List Cedar.Spec.Expr}
    (h : LowersTo Q d c R) (a : Attr) (as : List Attr) :
    LowersTo Q (.extHasAttr d a as) (.extHasAttr c a as) R :=
  ⟨fun r k hr => by simp [Expr.lowerVia, h.lower r k hr], by simpa [Expr.leaves] using h.leaves⟩

theorem LowersTo.and {d₁ d₂ : Expr} {c₁ c₂ : Cedar.Spec.Expr} {R₁ R₂ : List Cedar.Spec.Expr}
    (h₁ : LowersTo Q d₁ c₁ R₁) (h₂ : LowersTo Q d₂ c₂ R₂) :
    LowersTo Q (.and d₁ d₂) (.and c₁ c₂) (R₁ ++ R₂) :=
  ⟨fun r k hr => by
    simp [Expr.lowerVia, h₁.lower r k hr.left, h₂.lower r _ hr.right, Nat.add_assoc],
   by simpa [Expr.leaves] using h₁.leaves.append h₂.leaves⟩

theorem LowersTo.or {d₁ d₂ : Expr} {c₁ c₂ : Cedar.Spec.Expr} {R₁ R₂ : List Cedar.Spec.Expr}
    (h₁ : LowersTo Q d₁ c₁ R₁) (h₂ : LowersTo Q d₂ c₂ R₂) :
    LowersTo Q (.or d₁ d₂) (.or c₁ c₂) (R₁ ++ R₂) :=
  ⟨fun r k hr => by
    simp [Expr.lowerVia, h₁.lower r k hr.left, h₂.lower r _ hr.right, Nat.add_assoc],
   by simpa [Expr.leaves] using h₁.leaves.append h₂.leaves⟩

/-! ### Cedar's folding of Boolean literals

Cedar's `ExprBuilder` folds `&&` and `||` of two Boolean literals into one (`andC`, `orC`). The
folding commutes with lowering when no reference that stands for a leaf is a Boolean literal
(`NoBoolRef`): a lowered expression is then a Boolean literal exactly when its specification's
form is. -/

/-- No reference that stands for a leaf is a Boolean literal. -/
def NoBoolRef (Q : Leaf → Cedar.Spec.Expr → Prop) : Prop :=
  ∀ l ref, Q l ref → ∀ b, ref ≠ .lit (.bool b)

/-- References that read the list `R` from position `0` on. -/
theorem refsAt_getD (R : List Cedar.Spec.Expr) :
    RefsAt (fun j => R.getD j (.lit (.bool false))) 0 R := by
  intro j hj
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]

/-- A literal lowers to itself, with no leaf. -/
theorem LowersTo.lit_eq {p : Cedar.Spec.Prim} {c : Cedar.Spec.Expr} {R : List Cedar.Spec.Expr}
    (h : LowersTo Q (.lit p) c R) : c = .lit p ∧ R = [] := by
  have hl := h.lower _ 0 (refsAt_getD R)
  simp only [Expr.lowerVia, Prod.mk.injEq] at hl
  exact ⟨hl.1.symm, List.eq_nil_of_length_eq_zero (by omega)⟩

/-- A lowered expression is a Boolean literal only when its specification's form is that
literal: a leaf's reference is not one. -/
theorem LowersTo.boolLit {d : Expr} {c : Cedar.Spec.Expr} {R : List Cedar.Spec.Expr}
    (h : LowersTo Q d c R) (hQ : NoBoolRef Q) {b : Bool} (hc : c = .lit (.bool b)) :
    d = .lit (.bool b) := by
  have hl := h.lower _ 0 (refsAt_getD R)
  have hz := h.leaves
  subst hc
  cases d with
  | lit p =>
    simp only [Expr.lowerVia, Prod.mk.injEq, Cedar.Spec.Expr.lit.injEq] at hl
    rw [hl.1]
  | temporal φ =>
    simp only [Expr.leaves] at hz
    cases R with
    | nil => exact hz.elim
    | cons ref R =>
      simp only [Expr.lowerVia, List.getD_cons_zero, Prod.mk.injEq] at hl
      exact absurd hl.1 (hQ _ _ hz.1 b)
  | provider c' =>
    simp only [Expr.leaves] at hz
    cases R with
    | nil => exact hz.elim
    | cons ref R =>
      simp only [Expr.lowerVia, List.getD_cons_zero, Prod.mk.injEq] at hl
      exact absurd hl.1 (hQ _ _ hz.1 b)
  | _ => simp [Expr.lowerVia] at hl

theorem andS_of_not {d₁ d₂ : Expr} (h : ¬ ∃ a b, d₁ = .lit (.bool a) ∧ d₂ = .lit (.bool b)) :
    Frontend.Cedarify.andS d₁ d₂ = .and d₁ d₂ := by
  unfold Frontend.Cedarify.andS
  split
  · exact absurd ⟨_, _, rfl, rfl⟩ h
  · rfl

theorem orS_of_not {d₁ d₂ : Expr} (h : ¬ ∃ a b, d₁ = .lit (.bool a) ∧ d₂ = .lit (.bool b)) :
    Frontend.Cedarify.orS d₁ d₂ = .or d₁ d₂ := by
  unfold Frontend.Cedarify.orS
  split
  · exact absurd ⟨_, _, rfl, rfl⟩ h
  · rfl

theorem andC_of_not {c₁ c₂ : Cedar.Spec.Expr}
    (h : ¬ ∃ a b, c₁ = .lit (.bool a) ∧ c₂ = .lit (.bool b)) :
    Frontend.Cedarify.andC c₁ c₂ = .and c₁ c₂ := by
  unfold Frontend.Cedarify.andC
  split
  · exact absurd ⟨_, _, rfl, rfl⟩ h
  · rfl

theorem orC_of_not {c₁ c₂ : Cedar.Spec.Expr}
    (h : ¬ ∃ a b, c₁ = .lit (.bool a) ∧ c₂ = .lit (.bool b)) :
    Frontend.Cedarify.orC c₁ c₂ = .or c₁ c₂ := by
  unfold Frontend.Cedarify.orC
  split
  · exact absurd ⟨_, _, rfl, rfl⟩ h
  · rfl

/-- Of two lowered expressions, the forms are both Boolean literals when the lowered ones are,
and conversely. -/
theorem LowersTo.boolLits {d₁ d₂ : Expr} {c₁ c₂ : Cedar.Spec.Expr} {R₁ R₂ : List Cedar.Spec.Expr}
    (h₁ : LowersTo Q d₁ c₁ R₁) (h₂ : LowersTo Q d₂ c₂ R₂) (hQ : NoBoolRef Q) :
    (∃ a b, d₁ = .lit (.bool a) ∧ d₂ = .lit (.bool b)) ↔
      (∃ a b, c₁ = .lit (.bool a) ∧ c₂ = .lit (.bool b)) := by
  constructor
  · rintro ⟨a, b, rfl, rfl⟩
    exact ⟨a, b, h₁.lit_eq.1, h₂.lit_eq.1⟩
  · rintro ⟨a, b, rfl, rfl⟩
    exact ⟨a, b, h₁.boolLit hQ rfl, h₂.boolLit hQ rfl⟩

theorem LowersTo.andS {d₁ d₂ : Expr} {c₁ c₂ : Cedar.Spec.Expr} {R₁ R₂ : List Cedar.Spec.Expr}
    (h₁ : LowersTo Q d₁ c₁ R₁) (h₂ : LowersTo Q d₂ c₂ R₂) (hQ : NoBoolRef Q) :
    LowersTo Q (Frontend.Cedarify.andS d₁ d₂) (Frontend.Cedarify.andC c₁ c₂) (R₁ ++ R₂) := by
  by_cases hd : ∃ a b, d₁ = .lit (.bool a) ∧ d₂ = .lit (.bool b)
  · obtain ⟨a, b, rfl, rfl⟩ := hd
    obtain ⟨rfl, rfl⟩ := h₁.lit_eq
    obtain ⟨rfl, rfl⟩ := h₂.lit_eq
    exact lowersTo_lit _
  · have hc : ¬ ∃ a b, c₁ = .lit (.bool a) ∧ c₂ = .lit (.bool b) :=
      fun h => hd ((h₁.boolLits h₂ hQ).mpr h)
    rw [andS_of_not hd, andC_of_not hc]
    exact h₁.and h₂

theorem LowersTo.orS {d₁ d₂ : Expr} {c₁ c₂ : Cedar.Spec.Expr} {R₁ R₂ : List Cedar.Spec.Expr}
    (h₁ : LowersTo Q d₁ c₁ R₁) (h₂ : LowersTo Q d₂ c₂ R₂) (hQ : NoBoolRef Q) :
    LowersTo Q (Frontend.Cedarify.orS d₁ d₂) (Frontend.Cedarify.orC c₁ c₂) (R₁ ++ R₂) := by
  by_cases hd : ∃ a b, d₁ = .lit (.bool a) ∧ d₂ = .lit (.bool b)
  · obtain ⟨a, b, rfl, rfl⟩ := hd
    obtain ⟨rfl, rfl⟩ := h₁.lit_eq
    obtain ⟨rfl, rfl⟩ := h₂.lit_eq
    exact lowersTo_lit _
  · have hc : ¬ ∃ a b, c₁ = .lit (.bool a) ∧ c₂ = .lit (.bool b) :=
      fun h => hd ((h₁.boolLits h₂ hQ).mpr h)
    rw [orS_of_not hd, orC_of_not hc]
    exact h₁.or h₂

theorem LowersTo.binaryApp {d₁ d₂ : Expr} {c₁ c₂ : Cedar.Spec.Expr} {R₁ R₂ : List Cedar.Spec.Expr}
    (h₁ : LowersTo Q d₁ c₁ R₁) (h₂ : LowersTo Q d₂ c₂ R₂) (op : Cedar.Spec.BinaryOp) :
    LowersTo Q (.binaryApp op d₁ d₂) (.binaryApp op c₁ c₂) (R₁ ++ R₂) :=
  ⟨fun r k hr => by
    simp [Expr.lowerVia, h₁.lower r k hr.left, h₂.lower r _ hr.right, Nat.add_assoc],
   by simpa [Expr.leaves] using h₁.leaves.append h₂.leaves⟩

theorem LowersTo.ite {d₁ d₂ d₃ : Expr} {c₁ c₂ c₃ : Cedar.Spec.Expr}
    {R₁ R₂ R₃ : List Cedar.Spec.Expr}
    (h₁ : LowersTo Q d₁ c₁ R₁) (h₂ : LowersTo Q d₂ c₂ R₂) (h₃ : LowersTo Q d₃ c₃ R₃) :
    LowersTo Q (.ite d₁ d₂ d₃) (.ite c₁ c₂ c₃) (R₁ ++ R₂ ++ R₃) :=
  ⟨fun r k hr => by
    have h3 := h₃.lower r _ hr.right
    simp only [List.length_append] at h3
    simp [Expr.lowerVia, h₁.lower r k hr.left.left, h₂.lower r _ hr.left.right, Nat.add_assoc] at h3 ⊢
    simp [h3],
   by simpa [Expr.leaves] using (h₁.leaves.append h₂.leaves).append h₃.leaves⟩

theorem lowersToList_nil : LowersToList Q [] [] [] :=
  ⟨fun _ _ _ => rfl, by simp [Expr.leavesList, Zips]⟩

theorem LowersToList.cons {d : Expr} {c : Cedar.Spec.Expr} {ds : List Expr}
    {cs : List Cedar.Spec.Expr} {R R' : List Cedar.Spec.Expr}
    (h : LowersTo Q d c R) (hs : LowersToList Q ds cs R') :
    LowersToList Q (d :: ds) (c :: cs) (R ++ R') :=
  ⟨fun r k hr => by
    simp [Expr.lowerListVia, h.lower r k hr.left, hs.lower r _ hr.right, Nat.add_assoc],
   by simpa [Expr.leavesList] using h.leaves.append hs.leaves⟩

theorem lowersToRecord_nil : LowersToRecord Q [] [] [] :=
  ⟨fun _ _ _ => rfl, by simp [Expr.leavesRecord, Zips]⟩

theorem LowersToRecord.cons {a : Attr} {d : Expr} {c : Cedar.Spec.Expr} {ds : List (Attr × Expr)}
    {cs : List (Attr × Cedar.Spec.Expr)} {R R' : List Cedar.Spec.Expr}
    (h : LowersTo Q d c R) (hs : LowersToRecord Q ds cs R') :
    LowersToRecord Q ((a, d) :: ds) ((a, c) :: cs) (R ++ R') :=
  ⟨fun r k hr => by
    simp [Expr.lowerRecordVia, h.lower r k hr.left, hs.lower r _ hr.right, Nat.add_assoc],
   by simpa [Expr.leavesRecord] using h.leaves.append hs.leaves⟩

theorem LowersToList.set {ds : List Expr} {cs : List Cedar.Spec.Expr} {R : List Cedar.Spec.Expr}
    (h : LowersToList Q ds cs R) : LowersTo Q (.set ds) (.set cs) R :=
  ⟨fun r k hr => by simp [Expr.lowerVia, h.lower r k hr], by simpa [Expr.leaves] using h.leaves⟩

theorem LowersToList.call {ds : List Expr} {cs : List Cedar.Spec.Expr} {R : List Cedar.Spec.Expr}
    (h : LowersToList Q ds cs R) (f : Cedar.Spec.ExtFun) : LowersTo Q (.call f ds) (.call f cs) R :=
  ⟨fun r k hr => by simp [Expr.lowerVia, h.lower r k hr], by simpa [Expr.leaves] using h.leaves⟩

theorem LowersToRecord.record {ds : List (Attr × Expr)} {cs : List (Attr × Cedar.Spec.Expr)}
    {R : List Cedar.Spec.Expr} (h : LowersToRecord Q ds cs R) :
    LowersTo Q (.record ds) (.record cs) R :=
  ⟨fun r k hr => by simp [Expr.lowerVia, h.lower r k hr], by simpa [Expr.leaves] using h.leaves⟩

theorem LowersTo.unaryS {d : Expr} {c : Cedar.Spec.Expr} {R : List Cedar.Spec.Expr}
    (h : LowersTo Q d c R) (op : Surface.UnOp) : LowersTo Q (unaryS op d) (unaryC op c) R := by
  have hl : LowersToList Q [d] [c] R := by simpa using LowersToList.cons h lowersToList_nil
  cases op <;> first
    | exact h.unaryApp _
    | exact hl.call _

theorem LowersTo.binaryS {d₁ d₂ : Expr} {c₁ c₂ : Cedar.Spec.Expr} {R₁ R₂ : List Cedar.Spec.Expr}
    (h₁ : LowersTo Q d₁ c₁ R₁) (h₂ : LowersTo Q d₂ c₂ R₂) (hQ : NoBoolRef Q) (op : Surface.BinOp) :
    LowersTo Q (binaryS op d₁ d₂) (binaryC op c₁ c₂) (R₁ ++ R₂) := by
  have hl : LowersToList Q [d₁, d₂] [c₁, c₂] (R₁ ++ R₂) := by
    simpa using LowersToList.cons h₁ (LowersToList.cons h₂ lowersToList_nil)
  cases op <;> first
    | exact h₁.binaryApp h₂ _
    | exact (h₁.binaryApp h₂ _).unaryApp _
    | exact h₁.andS h₂ hQ
    | exact h₁.orS h₂ hQ
    | exact hl.call _

theorem LowersTo.hasRest {h g : Expr} {hc gc : Cedar.Spec.Expr} {R₁ R : List Cedar.Spec.Expr}
    (hh : LowersTo Q h hc R₁) (hg : LowersTo Q g gc R) :
    ∀ rest : List String,
      LowersTo Q (hasRestS h g rest) (hasRestC hc gc rest)
        (R₁ ++ (List.replicate rest.length R).flatten)
  | [] => by simpa [hasRestS, hasRestC] using hh
  | b :: rest => by
    have := LowersTo.hasRest (hh.and (hg.hasAttr b)) (hg.getAttr b) rest
    simpa [hasRestS, hasRestC, List.replicate_succ, List.flatten_cons, List.append_assoc]
      using this

theorem LowersTo.hasPath {d : Expr} {c : Cedar.Spec.Expr} {R : List Cedar.Spec.Expr}
    (h : LowersTo Q d c R) :
    ∀ attrs : List String, LowersTo Q (hasPathS d attrs) (hasPathC c attrs) (hasRefs R attrs)
  | [] => by simpa [hasPathS, hasPathC, hasRefs] using h.hasAttr ""
  | a :: rest => by
    simp only [hasPathS, hasPathC, hasRefs]
    split
    · exact h.extHasAttr a rest
    · have := LowersTo.hasRest (h.hasAttr a) (h.getAttr a) rest
      simpa [List.replicate_succ, List.flatten_cons] using this

end Dogwood.Thm.Frontend.Cedarify
