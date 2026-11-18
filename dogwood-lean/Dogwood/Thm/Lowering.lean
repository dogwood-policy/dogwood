import Dogwood.Spec.Validity
import Dogwood.Thm.Leaves
import Cedar.Thm.Data.List.Lemmas
import Cedar.Thm.Data.Map

/-!
# Lowering preserves evaluation

Lowering replaces each leaf of a rule by an attribute of the request context
(`Dogwood.Spec.PolicySet.lowered`). Cedar's evaluator, on the lowered rule and a request whose
context holds the leaves' values at their attributes and agrees with the original context
elsewhere, gives what Dogwood's evaluator gives on the rule (`evaluate_lower`). The rule must
read the context only through attributes outside the leaves' (`Expr.ReadsContext`). So the
per-request authorizer decides a policy set as Cedar decides its lowering, on the augmented
request (`isAuthorized_lower`). A rule without leaves is its own lowering, on the request itself,
whatever it reads (`evaluate_lower_self`, `isAuthorized_lower_self`).
-/

namespace Dogwood.Thm

open Dogwood.Spec
open Cedar.Spec (Value Attr Request Entities Result bindAttr)
open Cedar.Data (Map)

/-- The value a leaf valuation gives a leaf: a temporal leaf's `Bool`, a provider leaf's
value. -/
def _root_.Dogwood.Spec.Leaves.valueOf (θ : Leaves) : Leaf → Value
  | .inl φ => .prim (.bool (θ.temporal φ))
  | .inr c => θ.provider c

/-! ## Leaf numbering -/

mutual

theorem lowerFrom_snd : (x : Expr) → (k : Nat) → (x.lowerFrom k).2 = k + x.leaves.length
  | .lit _, k | .var _, k => by simp [Expr.lowerFrom, Expr.leaves]
  | .ite a b c, k => by
    simp only [Expr.lowerFrom, Expr.leaves, List.length_append, lowerFrom_snd c, lowerFrom_snd b,
      lowerFrom_snd a]
    omega
  | .and a b, k | .or a b, k | .binaryApp _ a b, k => by
    simp only [Expr.lowerFrom, Expr.leaves, List.length_append, lowerFrom_snd b, lowerFrom_snd a]
    omega
  | .unaryApp _ a, k | .getAttr a _, k | .hasAttr a _, k | .extHasAttr a _ _, k => by
    simp only [Expr.lowerFrom, Expr.leaves, lowerFrom_snd a]
  | .set xs, k | .call _ xs, k => by simp only [Expr.lowerFrom, Expr.leaves, lowerListFrom_snd xs]
  | .record axs, k => by simp only [Expr.lowerFrom, Expr.leaves, lowerRecordFrom_snd axs]
  | .temporal _, k | .provider _, k => by simp [Expr.lowerFrom, Expr.leaves]

theorem lowerListFrom_snd : (xs : List Expr) → (k : Nat) →
    (Expr.lowerListFrom k xs).2 = k + (Expr.leavesList xs).length
  | [], k => by simp [Expr.lowerListFrom, Expr.leavesList]
  | x :: xs, k => by
    simp only [Expr.lowerListFrom, Expr.leavesList, List.length_append, lowerListFrom_snd xs,
      lowerFrom_snd x]
    omega

theorem lowerRecordFrom_snd : (axs : List (Attr × Expr)) → (k : Nat) →
    (Expr.lowerRecordFrom k axs).2 = k + (Expr.leavesRecord axs).length
  | [], k => by simp [Expr.lowerRecordFrom, Expr.leavesRecord]
  | (_, x) :: axs, k => by
    simp only [Expr.lowerRecordFrom, Expr.leavesRecord, List.length_append,
      lowerRecordFrom_snd axs, lowerFrom_snd x]
    omega

end

/-! ## Evaluation -/

/-- The context holds the leaves `ls`' values at the attributes numbered from `k`. -/
def LeavesAt (θ : Leaves) (ctx : Map Attr Value) (k : Nat) (ls : List Leaf) : Prop :=
  ∀ i l, ls[i]? = some l → ctx.find? (leafAttr (k + i)) = some (θ.valueOf l)

theorem LeavesAt.left {θ : Leaves} {ctx : Map Attr Value} {k : Nat} {l₁ l₂ : List Leaf}
    (h : LeavesAt θ ctx k (l₁ ++ l₂)) : LeavesAt θ ctx k l₁ := fun i l hl => by
  have hi : i < l₁.length := by
    rcases Nat.lt_or_ge i l₁.length with h' | h'
    · exact h'
    · rw [List.getElem?_eq_none h'] at hl; cases hl
  exact h i l (by rw [List.getElem?_append_left hi]; exact hl)

theorem LeavesAt.right {θ : Leaves} {ctx : Map Attr Value} {k : Nat} {l₁ l₂ : List Leaf}
    (h : LeavesAt θ ctx k (l₁ ++ l₂)) : LeavesAt θ ctx (k + l₁.length) l₂ := fun i l hl => by
  have := h (l₁.length + i) l (by rw [List.getElem?_append_right (by omega)]; simpa using hl)
  rw [← Nat.add_assoc] at this
  exact this

section

variable (θ : Leaves) (req : Request) (es : Entities) (ctx : Map Attr Value)
  (reserved : List Attr)

mutual

/-- **Lowering preserves evaluation.** On a context that holds the leaves' values at their
attributes, and agrees with the request's context outside `reserved`, Cedar's evaluator on the
lowered expression gives what Dogwood's evaluator gives on the expression, when the expression
reads the context only outside `reserved`. -/
theorem evaluate_lower (hctx : ∀ a, a ∉ reserved → ctx.find? a = req.context.find? a) :
    (x : Expr) → (k : Nat) → x.ReadsContext reserved → LeavesAt θ ctx k x.leaves →
      Cedar.Spec.evaluate (x.lowerFrom k).1 { req with context := ctx } es =
        evaluate θ x req es
  | .lit _, _, _, _ => by simp [Expr.lowerFrom, Cedar.Spec.evaluate, evaluate]
  | .var v, _, hr, _ => by
    cases v <;> simp_all [Expr.lowerFrom, Cedar.Spec.evaluate, evaluate, Expr.ReadsContext]
  | .ite a b c, k, hr, hl => by
    obtain ⟨ha, hb, hc⟩ := hr
    have ea := evaluate_lower hctx a k ha hl.left.left
    have eb := evaluate_lower hctx b (a.lowerFrom k).2 hb (by rw [lowerFrom_snd]; exact hl.left.right)
    have ec := evaluate_lower hctx c (b.lowerFrom (a.lowerFrom k).2).2 hc (by
      rw [lowerFrom_snd, lowerFrom_snd]
      have := hl.right
      simpa [Nat.add_assoc] using this)
    simp only [Expr.lowerFrom, Cedar.Spec.evaluate, evaluate, ea, eb, ec]
  | .and a b, k, hr, hl => by
    have ea := evaluate_lower hctx a k hr.1 hl.left
    have eb := evaluate_lower hctx b (a.lowerFrom k).2 hr.2 (by rw [lowerFrom_snd]; exact hl.right)
    simp only [Expr.lowerFrom, Cedar.Spec.evaluate, evaluate, ea, eb]
  | .or a b, k, hr, hl => by
    have ea := evaluate_lower hctx a k hr.1 hl.left
    have eb := evaluate_lower hctx b (a.lowerFrom k).2 hr.2 (by rw [lowerFrom_snd]; exact hl.right)
    simp only [Expr.lowerFrom, Cedar.Spec.evaluate, evaluate, ea, eb]
  | .binaryApp _ a b, k, hr, hl => by
    have ea := evaluate_lower hctx a k hr.1 hl.left
    have eb := evaluate_lower hctx b (a.lowerFrom k).2 hr.2 (by rw [lowerFrom_snd]; exact hl.right)
    simp only [Expr.lowerFrom, Cedar.Spec.evaluate, evaluate, ea, eb]
  | .unaryApp _ a, k, hr, hl => by
    simp only [Expr.lowerFrom, Cedar.Spec.evaluate, evaluate, evaluate_lower hctx a k hr hl]
  | .getAttr a x, k, hr, hl => by
    simp only [Expr.ReadsContext] at hr
    split at hr
    · rename_i hcx
      cases a with
      | var v =>
        cases v <;> simp [Expr.isContext] at hcx
        simp [Expr.lowerFrom, Cedar.Spec.evaluate, evaluate, Cedar.Spec.getAttr,
          Cedar.Spec.attrsOf, Map.findOrErr, hctx x hr]
      | _ => simp [Expr.isContext] at hcx
    · simp only [Expr.lowerFrom, Cedar.Spec.evaluate, evaluate, evaluate_lower hctx a k hr hl]
  | .hasAttr a x, k, hr, hl => by
    simp only [Expr.ReadsContext] at hr
    split at hr
    · rename_i hcx
      cases a with
      | var v =>
        cases v <;> simp [Expr.isContext] at hcx
        simp [Expr.lowerFrom, Cedar.Spec.evaluate, evaluate, Cedar.Spec.hasAttr,
          Cedar.Spec.attrsOf, Map.contains, hctx x hr]
      | _ => simp [Expr.isContext] at hcx
    · simp only [Expr.lowerFrom, Cedar.Spec.evaluate, evaluate, evaluate_lower hctx a k hr hl]
  | .extHasAttr a x xs, k, hr, hl => by
    simp only [Expr.ReadsContext] at hr
    split at hr
    · rename_i hcx
      cases a with
      | var v =>
        cases v <;> simp [Expr.isContext] at hcx
        simp [Expr.lowerFrom, Cedar.Spec.evaluate, evaluate, Cedar.Spec.hasAttrs,
          Cedar.Spec.hasAttrs.loop, Cedar.Spec.attrsOf, hctx x hr]
      | _ => simp [Expr.isContext] at hcx
    · simp only [Expr.lowerFrom, Cedar.Spec.evaluate, evaluate, evaluate_lower hctx a k hr hl]
  | .set xs, k, hr, hl => by
    simp only [Expr.lowerFrom, Cedar.Spec.evaluate, evaluate]
    rw [List.mapM₁_eq_mapM (Cedar.Spec.evaluate · _ es), List.mapM₁_eq_mapM (evaluate θ · req es),
      evaluate_lowerList hctx xs k hr hl]
  | .call _ xs, k, hr, hl => by
    simp only [Expr.lowerFrom, Cedar.Spec.evaluate, evaluate]
    rw [List.mapM₁_eq_mapM (Cedar.Spec.evaluate · _ es), List.mapM₁_eq_mapM (evaluate θ · req es),
      evaluate_lowerList hctx xs k hr hl]
  | .record axs, k, hr, hl => by
    simp only [Expr.lowerFrom, Cedar.Spec.evaluate, evaluate]
    rw [List.mapM₂_eq_mapM (fun (ax : Attr × Cedar.Spec.Expr) =>
        bindAttr ax.fst (Cedar.Spec.evaluate ax.snd { req with context := ctx } es)),
      List.mapM₂_eq_mapM (fun (ax : Attr × Expr) => bindAttr ax.fst (evaluate θ ax.snd req es)),
      evaluate_lowerRecord hctx axs k hr hl]
  | .temporal φ, k, _, hl => by
    have := hl 0 (.inl φ) rfl
    simp only [Nat.add_zero, Leaves.valueOf] at this
    simp [Expr.lowerFrom, Cedar.Spec.evaluate, evaluate, Cedar.Spec.getAttr, Cedar.Spec.attrsOf,
      Map.findOrErr, this]
  | .provider c, k, _, hl => by
    have := hl 0 (.inr c) rfl
    simp only [Nat.add_zero, Leaves.valueOf] at this
    simp [Expr.lowerFrom, Cedar.Spec.evaluate, evaluate, Cedar.Spec.getAttr, Cedar.Spec.attrsOf,
      Map.findOrErr, this]

theorem evaluate_lowerList (hctx : ∀ a, a ∉ reserved → ctx.find? a = req.context.find? a) :
    (xs : List Expr) → (k : Nat) → Expr.ReadsContextList reserved xs →
      LeavesAt θ ctx k (Expr.leavesList xs) →
      (Expr.lowerListFrom k xs).1.mapM (Cedar.Spec.evaluate · { req with context := ctx } es) =
        xs.mapM (evaluate θ · req es)
  | [], _, _, _ => rfl
  | x :: xs, k, hr, hl => by
    have e₁ := evaluate_lower hctx x k hr.1 hl.left
    have e₂ := evaluate_lowerList hctx xs (x.lowerFrom k).2 hr.2
      (by rw [lowerFrom_snd]; exact hl.right)
    simp only [Expr.lowerListFrom, List.mapM_cons, e₁, e₂]

theorem evaluate_lowerRecord (hctx : ∀ a, a ∉ reserved → ctx.find? a = req.context.find? a) :
    (axs : List (Attr × Expr)) → (k : Nat) → Expr.ReadsContextRecord reserved axs →
      LeavesAt θ ctx k (Expr.leavesRecord axs) →
      (Expr.lowerRecordFrom k axs).1.mapM (fun ax =>
          bindAttr ax.fst (Cedar.Spec.evaluate ax.snd { req with context := ctx } es)) =
        axs.mapM (fun ax => bindAttr ax.fst (evaluate θ ax.snd req es))
  | [], _, _, _ => rfl
  | (a, x) :: axs, k, hr, hl => by
    have e₁ := evaluate_lower hctx x k hr.1 hl.left
    have e₂ := evaluate_lowerRecord hctx axs (x.lowerFrom k).2 hr.2
      (by rw [lowerFrom_snd]; exact hl.right)
    simp only [Expr.lowerRecordFrom, List.mapM_cons, e₁, e₂]

end

end

section

variable (θ : Leaves) (req : Request) (es : Entities)

mutual

/-- **Lowering preserves evaluation on the request itself**, whatever the expression reads of the
context, when the request's own context holds the leaves' values at their attributes: for an
expression without leaves, always. -/
theorem evaluate_lower_self :
    (x : Expr) → (k : Nat) → LeavesAt θ req.context k x.leaves →
      Cedar.Spec.evaluate (x.lowerFrom k).1 req es = evaluate θ x req es
  | .lit _, _, _ => by simp [Expr.lowerFrom, Cedar.Spec.evaluate, evaluate]
  | .var v, _, _ => by cases v <;> simp [Expr.lowerFrom, Cedar.Spec.evaluate, evaluate]
  | .ite a b c, k, hl => by
    have ea := evaluate_lower_self a k hl.left.left
    have eb := evaluate_lower_self b (a.lowerFrom k).2 (by rw [lowerFrom_snd]; exact hl.left.right)
    have ec := evaluate_lower_self c (b.lowerFrom (a.lowerFrom k).2).2 (by
      rw [lowerFrom_snd, lowerFrom_snd]
      have := hl.right
      simpa [Nat.add_assoc] using this)
    simp only [Expr.lowerFrom, Cedar.Spec.evaluate, evaluate, ea, eb, ec]
  | .and a b, k, hl => by
    have ea := evaluate_lower_self a k hl.left
    have eb := evaluate_lower_self b (a.lowerFrom k).2 (by rw [lowerFrom_snd]; exact hl.right)
    simp only [Expr.lowerFrom, Cedar.Spec.evaluate, evaluate, ea, eb]
  | .or a b, k, hl => by
    have ea := evaluate_lower_self a k hl.left
    have eb := evaluate_lower_self b (a.lowerFrom k).2 (by rw [lowerFrom_snd]; exact hl.right)
    simp only [Expr.lowerFrom, Cedar.Spec.evaluate, evaluate, ea, eb]
  | .binaryApp _ a b, k, hl => by
    have ea := evaluate_lower_self a k hl.left
    have eb := evaluate_lower_self b (a.lowerFrom k).2 (by rw [lowerFrom_snd]; exact hl.right)
    simp only [Expr.lowerFrom, Cedar.Spec.evaluate, evaluate, ea, eb]
  | .unaryApp _ a, k, hl => by
    simp only [Expr.lowerFrom, Cedar.Spec.evaluate, evaluate, evaluate_lower_self a k hl]
  | .getAttr a _, k, hl => by
    simp only [Expr.lowerFrom, Cedar.Spec.evaluate, evaluate, evaluate_lower_self a k hl]
  | .hasAttr a _, k, hl => by
    simp only [Expr.lowerFrom, Cedar.Spec.evaluate, evaluate, evaluate_lower_self a k hl]
  | .extHasAttr a _ _, k, hl => by
    simp only [Expr.lowerFrom, Cedar.Spec.evaluate, evaluate, evaluate_lower_self a k hl]
  | .set xs, k, hl => by
    simp only [Expr.lowerFrom, Cedar.Spec.evaluate, evaluate]
    rw [List.mapM₁_eq_mapM (Cedar.Spec.evaluate · _ es), List.mapM₁_eq_mapM (evaluate θ · req es),
      evaluate_lowerList_self xs k hl]
  | .call _ xs, k, hl => by
    simp only [Expr.lowerFrom, Cedar.Spec.evaluate, evaluate]
    rw [List.mapM₁_eq_mapM (Cedar.Spec.evaluate · _ es), List.mapM₁_eq_mapM (evaluate θ · req es),
      evaluate_lowerList_self xs k hl]
  | .record axs, k, hl => by
    simp only [Expr.lowerFrom, Cedar.Spec.evaluate, evaluate]
    rw [List.mapM₂_eq_mapM (fun (ax : Attr × Cedar.Spec.Expr) =>
        bindAttr ax.fst (Cedar.Spec.evaluate ax.snd req es)),
      List.mapM₂_eq_mapM (fun (ax : Attr × Expr) => bindAttr ax.fst (evaluate θ ax.snd req es)),
      evaluate_lowerRecord_self axs k hl]
  | .temporal φ, k, hl => by
    have := hl 0 (.inl φ) rfl
    simp only [Nat.add_zero, Leaves.valueOf] at this
    simp [Expr.lowerFrom, Cedar.Spec.evaluate, evaluate, Cedar.Spec.getAttr, Cedar.Spec.attrsOf,
      Map.findOrErr, this]
  | .provider c, k, hl => by
    have := hl 0 (.inr c) rfl
    simp only [Nat.add_zero, Leaves.valueOf] at this
    simp [Expr.lowerFrom, Cedar.Spec.evaluate, evaluate, Cedar.Spec.getAttr, Cedar.Spec.attrsOf,
      Map.findOrErr, this]

theorem evaluate_lowerList_self :
    (xs : List Expr) → (k : Nat) → LeavesAt θ req.context k (Expr.leavesList xs) →
      (Expr.lowerListFrom k xs).1.mapM (Cedar.Spec.evaluate · req es) =
        xs.mapM (evaluate θ · req es)
  | [], _, _ => rfl
  | x :: xs, k, hl => by
    have e₁ := evaluate_lower_self x k hl.left
    have e₂ := evaluate_lowerList_self xs (x.lowerFrom k).2 (by rw [lowerFrom_snd]; exact hl.right)
    simp only [Expr.lowerListFrom, List.mapM_cons, e₁, e₂]

theorem evaluate_lowerRecord_self :
    (axs : List (Attr × Expr)) → (k : Nat) → LeavesAt θ req.context k (Expr.leavesRecord axs) →
      (Expr.lowerRecordFrom k axs).1.mapM (fun ax =>
          bindAttr ax.fst (Cedar.Spec.evaluate ax.snd req es)) =
        axs.mapM (fun ax => bindAttr ax.fst (evaluate θ ax.snd req es))
  | [], _, _ => rfl
  | (a, x) :: axs, k, hl => by
    have e₁ := evaluate_lower_self x k hl.left
    have e₂ := evaluate_lowerRecord_self axs (x.lowerFrom k).2
      (by rw [lowerFrom_snd]; exact hl.right)
    simp only [Expr.lowerRecordFrom, List.mapM_cons, e₁, e₂]

end

end

/-! ## Rules -/

mutual

/-- A Cedar expression has no leaves, so lowering leaves it as it is. -/
theorem lowerFrom_ofCedar : (x : Cedar.Spec.Expr) → (k : Nat) →
    (Expr.ofCedar x).lowerFrom k = (x, k)
  | .lit _, _ | .var _, _ => rfl
  | .ite a b c, k => by
    simp only [Expr.ofCedar, Expr.lowerFrom, lowerFrom_ofCedar a, lowerFrom_ofCedar b,
      lowerFrom_ofCedar c]
  | .and a b, k => by simp only [Expr.ofCedar, Expr.lowerFrom, lowerFrom_ofCedar a, lowerFrom_ofCedar b]
  | .or a b, k => by simp only [Expr.ofCedar, Expr.lowerFrom, lowerFrom_ofCedar a, lowerFrom_ofCedar b]
  | .binaryApp _ a b, k => by
    simp only [Expr.ofCedar, Expr.lowerFrom, lowerFrom_ofCedar a, lowerFrom_ofCedar b]
  | .unaryApp _ a, k => by simp only [Expr.ofCedar, Expr.lowerFrom, lowerFrom_ofCedar a]
  | .getAttr a _, k => by simp only [Expr.ofCedar, Expr.lowerFrom, lowerFrom_ofCedar a]
  | .hasAttr a _, k => by simp only [Expr.ofCedar, Expr.lowerFrom, lowerFrom_ofCedar a]
  | .extHasAttr a _ _, k => by simp only [Expr.ofCedar, Expr.lowerFrom, lowerFrom_ofCedar a]
  | .set xs, k => by simp only [Expr.ofCedar, Expr.lowerFrom, lowerListFrom_ofCedar xs]
  | .call _ xs, k => by simp only [Expr.ofCedar, Expr.lowerFrom, lowerListFrom_ofCedar xs]
  | .record axs, k => by simp only [Expr.ofCedar, Expr.lowerFrom, lowerRecordFrom_ofCedar axs]

theorem lowerListFrom_ofCedar : (xs : List Cedar.Spec.Expr) → (k : Nat) →
    Expr.lowerListFrom k (Expr.ofCedarList xs) = (xs, k)
  | [], _ => rfl
  | x :: xs, k => by
    simp only [Expr.ofCedarList, Expr.lowerListFrom, lowerFrom_ofCedar x, lowerListFrom_ofCedar xs]

theorem lowerRecordFrom_ofCedar : (axs : List (Attr × Cedar.Spec.Expr)) → (k : Nat) →
    Expr.lowerRecordFrom k (Expr.ofCedarRecord axs) = (axs, k)
  | [], _ => rfl
  | (_, x) :: axs, k => by
    simp only [Expr.ofCedarRecord, Expr.lowerRecordFrom, lowerFrom_ofCedar x,
      lowerRecordFrom_ofCedar axs]

end

theorem conditions_toExpr_cons (c : Condition) (cs : Conditions) (hcs : cs ≠ []) :
    Conditions.toExpr (c :: cs) = .and c.toExpr (Conditions.toExpr cs) := by
  unfold Conditions.toExpr
  rw [List.reverse_cons]
  cases h : cs.reverse with
  | nil => exact absurd (List.reverse_eq_nil_iff.mp h) hcs
  | cons d rest => simp [List.foldl_append]

theorem cedar_conditions_toExpr_cons (c : Cedar.Spec.Condition) (cs : Cedar.Spec.Conditions)
    (hcs : cs ≠ []) :
    Cedar.Spec.Conditions.toExpr (c :: cs) = .and c.toExpr (Cedar.Spec.Conditions.toExpr cs) := by
  unfold Cedar.Spec.Conditions.toExpr
  rw [List.reverse_cons]
  cases h : cs.reverse with
  | nil => exact absurd (List.reverse_eq_nil_iff.mp h) hcs
  | cons d rest => simp [List.foldl_append]

theorem condition_lowerFrom (c : Condition) (k : Nat) :
    c.toExpr.lowerFrom k =
      ((Cedar.Spec.Condition.mk c.kind (c.body.lowerFrom k).1).toExpr, (c.body.lowerFrom k).2) := by
  obtain ⟨kind, body⟩ := c
  cases kind <;> rfl

theorem conditions_lowerFrom : (cs : Conditions) → (k : Nat) →
    ((Conditions.toExpr cs).lowerFrom k).1 = Cedar.Spec.Conditions.toExpr (Conditions.lowerFrom k cs).1
  | [], _ => rfl
  | [c], k => by
    simp only [Conditions.lowerFrom]
    rw [show Conditions.toExpr [c] = c.toExpr from rfl, condition_lowerFrom]
    rfl
  | c :: d :: cs, k => by
    rw [conditions_toExpr_cons c (d :: cs) (by simp)]
    simp only [Expr.lowerFrom, Conditions.lowerFrom]
    rw [cedar_conditions_toExpr_cons _ _ (by simp)]
    rw [condition_lowerFrom]
    simp only
    have := conditions_lowerFrom (d :: cs) (c.body.lowerFrom k).2
    simp only [Conditions.lowerFrom] at this
    rw [this]

theorem policy_lowerFrom (p : Policy) (k : Nat) :
    (p.lowerFrom k).1.toExpr = (p.toExpr.lowerFrom k).1 := by
  simp only [Policy.lowerFrom, Cedar.Spec.Policy.toExpr, Policy.toExpr, Expr.lowerFrom,
    lowerFrom_ofCedar]
  rw [conditions_lowerFrom]

theorem policy_lowerFrom_snd (p : Policy) (k : Nat) :
    (p.lowerFrom k).2 = k + p.toExpr.leaves.length := by
  have : (p.lowerFrom k).2 = (p.toExpr.lowerFrom k).2 := by
    simp only [Policy.lowerFrom, Policy.toExpr, Expr.lowerFrom, lowerFrom_ofCedar]
    -- The conditions' leaves are numbered from `k`.
    suffices h : ∀ (cs : Conditions) (k : Nat),
        (Conditions.lowerFrom k cs).2 = ((Conditions.toExpr cs).lowerFrom k).2 by
      exact h _ _
    intro cs
    induction cs with
    | nil => intro k; rfl
    | cons c cs ih =>
      intro k
      cases cs with
      | nil =>
        simp only [Conditions.lowerFrom]
        rw [show Conditions.toExpr [c] = c.toExpr from rfl, condition_lowerFrom]
      | cons d cs =>
        rw [conditions_toExpr_cons c (d :: cs) (by simp)]
        simp only [Conditions.lowerFrom, Expr.lowerFrom]
        rw [condition_lowerFrom]
        exact ih _
  rw [this, lowerFrom_snd]

/-- **A lowered rule evaluates as the rule.** -/
theorem evaluate_policy_lower (θ : Leaves) (req : Request) (es : Entities) (ctx : Map Attr Value)
    (reserved : List Attr) (hctx : ∀ a, a ∉ reserved → ctx.find? a = req.context.find? a)
    (p : Policy) (k : Nat) (hr : p.toExpr.ReadsContext reserved)
    (hl : LeavesAt θ ctx k p.toExpr.leaves) :
    Cedar.Spec.evaluate (p.lowerFrom k).1.toExpr { req with context := ctx } es =
      evaluate θ p.toExpr req es := by
  rw [policy_lowerFrom]
  exact evaluate_lower θ req es ctx reserved hctx p.toExpr k hr hl

/-- **The per-request authorizer decides as Cedar decides the lowering.** On a context that holds
every leaf's value at its attribute, and agrees with the request's context outside `reserved`,
Cedar's authorizer on the lowered rules gives Dogwood's response. -/
theorem isAuthorized_lower (θ : Leaves) (req : Request) (es : Entities) (ctx : Map Attr Value)
    (reserved : List Attr) (hctx : ∀ a, a ∉ reserved → ctx.find? a = req.context.find? a) :
    (ps : Policies) → (k : Nat) → (∀ p ∈ ps, p.toExpr.ReadsContext reserved) →
      LeavesAt θ ctx k (ps.flatMap (·.toExpr.leaves)) →
      Cedar.Spec.isAuthorized { req with context := ctx } es (Policies.lowerFrom k ps).1 =
        isAuthorized θ req es ps := by
  intro ps k hr hl
  -- Policy by policy, the lowered rule is satisfied, and errs, as the rule does.
  have key : ∀ (ps : Policies) (k : Nat), (∀ p ∈ ps, p.toExpr.ReadsContext reserved) →
      LeavesAt θ ctx k (ps.flatMap (·.toExpr.leaves)) →
      (∀ eff, (Policies.lowerFrom k ps).1.filterMap
          (Cedar.Spec.satisfiedWithEffect eff · { req with context := ctx } es) =
        ps.filterMap (satisfiedWithEffect θ eff · req es)) ∧
      (Policies.lowerFrom k ps).1.filterMap (Cedar.Spec.errored · { req with context := ctx } es) =
        ps.filterMap (errored θ · req es) := by
    intro ps
    induction ps with
    | nil => intro k _ _; exact ⟨fun _ => rfl, rfl⟩
    | cons p ps ih =>
      intro k hr hl
      simp only [List.flatMap_cons] at hl
      have he := evaluate_policy_lower θ req es ctx reserved hctx p k (hr p (by simp)) hl.left
      have hrest := ih (p.lowerFrom k).2 (fun q hq => hr q (by simp [hq]))
        (by rw [policy_lowerFrom_snd]; exact hl.right)
      refine ⟨fun eff => ?_, ?_⟩
      · simp only [Policies.lowerFrom, List.filterMap_cons, hrest.1 eff]
        simp only [Cedar.Spec.satisfiedWithEffect, satisfiedWithEffect, Cedar.Spec.satisfied,
          satisfied, he]
        rfl
      · simp only [Policies.lowerFrom, List.filterMap_cons, hrest.2]
        simp only [Cedar.Spec.errored, errored, Cedar.Spec.hasError, hasError, he]
        rfl
  obtain ⟨hsat, herr⟩ := key ps k hr hl
  simp only [Cedar.Spec.isAuthorized, isAuthorized, Cedar.Spec.satisfiedPolicies,
    satisfiedPolicies, Cedar.Spec.errorPolicies, errorPolicies, hsat, herr] <;> rfl

/-- **A lowered rule evaluates as the rule, on the request itself**, when the request's context
holds the rule's leaves' values: for a rule without leaves, always. -/
theorem evaluate_policy_lower_self (θ : Leaves) (req : Request) (es : Entities) (p : Policy)
    (k : Nat) (hl : LeavesAt θ req.context k p.toExpr.leaves) :
    Cedar.Spec.evaluate (p.lowerFrom k).1.toExpr req es = evaluate θ p.toExpr req es := by
  rw [policy_lowerFrom]
  exact evaluate_lower_self θ req es p.toExpr k hl

/-- **The per-request authorizer decides as Cedar decides the lowering, on the request
itself**, when the request's context holds every leaf's value at its attribute, whatever the
rules read of the context: for rules without leaves, always. -/
theorem isAuthorized_lower_self (θ : Leaves) (req : Request) (es : Entities) :
    (ps : Policies) → (k : Nat) → LeavesAt θ req.context k (ps.flatMap (·.toExpr.leaves)) →
      Cedar.Spec.isAuthorized req es (Policies.lowerFrom k ps).1 = isAuthorized θ req es ps := by
  intro ps k hl
  have key : ∀ (ps : Policies) (k : Nat), LeavesAt θ req.context k (ps.flatMap (·.toExpr.leaves)) →
      (∀ eff, (Policies.lowerFrom k ps).1.filterMap (Cedar.Spec.satisfiedWithEffect eff · req es) =
        ps.filterMap (satisfiedWithEffect θ eff · req es)) ∧
      (Policies.lowerFrom k ps).1.filterMap (Cedar.Spec.errored · req es) =
        ps.filterMap (errored θ · req es) := by
    intro ps
    induction ps with
    | nil => intro k _; exact ⟨fun _ => rfl, rfl⟩
    | cons p ps ih =>
      intro k hl
      simp only [List.flatMap_cons] at hl
      have he := evaluate_policy_lower_self θ req es p k hl.left
      have hrest := ih (p.lowerFrom k).2 (by rw [policy_lowerFrom_snd]; exact hl.right)
      refine ⟨fun eff => ?_, ?_⟩
      · simp only [Policies.lowerFrom, List.filterMap_cons, hrest.1 eff]
        simp only [Cedar.Spec.satisfiedWithEffect, satisfiedWithEffect, Cedar.Spec.satisfied,
          satisfied, he]
        rfl
      · simp only [Policies.lowerFrom, List.filterMap_cons, hrest.2]
        simp only [Cedar.Spec.errored, errored, Cedar.Spec.hasError, hasError, he]
        rfl
  obtain ⟨hsat, herr⟩ := key ps k hl
  simp only [Cedar.Spec.isAuthorized, isAuthorized, Cedar.Spec.satisfiedPolicies,
    satisfiedPolicies, Cedar.Spec.errorPolicies, errorPolicies, hsat, herr] <;> rfl

end Dogwood.Thm
