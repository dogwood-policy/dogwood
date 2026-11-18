import Dogwood.Thm.Frontend.Cedarify.Rules

/-!
# How the lowered rules read the request context

The specification requires the Cedar part of a rule to read `context` only through attribute
accesses and `has` tests, of attributes other than the leaves' (`Expr.ReadsContext`, the
`readsContext` clause of `PolicySet.Valid`). Cedarify neither establishes nor checks it: a rule
in the specification's form reads the context exactly as the rule as written does
(`cedarify_readsContext_iff`, with `SReads` the same condition on the surface syntax: `context`
only under `.a` or `has a`, with `a` not reserved). So the condition holds after lowering exactly
when it holds of the source, and lowering accepts sources that violate it
(`Dogwood.Thm.Frontend.Cedarify.Examples`).
-/

namespace Dogwood.Thm.Frontend.Cedarify

open Dogwood.Spec
open Dogwood.Frontend
open Dogwood.Frontend.Cedarify

/-- The surface expression is the variable `context`. -/
def isContextS (e : Surface.Expr) : Bool :=
  match e.kind with
  | .var .context => true
  | _ => false

mutual

/-- The surface expression reads `context` only through an attribute access `context.a` or a
test `context has a`, with `a` outside `R`. Leaves (temporal blocks, provider chains) do not
count: the specification's `ReadsContext` does not look into them. -/
def SReads (R : List String) : Surface.Expr → Prop
  | ⟨k, _⟩ => SReadsKind R k

def SReadsKind (R : List String) : Surface.ExprKind → Prop
  | .lit _ => True
  | .var v => v ≠ .context
  | .slot _ | .extension _ | .call _ _ | .methodCall _ _ _ | .paramRef _ => True
  | .unaryApp _ e | .like e _ | .is e _ none => SReads R e
  | .is e _ (some x) => SReads R e ∧ SReads R x
  | .getAttr e a => if isContextS e then a ∉ R else SReads R e
  | .hasAttr e attrs => if isContextS e then attrs.headD "" ∉ R else SReads R e
  | .binaryApp _ l r => SReads R l ∧ SReads R r
  | .ite c t e => SReads R c ∧ SReads R t ∧ SReads R e
  | .set xs => SReadsList R xs
  | .record m => SReadsRecord R m

def SReadsList (R : List String) : List Surface.Expr → Prop
  | [] => True
  | x :: xs => SReads R x ∧ SReadsList R xs

def SReadsRecord (R : List String) : List (String × Surface.Expr) → Prop
  | [] => True
  | (_, x) :: xs => SReads R x ∧ SReadsRecord R xs

end

variable {R : List String}

theorem readsContext_unaryS (op : Surface.UnOp) (d : Expr) :
    (unaryS op d).ReadsContext R ↔ d.ReadsContext R := by
  cases op <;> simp [unaryS, Expr.ReadsContext, Expr.ReadsContextList]

theorem readsContext_andS (l r : Expr) :
    (andS l r).ReadsContext R ↔ l.ReadsContext R ∧ r.ReadsContext R := by
  unfold andS
  split <;> simp [Expr.ReadsContext]

theorem readsContext_orS (l r : Expr) :
    (orS l r).ReadsContext R ↔ l.ReadsContext R ∧ r.ReadsContext R := by
  unfold orS
  split <;> simp [Expr.ReadsContext]

theorem readsContext_binaryS (op : Surface.BinOp) (l r : Expr) :
    (binaryS op l r).ReadsContext R ↔ l.ReadsContext R ∧ r.ReadsContext R := by
  cases op <;> simp [binaryS, Expr.ReadsContext, Expr.ReadsContextList, readsContext_andS,
    readsContext_orS]

theorem isContext_unaryS (op : Surface.UnOp) (d : Expr) : (unaryS op d).isContext = false := by
  cases op <;> rfl

theorem isContext_binaryS (op : Surface.BinOp) (l r : Expr) :
    (binaryS op l r).isContext = false := by
  cases op <;> first
    | rfl
    | (simp only [binaryS, andS, orS]; split <;> rfl)

theorem hasRestS_isContext {h : Expr} (hh : h.isContext = false) :
    ∀ (g : Expr) (rest : List String), (hasRestS h g rest).isContext = false := by
  intro g rest
  induction rest generalizing h g with
  | nil => exact hh
  | cons b rest ih => exact ih (h := .and h (.hasAttr g b)) rfl _

theorem isContext_hasPathS (d : Expr) (attrs : List String) :
    (hasPathS d attrs).isContext = false := by
  cases attrs with
  | nil => rfl
  | cons a rest =>
    simp only [hasPathS]
    split
    · rfl
    · exact hasRestS_isContext (h := .hasAttr d a) rfl _ _

theorem readsContext_hasRestS :
    ∀ (rest : List String) (h g : Expr), g.isContext = false →
      (h.ReadsContext R → g.ReadsContext R) →
      ((hasRestS h g rest).ReadsContext R ↔ h.ReadsContext R)
  | [], _, _, _, _ => Iff.rfl
  | b :: rest, h, g, hg, hhg => by
    simp only [hasRestS]
    rw [readsContext_hasRestS rest (.and h (.hasAttr g b)) (.getAttr g b) rfl (by
      intro hr
      simp only [Expr.ReadsContext, hg] at hr ⊢
      simpa [Expr.isContext, hg] using hr.2)]
    simp only [Expr.ReadsContext, hg, Bool.false_eq_true, ↓reduceIte]
    exact ⟨fun h => h.1, fun h => ⟨h, hhg h⟩⟩

theorem readsContext_hasPathS (d : Expr) (attrs : List String) :
    (hasPathS d attrs).ReadsContext R ↔
      if d.isContext then attrs.headD "" ∉ R else d.ReadsContext R := by
  cases attrs with
  | nil => simp [hasPathS, Expr.ReadsContext]
  | cons a rest =>
    simp only [hasPathS, List.headD_cons]
    split
    · simp [Expr.ReadsContext]
    · rw [readsContext_hasRestS rest (.hasAttr d a) (.getAttr d a) rfl (by simp [Expr.ReadsContext])]
      simp [Expr.ReadsContext]

/-- What lowering an expression keeps of how it reads the context. -/
def ReadsSame (R : List String) (e : Surface.Expr) (o : Out) : Prop :=
  (o.spec.ReadsContext R ↔ SReads R e) ∧ o.spec.isContext = isContextS e

theorem readsSame_leaf {R : List String} {e : Surface.Expr} {o : Out}
    (h : o.spec.ReadsContext R ∧ o.spec.isContext = false) (he : SReads R e)
    (hc : isContextS e = false) : ReadsSame R e o :=
  ⟨⟨fun _ => he, fun _ => h.1⟩, by rw [h.2, hc]⟩

theorem hoistTemporal_spec (env : Env) (t : Surface.Temporal.Block) (s : St) :
    ∃ φ, (hoistTemporal env t s).1.spec = .temporal φ := by
  simp only [hoistTemporal]; split <;> exact ⟨_, rfl⟩

theorem hoistProvider_spec (env : Env) (inv : Frontend.Provider.Invocation)
    (ms : List Frontend.Provider.MethodCall) (s : St) :
    ∃ c, (hoistProvider env inv ms s).1.spec = .provider c := by
  simp only [hoistProvider]; split <;> exact ⟨_, rfl⟩

mutual

theorem lowerExpr_reads (env : Env) (R : List String) : (e : Surface.Expr) → (s : St) →
    (o : Out) → (s' : St) → lowerExpr env e s = .ok (o, s') → ReadsSame R e o
  | ⟨k, sp⟩, s, o, s', h => lowerKind_reads env R sp k s o s' h

theorem lowerKind_reads (env : Env) (R : List String) (sp : Span) : (k : Surface.ExprKind) →
    (s : St) → (o : Out) → (s' : St) → lowerKind env sp k s = .ok (o, s') →
    ReadsSame R ⟨k, sp⟩ o
  | .lit l, s, o, s', h => by
    simp only [lowerKind, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp [ReadsSame, SReads, SReadsKind, Expr.ReadsContext, Expr.isContext, isContextS]
  | .var v, s, o, s', h => by
    simp only [lowerKind, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    cases v <;> simp [ReadsSame, SReads, SReadsKind, Expr.ReadsContext, Expr.isContext, isContextS]
  | .slot _, s, o, s', h => by
    simp only [lowerKind, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp [ReadsSame, SReads, SReadsKind, Expr.ReadsContext, Expr.isContext, isContextS]
  | .extension t, s, o, s', h => by
    simp only [lowerKind, Except.ok.injEq] at h
    have ho : o = (hoistTemporal env t s).1 := by rw [h]
    obtain ⟨φ, hφ⟩ := hoistTemporal_spec env t s
    subst ho
    exact readsSame_leaf (by simp [hφ, Expr.ReadsContext, Expr.isContext]) (by simp [SReads, SReadsKind])
      (by simp [isContextS])
  | .unaryApp op e, s, o, s', h => by
    simp only [lowerKind] at h
    cases he : lowerExpr env e s with
    | error _ => simp [he, bind, Except.bind] at h
    | ok p =>
      obtain ⟨o₁, s₁⟩ := p
      simp [he, bind, Except.bind, pure, Except.pure] at h
      obtain ⟨rfl, rfl⟩ := h
      have ih := lowerExpr_reads env R e s o₁ s₁ he
      exact ⟨by simp [readsContext_unaryS, SReads, SReadsKind, ih.1],
        by simp [isContext_unaryS, isContextS]⟩
  | .binaryApp op l r, s, o, s', h => by
    simp only [lowerKind] at h
    cases hl : lowerExpr env l s with
    | error _ => simp [hl, bind, Except.bind] at h
    | ok p =>
      obtain ⟨o₁, s₁⟩ := p
      cases hr : lowerExpr env r s₁ with
      | error _ => simp [hl, hr, bind, Except.bind] at h
      | ok q =>
        obtain ⟨o₂, s₂⟩ := q
        simp [hl, hr, bind, Except.bind, pure, Except.pure] at h
        obtain ⟨rfl, rfl⟩ := h
        have ih₁ := lowerExpr_reads env R l s o₁ s₁ hl
        have ih₂ := lowerExpr_reads env R r s₁ o₂ s₂ hr
        exact ⟨by simp [readsContext_binaryS, SReads, SReadsKind, ih₁.1, ih₂.1],
          by simp [isContext_binaryS, isContextS]⟩
  | .getAttr e a, s, o, s', h => by
    simp only [lowerKind] at h
    cases he : lowerExpr env e s with
    | error _ => simp [he, bind, Except.bind] at h
    | ok p =>
      obtain ⟨o₁, s₁⟩ := p
      simp [he, bind, Except.bind, pure, Except.pure] at h
      obtain ⟨rfl, rfl⟩ := h
      have ih := lowerExpr_reads env R e s o₁ s₁ he
      refine ⟨?_, by simp [Expr.isContext, isContextS]⟩
      simp only [Expr.ReadsContext, SReads, SReadsKind, ih.2]
      split <;> simp [ih.1]
  | .hasAttr e attrs, s, o, s', h => by
    simp only [lowerKind] at h
    cases he : lowerExpr env e s with
    | error _ => simp [he, bind, Except.bind] at h
    | ok p =>
      obtain ⟨o₁, s₁⟩ := p
      simp [he, bind, Except.bind, pure, Except.pure] at h
      obtain ⟨rfl, rfl⟩ := h
      have ih := lowerExpr_reads env R e s o₁ s₁ he
      refine ⟨?_, by simp [isContext_hasPathS, isContextS]⟩
      simp only [readsContext_hasPathS, SReads, SReadsKind, ih.2]
      split <;> simp [ih.1]
  | .like e p, s, o, s', h => by
    simp only [lowerKind] at h
    cases he : lowerExpr env e s with
    | error _ => simp [he, bind, Except.bind] at h
    | ok q =>
      obtain ⟨o₁, s₁⟩ := q
      simp [he, bind, Except.bind, pure, Except.pure] at h
      obtain ⟨rfl, rfl⟩ := h
      have ih := lowerExpr_reads env R e s o₁ s₁ he
      exact ⟨by simp [Expr.ReadsContext, SReads, SReadsKind, ih.1], by simp [Expr.isContext, isContextS]⟩
  | .is e ty none, s, o, s', h => by
    simp only [lowerKind] at h
    cases he : lowerExpr env e s with
    | error _ => simp [he, bind, Except.bind] at h
    | ok q =>
      obtain ⟨o₁, s₁⟩ := q
      simp [he, bind, Except.bind, pure, Except.pure] at h
      obtain ⟨rfl, rfl⟩ := h
      have ih := lowerExpr_reads env R e s o₁ s₁ he
      exact ⟨by simp [Expr.ReadsContext, SReads, SReadsKind, ih.1], by simp [Expr.isContext, isContextS]⟩
  | .is e ty (some x), s, o, s', h => by
    simp only [lowerKind] at h
    cases he : lowerExpr env e s with
    | error _ => simp [he, bind, Except.bind] at h
    | ok p =>
      obtain ⟨o₁, s₁⟩ := p
      cases hx : lowerExpr env x s₁ with
      | error _ => simp [he, hx, bind, Except.bind] at h
      | ok q =>
        obtain ⟨o₂, s₂⟩ := q
        simp [he, hx, bind, Except.bind, pure, Except.pure] at h
        obtain ⟨rfl, rfl⟩ := h
        have ih₁ := lowerExpr_reads env R e s o₁ s₁ he
        have ih₂ := lowerExpr_reads env R x s₁ o₂ s₂ hx
        refine ⟨?_, by simp [Expr.isContext, isContextS]⟩
        simp only [Expr.ReadsContext, SReads, SReadsKind, ih₁.1, ih₂.1]
        exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, h.1, h.2⟩⟩
  | .ite c t e, s, o, s', h => by
    simp only [lowerKind] at h
    cases hc : lowerExpr env c s with
    | error _ => simp [hc, bind, Except.bind] at h
    | ok p =>
      obtain ⟨o₁, s₁⟩ := p
      cases ht : lowerExpr env t s₁ with
      | error _ => simp [hc, ht, bind, Except.bind] at h
      | ok q =>
        obtain ⟨o₂, s₂⟩ := q
        cases he : lowerExpr env e s₂ with
        | error _ => simp [hc, ht, he, bind, Except.bind] at h
        | ok w =>
          obtain ⟨o₃, s₃⟩ := w
          simp [hc, ht, he, bind, Except.bind, pure, Except.pure] at h
          obtain ⟨rfl, rfl⟩ := h
          have ih₁ := lowerExpr_reads env R c s o₁ s₁ hc
          have ih₂ := lowerExpr_reads env R t s₁ o₂ s₂ ht
          have ih₃ := lowerExpr_reads env R e s₂ o₃ s₃ he
          exact ⟨by simp [Expr.ReadsContext, SReads, SReadsKind, ih₁.1, ih₂.1, ih₃.1],
            by simp [Expr.isContext, isContextS]⟩
  | .set xs, s, o, s', h => by
    simp only [lowerKind] at h
    cases hx : lowerList env xs s with
    | error _ => simp [hx, bind, Except.bind] at h
    | ok p =>
      obtain ⟨os, s₁⟩ := p
      simp [hx, bind, Except.bind, pure, Except.pure] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨by simp [Expr.ReadsContext, SReads, SReadsKind, lowerList_reads env R xs s os s₁ hx],
        by simp [Expr.isContext, isContextS]⟩
  | .record m, s, o, s', h => by
    simp only [lowerKind] at h
    cases hx : lowerRecord env m s with
    | error _ => simp [hx, bind, Except.bind] at h
    | ok p =>
      obtain ⟨os, s₁⟩ := p
      simp [hx, bind, Except.bind, pure, Except.pure] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨by simp [Expr.ReadsContext, SReads, SReadsKind, lowerRecord_reads env R m s os s₁ hx],
        by simp [Expr.isContext, isContextS]⟩
  | .call name args, s, o, s', h => by
    simp only [lowerKind] at h
    split at h
    · cases hi : toInvocation name args sp with
      | error _ => simp [hi, bind, Except.bind] at h
      | ok inv =>
        simp [hi, bind, Except.bind, pure, Except.pure] at h
        have ho : o = (hoistProvider env inv [] s).1 := by rw [h]
        obtain ⟨c, hc⟩ := hoistProvider_spec env inv [] s
        subst ho
        exact readsSame_leaf (by simp [hc, Expr.ReadsContext, Expr.isContext])
          (by simp [SReads, SReadsKind]) (by simp [isContextS])
    · simp [throw, throwThe, MonadExceptOf.throw] at h
  | .methodCall recv m args, s, o, s', h => by
    simp only [lowerKind] at h
    cases hp : peel ⟨.methodCall recv m args, sp⟩ with
    | error _ => simp [hp, bind, Except.bind] at h
    | ok r =>
      cases r with
      | none => simp [hp, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
      | some r =>
        obtain ⟨accs, inv⟩ := r
        simp only [hp, bind, Except.bind] at h
        split at h
        · simp [throw, throwThe, MonadExceptOf.throw] at h
        · simp [pure, Except.pure] at h
          have ho : o = (hoistProvider env inv (List.filterMap Accessor.method? accs).reverse s).1 := by
            rw [h]
          obtain ⟨c, hc⟩ := hoistProvider_spec env inv (List.filterMap Accessor.method? accs).reverse s
          subst ho
          exact readsSame_leaf (by simp [hc, Expr.ReadsContext, Expr.isContext])
            (by simp [SReads, SReadsKind]) (by simp [isContextS])
  | .paramRef _, s, o, s', h => by simp [lowerKind, throw, throwThe, MonadExceptOf.throw] at h

theorem lowerList_reads (env : Env) (R : List String) : (xs : List Surface.Expr) → (s : St) →
    (os : List Out) → (s' : St) → lowerList env xs s = .ok (os, s') →
    (Expr.ReadsContextList R (os.map (·.spec)) ↔ SReadsList R xs)
  | [], s, os, s', h => by
    simp only [lowerList, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp [Expr.ReadsContextList, SReadsList]
  | x :: xs, s, os, s', h => by
    simp only [lowerList] at h
    cases hx : lowerExpr env x s with
    | error _ => simp [hx, bind, Except.bind] at h
    | ok p =>
      obtain ⟨o₁, s₁⟩ := p
      cases hxs : lowerList env xs s₁ with
      | error _ => simp [hx, hxs, bind, Except.bind] at h
      | ok q =>
        obtain ⟨os₂, s₂⟩ := q
        simp [hx, hxs, bind, Except.bind, pure, Except.pure] at h
        obtain ⟨rfl, rfl⟩ := h
        simp [Expr.ReadsContextList, SReadsList, (lowerExpr_reads env R x s o₁ s₁ hx).1,
          lowerList_reads env R xs s₁ os₂ s₂ hxs]

theorem lowerRecord_reads (env : Env) (R : List String) : (xs : List (String × Surface.Expr)) →
    (s : St) → (os : List (String × Out)) → (s' : St) → lowerRecord env xs s = .ok (os, s') →
    (Expr.ReadsContextRecord R (os.map fun (a, o) => (a, o.spec)) ↔ SReadsRecord R xs)
  | [], s, os, s', h => by
    simp only [lowerRecord, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp [Expr.ReadsContextRecord, SReadsRecord]
  | (a, x) :: xs, s, os, s', h => by
    simp only [lowerRecord] at h
    cases hx : lowerExpr env x s with
    | error _ => simp [hx, bind, Except.bind] at h
    | ok p =>
      obtain ⟨o₁, s₁⟩ := p
      cases hxs : lowerRecord env xs s₁ with
      | error _ => simp [hx, hxs, bind, Except.bind] at h
      | ok q =>
        obtain ⟨os₂, s₂⟩ := q
        simp [hx, hxs, bind, Except.bind, pure, Except.pure] at h
        obtain ⟨rfl, rfl⟩ := h
        simp [Expr.ReadsContextRecord, SReadsRecord, (lowerExpr_reads env R x s o₁ s₁ hx).1,
          lowerRecord_reads env R xs s₁ os₂ s₂ hxs]

end

/-! ## Rules -/

theorem lowerClauses_reads (env : Env) (R : List String) : (cs : List Surface.Cond) → (s : St) →
    (os : List Out) → (s' : St) → lowerClauses env cs s = .ok (os, s') →
    Zips (fun c o => o.spec.ReadsContext R ↔ SReads R c.body) cs os
  | [], s, os, s', h => by
    simp only [lowerClauses, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    trivial
  | c :: cs, s, os, s', h => by
    simp only [lowerClauses] at h
    cases hc : lowerExpr env c.body s with
    | error _ => simp [hc, bind, Except.bind] at h
    | ok p =>
      obtain ⟨o₁, s₁⟩ := p
      cases hcs : lowerClauses env cs s₁ with
      | error _ => simp [hc, hcs, bind, Except.bind] at h
      | ok q =>
        obtain ⟨os₂, s₂⟩ := q
        simp [hc, hcs, bind, Except.bind, pure, Except.pure] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨?_, lowerClauses_reads env R cs s₁ os₂ s₂ hcs⟩
        have ih := (lowerExpr_reads env R c.body s o₁ s₁ hc).1
        cases c.keyword
        · exact ih
        · simpa [Expr.ReadsContext] using ih

theorem readsContext_conjoin (os : List Out) :
    (conjoin os).spec.ReadsContext R ↔ ∀ o ∈ os, o.spec.ReadsContext R := by
  cases os with
  | nil => simp [conjoin, Expr.ReadsContext]
  | cons o os =>
    simp only [conjoin]
    exact balancedFold_all andOut (fun o => o.spec.ReadsContext R)
      (fun a b => readsContext_andS a.spec b.spec) o os

theorem readsContext_ofCedar_scope (s : Cedar.Spec.Scope) (v : Cedar.Spec.Var) (hv : v ≠ .context) :
    (Expr.ofCedar (s.toExpr v)).ReadsContext R := by
  cases s <;> simp [Cedar.Spec.Scope.toExpr, Cedar.Spec.Var.eqEntityUID, Cedar.Spec.Var.inEntityUID,
    Cedar.Spec.Var.isEntityType, Expr.ofCedar, Expr.ReadsContext, hv]

theorem readsContextList_lits (es : List Cedar.Spec.EntityUID) :
    Expr.ReadsContextList R (Expr.ofCedarList (es.map fun e => .lit (.entityUID e))) := by
  induction es with
  | nil => simp [Expr.ofCedarList, Expr.ReadsContextList]
  | cons e es ih => simpa [Expr.ofCedarList, Expr.ReadsContextList, Expr.ofCedar, Expr.ReadsContext]
      using ih

theorem readsContext_ofCedar_actionScope (a : Cedar.Spec.ActionScope) :
    (Expr.ofCedar a.toExpr).ReadsContext R := by
  cases a with
  | actionScope s => exact readsContext_ofCedar_scope s .action (by simp)
  | actionInAny es =>
    simp only [Cedar.Spec.ActionScope.toExpr, Expr.ofCedar, Expr.ReadsContext, 
      ]
    exact ⟨by simp, readsContextList_lits es⟩

theorem zips_iff_all {α β : Type} {P : β → Prop} {Q : α → Prop} :
    ∀ {cs : List α} {os : List β}, Zips (fun c o => P o ↔ Q c) cs os →
      ((∀ o ∈ os, P o) ↔ ∀ c ∈ cs, Q c)
  | [], [], _ => by simp
  | c :: cs, o :: os, h => by
    simp only [List.mem_cons, forall_eq_or_imp, h.1, zips_iff_all h.2]
  | [], _ :: _, h | _ :: _, [], h => h.elim

theorem lowerPolicy_reads {decls : Option ProviderDecls.Declarations}
    {enumNames : List (String × String)} {key id : String} {p : Surface.Policy} {s : St}
    {ro : RuleOut} {s' : St} (h : lowerPolicy decls enumNames key id p s = .ok (ro, s')) :
    ro.spec.toExpr.ReadsContext R ↔ ∀ c ∈ p.conditions, SReads R c.body := by
  simp only [lowerPolicy] at h
  cases hc : lowerClauses (ruleEnv decls enumNames p) p.conditions { s with key, ordinal := 0 } with
  | error _ => simp [hc, bind, Except.bind] at h
  | ok q =>
    obtain ⟨os, s₁⟩ := q
    simp only [hc, bind, Except.bind] at h
    split at h
    · simp [throw, throwThe, MonadExceptOf.throw] at h
    · simp [pure, Except.pure] at h
      obtain ⟨rfl, rfl⟩ := h
      have hz := lowerClauses_reads _ R p.conditions _ os s₁ hc
      simp only [Policy.toExpr, Expr.ReadsContext, Conditions.toExpr, List.reverse_cons,
        List.reverse_nil, List.nil_append, List.foldl_nil, Condition.toExpr]
      rw [readsContext_conjoin]
      have hps := readsContext_ofCedar_scope (R := R) (scopeOf p.scope.principal) .principal (by simp)
      have hrs := readsContext_ofCedar_scope (R := R) (scopeOf p.scope.resource) .resource (by simp)
      have has := readsContext_ofCedar_actionScope (R := R) (actionScopeOf p.scope.action)
      simp only [Cedar.Spec.PrincipalScope.toExpr, Cedar.Spec.ResourceScope.toExpr]
      have := zips_iff_all hz
      exact ⟨fun ⟨_, _, _, hall⟩ => this.mp hall, fun hall => ⟨hps, has, hrs, this.mpr hall⟩⟩

/-- **Lowering keeps how a rule reads the context.** Each rule in the specification's form reads
the context through attribute accesses and `has` tests of attributes outside `R` (the
specification's `ReadsContext R`) exactly when its clauses as written do (`SReads R`), for any
`R`: the specification's leaf names, or the crate's. Lowering does not check it. -/
theorem cedarify_readsContext_iff {ps : Surface.PolicySet} {frag : CedarSchema.Fragment}
    {decls : Option ProviderDecls.Declarations} {d : Option String} {ids : Option (List String)}
    {w : WithSpec} (h : cedarifyFull ps frag decls d ids = .ok w) (R : List String) :
    Zips (fun p q => q.toExpr.ReadsContext R ↔ ∀ c ∈ p.conditions, SReads R c.body)
      ps.policies w.spec :=
  cedarifyFull_zips (fun hp => lowerPolicy_reads hp) h

end Dogwood.Thm.Frontend.Cedarify
