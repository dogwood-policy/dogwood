import Dogwood.Thm.Frontend.Cedarify.Rules

/-!
# The actions a rule's hoisted leaves attach to

`scopeTargetActions` computes, for an action scope, the actions of the fragment the scope can
match: for `action == A`, `A`; for `action in [A, …]`, each `A` and every action that is,
transitively, a member of one (`Reaches`); for a bare `action`, every declared action. It then
drops the declared actions that cannot receive a request, keeping the undeclared ones
(`mem_scopeTargetActions`); the result has no duplicates (`nodup_scopeTargetActions`). Every field
cedarify hoists carries its rule's action scope, principal and resource constraints, and the
target actions of that scope (`cedarify_targets`).

The descendants are the fixpoint of one-step expansion (`mem_closure`): expanding a set adds
declared actions it lacks, so after one expansion per declared action, plus one, nothing is
left to add.

The specification reads the same relation off the compiled schema (`actionScopeAdmits`, through
the actions' ancestors); the two agree when Cedar's compilation of the fragment gives each
action, as ancestors, the actions it `Reaches` up to (the schema resolver's business, not
lowering's).
-/

namespace Dogwood.Thm.Frontend.Cedarify

open Dogwood.Frontend
open Dogwood.Frontend.Cedarify
open CedarSchema

/-! ## Reaching an action through `memberOf` -/

/-- `x` is `b`, or, transitively, a member of `b`, in the fragment `f`. -/
inductive Reaches (f : Fragment) (b : ActionKey) : ActionKey → Prop
  | refl : Reaches f b b
  | member {p c : ActionKey} {d : ActionDef} : Reaches f b p → (c, d) ∈ actionDefs f →
      isMemberOf c d p = true → Reaches f b c

/-- The members of `S`'s actions that are not in `S`. -/
def newMembers (f : Fragment) (S : List ActionKey) : List (ActionKey × ActionDef) :=
  (actionDefs f).filter fun (c, d) => !S.contains c && S.any (isMemberOf c d ·)

theorem expandOnce_eq (f : Fragment) (S : List ActionKey) :
    expandOnce f S = S ++ (newMembers f S).map (·.1) := rfl

/-- `S` holds every member of each of its actions. -/
def Closed (f : Fragment) (S : List ActionKey) : Prop :=
  ∀ p ∈ S, ∀ c d, (c, d) ∈ actionDefs f → isMemberOf c d p = true → c ∈ S

theorem mem_newMembers {f : Fragment} {S : List ActionKey} {c : ActionKey} {d : ActionDef} :
    (c, d) ∈ newMembers f S ↔ (c, d) ∈ actionDefs f ∧ c ∉ S ∧ ∃ p ∈ S, isMemberOf c d p = true := by
  simp [newMembers]

theorem closed_of_newMembers {f : Fragment} {S : List ActionKey} (h : newMembers f S = []) :
    Closed f S := by
  intro p hp c d hcd hm
  by_contra hc
  have : (c, d) ∈ newMembers f S := mem_newMembers.mpr ⟨hcd, hc, p, hp, hm⟩
  rw [h] at this
  simp at this

theorem expandN_of_newMembers {f : Fragment} {S : List ActionKey} (h : newMembers f S = []) :
    ∀ n, expandN f n S = S
  | 0 => rfl
  | n + 1 => by
    simp only [expandN, expandOnce_eq, h, List.map_nil, List.append_nil]
    exact expandN_of_newMembers h n

/-- The declared actions outside `S`, counted with their declarations. -/
def missing (f : Fragment) (S : List ActionKey) : Nat :=
  ((actionDefs f).filter fun x => !S.contains x.1).length

theorem length_filter_le_of_imp {α : Type} (p q : α → Bool) :
    ∀ L : List α, (∀ x ∈ L, q x = true → p x = true) → (L.filter q).length ≤ (L.filter p).length
  | [], _ => by simp
  | a :: L, h => by
    have ih := length_filter_le_of_imp p q L fun x hx => h x (by simp [hx])
    cases hq : q a <;> cases hp : p a <;> simp [hq, hp] <;>
      first | omega | (have := h a (by simp) hq; simp_all)

theorem length_filter_lt_of_imp {α : Type} (p q : α → Bool) :
    ∀ L : List α, (∀ x ∈ L, q x = true → p x = true) → (∃ x ∈ L, p x = true ∧ q x = false) →
      (L.filter q).length < (L.filter p).length
  | [], _, ⟨_, hx, _⟩ => by simp at hx
  | a :: L, h, ⟨x, hx, hpx, hqx⟩ => by
    have hle := length_filter_le_of_imp p q L fun y hy => h y (by simp [hy])
    rcases List.mem_cons.mp hx with rfl | hx
    · simp [hpx, hqx]; omega
    · have ih := length_filter_lt_of_imp p q L (fun y hy => h y (by simp [hy])) ⟨x, hx, hpx, hqx⟩
      cases hq : q a <;> cases hp : p a <;> simp [hq, hp] <;>
        first | omega | (have := h a (by simp) hq; simp_all)

theorem missing_lt {f : Fragment} {S : List ActionKey} (h : newMembers f S ≠ []) :
    missing f (expandOnce f S) < missing f S := by
  obtain ⟨⟨c, d⟩, hm⟩ := List.exists_mem_of_ne_nil _ h
  obtain ⟨hcd, hc, -⟩ := mem_newMembers.mp hm
  apply length_filter_lt_of_imp
  · intro x _ hx
    have hx' : x.1 ∉ expandOnce f S := by simpa using hx
    have : x.1 ∉ S := fun hS => hx' (by rw [expandOnce_eq]; exact List.mem_append_left _ hS)
    simpa using this
  · refine ⟨(c, d), hcd, by simpa using hc, ?_⟩
    simp only [expandOnce_eq, Bool.not_eq_false', List.contains_iff_mem, List.mem_append, List.mem_map]
    exact .inr ⟨(c, d), hm, rfl⟩

theorem expandN_closed (f : Fragment) : ∀ n S, missing f S < n → Closed f (expandN f n S)
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, S, h => by
    simp only [expandN]
    by_cases hn : newMembers f S = []
    · rw [show expandOnce f S = S by simp [expandOnce_eq, hn], expandN_of_newMembers hn]
      exact closed_of_newMembers hn
    · exact expandN_closed f n _ (by have := missing_lt hn; omega)

theorem subset_expandN (f : Fragment) : ∀ n (S : List ActionKey), ∀ x ∈ S, x ∈ expandN f n S
  | 0, _, _, hx => hx
  | n + 1, S, x, hx => subset_expandN f n _ x (by simp [expandOnce_eq, hx])

theorem reaches_of_mem_expandN (f : Fragment) (starts : List ActionKey) :
    ∀ n (S : List ActionKey), (∀ x ∈ S, ∃ b ∈ starts, Reaches f b x) →
      ∀ x ∈ expandN f n S, ∃ b ∈ starts, Reaches f b x
  | 0, _, hS, x, hx => hS x hx
  | n + 1, S, hS, x, hx => by
    refine reaches_of_mem_expandN f starts n _ ?_ x hx
    intro y hy
    simp only [expandOnce_eq, List.mem_append, List.mem_map] at hy
    rcases hy with hy | ⟨⟨c, d⟩, hm, rfl⟩
    · exact hS y hy
    · obtain ⟨hcd, -, p, hp, hmem⟩ := mem_newMembers.mp hm
      obtain ⟨b, hb, hr⟩ := hS p hp
      exact ⟨b, hb, .member hr hcd hmem⟩

theorem mem_of_reaches {f : Fragment} {C : List ActionKey} (hC : Closed f C) {b x : ActionKey}
    (hb : b ∈ C) (h : Reaches f b x) : x ∈ C := by
  induction h with
  | refl => exact hb
  | member _ hcd hm ih => exact hC _ ih _ _ hcd hm

/-- **The descendants.** An action is in the closure of `starts` exactly when it is one of them
or, transitively, a member of one. -/
theorem mem_closure {f : Fragment} {starts : List ActionKey} {x : ActionKey} :
    x ∈ closure f starts ↔ ∃ b ∈ starts, Reaches f b x := by
  constructor
  · exact reaches_of_mem_expandN f starts _ starts (fun x hx => ⟨x, hx, .refl⟩) x
  · rintro ⟨b, hb, hr⟩
    have hC : Closed f (closure f starts) :=
      expandN_closed f _ starts (Nat.lt_succ_of_le (List.length_filter_le _ _))
    exact mem_of_reaches hC (subset_expandN f _ starts b hb) hr

/-! ## The target actions -/

/-- The actions an action scope can match: the action itself for `==`, the listed actions and
everything that reaches up to one of them for `in`, every declared action for a bare `action`. -/
def ScopeReaches (f : Fragment) : ScopedAction → ActionKey → Prop
  | .concrete ns id, x => x = (ns, id)
  | .list l, x => ∃ b ∈ l, Reaches f b x
  | .unconstrained, x => ∃ d, (x, d) ∈ actionDefs f

theorem nodup_eraseDups {α : Type} [BEq α] [LawfulBEq α] :
    ∀ (n : Nat) (l : List α), l.length ≤ n → l.eraseDups.Nodup
  | _, [], _ => by simp
  | n + 1, a :: as, h => by
    rw [List.eraseDups_cons]
    refine List.nodup_cons.mpr ⟨?_, nodup_eraseDups n _ ?_⟩
    · simp [List.mem_eraseDups, List.mem_filter]
    · have := List.length_filter_le (fun b => !b == a) as
      simp at h; omega
  | 0, _ :: _, h => by simp at h

/-- **The target actions are exactly the actions the scope can match**, less the declared ones
that cannot receive a request. -/
theorem mem_scopeTargetActions {a : ScopedAction} {f : Fragment} {x : ActionKey} :
    x ∈ scopeTargetActions a f ↔
      ScopeReaches f a x ∧ (isDeclared f x = false ∨ isAppliable f x = true) := by
  simp only [scopeTargetActions, List.mem_eraseDups, List.mem_mergeSort, List.mem_filter,
    Bool.or_eq_true, Bool.not_eq_true']
  apply and_congr_left
  intro _
  cases a with
  | concrete ns id => simp [ScopeReaches]
  | list l => simp only [ScopeReaches]; exact mem_closure
  | unconstrained => simp [ScopeReaches]

theorem nodup_scopeTargetActions (a : ScopedAction) (f : Fragment) :
    (scopeTargetActions a f).Nodup :=
  nodup_eraseDups _ _ (Nat.le_refl _)

/-! ## The fields' scopes -/

/-- Every field of `s` carries the action scope and the principal and resource constraints of a
rule of `all`. -/
def ScopesFrom (all : List Surface.Policy) (s : St) : Prop :=
  (∀ f ∈ s.contextFields, ∃ p ∈ all, f.action = scopeAction p.scope.action ∧
    f.principal = scopeConstraint p.scope.principal ∧ f.resource = scopeConstraint p.scope.resource) ∧
  (∀ f ∈ s.providerFields, ∃ p ∈ all, f.action = scopeAction p.scope.action ∧
    f.principal = scopeConstraint p.scope.principal ∧ f.resource = scopeConstraint p.scope.resource)

theorem ScopesFrom.hoists {all : List Surface.Policy} {decls : Option ProviderDecls.Declarations}
    {enumNames : List (String × String)} {p : Surface.Policy} (hp : p ∈ all) {s s' : St}
    (h : Hoists (ruleEnv decls enumNames p) s s') (hs : ScopesFrom all s) : ScopesFrom all s' := by
  induction h with
  | refl => exact hs
  | temporal t _ ih =>
    apply ih
    obtain ⟨errs, he, -⟩ := hoistTemporal_snd (ruleEnv decls enumNames p) t _
    rw [he]
    refine ⟨fun f hf => ?_, hs.2⟩
    simp only [List.mem_append, List.mem_singleton] at hf
    rcases hf with hf | rfl
    · exact hs.1 f hf
    · exact ⟨p, hp, rfl, rfl, rfl⟩
  | provider inv ms _ ih =>
    apply ih
    obtain ⟨errs, he, -⟩ := hoistProvider_snd (ruleEnv decls enumNames p) inv ms _
    rw [he]
    refine ⟨hs.1, fun f hf => ?_⟩
    simp only [List.mem_append, List.mem_singleton] at hf
    rcases hf with hf | rfl
    · exact hs.2 f hf
    · exact ⟨p, hp, rfl, rfl, rfl⟩

theorem lowerPoliciesFrom_scopes {decls : Option ProviderDecls.Declarations}
    {enumNames : List (String × String)} {d : Option String} {ids : Option (List String)}
    {all : List Surface.Policy} :
    (i : Nat) → (ps : List Surface.Policy) → (acc res : Rules) →
    lowerPoliciesFrom decls enumNames d ids i ps acc = .ok res → (∀ p ∈ ps, p ∈ all) →
    ScopesFrom all acc.st → ScopesFrom all res.st
  | _, [], acc, res, h, _, hs => by
    simp only [lowerPoliciesFrom, Except.ok.injEq] at h
    subst h
    exact hs
  | i, p :: ps, acc, res, h, hall, hs => by
    simp only [lowerPoliciesFrom] at h
    cases hp : lowerPolicy decls enumNames (ruleKey d i) (ruleId d ids i) p acc.st with
    | error _ => simp [hp, bind, Except.bind] at h
    | ok q =>
      obtain ⟨ro, s₁⟩ := q
      simp only [hp, bind, Except.bind] at h
      split at h
      · simp at h
      · have hh := (lowerPolicy_lowers hp).1
        have hs₁ := ScopesFrom.hoists (hall p (by simp)) hh hs
        exact lowerPoliciesFrom_scopes (i + 1) ps _ res h (fun q hq => hall q (by simp [hq])) hs₁

/-- **The target actions of a rule.** Every field cedarify hoists carries the action scope,
principal and resource constraints of one of the set's rules, and its target actions are the
actions that scope matches (`mem_scopeTargetActions`). -/
theorem cedarify_targets {ps : Surface.PolicySet} {frag : CedarSchema.Fragment}
    {decls : Option ProviderDecls.Declarations} {d : Option String} {ids : Option (List String)}
    {w : WithSpec} (h : cedarifyFull ps frag decls d ids = .ok w) :
    (∀ f ∈ w.cedarified.contextFields, ∃ p ∈ ps.policies,
      f.action = scopeAction p.scope.action ∧ f.principal = scopeConstraint p.scope.principal ∧
      f.resource = scopeConstraint p.scope.resource ∧
      f.targetActions = scopeTargetActions (scopeAction p.scope.action) frag) ∧
    (∀ f ∈ w.cedarified.providerFields, ∃ p ∈ ps.policies,
      f.action = scopeAction p.scope.action ∧ f.principal = scopeConstraint p.scope.principal ∧
      f.resource = scopeConstraint p.scope.resource ∧
      f.targetActions = scopeTargetActions (scopeAction p.scope.action) frag) := by
  obtain ⟨enumNames, referenced, rules, hr, rfl⟩ := cedarifyFull_rules h
  have hs := lowerPoliciesFrom_scopes (all := ps.policies) 0 ps.policies _ rules hr (fun _ h => h)
    ⟨by simp, by simp⟩
  refine ⟨fun f hf => ?_, fun f hf => ?_⟩
  · simp only [assemble, List.mem_map] at hf
    obtain ⟨g, hg, rfl⟩ := hf
    obtain ⟨p, hp, ha, hpr, hre⟩ := hs.1 g hg
    exact ⟨p, hp, ha, hpr, hre, by simp [ha]⟩
  · simp only [assemble, List.mem_map] at hf
    obtain ⟨g, hg, rfl⟩ := hf
    obtain ⟨p, hp, ha, hpr, hre⟩ := hs.2 g hg
    exact ⟨p, hp, ha, hpr, hre, by simp [ha]⟩

end Dogwood.Thm.Frontend.Cedarify
