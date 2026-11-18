import Dogwood.Thm.Frontend.Validate.CompleteInterface
import Dogwood.Thm.Frontend.Validate.Provider

/-!
# The provider dialect's checks are complete

The converse of `provider_sound`: a provider leaf the specification accepts (`Provider.Call.Declared`,
and `Provider.Call.TypedIn` in every request environment of its rule) is one on which the crate's
provider dialect (`Validate.providerLeafFindings`) finds nothing (`provider_complete`), except where
the crate is stricter than the specification:

* `providerExceptionsOk`: an entity type the call references that is not a declared
  enum, a method named like a Cedar extension method, a path argument under a reserved context
  name, and a scope-attribute argument whose type differs between the entity types the rule
  admits;
* `providerCompleteOk`: a declaration that declares a method twice (the crate reads the first,
  the specification any), a string literal declared with a kind other than `string` that the crate
  types `String` (an unknown kind, or an entity without a type), and, in a rule that admits no
  request environment (where `Provider.Call.TypedIn` holds of every call), a bare `context`
  argument or a set literal declared with a kind other than `set`.

The proof runs the soundness proof backwards: a path the specification types in every environment
resolves on every target action and entity type (`descend_of_pathType?`, `resolveScopePath_cases`),
the crate's type of an argument in an environment is the specification's (`typeIn?_of_argType?`),
the literal types `argsMatchDecl` gives fix the declared kinds (`paramType_of_int` and the like),
and `Signature.Chains` is the chain check (`chain_nil`). A method's declaration in the crate's
signature is the one `lookup` finds when the declaration declares each method once
(`lookup_of_mem`).
-/

namespace Dogwood.Thm.Frontend

open Dogwood.Frontend Dogwood.Frontend.Validate
open Dogwood.Spec (Path)
open Dogwood.Spec.Temporal (TypingCtx pathType?)
open Cedar.Validation (CedarType RecordType QualifiedType Schema ActionSchemaEntry)
open ProviderDecls (ParamType ProviderDecl MethodDecl)

/-! ## The exceptions -/

mutual

/-- No argument of the list, a set's elements included, is the bare `context`. -/
def providerNoBareContext : List Provider.Arg → Bool
  | [] => true
  | .set items :: rest => providerNoBareContext items && providerNoBareContext rest
  | .field p :: rest => p != ["context"] && providerNoBareContext rest
  | _ :: rest => providerNoBareContext rest

end

/-- The literal arguments of a list are declared with their literal's kind where the specification
does not check the kind: a string literal is declared `string` (the specification checks its Cedar
type, which the crate also gives an unknown kind and an entity without a type), and, in a rule that
admits no request environment (`envless`), a set literal is declared `set` (the specification checks
the type of a set only in a request environment). -/
def providerLiteralKindsExact (envless : Bool) (args : List Provider.Arg) (params : List ParamType) :
    Bool :=
  (args.zip params).all fun x =>
    match x.1 with
    | .string _ => x.2.paramType == "string"
    | .set _ => !envless || x.2.paramType == "set"
    | _ => true

/-- The declaration declares each method once. -/
def providerMethodsDistinct (d : ProviderDecl) : Bool :=
  decide (d.methods.map (·.1)).Nodup

/-- A provider leaf avoids the crate's provider rules that are stricter than the specification and
that `providerExceptionsOk` does not state: its declaration declares each method once, its literal
arguments, and those of each method, have their literal's kind as `providerLiteralKindsExact`
requires, and, when its rule admits no request environment, no argument is the bare `context`. -/
def providerCompleteOk (S : Schema) (g : LoweredProviderField) (d : ProviderDecl) : Bool :=
  let envless := (providerCtx S g).envs.isEmpty
  providerMethodsDistinct d &&
  providerLiteralKindsExact envless g.invocation.args d.argumentTypes &&
  g.methods.all (fun m =>
    match d.methods.lookup m.name with
    | some md => providerLiteralKindsExact envless m.args md.argumentTypes
    | none => true) &&
  (!envless || (providerNoBareContext g.invocation.args &&
    g.methods.all fun m => providerNoBareContext m.args))

namespace ProviderComplete

/-! ## Lists -/

theorem exists_of_forall₂_mem_left {α β : Type} {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → ∀ a ∈ l₁, ∃ b ∈ l₂, R a b
  | _, _, .nil, _, ha => by cases ha
  | _ :: _, b :: _, .cons hab hrest, a, ha => by
    rcases List.mem_cons.mp ha with rfl | ha
    · exact ⟨b, List.mem_cons_self, hab⟩
    · obtain ⟨b', hb', h⟩ := exists_of_forall₂_mem_left hrest a ha
      exact ⟨b', List.mem_cons_of_mem _ hb', h⟩

theorem zip_forall₂ {α β γ δ : Type} {R : α → β → Prop} {f : γ → δ} :
    ∀ {l₁ : List α} {l₂ : List β} {ps : List γ} {a : α} {p : γ}, List.Forall₂ R l₁ l₂ →
      (a, p) ∈ l₁.zip ps → ∃ b, R a b ∧ (b, f p) ∈ l₂.zip (ps.map f)
  | _, _, [], _, _, _, h => by simp at h
  | [], [], _ :: _, _, _, .nil, h => by simp at h
  | _ :: _, y :: _, _ :: _, _, _, .cons hxy hrest, h => by
    simp only [List.zip_cons_cons, List.mem_cons, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | h
    · exact ⟨y, hxy, by simp⟩
    · obtain ⟨b, hb, hm⟩ := zip_forall₂ (f := f) hrest h
      exact ⟨b, hb, by simp [hm]⟩

theorem mem_zip_of_length {α β : Type} : ∀ {l₁ : List α} {l₂ : List β} {a : α},
    l₁.length = l₂.length → a ∈ l₁ → ∃ b, (a, b) ∈ l₁.zip l₂
  | [], _, _, _, h => by cases h
  | _ :: _, [], _, hl, _ => by simp at hl
  | _ :: _, y :: _, _, hl, h => by
    rcases List.mem_cons.mp h with rfl | h
    · exact ⟨y, by simp⟩
    · obtain ⟨b, hb⟩ := mem_zip_of_length (by simpa using hl) h
      exact ⟨b, by simp [hb]⟩

theorem lookup_of_mem {β : Type} : ∀ {l : List (String × β)} {k : String} {v : β},
    (l.map (·.1)).Nodup → (k, v) ∈ l → l.lookup k = some v
  | [], _, _, _, h => by cases h
  | (k', v') :: l, k, v, hn, h => by
    rw [List.map_cons, List.nodup_cons] at hn
    rcases List.mem_cons.mp h with h₁ | h₁
    · simp only [Prod.mk.injEq] at h₁
      obtain ⟨rfl, rfl⟩ := h₁
      simp [List.lookup]
    · have hne : k ≠ k' := by
        intro heq
        subst heq
        exact hn.1 (List.mem_map_of_mem (f := (·.1)) h₁)
      have hne' : (k == k') = false := by simpa using hne
      simp only [List.lookup, hne']
      exact lookup_of_mem hn.2 h₁

theorem mem_of_head?_eq {α : Type} {l : List α} {a : α} (h : l.head? = some a) : a ∈ l := by
  cases l with
  | nil => cases h
  | cons b l =>
    simp only [List.head?_cons, Option.some.injEq] at h
    subst h
    exact List.mem_cons_self

/-! ## Paths -/

/-- The converse of `pathType?_of_descend'`: a path with a declared type resolves. -/
theorem descend_of_pathType? : ∀ {p : Path} {rty : RecordType} {pre : Path} {a : String}
    {t : CedarType}, pathType? (fun _ => true) rty pre (a :: p) = some t →
    ∃ q, rty.find? a = some q ∧ descend q.getType p = .resolved t
  | [], rty, pre, a, t, h => by
    rw [pathType?] at h
    cases hq : rty.find? a with
    | none => rw [hq] at h; cases h
    | some q =>
      rw [hq] at h
      simp only [Bool.or_true, if_true, Option.some.injEq] at h
      exact ⟨q, rfl, by simp [descend, h]⟩
  | seg :: p, rty, pre, a, t, h => by
    rw [pathType?] at h
    cases hq : rty.find? a with
    | none => rw [hq] at h; cases h
    | some q =>
      rw [hq] at h
      simp only [Bool.or_true, if_true] at h
      cases hty : q.getType with
      | record rty' =>
        rw [hty] at h
        obtain ⟨q', hq', hd⟩ := descend_of_pathType? h
        exact ⟨q, rfl, by rw [hty]; simp only [descend, hq']; exact hd⟩
      | _ => rw [hty] at h; cases h

/-- The converse of `descend_of_go`. -/
theorem go_of_descend : ∀ {p : Path} {ty t : CedarType}, descend ty p = .resolved t →
    resolveOne.go ty p = .ok t
  | [], ty, t, h => by
    simp only [descend, PathResolution.resolved.injEq] at h
    simp [resolveOne.go, h]
  | seg :: p, ty, t, h => by
    cases ty with
    | record rty =>
      simp only [descend] at h
      simp only [resolveOne.go]
      cases hq : rty.find? seg with
      | none => rw [hq] at h; cases h
      | some q => rw [hq] at h; exact go_of_descend h
    | _ => simp [descend] at h

/-! ## The request environments -/

theorem mem_envs_of {C : ProviderCtx} {uid : Cedar.Spec.EntityUID} {entry : ActionSchemaEntry}
    {p r : Cedar.Spec.EntityType} (ht : (uid, entry) ∈ C.targets)
    (hp : p ∈ admittedTypes C.schema entry .principal C.principal)
    (hr : r ∈ admittedTypes C.schema entry .resource C.resource) :
    (⟨uid, entry, p, r⟩ : ReqEnv) ∈ C.envs := by
  simp only [ProviderCtx.envs, List.mem_flatMap, List.mem_map]
  exact ⟨(uid, entry), ht, p, hp, r, hr, rfl⟩

theorem admitted_of_admitsAnyEnv {S : Schema} {entry : ActionSchemaEntry} {p r : ScopeConstraint}
    (h : admitsAnyEnv S entry p r = true) :
    (∃ x, x ∈ admittedTypes S entry .principal p) ∧ (∃ y, y ∈ admittedTypes S entry .resource r) := by
  simp only [admitsAnyEnv, Bool.and_eq_true, List.any_eq_true] at h
  obtain ⟨⟨x, hx, hx'⟩, ⟨y, hy, hy'⟩⟩ := h
  exact ⟨⟨x, by simp [admittedTypes, hx, hx']⟩, ⟨y, by simp [admittedTypes, hy, hy']⟩⟩

/-- Every entity type a target action admitting an environment admits for a root is the root's
type in an environment of it. -/
theorem env_of_root {C : ProviderCtx} {uid : Cedar.Spec.EntityUID} {entry : ActionSchemaEntry}
    (ht : (uid, entry) ∈ C.targets) (hadm : admitsAnyEnv C.schema entry C.principal C.resource = true)
    (r : Root) {ety : Cedar.Spec.EntityType} (hety : ety ∈ admittedTypes C.schema entry r (C.narrow r)) :
    ∃ e ∈ C.envs, e.entry = entry ∧ rootType e r = ety := by
  obtain ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ := admitted_of_admitsAnyEnv hadm
  cases r with
  | principal => exact ⟨⟨uid, entry, ety, y⟩, mem_envs_of ht hety hy, rfl, rfl⟩
  | resource => exact ⟨⟨uid, entry, x, ety⟩, mem_envs_of ht hx hety, rfl, rfl⟩

theorem env_of_target {C : ProviderCtx} {uid : Cedar.Spec.EntityUID} {entry : ActionSchemaEntry}
    (ht : (uid, entry) ∈ C.targets) (hadm : admitsAnyEnv C.schema entry C.principal C.resource = true) :
    ∃ e ∈ C.envs, e.entry = entry := by
  obtain ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ := admitted_of_admitsAnyEnv hadm
  exact ⟨⟨uid, entry, x, y⟩, mem_envs_of ht hx hy, rfl⟩

/-! ## The exceptions, argument by argument -/

theorem providerArgsOk_cons (C : ProviderCtx) (a : Provider.Arg) (rest : List Provider.Arg) :
    providerArgsOk C (a :: rest) = (providerArgsOk C [a] && providerArgsOk C rest) := by
  cases a with
  | set items => simp [providerArgsOk]
  | field p =>
    match p with
    | [] => simp [providerArgsOk]
    | [x] => simp [providerArgsOk]
    | root :: y :: ys =>
      by_cases h : root = "context"
      · subst h; simp [providerArgsOk]
      · simp [providerArgsOk]
  | _ => simp [providerArgsOk]

theorem providerArgsOk_mem {C : ProviderCtx} :
    ∀ {args : List Provider.Arg}, providerArgsOk C args = true → ∀ a ∈ args, providerArgsOk C [a] = true
  | [], _, a, ha => by cases ha
  | b :: bs, h, a, ha => by
    rw [providerArgsOk_cons, Bool.and_eq_true] at h
    rcases List.mem_cons.mp ha with rfl | ha
    · exact h.1
    · exact providerArgsOk_mem h.2 a ha

theorem noBareContext_cons (a : Provider.Arg) (rest : List Provider.Arg) :
    providerNoBareContext (a :: rest) = (providerNoBareContext [a] && providerNoBareContext rest) := by
  cases a <;> simp [providerNoBareContext]

theorem noBareContext_mem :
    ∀ {args : List Provider.Arg}, providerNoBareContext args = true → ∀ a ∈ args,
      providerNoBareContext [a] = true
  | [], _, a, ha => by cases ha
  | b :: bs, h, a, ha => by
    rw [noBareContext_cons, Bool.and_eq_true] at h
    rcases List.mem_cons.mp ha with rfl | ha
    · exact h.1
    · exact noBareContext_mem h.2 a ha


/-! ## Declared kinds -/

section kinds

variable (names : List (String × String))

theorem paramType_of_int {p : ParamType} (h : paramCType names p = .int) :
    p.paramType = "integer" ∨ p.paramType = "long" := by
  obtain ⟨kind, fields, items, required, et⟩ := p
  simp only
  unfold paramCType at h
  split at h
  all_goals first | exact .inl rfl | exact .inr rfl | (cases h; done) | (split at h <;> cases h)

theorem paramType_of_decimal {p : ParamType} (h : paramCType names p = .ext .decimal) :
    p.paramType = "decimal" := by
  obtain ⟨kind, fields, items, required, et⟩ := p
  simp only
  unfold paramCType at h
  split at h
  all_goals first | rfl | (cases h; done) | (split at h <;> cases h)

theorem paramType_of_bool {p : ParamType} (h : paramCType names p = .bool .anyBool) :
    p.paramType = "bool" ∨ p.paramType = "boolean" := by
  obtain ⟨kind, fields, items, required, et⟩ := p
  simp only
  unfold paramCType at h
  split at h
  all_goals first | exact .inl rfl | exact .inr rfl | (cases h; done) | (split at h <;> cases h)

end kinds

/-! ## Paths that the specification types exist -/

/-- A scope path that resolves on every entity type the action admits for the root, under the
rule's narrowing, is not missing on any. -/
theorem resolveScopePath_cases {S : Schema} {entry : ActionSchemaEntry} {r : Root}
    {narrow : ScopeConstraint} {first : String} {rest : List String}
    (h : ∀ ety ∈ admittedTypes S entry r narrow, ∀ attrs, entityAttrs? S ety = some attrs →
      ∃ t, resolveOne attrs first rest = .ok t) :
    resolveScopePath S entry r narrow (first :: rest) = .unknown ∨
      resolveScopePath S entry r narrow (first :: rest) = .resolved ∨
      ∃ ts, resolveScopePath S entry r narrow (first :: rest) = .ambiguous ts := by
  unfold resolveScopePath
  simp only
  split
  · exact .inl rfl
  · split
    · exact .inl rfl
    · rename_i hany
      generalize hF : List.mergeSort _ _ = failed
      have hlen := congrArg List.length hF
      rw [List.length_mergeSort, List.filterMap_eq_nil_iff.mpr ?_] at hlen
      · cases failed with
        | cons _ _ => simp at hlen
        | nil =>
          simp only
          split
          · exact .inr (.inr ⟨_, rfl⟩)
          · exact .inr (.inl rfl)
      · intro x hx
        obtain ⟨ety, hety, rfl⟩ := List.mem_map.mp hx
        have hsome : (entityAttrs? S ety).isSome = true := by
          simp only [List.any_eq_true, not_exists, not_and, Option.isNone_iff_eq_none] at hany
          cases hq : entityAttrs? S ety with
          | none => exact absurd hq (hany ety hety)
          | some _ => rfl
        obtain ⟨attrs, hattrs⟩ := Option.isSome_iff_exists.mp hsome
        obtain ⟨t, ht⟩ := h ety hety attrs hattrs
        simp [hattrs, ht]

/-- A `context` path whose head lowering does not reserve resolves where the specification gives
it a declared type. -/
theorem resolveContextPath_of_typeIn {C' : TypingCtx} {S : Schema} {e : ReqEnv}
    (hv : EnvView C' S e) {h : String} {rest : List String} (hh : isHoistedName h = false)
    {t : CedarType} (ht : (Dogwood.Spec.Provider.Arg.context (h :: rest)).typeIn? C' = some t) :
    resolveContextPath e.entry.context (h :: rest) = .resolved t := by
  simp only [Dogwood.Spec.Provider.Arg.typeIn?, Dogwood.Spec.declaredPathType?] at ht
  obtain ⟨q, hq, hd⟩ := descend_of_pathType? ht
  rw [hv.context h hh] at hq
  simp [resolveContextPath, hh, hq, hd]

/-- A scope attribute path the specification types in an environment resolves on the root's
entity type there. -/
theorem resolveOne_of_typeIn {C' : TypingCtx} {S : Schema} {e : ReqEnv} (hv : EnvView C' S e)
    (r : Root) {first : String} {rest : List String} {attrs : RecordType}
    (hattrs : entityAttrs? S (rootType e r) = some attrs)
    (hsome : ((Dogwood.Spec.Provider.Arg.scope r.toSpec (first :: rest)).typeIn? C').isSome = true) :
    ∃ t, resolveOne attrs first rest = .ok t := by
  have hattrs' : C'.env.ets.attrs? (C'.scopeType r.toSpec) = some attrs := by
    rw [scopeType_toSpec hv r, hv.ets]; exact hattrs
  simp only [Dogwood.Spec.Provider.Arg.typeIn?, hattrs', Option.bind_some] at hsome
  obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp hsome
  simp only [Dogwood.Spec.declaredPathType?] at ht
  obtain ⟨q, hq, hd⟩ := descend_of_pathType? ht
  refine ⟨t, ?_⟩
  unfold resolveOne
  rw [hq]
  exact go_of_descend hd


theorem typeIn?_context_nil (C' : TypingCtx) :
    (Dogwood.Spec.Provider.Arg.context []).typeIn? C' = none := by
  simp [Dogwood.Spec.Provider.Arg.typeIn?, Dogwood.Spec.declaredPathType?, pathType?]

/-- **A path argument the specification types in every environment exists** on every target
action that admits an environment: it is not the bare `context` (which has no type), unless the
rule admits no environment and the exception excludes it. -/
theorem pathProblem_none {C : ProviderCtx} {p : List String} {a' : Dogwood.Spec.Provider.Arg}
    (hs : Provider.Arg.toSpec (.field p) = .ok a')
    (hty : ∀ e ∈ C.envs, ∃ C', EnvView C' C.schema e ∧ (a'.typeIn? C').isSome = true)
    (hbare : C.envs = [] → p ≠ ["context"]) (hok : providerArgsOk C [.field p] = true) :
    C.pathProblem p = none := by
  rcases toSpec_field' hs with ⟨rest, rfl, rfl⟩ | ⟨r, rest, rfl, rfl⟩
  · match rest with
    | [] =>
      exfalso
      by_cases hE : C.envs = []
      · exact hbare hE rfl
      · obtain ⟨e, he⟩ := List.exists_mem_of_ne_nil _ hE
        obtain ⟨C', _, hsome⟩ := hty e he
        rw [typeIn?_context_nil] at hsome
        cases hsome
    | h :: rest' =>
      have hh : isHoistedName h = false := by simpa [providerArgsOk] using hok
      simp only [ProviderCtx.pathProblem, List.findSome?_eq_none_iff]
      intro ⟨uid, entry⟩ hmem
      simp only
      split
      · rfl
      · rename_i hadm
        have hadm : admitsAnyEnv C.schema entry C.principal C.resource = true := by simpa using hadm
        obtain ⟨e, he, rfl⟩ := env_of_target hmem hadm
        obtain ⟨C', hv, hsome⟩ := hty e he
        obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp hsome
        simp [resolveContextPath_of_typeIn hv hh ht]
  · have hroot : (r.name == "context") = false := by cases r <;> rfl
    match rest with
    | [] => simp [ProviderCtx.pathProblem, hroot]
    | first :: rest' =>
      have hr? : (if r.name == "principal" then some Root.principal
          else if r.name == "resource" then some Root.resource else none) = some r := by
        cases r <;> rfl
      simp only [ProviderCtx.pathProblem, List.findSome?_eq_none_iff]
      intro ⟨uid, entry⟩ hmem
      simp only [hroot, Bool.false_eq_true, if_false, hr?]
      split
      · rfl
      · rename_i hadm
        have hadm : admitsAnyEnv C.schema entry C.principal C.resource = true := by simpa using hadm
        have hres := resolveScopePath_cases (S := C.schema) (entry := entry) (r := r)
          (narrow := C.narrow r) (first := first) (rest := rest') fun ety hety attrs hattrs => by
          obtain ⟨e, he, rfl, rfl⟩ := env_of_root hmem hadm r hety
          obtain ⟨C', hv, hsome⟩ := hty e he
          exact resolveOne_of_typeIn hv r hattrs hsome
        rcases hres with h | h | ⟨_, h⟩ <;> simp [h]

/-- A typed argument that is not a set has a type. -/
theorem typeIn?_of_hasTypeIn {C' : TypingCtx} {a' : Dogwood.Spec.Provider.Arg} {ty : CedarType}
    (hns : ∀ items, a' ≠ .set items) (h : a'.hasTypeIn C' ty = true) : a'.typeIn? C' = some ty := by
  cases a' with
  | set items => exact absurd rfl (hns items)
  | _ => simpa [Dogwood.Spec.Provider.Arg.hasTypeIn] using h

theorem toSpec_field_not_set {p : List String} {a' : Dogwood.Spec.Provider.Arg}
    (hs : Provider.Arg.toSpec (.field p) = .ok a') : ∀ items, a' ≠ .set items := by
  rcases toSpec_field' hs with ⟨_, _, rfl⟩ | ⟨_, _, _, rfl⟩ <;> intro _ h <;> cases h

theorem toSpec_set {items : List Provider.Arg} {a' : Dogwood.Spec.Provider.Arg}
    (hs : Provider.Arg.toSpec (.set items) = .ok a') :
    ∃ items', Provider.Arg.toSpec.argsToSpec items = .ok items' ∧ a' = .set items' := by
  rw [Provider.Arg.toSpec.eq_9] at hs
  cases h : Provider.Arg.toSpec.argsToSpec items with
  | error _ => rw [h] at hs; cases hs
  | ok items' =>
    rw [h] at hs
    simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hs
    exact ⟨items', rfl, hs.symm⟩

theorem argsToSpec_cons {x : Provider.Arg} {xs : List Provider.Arg}
    {items' : List Dogwood.Spec.Provider.Arg}
    (h : Provider.Arg.toSpec.argsToSpec (x :: xs) = .ok items') :
    ∃ x' xs', x.toSpec = .ok x' ∧ Provider.Arg.toSpec.argsToSpec xs = .ok xs' ∧ items' = x' :: xs' := by
  rw [Provider.Arg.toSpec.argsToSpec.eq_2] at h
  cases hx : x.toSpec with
  | error _ => rw [hx] at h; cases h
  | ok x' =>
    cases hxs : Provider.Arg.toSpec.argsToSpec xs with
    | error _ => rw [hx, hxs] at h; cases h
    | ok xs' =>
      rw [hx, hxs] at h
      simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
      exact ⟨x', xs', rfl, rfl, h.symm⟩

mutual

/-- The existence check passes an argument the specification types in every environment. -/
theorem argPaths_nil {C : ProviderCtx} : (a : Provider.Arg) → (a' : Dogwood.Spec.Provider.Arg) →
    Provider.Arg.toSpec a = .ok a' → providerArgsOk C [a] = true →
    (C.envs = [] → providerNoBareContext [a] = true) →
    (∀ e ∈ C.envs, ∃ C', EnvView C' C.schema e ∧ ∃ ty, a'.hasTypeIn C' ty = true) →
    C.pathProblems [a] = []
  | .field p, a', hs, hok, hbare, hty => by
    simp only [ProviderCtx.pathProblems, List.append_nil, Option.toList_eq_nil_iff]
    refine pathProblem_none hs (fun e he => ?_) (fun hE hp => ?_) hok
    · obtain ⟨C', hv, ty, h⟩ := hty e he
      exact ⟨C', hv, by rw [typeIn?_of_hasTypeIn (toSpec_field_not_set hs) h]; rfl⟩
    · have := hbare hE
      subst hp
      simp [providerNoBareContext] at this
  | .set items, a', hs, hok, hbare, hty => by
    obtain ⟨items', h, rfl⟩ := toSpec_set hs
    simp only [ProviderCtx.pathProblems, List.append_nil]
    refine itemPaths_nil items items' h (by simpa [providerArgsOk] using hok)
      (fun hE => by simpa [providerNoBareContext] using hbare hE) fun e he => ?_
    obtain ⟨C', hv, ty, h⟩ := hty e he
    cases ty with
    | set τ => exact ⟨C', hv, τ, by simpa [Dogwood.Spec.Provider.Arg.hasTypeIn] using h⟩
    | _ => simp [Dogwood.Spec.Provider.Arg.hasTypeIn] at h
  | .string _, _, _, _, _, _ => by simp [ProviderCtx.pathProblems]
  | .integer _, _, _, _, _, _ => by simp [ProviderCtx.pathProblems]
  | .decimal _, _, _, _, _, _ => by simp [ProviderCtx.pathProblems]
  | .bool _, _, _, _, _, _ => by simp [ProviderCtx.pathProblems]

/-- The existence check passes the elements of a set the specification types in every
environment. -/
theorem itemPaths_nil {C : ProviderCtx} : (items : List Provider.Arg) →
    (items' : List Dogwood.Spec.Provider.Arg) → Provider.Arg.toSpec.argsToSpec items = .ok items' →
    providerArgsOk C items = true → (C.envs = [] → providerNoBareContext items = true) →
    (∀ e ∈ C.envs, ∃ C', EnvView C' C.schema e ∧ ∃ τ,
      Dogwood.Spec.Provider.Arg.allHaveTypeIn C' items' τ = true) →
    C.pathProblems items = []
  | [], _, _, _, _, _ => by simp [ProviderCtx.pathProblems]
  | x :: xs, items', h, hok, hbare, hty => by
    obtain ⟨x', xs', hx, hxs, rfl⟩ := argsToSpec_cons h
    rw [providerArgsOk_cons, Bool.and_eq_true] at hok
    rw [pathProblems_cons, List.append_eq_nil_iff]
    refine ⟨argPaths_nil x x' hx hok.1
        (fun hE => by have := hbare hE; rw [noBareContext_cons, Bool.and_eq_true] at this; exact this.1)
        (fun e he => ?_),
      itemPaths_nil xs xs' hxs hok.2
        (fun hE => by have := hbare hE; rw [noBareContext_cons, Bool.and_eq_true] at this; exact this.2)
        (fun e he => ?_)⟩
    · obtain ⟨C', hv, τ, h⟩ := hty e he
      simp only [Dogwood.Spec.Provider.Arg.allHaveTypeIn, Bool.and_eq_true] at h
      exact ⟨C', hv, τ, h.1⟩
    · obtain ⟨C', hv, τ, h⟩ := hty e he
      simp only [Dogwood.Spec.Provider.Arg.allHaveTypeIn, Bool.and_eq_true] at h
      exact ⟨C', hv, τ, h.2⟩

end


/-! ## The crate's types are the specification's -/

/-- **The crate's type of an argument in an environment is the specification's**, when the crate
gives it one. -/
theorem typeIn?_of_argType? {C : ProviderCtx} {C' : TypingCtx} {e : ReqEnv}
    (hv : EnvView C' C.schema e) {a : Provider.Arg} {a' : Dogwood.Spec.Provider.Arg}
    (hs : Provider.Arg.toSpec a = .ok a') {t : CedarType} (ht : C.argType? e a = some t) :
    a'.typeIn? C' = some t := by
  cases a with
  | string s =>
    simp [Provider.Arg.toSpec, pure, Except.pure] at hs; subst hs
    simp [ProviderCtx.argType?] at ht; subst ht
    rfl
  | integer i =>
    simp [Provider.Arg.toSpec, pure, Except.pure] at hs; subst hs
    simp [ProviderCtx.argType?] at ht; subst ht
    rfl
  | decimal d =>
    simp [Provider.Arg.toSpec, pure, Except.pure] at hs; subst hs
    simp [ProviderCtx.argType?] at ht; subst ht
    rfl
  | bool b =>
    simp [Provider.Arg.toSpec, pure, Except.pure] at hs; subst hs
    simp [ProviderCtx.argType?] at ht; subst ht
    rfl
  | set items => simp [ProviderCtx.argType?] at ht
  | field p =>
    rcases toSpec_field' hs with ⟨rest, rfl, rfl⟩ | ⟨r, rest, rfl, rfl⟩
    · simp only [ProviderCtx.argType?, beq_self_eq_true, if_true, contextPathType?] at ht
      split at ht
      · rename_i t' hres
        cases ht
        match rest, hres with
        | [], hres => simp [resolveContextPath] at hres
        | h :: rest', hres =>
          simp only [resolveContextPath] at hres
          split at hres
          · cases hres
          · rename_i hh
            cases hq : e.entry.context.find? h with
            | none => rw [hq] at hres; cases hres
            | some q =>
              rw [hq] at hres
              have hq' := hv.context h (by simpa using hh)
              rw [hq] at hq'
              simp [Dogwood.Spec.Provider.Arg.typeIn?, Dogwood.Spec.declaredPathType?,
                pathType?_of_descend' hq' hres]
      · cases ht
    · have hscope := scopeType_toSpec hv r
      match rest with
      | [] =>
        rw [argType?_root_nil C e r] at ht
        cases ht
        simp [Dogwood.Spec.Provider.Arg.typeIn?, hscope]
      | first :: rest' =>
        rw [argType?_root_attr C e r] at ht
        simp only [scopeAttrCedarType?] at ht
        cases hattrs : entityAttrs? C.schema (rootType e r) with
        | none => rw [hattrs] at ht; cases ht
        | some attrs =>
          rw [hattrs] at ht
          simp only at ht
          cases hq : attrs.find? first with
          | none => rw [hq] at ht; cases ht
          | some q =>
            rw [hq] at ht
            simp only at ht
            split at ht
            · rename_i ty hd
              cases ht
              have hattrs' : C'.env.ets.attrs? (C'.scopeType r.toSpec) = some attrs := by
                rw [hscope, hv.ets]; exact hattrs
              simp [Dogwood.Spec.Provider.Arg.typeIn?, hattrs', Dogwood.Spec.declaredPathType?,
                pathType?_of_descend' hq hd]
            · cases ht

/-- The ambiguity check passes an argument `providerArgsOk` admits. -/
theorem ambiguity_none {C : ProviderCtx} {a : Provider.Arg} (param : ParamType)
    (hok : providerArgsOk C [a] = true) : C.ambiguity a param = none := by
  cases a with
  | field p =>
    match p with
    | [] => simp [ProviderCtx.ambiguity]
    | [x] => simp [ProviderCtx.ambiguity]
    | root :: y :: ys =>
      by_cases hc : root = "context"
      · subst hc; simp [ProviderCtx.ambiguity]
      · simp only [providerArgsOk, Bool.and_true, List.all_eq_true] at hok
        simp only [ProviderCtx.ambiguity]
        split
        · rfl
        · rename_i r hr
          rw [List.findSome?_eq_none_iff]
          intro e he
          have := hok e he
          rw [hr] at this
          revert this
          split
          · rename_i heq
            cases heq
            split <;> simp
          · rename_i heq
            cases heq
  | _ => simp [ProviderCtx.ambiguity]

/-- The scalar type check passes an argument that has, in every environment, the declared type
when it has a type. -/
theorem scalar_nil {C : ProviderCtx} {a : Provider.Arg} {param : ParamType} {ty : CedarType}
    (hamb : C.ambiguity a param = none)
    (h : ∀ e ∈ C.envs, ∀ t, C.argType? e a = some t → t = ty) :
    C.argTypeProblemsScalar a param ty = [] := by
  unfold ProviderCtx.argTypeProblemsScalar
  rw [hamb]
  simp only [Option.toList_eq_nil_iff, List.findSome?_eq_none_iff]
  intro e he
  cases hat : C.argType? e a with
  | none => rfl
  | some t =>
    have := h e he t hat
    subst this
    simp

/-- An argument other than a set that the specification types in every environment passes the
scalar type check. -/
theorem scalar_of_typed {C : ProviderCtx} {a : Provider.Arg} {a' : Dogwood.Spec.Provider.Arg}
    {param : ParamType} {ty : CedarType} (hs : Provider.Arg.toSpec a = .ok a')
    (hns : ∀ items, a' ≠ .set items) (hamb : C.ambiguity a param = none)
    (hty : ∀ e ∈ C.envs, ∃ C', EnvView C' C.schema e ∧ a'.hasTypeIn C' ty = true) :
    C.argTypeProblemsScalar a param ty = [] := by
  refine scalar_nil hamb fun e he t ht => ?_
  obtain ⟨C', hv, h⟩ := hty e he
  have h₁ := typeIn?_of_argType? hv hs ht
  rw [typeIn?_of_hasTypeIn hns h] at h₁
  exact (Option.some.inj h₁).symm

theorem toSpec_lit_not_set {a : Provider.Arg} {a' : Dogwood.Spec.Provider.Arg}
    (hs : Provider.Arg.toSpec a = .ok a') (ha : ∀ items, a ≠ .set items) : ∀ items, a' ≠ .set items := by
  cases a with
  | field p => exact toSpec_field_not_set hs
  | set items => exact absurd rfl (ha items)
  | _ => simp [Provider.Arg.toSpec, pure, Except.pure] at hs; subst hs; intro _ h; cases h

mutual

/-- **The type check passes an argument the specification types** in every environment. -/
theorem argTypes_nil {C : ProviderCtx} : (a : Provider.Arg) → (top : Bool) → (param : ParamType) →
    (a' : Dogwood.Spec.Provider.Arg) → Provider.Arg.toSpec a = .ok a' →
    providerArgsOk C [a] = true →
    (∀ e ∈ C.envs, ∃ C', EnvView C' C.schema e ∧
      a'.hasTypeIn C' (paramCType C.names param) = true) →
    C.argTypeProblems top a param = []
  | .set items, top, param, a', hs, hok, hty => by
    obtain ⟨items', h, rfl⟩ := toSpec_set hs
    rw [ProviderCtx.argTypeProblems]
    split
    · rename_i τ hτ
      have hτ' := paramCType_setKind C.names (paramType_of_set C.names hτ)
      rw [hτ] at hτ'
      cases hτ'
      refine itemTypes_nil items _ items' h (by simpa [providerArgsOk] using hok) fun e he => ?_
      obtain ⟨C', hv, ht⟩ := hty e he
      rw [hτ] at ht
      exact ⟨C', hv, by simpa [Dogwood.Spec.Provider.Arg.hasTypeIn] using ht⟩
    · rename_i hns
      cases top with
      | true => rfl
      | false =>
        simp only [Bool.false_eq_true, if_false]
        cases hh : C.envs.head? with
        | none => rfl
        | some e =>
          exfalso
          obtain ⟨C', _, ht⟩ := hty e (mem_of_head?_eq hh)
          cases hp : paramCType C.names param with
          | set τ => exact hns τ hp
          | _ => rw [hp] at ht; simp [Dogwood.Spec.Provider.Arg.hasTypeIn] at ht
  | .field p, top, param, a', hs, hok, hty => by
    rw [ProviderCtx.argTypeProblems]
    split
    · rfl
    · exact scalar_of_typed hs (toSpec_field_not_set hs) (ambiguity_none param hok) hty
  | .string s, top, param, a', hs, hok, hty => by
    rw [ProviderCtx.argTypeProblems]
    cases top with
    | true => rfl
    | false =>
      exact scalar_of_typed hs (toSpec_lit_not_set hs (by intro _ h; cases h))
        (ambiguity_none param hok) hty
  | .integer i, top, param, a', hs, hok, hty => by
    rw [ProviderCtx.argTypeProblems]
    cases top with
    | true => rfl
    | false =>
      exact scalar_of_typed hs (toSpec_lit_not_set hs (by intro _ h; cases h))
        (ambiguity_none param hok) hty
  | .decimal d, top, param, a', hs, hok, hty => by
    rw [ProviderCtx.argTypeProblems]
    cases top with
    | true => rfl
    | false =>
      exact scalar_of_typed hs (toSpec_lit_not_set hs (by intro _ h; cases h))
        (ambiguity_none param hok) hty
  | .bool b, top, param, a', hs, hok, hty => by
    rw [ProviderCtx.argTypeProblems]
    cases top with
    | true => rfl
    | false =>
      exact scalar_of_typed hs (toSpec_lit_not_set hs (by intro _ h; cases h))
        (ambiguity_none param hok) hty

/-- The type check passes the elements of a set the specification types in every environment. -/
theorem itemTypes_nil {C : ProviderCtx} : (items : List Provider.Arg) → (element : ParamType) →
    (items' : List Dogwood.Spec.Provider.Arg) → Provider.Arg.toSpec.argsToSpec items = .ok items' →
    providerArgsOk C items = true →
    (∀ e ∈ C.envs, ∃ C', EnvView C' C.schema e ∧
      Dogwood.Spec.Provider.Arg.allHaveTypeIn C' items' (paramCType C.names element) = true) →
    C.setItemProblems items element = []
  | [], _, _, _, _, _ => by rw [ProviderCtx.setItemProblems]
  | x :: xs, element, items', h, hok, hty => by
    obtain ⟨x', xs', hx, hxs, rfl⟩ := argsToSpec_cons h
    rw [providerArgsOk_cons, Bool.and_eq_true] at hok
    rw [ProviderCtx.setItemProblems, List.append_eq_nil_iff]
    refine ⟨argTypes_nil x false element x' hx hok.1 fun e he => ?_,
      itemTypes_nil xs element xs' hxs hok.2 fun e he => ?_⟩
    · obtain ⟨C', hv, h⟩ := hty e he
      simp only [Dogwood.Spec.Provider.Arg.allHaveTypeIn, Bool.and_eq_true] at h
      exact ⟨C', hv, h.1⟩
    · obtain ⟨C', hv, h⟩ := hty e he
      simp only [Dogwood.Spec.Provider.Arg.allHaveTypeIn, Bool.and_eq_true] at h
      exact ⟨C', hv, h.2⟩

end


/-! ## Argument lists -/

/-- **The literal check passes literals of the declared types**: `argsMatchDecl` fixes the kind of
an integer, decimal or boolean literal; the exception fixes that of a string literal, and that of a
set literal when the rule admits no environment (`hset` gives it otherwise). -/
theorem literalProblems_nil {names : List (String × String)} {key what : String} {envless : Bool}
    {args : List Provider.Arg} {args' : List Dogwood.Spec.Provider.Arg} {params : List ParamType}
    (hr : List.Forall₂ (fun a a' => Provider.Arg.toSpec a = .ok a') args args')
    (hm : Dogwood.Spec.Provider.argsMatchDecl args' (params.map (paramCType names)))
    (hk : providerLiteralKindsExact envless args params = true)
    (hset : envless = false → ∀ items p, (Provider.Arg.set items, p) ∈ args.zip params →
      p.paramType = "set") :
    literalProblems key what args params = [] := by
  unfold literalProblems
  rw [List.filterMap_eq_nil_iff]
  intro ⟨a, p⟩ hx
  have hkx := List.all_eq_true.mp hk (a, p) hx
  obtain ⟨a', ha', hm'⟩ := zip_forall₂ (f := paramCType names) hr hx
  have hlit := hm.2 _ hm'
  simp only at hkx hlit ⊢
  cases a with
  | field _ => rfl
  | string s =>
    simp only [beq_iff_eq] at hkx
    simp [argKind, paramTypeAccepts, hkx]
  | integer i =>
    simp [Provider.Arg.toSpec, pure, Except.pure] at ha'; subst ha'
    simp only [Dogwood.Spec.Provider.Arg.literalType?, reduceCtorEq, false_or,
      Option.some.injEq] at hlit
    rcases paramType_of_int names hlit.symm with h | h <;> simp [argKind, paramTypeAccepts, h]
  | decimal t =>
    simp [Provider.Arg.toSpec, pure, Except.pure] at ha'; subst ha'
    simp only [Dogwood.Spec.Provider.Arg.literalType?, reduceCtorEq, false_or,
      Option.some.injEq] at hlit
    simp [argKind, paramTypeAccepts, paramType_of_decimal names hlit.symm]
  | bool b =>
    simp [Provider.Arg.toSpec, pure, Except.pure] at ha'; subst ha'
    simp only [Dogwood.Spec.Provider.Arg.literalType?, reduceCtorEq, false_or,
      Option.some.injEq] at hlit
    rcases paramType_of_bool names hlit.symm with h | h <;> simp [argKind, paramTypeAccepts, h]
  | set items =>
    have hp : p.paramType = "set" := by
      cases envless with
      | true => simpa using hkx
      | false => exact hset rfl items p hx
    simp [argKind, paramTypeAccepts, hp]

theorem pathProblems_of_mem {C : ProviderCtx} : ∀ {args : List Provider.Arg},
    (∀ a ∈ args, C.pathProblems [a] = []) → C.pathProblems args = []
  | [], _ => by simp [ProviderCtx.pathProblems]
  | a :: rest, h => by
    rw [pathProblems_cons, List.append_eq_nil_iff]
    exact ⟨h a List.mem_cons_self, pathProblems_of_mem fun b hb => h b (List.mem_cons_of_mem _ hb)⟩

/-- **An argument list the specification accepts passes the literal, existence and type checks**:
the arguments match their declared types (`argsMatchDecl`), and have them in every environment
(`ArgsTypedIn`). -/
theorem block_nil {C : ProviderCtx} {key what : String}
    {args : List Provider.Arg} {args' : List Dogwood.Spec.Provider.Arg} {params : List ParamType}
    (hr : List.Forall₂ (fun a a' => Provider.Arg.toSpec a = .ok a') args args')
    (hm : Dogwood.Spec.Provider.argsMatchDecl args' (params.map (paramCType C.names)))
    (hT : ∀ e ∈ C.envs, ∃ C', EnvView C' C.schema e ∧
      Dogwood.Spec.Provider.ArgsTypedIn C' args' (params.map (paramCType C.names)))
    (hok : providerArgsOk C args = true)
    (hk : providerLiteralKindsExact C.envs.isEmpty args params = true)
    (hbare : C.envs = [] → providerNoBareContext args = true) :
    literalProblems key what args params = [] ∧ C.pathProblems args = [] ∧
      ∀ x ∈ args.zip params, C.argTypeProblems true x.1 x.2 = [] := by
  have hlen : args.length = params.length := by
    rw [forall₂_length hr, hm.1, List.length_map]
  have htyped : ∀ a p, (a, p) ∈ args.zip params → ∃ a', Provider.Arg.toSpec a = .ok a' ∧
      ∀ e ∈ C.envs, ∃ C', EnvView C' C.schema e ∧ a'.hasTypeIn C' (paramCType C.names p) = true := by
    intro a p hx
    obtain ⟨a', ha', hm'⟩ := zip_forall₂ (f := paramCType C.names) hr hx
    exact ⟨a', ha', fun e he => by
      obtain ⟨C', hv, hT'⟩ := hT e he
      exact ⟨C', hv, hT'.2 _ hm'⟩⟩
  refine ⟨literalProblems_nil hr hm hk fun hne items p hx => ?_, ?_, ?_⟩
  · obtain ⟨e, he⟩ : ∃ e, e ∈ C.envs := by
      cases h : C.envs with
      | nil => simp [h] at hne
      | cons e _ => exact ⟨e, List.mem_cons_self⟩
    obtain ⟨a', ha', hall⟩ := htyped _ _ hx
    obtain ⟨items', _, rfl⟩ := toSpec_set ha'
    obtain ⟨C', _, ht⟩ := hall e he
    cases hp : paramCType C.names p with
    | set τ => exact paramType_of_set C.names hp
    | _ => rw [hp] at ht; simp [Dogwood.Spec.Provider.Arg.hasTypeIn] at ht
  · apply pathProblems_of_mem
    intro a ha
    obtain ⟨p, hx⟩ := mem_zip_of_length hlen ha
    obtain ⟨a', ha', hall⟩ := htyped _ _ hx
    exact argPaths_nil a a' ha' (providerArgsOk_mem hok a ha)
      (fun hE => noBareContext_mem (hbare hE) a ha)
      (fun e he => by obtain ⟨C', hv, h⟩ := hall e he; exact ⟨C', hv, _, h⟩)
  · intro ⟨a, p⟩ hx
    obtain ⟨a', ha', hall⟩ := htyped _ _ hx
    exact argTypes_nil a true p a' ha' (providerArgsOk_mem hok a (mem_of_mem_zip_left hx)) hall

/-! ## Methods -/

theorem mem_crateMethods {names : List (String × String)} {fn : Cedar.Spec.Name} {d : ProviderDecl}
    {ms : Dogwood.Spec.Provider.MethodSig} (h : ms ∈ (crateSignature names fn d).methods) :
    ∃ md, (ms.name, md) ∈ d.methods ∧ ms.args = md.argumentTypes.map (paramCType names) := by
  simp only [crateSignature, List.mem_map] at h
  obtain ⟨⟨n, md⟩, hmem, rfl⟩ := h
  exact ⟨md, hmem, rfl⟩

/-- **The chain check passes a chain that `Signature.Chains`**: each method is declared, takes the
type the stage before it produces, and has its declared number of arguments, of the declared
kinds. -/
theorem chain_nil {C : ProviderCtx} {d : ProviderDecl} {fn : Cedar.Spec.Name} :
    ∀ {ms : List Provider.MethodCall} {ms' : List Dogwood.Spec.Provider.MethodCall}
      {pipeline : ParamType},
    List.Forall₂ (fun (m : Provider.MethodCall) (m' : Dogwood.Spec.Provider.MethodCall) =>
      m'.name = m.name ∧ List.Forall₂ (fun a a' => Provider.Arg.toSpec a = .ok a') m.args m'.args)
      ms ms' →
    (crateSignature C.names fn d).Chains (paramCType C.names pipeline) ms' →
    (∀ m ∈ ms, cedarExtensionMethods.contains m.name = false) →
    (∀ m ∈ ms, ∀ md, d.methods.lookup m.name = some md →
      md.argumentTypes.length = m.args.length ∧
      ∀ what, literalProblems C.key what m.args md.argumentTypes = []) →
    chainProblems C d pipeline ms = []
  | [], [], _, .nil, _, _, _ => by simp [chainProblems]
  | m :: ms, m' :: ms', pipeline, .cons ⟨hn, _⟩ hrest, hch, hext, hlit => by
    simp only [Dogwood.Spec.Provider.Signature.Chains, hn, find?_crateMethods] at hch
    cases hmd : d.methods.lookup m.name with
    | none => rw [hmd] at hch; cases hch
    | some md =>
      rw [hmd] at hch
      simp only [Option.map_some] at hch
      obtain ⟨hin, hch'⟩ := hch
      obtain ⟨hlen, hl⟩ := hlit m List.mem_cons_self md hmd
      have hx : cedarExtensionMethods.contains m.name = false := hext m List.mem_cons_self
      rw [chainProblems, if_neg (by simp only [hx]; exact Bool.false_ne_true)]
      simp only [hmd, List.append_eq_nil_iff]
      refine ⟨⟨?_, ?_⟩, chain_nil hrest hch' (fun x hx => hext x (List.mem_cons_of_mem _ hx))
        (fun x hx => hlit x (List.mem_cons_of_mem _ hx))⟩
      · cases hi : md.inputType with
        | none => rfl
        | some input =>
          rw [hi] at hin
          simp only [Option.map_some, reduceCtorEq, false_or, Option.some.injEq] at hin
          simp [hin]
      · simp [hlen, hl]


end ProviderComplete

/-! ## The provider leaf -/

open ProviderComplete in
/-- **The provider dialect is complete.** A provider leaf whose provider the specification declares
as the crate does, and that the specification accepts (`Provider.Call.Declared`, and
`Provider.Call.TypedIn` in every request environment of its rule), is one on which the crate's
checks find nothing, unless it meets one of the crate's stricter rules: those
`providerExceptionsOk` states, and those `providerCompleteOk` states. -/
theorem provider_complete {S : Schema} {g : LoweredProviderField} {d : ProviderDecls.ProviderDecl}
    {c : Dogwood.Spec.Provider.Call} {D : Dogwood.Spec.Provider.Declarations}
    (hd : g.declaration = some d) (hc : g.toCall = .ok c)
    (hD : D.find? c.function = some (crateSignature g.entityTypeNames c.function d))
    (hdecl : c.Declared D)
    (htyped : ∀ e ∈ (providerCtx S g).envs, ∃ C', EnvView C' S e ∧ c.TypedIn C' D)
    (hX : providerExceptionsOk S g d = true) (hY : providerCompleteOk S g d = true) :
    providerLeafFindings S g = [] := by
  obtain ⟨hargs, hmethods⟩ := toCall_ok hc
  obtain ⟨sig, hsig, hmatch, hmeth, hchain⟩ := hdecl
  rw [hD, Option.some.injEq] at hsig
  subst hsig
  have hT : ∀ e ∈ (providerCtx S g).envs, ∃ C', EnvView C' S e ∧
      Dogwood.Spec.Provider.ArgsTypedIn C' c.args (d.argumentTypes.map (paramCType g.entityTypeNames)) ∧
      ∀ m ∈ c.methods, ∃ ms ∈ (crateSignature g.entityTypeNames c.function d).methods,
        ms.name = m.name ∧ Dogwood.Spec.Provider.ArgsTypedIn C' m.args ms.args := by
    intro e he
    obtain ⟨C', hv, sig', hsig', ht, hmt⟩ := htyped e he
    rw [hD, Option.some.injEq] at hsig'
    subst hsig'
    exact ⟨C', hv, ht, hmt⟩
  simp only [providerExceptionsOk, Bool.and_eq_true, List.all_eq_true] at hX
  obtain ⟨⟨⟨henum, hext⟩, hok⟩, hokm⟩ := hX
  simp only [providerCompleteOk, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true,
    Bool.not_eq_true'] at hY
  obtain ⟨⟨⟨hdistinct, hk⟩, hkm⟩, hbare⟩ := hY
  have hnodup : (d.methods.map (·.1)).Nodup := of_decide_eq_true hdistinct
  have hbare' : (providerCtx S g).envs = [] → providerNoBareContext g.invocation.args = true ∧
      ∀ m ∈ g.methods, providerNoBareContext m.args = true := by
    intro hE
    rcases hbare with h | h
    · simp [hE] at h
    · exact h
  -- each method of the leaf, its translation, and its declaration, the one `lookup` finds
  have hmi : ∀ m ∈ g.methods, ∃ (m' : Dogwood.Spec.Provider.MethodCall) (md : MethodDecl),
      d.methods.lookup m.name = some md ∧
      List.Forall₂ (fun a a' => Provider.Arg.toSpec a = .ok a') m.args m'.args ∧
      Dogwood.Spec.Provider.argsMatchDecl m'.args
        (md.argumentTypes.map (paramCType g.entityTypeNames)) ∧
      ∀ e ∈ (providerCtx S g).envs, ∃ C', EnvView C' S e ∧
        Dogwood.Spec.Provider.ArgsTypedIn C' m'.args
          (md.argumentTypes.map (paramCType g.entityTypeNames)) := by
    intro m hm
    obtain ⟨m', hm', hn, hr⟩ := exists_of_forall₂_mem_left hmethods m hm
    obtain ⟨ms, hms, hmsn, hmsm⟩ := hmeth m' hm'
    obtain ⟨md, hmem, hargs'⟩ := mem_crateMethods hms
    rw [hmsn, hn] at hmem
    have hlk := lookup_of_mem hnodup hmem
    refine ⟨m', md, hlk, hr, hargs' ▸ hmsm, fun e he => ?_⟩
    obtain ⟨C', hv, _, hmt⟩ := hT e he
    obtain ⟨ms₂, hms₂, hn₂, ht₂⟩ := hmt m' hm'
    obtain ⟨md₂, hmem₂, hargs₂⟩ := mem_crateMethods hms₂
    rw [hn₂, hn] at hmem₂
    rw [lookup_of_mem hnodup hmem₂, Option.some.injEq] at hlk
    subst hlk
    exact ⟨C', hv, hargs₂ ▸ ht₂⟩
  have hlen : d.argumentTypes.length = g.invocation.args.length := by
    rw [forall₂_length hargs, hmatch.1]
    simp [crateSignature]
  have htop := block_nil (C := providerCtx S g) (key := g.invocation.key) (what := "") hargs hmatch
    (fun e he => by obtain ⟨C', hv, ht, _⟩ := hT e he; exact ⟨C', hv, ht⟩) hok hk
    (fun hE => (hbare' hE).1)
  have hblock : ∀ m ∈ g.methods, ∀ md, d.methods.lookup m.name = some md →
      md.argumentTypes.length = m.args.length ∧
      (∀ what, literalProblems g.invocation.key what m.args md.argumentTypes = []) ∧
      (providerCtx S g).pathProblems m.args = [] ∧
      ∀ x ∈ m.args.zip md.argumentTypes, (providerCtx S g).argTypeProblems true x.1 x.2 = [] := by
    intro m hm md hmd
    obtain ⟨m', md', hlk, hr, hmm, hmt⟩ := hmi m hm
    rw [hmd, Option.some.injEq] at hlk
    subst hlk
    have hkm' := hkm m hm
    simp only [hmd] at hkm'
    have hb := fun what => block_nil (C := providerCtx S g) (key := g.invocation.key) (what := what)
      hr hmm hmt (hokm m hm) hkm' (fun hE => (hbare' hE).2 m hm)
    exact ⟨by rw [forall₂_length hr, hmm.1, List.length_map], fun what => (hb what).1,
      (hb "").2.1, (hb "").2.2⟩
  simp only [providerLeafFindings, hd]
  split
  · rename_i h
    simp [hlen] at h
  · simp only [List.append_eq_nil_iff]
    refine ⟨⟨⟨⟨⟨⟨?_, htop.1⟩, htop.2.1⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
    · -- the entity types are declared enums
      rw [List.filterMap_eq_nil_iff]
      intro name hname
      have := henum name hname
      cases hq : S.ets.find? (parseEntityType ((g.entityTypeNames.lookup name).getD name)) with
      | none => simp [hq] at this
      | some entry =>
        cases entry with
        | standard _ => simp [hq] at this
        | enum _ => simp
    · -- the methods' paths exist
      rw [List.flatMap_eq_nil_iff]
      intro m hm
      obtain ⟨m', md, hlk, _⟩ := hmi m hm
      exact (hblock m hm md hlk).2.2.1
    · -- the arguments have their types
      rw [List.flatMap_eq_nil_iff]
      intro ⟨a, p⟩ hx
      exact htop.2.2 (a, p) hx
    · -- the methods' arguments have their types
      rw [List.flatMap_eq_nil_iff]
      intro m hm
      obtain ⟨m', md, hlk, _⟩ := hmi m hm
      simp only [hlk]
      rw [List.flatMap_eq_nil_iff]
      intro ⟨a, p⟩ hx
      exact (hblock m hm md hlk).2.2.2 (a, p) hx
    · -- the chain
      exact chain_nil (C := providerCtx S g) (pipeline := d.outputType) hmethods hchain
        (fun m hm => by simpa using hext m hm)
        (fun m hm md hmd => ⟨(hblock m hm md hmd).1, (hblock m hm md hmd).2.1⟩)


namespace ProviderComplete

/-! ## The exceptions are needed

Each conjunct of `providerCompleteOk` is needed. In each example, the leaf's rule has no target
action, so it admits no request environment and `htyped` holds; the leaf meets every other premise
of `provider_complete` and the other conjuncts, and the crate reports it. -/

/-- A leaf calling `f`, of a rule without target actions. -/
def envlessLeaf (d : ProviderDecl) (args : List Provider.Arg) (ms : List Provider.MethodCall) :
    LoweredProviderField :=
  { id := "p", action := .unconstrained, targetActions := [], principal := .any, resource := .any,
    invocation := { span := default, function := ["f"], args }, methods := ms, bodyBase := 0,
    declaration := some d, entityTypes := [], entityTypeNames := [] }

/-- The declaration of `f`. -/
def declOf (args : List ParamType) (methods : List (String × MethodDecl)) : ProviderDecl :=
  { argumentTypes := args, outputType := { paramType := "string" }, methods, implementation := none }

/-- A bare `context` argument: the specification gives it no type, which `TypedIn` checks only in
a request environment. -/
example :
    let d := declOf [{ paramType := "string" }] []
    let g := envlessLeaf d [.field ["context"]] []
    let c : Dogwood.Spec.Provider.Call := { function := ⟨"f", []⟩, args := [.context []], methods := [] }
    g.toCall = .ok c ∧ c.Declared [crateSignature [] c.function d] ∧
      (providerCtx default g).envs = [] ∧ providerExceptionsOk default g d = true ∧
      providerCompleteOk default g d = false ∧ providerLeafFindings default g ≠ [] := by
  intro d g c
  refine ⟨rfl, ⟨crateSignature [] c.function d, rfl, ⟨rfl, ?_⟩, by simp [c], trivial⟩, rfl, ?_, ?_, ?_⟩
  · simp [c, d, declOf, crateSignature, Dogwood.Spec.Provider.Arg.literalType?]
  · simp [providerExceptionsOk, ProviderDecls.ProviderDecl.referencedEntityTypes, ProviderDecls.sortedSet,
      ProviderDecls.ParamType.entityTypes, ProviderDecls.ParamType.entityTypesOpt,
      ProviderDecls.ParamType.entityTypesFields, g, d, envlessLeaf, declOf, providerArgsOk]
  · simp [providerCompleteOk, providerMethodsDistinct, providerLiteralKindsExact, providerNoBareContext,
      g, d, envlessLeaf, declOf, providerCtx, ProviderCtx.envs]
  · simp [providerLeafFindings, g, d, envlessLeaf, declOf, ProviderCtx.pathProblems,
      ProviderCtx.pathProblem]

/-- A string literal declared with an unknown kind: the specification types it `String`, as the
crate types the parameter, and accepts it in every environment too. -/
example :
    let d := declOf [{ paramType := "text" }] []
    let g := envlessLeaf d [.string "x"] []
    let c : Dogwood.Spec.Provider.Call := { function := ⟨"f", []⟩, args := [.string "x"], methods := [] }
    g.toCall = .ok c ∧ c.Declared [crateSignature [] c.function d] ∧
      (providerCtx default g).envs = [] ∧ providerExceptionsOk default g d = true ∧
      providerCompleteOk default g d = false ∧ providerLeafFindings default g ≠ [] := by
  intro d g c
  refine ⟨rfl, ⟨crateSignature [] c.function d, rfl, ⟨rfl, ?_⟩, by simp [c], trivial⟩, rfl, ?_, ?_, ?_⟩
  · simp [c, d, declOf, crateSignature, paramCType, Dogwood.Spec.Provider.Arg.literalType?]
  · simp [providerExceptionsOk, ProviderDecls.ProviderDecl.referencedEntityTypes, ProviderDecls.sortedSet,
      ProviderDecls.ParamType.entityTypes, ProviderDecls.ParamType.entityTypesOpt,
      ProviderDecls.ParamType.entityTypesFields, g, d, envlessLeaf, declOf, providerArgsOk]
  · simp [providerCompleteOk, providerMethodsDistinct, providerLiteralKindsExact, g, d, envlessLeaf,
      declOf, providerCtx, ProviderCtx.envs]
  · simp [providerLeafFindings, g, d, envlessLeaf, declOf, literalProblems, argKind, paramTypeAccepts]

/-- A set literal declared `string`, in a rule that admits no request environment: the
specification checks the type of a set only in a request environment. -/
example :
    let d := declOf [{ paramType := "string" }] []
    let g := envlessLeaf d [.set []] []
    let c : Dogwood.Spec.Provider.Call := { function := ⟨"f", []⟩, args := [.set []], methods := [] }
    g.toCall = .ok c ∧ c.Declared [crateSignature [] c.function d] ∧
      (providerCtx default g).envs = [] ∧ providerExceptionsOk default g d = true ∧
      providerCompleteOk default g d = false ∧ providerLeafFindings default g ≠ [] := by
  intro d g c
  refine ⟨rfl, ⟨crateSignature [] c.function d, rfl, ⟨rfl, ?_⟩, by simp [c], trivial⟩, rfl, ?_, ?_, ?_⟩
  · simp [c, d, declOf, crateSignature, Dogwood.Spec.Provider.Arg.literalType?]
  · simp [providerExceptionsOk, ProviderDecls.ProviderDecl.referencedEntityTypes, ProviderDecls.sortedSet,
      ProviderDecls.ParamType.entityTypes, ProviderDecls.ParamType.entityTypesOpt,
      ProviderDecls.ParamType.entityTypesFields, g, d, envlessLeaf, declOf, providerArgsOk]
  · simp [providerCompleteOk, providerMethodsDistinct, providerLiteralKindsExact, g, d, envlessLeaf,
      declOf, providerCtx, ProviderCtx.envs]
  · simp [providerLeafFindings, g, d, envlessLeaf, declOf, literalProblems, argKind, paramTypeAccepts]

/-- A method declared twice: the specification may read either declaration of `m`, the crate reads
the first, whose argument is a string. -/
example :
    let md₁ : MethodDecl := ⟨[{ paramType := "string" }], { paramType := "string" }, none⟩
    let md₂ : MethodDecl := ⟨[{ paramType := "integer" }], { paramType := "string" }, none⟩
    let d := declOf [] [("m", md₁), ("m", md₂)]
    let g := envlessLeaf d [] [{ span := default, name := "m", args := [.integer 1] }]
    let c : Dogwood.Spec.Provider.Call :=
      { function := ⟨"f", []⟩, args := [], methods := [{ name := "m", args := [.long 1] }] }
    g.toCall = .ok c ∧ c.Declared [crateSignature [] c.function d] ∧
      (providerCtx default g).envs = [] ∧ providerExceptionsOk default g d = true ∧
      providerCompleteOk default g d = false ∧ providerLeafFindings default g ≠ [] := by
  intro md₁ md₂ d g c
  refine ⟨rfl, ⟨crateSignature [] c.function d, rfl, ⟨rfl, by simp [c]⟩, ?_, ?_⟩, rfl, ?_, ?_, ?_⟩
  · intro m hm
    simp only [c, List.mem_singleton] at hm
    subst hm
    refine ⟨{ name := "m", args := [.int], input := none, output := .string },
      by simp [crateSignature, d, declOf, md₂, paramCType], rfl, rfl, ?_⟩
    simp [Dogwood.Spec.Provider.Arg.literalType?]
  · simp [Dogwood.Spec.Provider.Signature.Chains, crateSignature, c, d, declOf, md₁]
  · simp [providerExceptionsOk, ProviderDecls.ProviderDecl.referencedEntityTypes, ProviderDecls.sortedSet,
      ProviderDecls.ParamType.entityTypes, ProviderDecls.ParamType.entityTypesOpt,
      ProviderDecls.ParamType.entityTypesFields, g, d, envlessLeaf, declOf, md₁, providerArgsOk,
      cedarExtensionMethods]
  · simp [providerCompleteOk, providerMethodsDistinct, g, d, envlessLeaf, declOf]
  · intro h
    simp only [providerLeafFindings, g, d, envlessLeaf, declOf, List.length_nil, bne_self_eq_false,
      Bool.false_eq_true, ↓reduceIte, List.append_eq_nil_iff] at h
    have h := h.2
    simp [chainProblems, List.lookup, md₁, cedarExtensionMethods, literalProblems, argKind,
      paramTypeAccepts] at h

end ProviderComplete

end Dogwood.Thm.Frontend
