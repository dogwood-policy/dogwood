import Dogwood.Thm.Frontend.Validate.Interface

/-!
# The provider dialect's checks are sound

A provider leaf on which the crate's provider dialect (ported as `Validate.providerLeafFindings`)
finds nothing is valid in the specification's sense (`provider_sound`), when the specification
declares its provider as the crate does (`crateSignature`):

* the literal-kind checks give `Provider.argsMatchDecl` (`argsMatchDecl_of`), and the chain
  checks `Provider.Signature.Chains` (`chain_of`): the crate's signature finds a method by its
  name as the declaration's `lookup` does (`find?_crateMethods`);
* the existence and type checks give `Provider.ArgsTypedIn` in every request environment of the
  rule (`argsTypedIn_of`, `argHasType`): a path the existence check passes resolves in every
  environment (`resolved_of_pathProblem_context`, `resolveOne_of_pathProblem_scope`), so its type
  is checked there, and it is the specification's declared type of the path (`fieldHasType`);
  the declared entity types of the environment's action rule out an unresolved scope path
  (`EnvView.declared`).
-/

namespace Dogwood.Thm.Frontend

open Dogwood.Frontend Dogwood.Frontend.Validate
open Dogwood.Spec (Path)
open Dogwood.Spec.Temporal (TypingCtx pathType?)
open Cedar.Validation (CedarType RecordType QualifiedType Schema ActionSchemaEntry)
open ProviderDecls (ParamType ProviderDecl MethodDecl)

/-- A path that resolves, whatever the presence of its optional attributes, has its type as the
specification's declared path type. -/
theorem pathType?_of_descend' : ∀ {p : Path} {rty : RecordType} {pre : Path} {a : String}
    {q : QualifiedType} {t : CedarType}, rty.find? a = some q → descend q.getType p = .resolved t →
    pathType? (fun _ => true) rty pre (a :: p) = some t
  | [], rty, pre, a, q, t, hq, hd => by
    simp [descend] at hd
    subst hd
    simp [pathType?, hq]
  | seg :: p, rty, pre, a, q, t, hq, hd => by
    cases hty : q.getType with
    | record rty' =>
      rw [hty] at hd
      simp only [descend] at hd
      cases hq' : rty'.find? seg with
      | none => rw [hq'] at hd; cases hd
      | some q' =>
        rw [hq'] at hd
        have := pathType?_of_descend' (pre := pre ++ [a]) hq' hd
        rw [pathType?, hq]
        simp only [Bool.or_true, if_true, hty]
        exact this
    | _ => rw [hty] at hd; simp [descend] at hd


/-- A scope attribute path resolves as a context path does. -/
theorem descend_of_go : ∀ {p : Path} {ty t : CedarType}, resolveOne.go ty p = .ok t →
    descend ty p = .resolved t
  | [], ty, t, h => by simp [resolveOne.go] at h; simp [descend, h]
  | seg :: p, ty, t, h => by
    cases ty with
    | record rty =>
      simp only [resolveOne.go] at h
      simp only [descend]
      cases hq : rty.find? seg with
      | none => rw [hq] at h; cases h
      | some q => rw [hq] at h; exact descend_of_go h
    | _ => simp [resolveOne.go] at h

/-- A field argument the projection translates is rooted at `context`, `principal` or
`resource`. -/
theorem toSpec_field {p : List String} {a' : Dogwood.Spec.Provider.Arg}
    (h : Provider.Arg.toSpec (.field p) = .ok a') :
    (∃ rest, p = "context" :: rest ∧ a' = .context rest) ∨
      (∃ rest, p = "principal" :: rest ∧ a' = .scope .principal rest) ∨
      (∃ rest, p = "resource" :: rest ∧ a' = .scope .resource rest) := by
  match p with
  | [] => simp [Provider.Arg.toSpec] at h
  | root :: rest =>
    by_cases h₁ : root = "context"
    · subst h₁; simp [Provider.Arg.toSpec, pure, Except.pure] at h; exact .inl ⟨rest, rfl, h.symm⟩
    by_cases h₂ : root = "principal"
    · subst h₂; simp [Provider.Arg.toSpec, pure, Except.pure] at h
      exact .inr (.inl ⟨rest, rfl, h.symm⟩)
    by_cases h₃ : root = "resource"
    · subst h₃; simp [Provider.Arg.toSpec, pure, Except.pure] at h
      exact .inr (.inr ⟨rest, rfl, h.symm⟩)
    rw [Provider.Arg.toSpec.eq_4 _ (by simp [h₁]) (by simp [h₂]) (by simp [h₃])] at h
    cases h


/-! ## The request environments of a provider leaf -/

theorem mem_providerEnvs {C : ProviderCtx} {e : ReqEnv} (he : e ∈ C.envs) :
    (e.uid, e.entry) ∈ C.targets ∧ e.principal ∈ admittedTypes C.schema e.entry .principal C.principal ∧
      e.resource ∈ admittedTypes C.schema e.entry .resource C.resource := by
  simp only [ProviderCtx.envs, List.mem_flatMap, List.mem_map] at he
  obtain ⟨⟨uid, entry⟩, hmem, p, hp, r, hr, rfl⟩ := he
  exact ⟨hmem, hp, hr⟩

theorem admitsAnyEnv_of_mem_envs {C : ProviderCtx} {e : ReqEnv} (he : e ∈ C.envs) :
    admitsAnyEnv C.schema e.entry C.principal C.resource = true := by
  obtain ⟨_, hp, hr⟩ := mem_providerEnvs he
  simp only [admittedTypes, List.mem_filter] at hp hr
  simp only [admitsAnyEnv, Bool.and_eq_true, List.any_eq_true]
  exact ⟨⟨_, hp.1, hp.2⟩, ⟨_, hr.1, hr.2⟩⟩

/-- In every environment, a scalar argument the type check passes has the declared type, when it
has a type there. -/
theorem argType?_of_scalar {C : ProviderCtx} {e : ReqEnv} (he : e ∈ C.envs) {a : Provider.Arg}
    {param : ParamType} {ty : CedarType} (h : C.argTypeProblemsScalar a param ty = [])
    {t : CedarType} (ht : C.argType? e a = some t) : t = ty := by
  unfold ProviderCtx.argTypeProblemsScalar at h
  split at h
  · cases h
  · simp only [Option.toList_eq_nil_iff, List.findSome?_eq_none_iff] at h
    have := h e he
    rw [ht] at this
    simpa using this

/-- A context path that passes the existence check resolves in every environment. -/
theorem resolved_of_pathProblem_context {C : ProviderCtx} {e : ReqEnv} (he : e ∈ C.envs)
    {h : String} {rest : List String} (hp : C.pathProblem ("context" :: h :: rest) = none) :
    ∃ t, resolveContextPath e.entry.context (h :: rest) = .resolved t := by
  simp only [ProviderCtx.pathProblem, List.findSome?_eq_none_iff] at hp
  have := hp (e.uid, e.entry) (mem_providerEnvs he).1
  simp only [admitsAnyEnv_of_mem_envs he] at this
  cases hr : resolveContextPath e.entry.context (h :: rest) with
  | resolved t => exact ⟨t, rfl⟩
  | _ => simp [hr] at this


/-- The entity types a rule admits for a root, declared, resolve a scope path that passes the
existence check: it fails on none of them. -/
theorem resolveOne_of_resolveScopePath' {S : Schema} {entry : ActionSchemaEntry} {r : Root}
    {narrow : ScopeConstraint} {first : String} {rest : List String} {ety : Cedar.Spec.EntityType}
    (hety : ety ∈ admittedTypes S entry r narrow)
    (hdecl : ∀ x ∈ admittedTypes S entry r narrow, (entityAttrs? S x).isSome = true)
    (h : ∀ es seg, resolveScopePath S entry r narrow (first :: rest) ≠ .missing es seg)
    (h' : ∀ seg, resolveScopePath S entry r narrow (first :: rest) ≠ .nonRecord seg) :
    ∃ attrs t, entityAttrs? S ety = some attrs ∧ resolveOne attrs first rest = .ok t := by
  obtain ⟨attrs, hattrs⟩ := Option.isSome_iff_exists.mp (hdecl ety hety)
  refine ⟨attrs, ?_⟩
  cases hres : resolveOne attrs first rest with
  | ok t => exact ⟨t, hattrs, rfl⟩
  | error f =>
    exfalso
    have hne : (admittedTypes S entry r narrow).isEmpty = false := by
      cases hl : admittedTypes S entry r narrow with
      | nil => rw [hl] at hety; cases hety
      | cons _ _ => rfl
    have hany : (admittedTypes S entry r narrow).any
        (fun ety => (entityAttrs? S ety).isNone) = false := by
      simp only [List.any_eq_false, Option.isNone_iff_eq_none]
      intro x hx hn
      have := hdecl x hx
      rw [hn] at this; cases this
    unfold resolveScopePath at h h'
    simp only [hne, hany, Bool.false_eq_true, if_false] at h h'
    generalize hF : List.mergeSort _ _ = failed at h h'
    have hlen := congrArg List.length hF
    rw [List.length_mergeSort] at hlen
    have hpos : 0 < failed.length := by
      rw [← hlen]
      apply List.length_pos_of_mem (a := (nameText ety, f))
      simp only [List.mem_filterMap, List.mem_map]
      exact ⟨_, ⟨ety, hety, rfl⟩, by simp [hattrs, hres]⟩
    match failed, hpos with
    | (_, f') :: _, _ =>
      cases f' with
      | missing seg => exact h _ _ rfl
      | nonRecord seg => exact h' _ rfl

/-- The entity type of a scope root in a request environment. -/
def rootType (e : ReqEnv) : Root → Cedar.Spec.EntityType
  | .principal => e.principal
  | .resource => e.resource

theorem rootType_mem {C : ProviderCtx} {e : ReqEnv} (he : e ∈ C.envs) :
    ∀ r, rootType e r ∈ admittedTypes C.schema e.entry r (C.narrow r)
  | .principal => (mem_providerEnvs he).2.1
  | .resource => (mem_providerEnvs he).2.2

/-- A scope path that passes the existence check resolves on the environment's entity type. -/
theorem resolveOne_of_pathProblem_scope {C : ProviderCtx} {e : ReqEnv} (he : e ∈ C.envs)
    {r : Root} (hdecl : ∀ ety ∈ appliesTo e.entry r, C.schema.ets.contains ety = true)
    {first : String} {rest : List String} (hp : C.pathProblem (r.name :: first :: rest) = none) :
    ∃ attrs t, entityAttrs? C.schema (rootType e r) = some attrs ∧
      resolveOne attrs first rest = .ok t := by
  simp only [ProviderCtx.pathProblem, List.findSome?_eq_none_iff] at hp
  have := hp (e.uid, e.entry) (mem_providerEnvs he).1
  simp only [admitsAnyEnv_of_mem_envs he] at this
  have hroot : (r.name == "context") = false := by cases r <;> rfl
  have hr? : (if r.name == "principal" then some Root.principal
      else if r.name == "resource" then some Root.resource else none) = some r := by
    cases r <;> rfl
  simp only [hroot, Bool.false_eq_true, if_false, Bool.not_true, hr?] at this
  refine resolveOne_of_resolveScopePath' (rootType_mem he r) (fun x hx => ?_) (fun es seg h => ?_)
    (fun seg h => ?_)
  · simp only [admittedTypes, List.mem_filter] at hx
    have := hdecl x hx.1
    simpa [entityAttrs?, Cedar.Validation.EntitySchema.attrs?, Cedar.Validation.EntitySchema.contains]
      using this
  · rw [h] at this; cases this
  · rw [h] at this; cases this


/-! ## Declared types -/

section kinds

variable (names : List (String × String))

theorem paramCType_string {p : ParamType} (h : p.paramType = "string") :
    paramCType names p = .string := by
  obtain ⟨kind, _, _, _, _⟩ := p; simp only at h; subst h; simp [paramCType]

theorem paramCType_int {p : ParamType} (h : p.paramType = "integer" ∨ p.paramType = "long") :
    paramCType names p = .int := by
  obtain ⟨kind, _, _, _, _⟩ := p; simp only at h
  rcases h with rfl | rfl <;> simp [paramCType]

theorem paramCType_decimal {p : ParamType} (h : p.paramType = "decimal") :
    paramCType names p = .ext .decimal := by
  obtain ⟨kind, _, _, _, _⟩ := p; simp only at h; subst h; simp [paramCType]

theorem paramCType_bool {p : ParamType} (h : p.paramType = "bool" ∨ p.paramType = "boolean") :
    paramCType names p = .bool .anyBool := by
  obtain ⟨kind, _, _, _, _⟩ := p; simp only at h
  rcases h with rfl | rfl <;> simp [paramCType]

theorem paramCType_setKind {p : ParamType} (h : p.paramType = "set") :
    paramCType names p = .set (paramCType names (p.items.getD { paramType := "string" })) := by
  obtain ⟨kind, _, items, _, _⟩ := p; simp only at h; subst h
  cases items <;> simp [paramCType, paramCTypeOpt]

/-- A declared type that is a set is declared `set`. -/
theorem paramType_of_set {p : ParamType} {τ : CedarType} (h : paramCType names p = .set τ) :
    p.paramType = "set" := by
  obtain ⟨kind, fields, items, required, et⟩ := p
  simp only
  unfold paramCType at h
  split at h
  all_goals first | rfl | (cases h; done) | (split at h <;> cases h)

end kinds

/-- The specification's literal type of the translation of an argument the literal check passes,
when it has one, is the argument's declared type. -/
theorem literalType_of_kind {names : List (String × String)} {a : Provider.Arg}
    {a' : Dogwood.Spec.Provider.Arg} {param : ParamType} (hs : Provider.Arg.toSpec a = .ok a')
    (hk : ∀ k, argKind a = some k → paramTypeAccepts param.paramType k = true) :
    a'.literalType? = none ∨ a'.literalType? = some (paramCType names param) := by
  cases a with
  | string s =>
    simp [Provider.Arg.toSpec, pure, Except.pure] at hs; subst hs
    have := hk "string" rfl
    simp only [paramTypeAccepts, beq_iff_eq] at this
    simp [Dogwood.Spec.Provider.Arg.literalType?, paramCType_string names this]
  | integer i =>
    simp [Provider.Arg.toSpec, pure, Except.pure] at hs; subst hs
    have := hk "integer" rfl
    simp only [paramTypeAccepts, Bool.or_eq_true, beq_iff_eq] at this
    simp [Dogwood.Spec.Provider.Arg.literalType?, paramCType_int names this]
  | decimal t =>
    simp [Provider.Arg.toSpec, pure, Except.pure] at hs; subst hs
    have := hk "decimal" rfl
    simp only [paramTypeAccepts, beq_iff_eq] at this
    simp [Dogwood.Spec.Provider.Arg.literalType?, paramCType_decimal names this]
  | bool b =>
    simp [Provider.Arg.toSpec, pure, Except.pure] at hs; subst hs
    have := hk "bool" rfl
    simp only [paramTypeAccepts, Bool.or_eq_true, beq_iff_eq] at this
    simp [Dogwood.Spec.Provider.Arg.literalType?, paramCType_bool names this]
  | set xs =>
    rw [Provider.Arg.toSpec.eq_9] at hs
    cases h : Provider.Arg.toSpec.argsToSpec xs with
    | error _ => rw [h] at hs; cases hs
    | ok xs' =>
      rw [h] at hs
      simp [bind, Except.bind, pure, Except.pure] at hs; subst hs
      simp [Dogwood.Spec.Provider.Arg.literalType?]
  | field p =>
    rcases toSpec_field hs with ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ <;>
      simp [Dogwood.Spec.Provider.Arg.literalType?]


/-! ## Arguments, in an environment -/

/-- A field argument the projection translates is a context path, or a scope path. -/
theorem toSpec_field' {p : List String} {a' : Dogwood.Spec.Provider.Arg}
    (h : Provider.Arg.toSpec (.field p) = .ok a') :
    (∃ rest, p = "context" :: rest ∧ a' = .context rest) ∨
      (∃ (r : Root) (rest : List String), p = r.name :: rest ∧ a' = .scope r.toSpec rest) := by
  rcases toSpec_field h with h | ⟨rest, h₁, h₂⟩ | ⟨rest, h₁, h₂⟩
  · exact .inl h
  · exact .inr ⟨.principal, rest, h₁, h₂⟩
  · exact .inr ⟨.resource, rest, h₁, h₂⟩

theorem argType?_root_nil (C : ProviderCtx) (e : ReqEnv) (r : Root) :
    C.argType? e (.field [r.name]) = some (.entity (rootType e r)) := by
  cases r <;> rfl

theorem argType?_root_attr (C : ProviderCtx) (e : ReqEnv) (r : Root) {first : String}
    {rest : List String} :
    C.argType? e (.field (r.name :: first :: rest)) =
      scopeAttrCedarType? C.schema (rootType e r) (first :: rest) := by
  have hroot : (r.name == "context") = false := by cases r <;> rfl
  have hety : (if r.name == "principal" then some (rootType e Root.principal)
      else if r.name == "resource" then some (rootType e Root.resource) else none) =
      some (rootType e r) := by cases r <;> rfl
  simp only [ProviderCtx.argType?, hroot, Bool.false_eq_true, if_false]
  cases r <;> simp only [Root.name, rootType] at hety ⊢ <;> split <;> simp_all

theorem scopeType_toSpec {C' : TypingCtx} {S : Schema} {e : ReqEnv} (hv : EnvView C' S e) :
    ∀ r : Root, C'.scopeType r.toSpec = rootType e r
  | .principal => by simp [Root.toSpec, TypingCtx.scopeType, rootType, hv.principal]
  | .resource => by simp [Root.toSpec, TypingCtx.scopeType, rootType, hv.resource]


theorem pathProblems_cons (C : ProviderCtx) (a : Provider.Arg) (rest : List Provider.Arg) :
    C.pathProblems (a :: rest) = C.pathProblems [a] ++ C.pathProblems rest := by
  cases a <;> simp [ProviderCtx.pathProblems]

/-- A field argument the checks pass has its declared type in every environment. -/
theorem fieldHasType {C : ProviderCtx} {C' : TypingCtx} {e : ReqEnv} (he : e ∈ C.envs)
    (hv : EnvView C' C.schema e) {top : Bool} {p : List String} {param : ParamType}
    {a' : Dogwood.Spec.Provider.Arg} (hs : Provider.Arg.toSpec (.field p) = .ok a')
    (hty : C.argTypeProblems top (.field p) param = []) (hp : C.pathProblems [.field p] = []) :
    a'.hasTypeIn C' (paramCType C.names param) = true := by
  simp only [ProviderCtx.pathProblems, List.append_nil, Option.toList_eq_nil_iff] at hp
  rw [ProviderCtx.argTypeProblems] at hty
  rcases toSpec_field' hs with ⟨rest, rfl, rfl⟩ | ⟨r, rest, rfl, rfl⟩
  · -- `context.<rest>`
    match rest with
    | [] => simp [ProviderCtx.pathProblem] at hp
    | h :: rest' =>
      simp only [List.length_cons] at hty
      have hty : C.argTypeProblemsScalar (.field ("context" :: h :: rest')) param
          (paramCType C.names param) = [] := by simpa using hty
      obtain ⟨t, hres⟩ := resolved_of_pathProblem_context he hp
      have ht := argType?_of_scalar he hty (t := t) (by
        simp [ProviderCtx.argType?, contextPathType?, hres])
      subst ht
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
          simp [Dogwood.Spec.Provider.Arg.hasTypeIn, Dogwood.Spec.Provider.Arg.typeIn?,
            Dogwood.Spec.declaredPathType?, pathType?_of_descend' hq' hres]
  · -- `principal.<rest>` or `resource.<rest>`
    have hrn : r.name ≠ "context" := by cases r <;> simp [Root.name]
    have hty : C.argTypeProblemsScalar (.field (r.name :: rest)) param
        (paramCType C.names param) = [] := by simpa [hrn] using hty
    have hscope := scopeType_toSpec hv r
    match rest with
    | [] =>
      have ht := argType?_of_scalar he hty (argType?_root_nil C e r)
      rw [← ht]
      simp [Dogwood.Spec.Provider.Arg.hasTypeIn, Dogwood.Spec.Provider.Arg.typeIn?, hscope]
    | first :: rest' =>
      obtain ⟨attrs, t, hattrs, hres⟩ :=
        resolveOne_of_pathProblem_scope he (hv.declared r) hp
      have hfind : ∃ q, attrs.find? first = some q ∧ descend q.getType rest' = .resolved t := by
        unfold resolveOne at hres
        cases hq : attrs.find? first with
        | none => simp only [hq] at hres; cases hres
        | some q => simp only [hq] at hres; exact ⟨q, rfl, descend_of_go hres⟩
      obtain ⟨q, hq, hd⟩ := hfind
      have hat : C.argType? e (.field (r.name :: first :: rest')) = some t := by
        rw [argType?_root_attr C e r]
        simp [scopeAttrCedarType?, hattrs, hq, hd]
      have ht := argType?_of_scalar he hty hat
      rw [← ht]
      have hattrs' : C'.env.ets.attrs? (C'.scopeType r.toSpec) = some attrs := by
        rw [hscope, hv.ets]; exact hattrs
      simp [Dogwood.Spec.Provider.Arg.hasTypeIn, Dogwood.Spec.Provider.Arg.typeIn?,
        hattrs', Dogwood.Spec.declaredPathType?, pathType?_of_descend' hq hd]


theorem envs_head {C : ProviderCtx} {e : ReqEnv} (he : e ∈ C.envs) : ∃ e₀, C.envs.head? = some e₀ := by
  cases h : C.envs with
  | nil => rw [h] at he; cases he
  | cons e₀ _ => exact ⟨e₀, rfl⟩

mutual

/-- **An argument the checks pass has its declared type** in every environment of the rule. At
the top level, the literal check stands for the type check of a literal and of a set where no set
is declared. -/
theorem argHasType {C : ProviderCtx} {C' : TypingCtx} {e : ReqEnv} (he : e ∈ C.envs)
    (hv : EnvView C' C.schema e) : (a : Provider.Arg) → (top : Bool) → (param : ParamType) →
    (a' : Dogwood.Spec.Provider.Arg) → Provider.Arg.toSpec a = .ok a' →
    C.argTypeProblems top a param = [] → C.pathProblems [a] = [] →
    (top = true → ∀ k, argKind a = some k → paramTypeAccepts param.paramType k = true) →
    a'.hasTypeIn C' (paramCType C.names param) = true
  | .string s, top, param, a', hs, hty, _, hk => by
    simp [Provider.Arg.toSpec, pure, Except.pure] at hs; subst hs
    have hdecl : paramCType C.names param = .string := by
      cases top with
      | true =>
        have := hk rfl "string" rfl
        simp only [paramTypeAccepts, beq_iff_eq] at this
        exact paramCType_string _ this
      | false =>
        rw [ProviderCtx.argTypeProblems] at hty
        exact (argType?_of_scalar he (by simpa using hty) (t := .string) rfl).symm
    simp [Dogwood.Spec.Provider.Arg.hasTypeIn, Dogwood.Spec.Provider.Arg.typeIn?, hdecl]
  | .integer i, top, param, a', hs, hty, _, hk => by
    simp [Provider.Arg.toSpec, pure, Except.pure] at hs; subst hs
    have hdecl : paramCType C.names param = .int := by
      cases top with
      | true =>
        have := hk rfl "integer" rfl
        simp only [paramTypeAccepts, Bool.or_eq_true, beq_iff_eq] at this
        exact paramCType_int _ this
      | false =>
        rw [ProviderCtx.argTypeProblems] at hty
        exact (argType?_of_scalar he (by simpa using hty) (t := .int) rfl).symm
    simp [Dogwood.Spec.Provider.Arg.hasTypeIn, Dogwood.Spec.Provider.Arg.typeIn?, hdecl]
  | .decimal d, top, param, a', hs, hty, _, hk => by
    simp [Provider.Arg.toSpec, pure, Except.pure] at hs; subst hs
    have hdecl : paramCType C.names param = (.ext .decimal) := by
      cases top with
      | true =>
        have := hk rfl "decimal" rfl
        simp only [paramTypeAccepts, beq_iff_eq] at this
        exact paramCType_decimal _ this
      | false =>
        rw [ProviderCtx.argTypeProblems] at hty
        exact (argType?_of_scalar he (by simpa using hty) (t := (.ext .decimal)) rfl).symm
    simp [Dogwood.Spec.Provider.Arg.hasTypeIn, Dogwood.Spec.Provider.Arg.typeIn?, hdecl]
  | .bool b, top, param, a', hs, hty, _, hk => by
    simp [Provider.Arg.toSpec, pure, Except.pure] at hs; subst hs
    have hdecl : paramCType C.names param = (.bool .anyBool) := by
      cases top with
      | true =>
        have := hk rfl "bool" rfl
        simp only [paramTypeAccepts, Bool.or_eq_true, beq_iff_eq] at this
        exact paramCType_bool _ this
      | false =>
        rw [ProviderCtx.argTypeProblems] at hty
        exact (argType?_of_scalar he (by simpa using hty) (t := (.bool .anyBool)) rfl).symm
    simp [Dogwood.Spec.Provider.Arg.hasTypeIn, Dogwood.Spec.Provider.Arg.typeIn?, hdecl]
  | .field p, _, _, _, hs, hty, hp, _ => fieldHasType he hv hs hty hp
  | .set items, top, param, a', hs, hty, hp, hk => by
    rw [Provider.Arg.toSpec.eq_9] at hs
    cases h : Provider.Arg.toSpec.argsToSpec items with
    | error _ => rw [h] at hs; cases hs
    | ok items' =>
      rw [h] at hs
      simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hs
      subst hs
      rw [ProviderCtx.argTypeProblems] at hty
      have hp' : C.pathProblems items = [] := by simpa [ProviderCtx.pathProblems] using hp
      by_cases hset : ∃ τ, paramCType C.names param = .set τ
      · obtain ⟨τ, hτ⟩ := hset
        rw [hτ] at hty
        have hτ' := paramCType_setKind C.names (paramType_of_set C.names hτ)
        rw [hτ] at hτ'
        cases hτ'
        rw [hτ]
        simp only [Dogwood.Spec.Provider.Arg.hasTypeIn]
        exact itemsHaveType he hv items _ items' h hty hp'
      · exfalso
        cases top with
        | true =>
          have := hk rfl "set" rfl
          simp only [paramTypeAccepts, beq_iff_eq] at this
          exact hset ⟨_, paramCType_setKind C.names this⟩
        | false =>
          obtain ⟨e₀, he₀⟩ := envs_head he
          split at hty
          · rename_i τ hτ; exact hset ⟨τ, hτ⟩
          · simp [he₀] at hty

/-- The elements of a set argument the checks pass each have the element type. -/
theorem itemsHaveType {C : ProviderCtx} {C' : TypingCtx} {e : ReqEnv} (he : e ∈ C.envs)
    (hv : EnvView C' C.schema e) : (items : List Provider.Arg) → (element : ParamType) →
    (items' : List Dogwood.Spec.Provider.Arg) →
    Provider.Arg.toSpec.argsToSpec items = .ok items' → C.setItemProblems items element = [] →
    C.pathProblems items = [] →
    Dogwood.Spec.Provider.Arg.allHaveTypeIn C' items' (paramCType C.names element) = true
  | [], _, items', h, _, _ => by
    simp [Provider.Arg.toSpec.argsToSpec, pure, Except.pure] at h
    subst h
    simp [Dogwood.Spec.Provider.Arg.allHaveTypeIn]
  | x :: xs, element, items', h, hty, hp => by
    rw [Provider.Arg.toSpec.argsToSpec.eq_2] at h
    cases hx : x.toSpec with
    | error _ => rw [hx] at h; cases h
    | ok x' =>
      cases hxs : Provider.Arg.toSpec.argsToSpec xs with
      | error _ => rw [hx, hxs] at h; cases h
      | ok xs' =>
        rw [hx, hxs] at h
        simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
        subst h
        rw [ProviderCtx.setItemProblems] at hty
        simp only [List.append_eq_nil_iff] at hty
        rw [pathProblems_cons] at hp
        simp only [List.append_eq_nil_iff] at hp
        simp only [Dogwood.Spec.Provider.Arg.allHaveTypeIn, Bool.and_eq_true]
        exact ⟨argHasType he hv x false element x' hx hty.1 hp.1 (by simp),
          itemsHaveType he hv xs element xs' hxs hty.2 hp.2⟩

end


/-! ## Lists of arguments, and the invocation -/

theorem forall₂_of_mapM {α β ε : Type} {f : α → Except ε β} :
    ∀ {l : List α} {l' : List β}, l.mapM f = .ok l' → List.Forall₂ (fun a b => f a = .ok b) l l'
  | [], l', h => by
    simp [pure, Except.pure] at h
    subst h; exact .nil
  | a :: l, l', h => by
    rw [List.mapM_cons] at h
    cases ha : f a with
    | error _ => rw [ha] at h; cases h
    | ok b =>
      cases hl : l.mapM f with
      | error _ => rw [ha, hl] at h; cases h
      | ok bs =>
        rw [ha, hl] at h
        simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
        subst h
        exact .cons ha (forall₂_of_mapM hl)

/-- What the projection of a provider leaf's invocation translates: each argument, and each
method's name and arguments. -/
theorem toCall_ok {g : LoweredProviderField} {c : Dogwood.Spec.Provider.Call}
    (h : g.toCall = .ok c) :
    List.Forall₂ (fun a a' => Provider.Arg.toSpec a = .ok a') g.invocation.args c.args ∧
      List.Forall₂ (fun (m : Provider.MethodCall) (m' : Dogwood.Spec.Provider.MethodCall) =>
        m'.name = m.name ∧
          List.Forall₂ (fun a a' => Provider.Arg.toSpec a = .ok a') m.args m'.args)
        g.methods c.methods := by
  unfold LoweredProviderField.toCall at h
  dsimp only at h
  cases hl : g.invocation.function.getLast? with
  | none =>
    rw [hl] at h
    simp [bind, Except.bind] at h
  | some id =>
    rw [hl] at h
    simp only [bind, Except.bind, pure, Except.pure] at h
    split at h
    · cases h
    · rename_i args hargs
      split at h
      · cases h
      · rename_i methods hmethods
        simp only [Except.ok.injEq] at h
        subst h
        refine ⟨forall₂_of_mapM hargs, Cedar.List.Forall₂.imp (fun m m' hm => ?_)
          (forall₂_of_mapM hmethods)⟩
        split at hm
        · cases hm
        · rename_i margs hmargs
          simp only [Except.ok.injEq] at hm
          subst hm
          exact ⟨rfl, forall₂_of_mapM hmargs⟩


theorem forall_zip_of_forall₂ {α β γ δ : Type} {R : α → β → Prop} {f : γ → δ}
    {Q : β → δ → Prop} :
    ∀ {l₁ : List α} {l₂ : List β} {ps : List γ}, List.Forall₂ R l₁ l₂ →
      (∀ a b p, R a b → (a, p) ∈ l₁.zip ps → Q b (f p)) → ∀ q ∈ l₂.zip (ps.map f), Q q.1 q.2
  | _, _, [], _, _, q, hq => by simp at hq
  | [], [], _ :: _, .nil, _, q, hq => by simp at hq
  | a :: l₁, b :: l₂, p :: ps, .cons hab hrest, h, q, hq => by
    simp only [List.map_cons, List.zip_cons_cons, List.mem_cons] at hq
    rcases hq with rfl | hq
    · exact h a b p hab (by simp)
    · exact forall_zip_of_forall₂ hrest (fun a' b' p' hr hm => h a' b' p' hr (by simp [hm])) q hq

theorem literalProblems_eq_nil {key what : String} {args : List Provider.Arg}
    {params : List ParamType} (h : literalProblems key what args params = []) :
    ∀ x ∈ args.zip params, ∀ k, argKind x.1 = some k → paramTypeAccepts x.2.paramType k = true := by
  intro x hx k hk
  have := List.filterMap_eq_nil_iff.mp h x hx
  simp only [hk] at this
  split at this
  · assumption
  · cases this

theorem forall₂_length {α β : Type} {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → l₁.length = l₂.length
  | _, _, .nil => rfl
  | _, _, .cons _ h => by simp [forall₂_length h]

theorem pathProblems_mem {C : ProviderCtx} :
    ∀ {args : List Provider.Arg}, C.pathProblems args = [] → ∀ a ∈ args, C.pathProblems [a] = []
  | [], _, a, ha => by cases ha
  | b :: bs, hp, a, ha => by
    rw [pathProblems_cons, List.append_eq_nil_iff] at hp
    rcases List.mem_cons.mp ha with rfl | ha
    · exact hp.1
    · exact pathProblems_mem hp.2 a ha

theorem mem_of_mem_zip_left {α β : Type} : ∀ {l₁ : List α} {l₂ : List β} {a : α} {b : β},
    (a, b) ∈ l₁.zip l₂ → a ∈ l₁
  | [], _, _, _, h => by simp at h
  | _ :: _, [], _, _, h => by simp at h
  | x :: l₁, y :: l₂, a, b, h => by
    simp only [List.zip_cons_cons, List.mem_cons, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | h
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (mem_of_mem_zip_left h)

/-- Literal arguments the literal check passes match their declarations. -/
theorem argsMatchDecl_of {names : List (String × String)} {key what : String}
    {args : List Provider.Arg} {args' : List Dogwood.Spec.Provider.Arg} {params : List ParamType}
    (hr : List.Forall₂ (fun a a' => Provider.Arg.toSpec a = .ok a') args args')
    (hlen : params.length = args.length) (hl : literalProblems key what args params = []) :
    Dogwood.Spec.Provider.argsMatchDecl args' (params.map (paramCType names)) := by
  refine ⟨by rw [List.length_map, hlen, forall₂_length hr], ?_⟩
  exact forall_zip_of_forall₂ (f := paramCType names)
    (Q := fun b ty => b.literalType? = none ∨ b.literalType? = some ty) hr fun a a' p hs hm =>
    literalType_of_kind (a := a) (param := p) hs (literalProblems_eq_nil hl (a, p) hm)

/-- Arguments the checks pass have their declared types in every environment. -/
theorem argsTypedIn_of {C : ProviderCtx} {C' : TypingCtx} {e : ReqEnv} (he : e ∈ C.envs)
    (hv : EnvView C' C.schema e) {key what : String}
    {args : List Provider.Arg} {args' : List Dogwood.Spec.Provider.Arg} {params : List ParamType}
    (hr : List.Forall₂ (fun a a' => Provider.Arg.toSpec a = .ok a') args args')
    (hlen : params.length = args.length)
    (hty : ∀ x ∈ args.zip params, C.argTypeProblems true x.1 x.2 = [])
    (hp : C.pathProblems args = []) (hl : literalProblems key what args params = []) :
    Dogwood.Spec.Provider.ArgsTypedIn C' args' (params.map (paramCType C.names)) := by
  refine ⟨by rw [List.length_map, hlen, forall₂_length hr], ?_⟩
  exact forall_zip_of_forall₂ (f := paramCType C.names)
    (Q := fun b ty => b.hasTypeIn C' ty = true) hr fun a a' p hs hm =>
    argHasType he hv a true p a' hs (hty (a, p) hm) (pathProblems_mem hp a (mem_of_mem_zip_left hm))
      (fun _ => literalProblems_eq_nil hl (a, p) hm)


/-! ## The method chain -/

/-- The crate's signature finds a method by its name as the declaration's `lookup` does. -/
theorem find?_crateMethods (names : List (String × String)) (fn : Cedar.Spec.Name)
    (d : ProviderDecl) (n : String) :
    (crateSignature names fn d).methods.find? (·.name == n) =
      (d.methods.lookup n).map fun md =>
        { name := n, args := md.argumentTypes.map (paramCType names),
          input := md.inputType.map (paramCType names), output := paramCType names md.outputType } := by
  simp only [crateSignature]
  generalize d.methods = ms
  induction ms with
  | nil => rfl
  | cons hd tl ih =>
    obtain ⟨k, md⟩ := hd
    by_cases h : k = n
    · subst h; simp [List.lookup]
    · have h' : (n == k) = false := by simpa using Ne.symm h
      simp [List.lookup, h, h', ih]

theorem exists_of_forall₂_mem {α β : Type} {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → ∀ b ∈ l₂, ∃ a ∈ l₁, R a b
  | _, _, .nil, _, hb => by cases hb
  | a :: _, _ :: _, .cons hab hrest, b, hb => by
    rcases List.mem_cons.mp hb with rfl | hb
    · exact ⟨a, List.mem_cons_self, hab⟩
    · obtain ⟨a', ha', h⟩ := exists_of_forall₂_mem hrest b hb
      exact ⟨a', List.mem_cons_of_mem _ ha', h⟩

theorem getLast?_forall₂ {α β : Type} {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ →
      (l₁.getLast? = none ∧ l₂.getLast? = none) ∨
        ∃ a b, l₁.getLast? = some a ∧ l₂.getLast? = some b ∧ R a b
  | _, _, .nil => .inl ⟨rfl, rfl⟩
  | a :: l₁, b :: l₂, .cons hab hrest => by
    cases hrest with
    | nil => exact .inr ⟨a, b, rfl, rfl, hab⟩
    | cons hab' hrest' =>
      rw [List.getLast?_cons_cons, List.getLast?_cons_cons]
      exact getLast?_forall₂ (.cons hab' hrest')

/-- A method chain the checks pass is declared method by method, each taking the type the stage
before it produces, with the declared number of arguments, of the declared kinds. -/
theorem chain_of {C : ProviderCtx} {d : ProviderDecl} {fn : Cedar.Spec.Name} :
    ∀ {ms : List Provider.MethodCall} {ms' : List Dogwood.Spec.Provider.MethodCall}
      {pipeline : ParamType},
    List.Forall₂ (fun (m : Provider.MethodCall) (m' : Dogwood.Spec.Provider.MethodCall) =>
      m'.name = m.name ∧ List.Forall₂ (fun a a' => Provider.Arg.toSpec a = .ok a') m.args m'.args)
      ms ms' →
    chainProblems C d pipeline ms = [] →
    (crateSignature C.names fn d).Chains (paramCType C.names pipeline) ms' ∧
      ∀ m ∈ ms, ∃ md, d.methods.lookup m.name = some md ∧
        md.argumentTypes.length = m.args.length ∧
        ∃ what, literalProblems C.key what m.args md.argumentTypes = []
  | [], [], _, .nil, _ => ⟨trivial, by simp⟩
  | m :: ms, m' :: ms', pipeline, .cons ⟨hn, _⟩ hrest, h => by
    simp only [chainProblems] at h
    split at h
    · cases h
    · cases hmd : d.methods.lookup m.name with
      | none => rw [hmd] at h; cases h
      | some md =>
        rw [hmd] at h
        simp only [List.append_eq_nil_iff] at h
        obtain ⟨⟨hin, hargs⟩, hrest'⟩ := h
        have ih := chain_of (fn := fn) hrest hrest'
        refine ⟨?_, ?_⟩
        · simp only [Dogwood.Spec.Provider.Signature.Chains, hn, find?_crateMethods, hmd,
            Option.map_some]
          refine ⟨?_, ih.1⟩
          cases hi : md.inputType with
          | none => exact .inl rfl
          | some input =>
            rw [hi] at hin
            simp only at hin
            split at hin
            · rename_i heq
              exact .inr (by simpa using heq)
            · cases hin
        · intro x hx
          rcases List.mem_cons.mp hx with rfl | hx
          · refine ⟨md, hmd, ?_⟩
            split at hargs
            · cases hargs
            · rename_i hlen
              exact ⟨by simpa using hlen, _, hargs⟩
          · exact ih.2 x hx


/-! ## The provider leaf -/

/-- **The provider dialect is sound.** A provider leaf on which the crate's checks find nothing,
and whose provider the specification declares as the crate does, names a declared provider and
declared methods, each taking the type the stage before it produces, with arguments that match
their declarations (`Provider.Call.Declared`); its value has the type the crate gives it; and in
every request environment of its rule, its arguments have their declared types
(`Provider.Call.TypedIn`). -/
theorem provider_sound {S : Schema} {g : LoweredProviderField} {d : ProviderDecls.ProviderDecl}
    {c : Dogwood.Spec.Provider.Call} {D : Dogwood.Spec.Provider.Declarations}
    (hf : providerLeafFindings S g = []) (hd : g.declaration = some d) (hc : g.toCall = .ok c)
    (hD : D.find? c.function = some (crateSignature g.entityTypeNames c.function d)) :
    c.Declared D ∧ c.outputType? D = crateOutputType g d ∧ (crateOutputType g d).isSome ∧
      ∀ (C' : TypingCtx) (e : ReqEnv), e ∈ (providerCtx S g).envs → EnvView C' S e →
        c.TypedIn C' D := by
  obtain ⟨hargs, hmethods⟩ := toCall_ok hc
  simp only [providerLeafFindings, hd] at hf
  split at hf
  · simp at hf
  · rename_i hlen
    have hlen : d.argumentTypes.length = g.invocation.args.length := by simpa using hlen
    simp only [List.append_eq_nil_iff] at hf
    obtain ⟨⟨⟨⟨⟨⟨_, hlit⟩, hpath⟩, hmpath⟩, htop⟩, hmty⟩, hchain⟩ := hf
    have hch := chain_of (C := providerCtx S g) (fn := c.function) hmethods hchain
    -- each method of the invocation is one of the leaf's, and the crate's signature declares it
    have hmeth : ∀ m' ∈ c.methods, ∃ m ∈ g.methods, ∃ md,
        m'.name = m.name ∧
        List.Forall₂ (fun a a' => Provider.Arg.toSpec a = .ok a') m.args m'.args ∧
        d.methods.lookup m.name = some md ∧ md.argumentTypes.length = m.args.length ∧
        (∃ what, literalProblems (providerCtx S g).key what m.args md.argumentTypes = []) ∧
        ((crateSignature g.entityTypeNames c.function d).methods.find? (·.name == m'.name) =
          some { name := m.name, args := md.argumentTypes.map (paramCType g.entityTypeNames),
                 input := md.inputType.map (paramCType g.entityTypeNames),
                 output := paramCType g.entityTypeNames md.outputType }) := by
      intro m' hm'
      obtain ⟨m, hm, hn, hr⟩ := exists_of_forall₂_mem hmethods m' hm'
      obtain ⟨md, hmd, hl, hw⟩ := hch.2 m hm
      exact ⟨m, hm, md, hn, hr, hmd, hl, hw, by rw [find?_crateMethods, hn, hmd]; rfl⟩
    refine ⟨⟨_, hD, argsMatchDecl_of hargs hlen hlit, fun m' hm' => ?_, hch.1⟩, ?_, ?_, ?_⟩
    · -- the methods are declared, with arguments that match
      obtain ⟨m, _, md, hn, hr, _, hl, ⟨_, hw⟩, hfind⟩ := hmeth m' hm'
      exact ⟨_, List.mem_of_find?_eq_some hfind, hn.symm, argsMatchDecl_of hr hl hw⟩
    · -- the value's type
      simp only [Dogwood.Spec.Provider.Call.outputType?, hD]
      rcases getLast?_forall₂ hmethods with ⟨h₁, h₂⟩ | ⟨m, m', h₁, h₂, hn, _⟩
      · simp [h₁, h₂, crateOutputType, crateSignature]
      · simp only [h₂, crateOutputType, h₁, hn, find?_crateMethods, Option.map_map]
        rfl
    · -- the type exists
      unfold crateOutputType
      split
      · rfl
      · rename_i m hlast
        obtain ⟨md, hmd, _⟩ := hch.2 m (List.mem_of_getLast? hlast)
        simp [hmd]
    · -- the arguments have their types in every environment
      intro C' e he hv
      refine ⟨_, hD, argsTypedIn_of (C := providerCtx S g) he hv hargs hlen
        (fun x hx => List.flatMap_eq_nil_iff.mp htop x hx) hpath hlit, fun m' hm' => ?_⟩
      obtain ⟨m, hm, md, hn, hr, hmd, hl, ⟨_, hw⟩, hfind⟩ := hmeth m' hm'
      refine ⟨_, List.mem_of_find?_eq_some hfind, hn.symm, ?_⟩
      have hty := List.flatMap_eq_nil_iff.mp hmty m hm
      rw [hmd] at hty
      exact argsTypedIn_of (C := providerCtx S g) he hv hr hl
        (fun x hx => List.flatMap_eq_nil_iff.mp hty x hx)
        (List.flatMap_eq_nil_iff.mp hmpath m hm) hw

end Dogwood.Thm.Frontend
