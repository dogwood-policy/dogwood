import Dogwood.Thm.Frontend.Validate.CompleteInterface
import Dogwood.Thm.Frontend.Validate.Typing
import Dogwood.Thm.Frontend.Validate.Monitor
import Cedar.Thm.Data.Map
import Dogwood.Frontend.Validate.Converse

/-!
# The validator's temporal checks are complete for typing

`leaf_complete`: the temporal dialect of the frontend's validator
(`Dogwood.Frontend.Validate.leafFindings`) reports nothing on a temporal leaf that is well-typed
in every request environment of its rule, in a typing context of the specification that sees the
environment exactly as the crate's validator does (`ViewExact`), and that monitors time, except
where the crate is stricter than the specification:

* `noReservedHeadReadsF`: the crate resolves no `context.<path>` whose head lowering reserves;
* `pinHeadsUnreserved`: nor a pin's `context.<path>` whose head lowering reserves;
* `actionsApart` (`Dogwood.Frontend.Validate.actionsApart`): the crate checks an entity literal by
  its type's name, an `Action` literal against the actions and any other against the entity types,
  where the specification accepts a literal that is either. Cedar's schemas keep the two apart.

The proof follows the passes. The typing of each sub-condition in every environment
(`AllTyped`) is decomposed along the walk of the condition (`nodes_typed`); the per-node checks
read it off one environment (event names, windows, wildcards, literals, summands) or off the
environments of each action and admitted entity type (request paths, `env_of_action`). The type
check is the typing derivation read back in each environment (`typesF_nil`), and the validity
rules are what the typing of binders, optional reads and pins requires (`validity_nil`).
-/

namespace Dogwood.Thm.Frontend

open Dogwood.Frontend Dogwood.Frontend.Validate
open Dogwood.Spec (Path ScopeRoot)
open Dogwood.Spec.Temporal
open Dogwood.Eval (acceptsB withinB)
open Cedar.Validation (CedarType Schema ActionSchemaEntry RecordType QualifiedType TypeEnv)
open Cedar.Spec (Attr EntityUID EntityType)

/-! ## The crate's further strictness -/

/-- No pin of a derived event correlates its field with a `context.<path>` whose head lowering
reserves: the crate's pin rule resolves no such path, where the specification resolves one the
action schema declares. -/
def pinHeadsUnreserved (d : DerivedEventSchema) : Bool :=
  d.events.all fun ev => ev.pins.all fun pin =>
    match pin.root, pin.contextPath with
    | .context, head :: _ => !isHoistedName head
    | _, _ => true

namespace TypingComplete

/-! ## Paths -/

/-- A path the specification types resolves in the crate's descent. -/
theorem descend_of_pathType {present : Path → Bool} :
    ∀ (p : Path) (R : RecordType) (pre : Path) (ty : CedarType),
      pathType? present R pre p = some ty → descend (.record R) p = .resolved ty
  | [], _, _, _, h => by simp [pathType?] at h
  | a :: p, R, pre, ty, h => by
    simp only [pathType?] at h
    simp only [descend]
    cases hq : R.find? a with
    | none => rw [hq] at h; cases h
    | some q =>
      rw [hq] at h
      simp only at h ⊢
      by_cases hr : (q.isRequired || present (pre ++ [a])) = true
      · rw [if_pos hr] at h
        cases p with
        | nil => simp only at h; cases h; simp [descend]
        | cons b p =>
          cases hT : q.getType with
          | record R' =>
            rw [hT] at h
            exact descend_of_pathType (b :: p) R' _ ty h
          | _ => rw [hT] at h; simp at h
      · rw [if_neg hr] at h; cases h

/-- `resolve_one`'s descent follows `descend`. -/
theorem go_of_descend : ∀ (T : CedarType) (rest : List String) (ty : CedarType),
    descend T rest = .resolved ty → resolveOne.go T rest = .ok ty
  | T, [], ty, h => by
    have : descend T [] = .resolved T := by cases T <;> rfl
    rw [this] at h; cases h; cases T <;> rfl
  | .record R, s :: rest, ty, h => by
    simp only [descend] at h
    simp only [resolveOne.go]
    cases hq : R.find? s with
    | none => rw [hq] at h; cases h
    | some q => rw [hq] at h; exact go_of_descend q.getType rest ty h
  | .bool _, _ :: _, _, h | .int, _ :: _, _, h | .string, _ :: _, _, h | .entity _, _ :: _, _, h
  | .set _, _ :: _, _, h | .ext _, _ :: _, _, h => by simp [descend] at h

/-- A context path the specification types, whose head lowering does not reserve, resolves in the
crate's view of the context. -/
theorem resolveContextPath_of_type {present : Path → Bool} {R R' : RecordType} {h : Attr}
    {rest : Path} {ty : CedarType} (hf : R.find? h = R'.find? h) (hh : isHoistedName h = false)
    (hty : pathType? present R [] (h :: rest) = some ty) :
    resolveContextPath R' (h :: rest) = .resolved ty := by
  rw [pathType?_congr hf] at hty
  have hd := descend_of_pathType _ _ _ _ hty
  simp only [descend] at hd
  simp only [resolveContextPath, hh, Bool.false_eq_true, if_false]
  cases hq : R'.find? h with
  | none => rw [hq] at hd; cases hd
  | some q => rw [hq] at hd; exact hd

/-- A scope attribute path the specification types resolves on the entity type's attributes. -/
theorem resolveOne_of_pathType {present : Path → Bool} {R : RecordType} {pre : Path} {a : Attr}
    {rest : Path} {ty : CedarType} (hty : pathType? present R pre (a :: rest) = some ty) :
    resolveOne R a rest = .ok ty := by
  have hd := descend_of_pathType _ _ _ _ hty
  simp only [descend] at hd
  simp only [resolveOne]
  cases hq : R.find? a with
  | none => rw [hq] at hd; cases hd
  | some q => rw [hq] at hd; exact go_of_descend _ _ _ hd

/-- A path the specification types, with every guard it reads one the crate's validator has, has
no unguarded optional attribute. -/
theorem unguarded_none {present guarded : Path → Bool}
    (hpg : ∀ q, present q = true → guarded q = true) :
    ∀ (p : Path) (R : RecordType) (pre : Path) (ty : CedarType),
      pathType? present R pre p = some ty → unguardedOptional guarded R pre p = none
  | [], _, _, _, _ => rfl
  | a :: p, R, pre, ty, h => by
    simp only [pathType?] at h
    simp only [unguardedOptional]
    cases hq : R.find? a with
    | none => rfl
    | some q =>
      rw [hq] at h
      simp only at h ⊢
      by_cases hr : (q.isRequired || present (pre ++ [a])) = true
      · rw [if_pos hr] at h
        have hnot : (!q.isRequired && !guarded (pre ++ [a])) = false := by
          cases hq' : q.isRequired
          · rw [hq', Bool.false_or] at hr; simp [hpg _ hr]
          · simp
        rw [hnot]
        simp only [Bool.false_eq_true, if_false]
        cases p with
        | nil => rfl
        | cons b p =>
          cases hT : q.getType with
          | record R' =>
            rw [hT] at h
            exact unguarded_none hpg (b :: p) R' _ ty h
          | _ => rfl
      · rw [if_neg hr] at h; cases h

/-- A path the specification types with no guard has every attribute along it required. -/
theorem required_of_pathType {present : Path → Bool} (hp : ∀ q, present q = false) :
    ∀ (p : Path) (R : RecordType) (pre : Path) (ty : CedarType),
      pathType? present R pre p = some ty → requiredPathType? R p = some ty
  | [], _, _, _, h => by simp [pathType?] at h
  | [a], R, pre, ty, h => by
    simp only [pathType?] at h
    simp only [requiredPathType?]
    cases hq : R.find? a with
    | none => rw [hq] at h; cases h
    | some q =>
      rw [hq] at h
      cases q with
      | optional t => simp [Cedar.Validation.Qualified.isRequired, hp] at h
      | required t =>
        simp only [Cedar.Validation.Qualified.isRequired, Bool.true_or, if_true,
          Cedar.Validation.Qualified.getType] at h
        exact h
  | a :: b :: p, R, pre, ty, h => by
    simp only [pathType?] at h
    simp only [requiredPathType?]
    cases hq : R.find? a with
    | none => rw [hq] at h; cases h
    | some q =>
      rw [hq] at h
      cases q with
      | optional t => simp [Cedar.Validation.Qualified.isRequired, hp] at h
      | required t =>
        simp only [Cedar.Validation.Qualified.isRequired, Bool.true_or, if_true,
          Cedar.Validation.Qualified.getType] at h
        cases t with
        | record R' => exact required_of_pathType hp (b :: p) R' _ ty h
        | _ => simp at h

/-! ## Binders -/

theorem declared_of_sort {S : Schema} {ty : BinderType} {τ : TType}
    (h : ty.sort? S.ets = some τ) : binderTypeDeclared S ty = true ∧ τ = annotationSort ty := by
  cases ty with
  | timepoint => simp [BinderType.sort?] at h; subst h; exact ⟨rfl, rfl⟩
  | named path =>
    simp only [BinderType.sort?, binderTypeDeclared, annotationSort] at h ⊢
    split at h <;> simp_all

theorem binder_of_sort {S : Schema} {ets : Cedar.Validation.EntitySchema} (hets : ets = S.ets)
    {x : Binder} {b : VarName × TType} (h : Binder.sort? ets x = some b) :
    binderTypeDeclared S x.ty = true ∧ b = (x.name, annotationSort x.ty) := by
  subst hets
  simp only [Binder.sort?] at h
  split at h
  · cases h
  · obtain ⟨τ, hτ, rfl⟩ := Option.map_eq_some_iff.mp h
    obtain ⟨hd, rfl⟩ := declared_of_sort hτ
    exact ⟨hd, rfl⟩

theorem mapM_sort {S : Schema} :
    ∀ {dom : List Binder} {Δ : Bindings}, dom.mapM (Binder.sort? S.ets) = some Δ →
      (∀ b ∈ dom, binderTypeDeclared S b.ty = true) ∧ Δ = binderBindings dom
  | [], Δ, h => by
    simp only [List.mapM_nil, pure, Option.some.injEq] at h
    subst h; exact ⟨fun _ hb => (by cases hb), rfl⟩
  | b :: dom, Δ, h => by
    simp only [List.mapM_cons, bind, Option.bind, pure] at h
    cases hb : Binder.sort? S.ets b with
    | none => rw [hb] at h; cases h
    | some y =>
      rw [hb] at h
      cases hd : dom.mapM (Binder.sort? S.ets) with
      | none => rw [hd] at h; cases h
      | some ys =>
        rw [hd] at h
        simp only [Option.some.injEq] at h
        subst h
        obtain ⟨hd1, rfl⟩ := binder_of_sort rfl hb
        obtain ⟨hd2, rfl⟩ := mapM_sort hd
        refine ⟨fun b' hb' => ?_, rfl⟩
        rcases List.mem_cons.mp hb' with rfl | hb'
        · exact hd1
        · exact hd2 b' hb'

theorem domain_of_sorts {S : Schema} {ets : Cedar.Validation.EntitySchema} (hets : ets = S.ets)
    {dom : List Binder} {Δ : Bindings} (h : domainSorts? ets dom = some Δ) :
    (dom.map (·.name)).Nodup ∧ (∀ b ∈ dom, binderTypeDeclared S b.ty = true) ∧
      Δ = binderBindings dom := by
  subst hets
  simp only [domainSorts?] at h
  split at h
  · rename_i hnd
    exact ⟨hnd, mapM_sort h⟩
  · cases h

theorem bindersTyped_of {S : Schema} {dom : List Binder} (hnd : (dom.map (·.name)).Nodup)
    (hd : ∀ b ∈ dom, binderTypeDeclared S b.ty = true) : bindersTyped S dom = true := by
  simp only [bindersTyped, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq]
  exact ⟨hd, hnd⟩

theorem binderValueSort_of_declared {S : Schema} {ty : BinderType}
    (hd : binderTypeDeclared S ty = true) (hnt : ty ≠ .timepoint) :
    binderValueSort? S ty = some (annotationSort ty) := by
  cases ty with
  | timepoint => exact absurd rfl hnt
  | named path =>
    simp only [binderValueSort?, annotationSort, binderTypeDeclared] at hd ⊢
    split <;> simp_all

theorem summand_of_int {s : VarName} {ty : BinderType} (h : annotationSort ty = .cedar .int) :
    summandProblem s ty = none := by
  cases ty with
  | timepoint => simp [annotationSort] at h
  | named path =>
    simp only [annotationSort, summandProblem] at h ⊢
    split at h <;> simp_all

theorem find?_of_mem_nodup {x : VarName} :
    ∀ {dom : List Binder} {b : Binder}, (dom.map (·.name)).Nodup → b ∈ dom → b.name = x →
      dom.find? (·.name == x) = some b
  | [], _, _, hb, _ => by cases hb
  | a :: t, b, hnd, hb, hx => by
    simp only [List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.mp hb with rfl | hb
    · simp [hx]
    · have hax : a.name ≠ x := fun h => hnd.1 (h ▸ hx ▸ List.mem_map.mpr ⟨b, hb, rfl⟩)
      simp only [List.find?_cons, show (a.name == x) = false by simpa using hax]
      exact find?_of_mem_nodup hnd.2 hb hx

/-! ## Request environments -/

section

variable {C : LeafCtx}

theorem env_mem {uid : EntityUID} {entry : ActionSchemaEntry} {p r : EntityType}
    (ht : (uid, entry) ∈ C.targets) (hp : p ∈ admittedTypes C.schema entry .principal C.principal)
    (hr : r ∈ admittedTypes C.schema entry .resource C.resource) :
    (⟨uid, entry, p, r⟩ : ReqEnv) ∈ C.envs := by
  simp only [LeafCtx.envs, List.mem_flatMap, List.mem_map]
  exact ⟨(uid, entry), ht, p, hp, r, hr, rfl⟩

theorem admitted_of_action {uid : EntityUID} {entry : ActionSchemaEntry}
    (h : (uid, entry) ∈ C.actions) :
    (uid, entry) ∈ C.targets ∧ (∃ p, p ∈ admittedTypes C.schema entry .principal C.principal) ∧
      (∃ r, r ∈ admittedTypes C.schema entry .resource C.resource) := by
  obtain ⟨ht, hadm⟩ := List.mem_filter.mp h
  simp only [admitsAnyEnv, Bool.and_eq_true, List.any_eq_true] at hadm
  obtain ⟨⟨p, hp, hpa⟩, ⟨r, hr, hra⟩⟩ := hadm
  exact ⟨ht, ⟨p, List.mem_filter.mpr ⟨hp, hpa⟩⟩, ⟨r, List.mem_filter.mpr ⟨hr, hra⟩⟩⟩

/-- An action of the leaf has a request environment for each entity type it admits for a root. -/
theorem env_of_action {uid : EntityUID} {entry : ActionSchemaEntry} (h : (uid, entry) ∈ C.actions)
    (r : ScopeRoot) {ety : EntityType}
    (hety : ety ∈ admittedTypes C.schema entry (Root.ofSpec r) (C.narrow (Root.ofSpec r))) :
    ∃ e ∈ C.envs, e.uid = uid ∧ e.entry = entry ∧ e.scopeType r = ety := by
  obtain ⟨ht, ⟨p, hp⟩, ⟨r', hr'⟩⟩ := admitted_of_action h
  cases r
  · exact ⟨⟨uid, entry, ety, r'⟩, env_mem ht hety hr', rfl, rfl, rfl⟩
  · exact ⟨⟨uid, entry, p, ety⟩, env_mem ht hp hety, rfl, rfl, rfl⟩

theorem env_of_action' {uid : EntityUID} {entry : ActionSchemaEntry}
    (h : (uid, entry) ∈ C.actions) :
    ∃ e ∈ C.envs, e.uid = uid ∧ e.entry = entry := by
  obtain ⟨ht, ⟨p, hp⟩, ⟨r', hr'⟩⟩ := admitted_of_action h
  exact ⟨⟨uid, entry, p, r'⟩, env_mem ht hp hr', rfl, rfl⟩

theorem env_admitted {e : ReqEnv} (he : e ∈ C.envs) (r : ScopeRoot) :
    e.scopeType r ∈ admittedTypes C.schema e.entry (Root.ofSpec r) (C.narrow (Root.ofSpec r)) := by
  obtain ⟨-, hp, hr⟩ := mem_envs he
  cases r
  · exact hp
  · exact hr

theorem env_attrs {C' : TypingCtx} {e : ReqEnv} (he : e ∈ C.envs) (hv : EnvView C' C.schema e)
    (r : ScopeRoot) : ∃ attrs, entityAttrs? C.schema (e.scopeType r) = some attrs := by
  have hmem := (List.mem_filter.mp (env_admitted he r)).1
  have hc := hv.declared _ _ hmem
  simp only [Cedar.Validation.EntitySchema.contains, Option.isSome_iff_exists] at hc
  obtain ⟨entry, he'⟩ := hc
  exact ⟨entry.attrs, by simp [entityAttrs?, Cedar.Validation.EntitySchema.attrs?, he']⟩

end

theorem view_scopeType {C' : TypingCtx} {S : Schema} {e : ReqEnv} (hv : EnvView C' S e)
    (r : ScopeRoot) : C'.scopeType r = e.scopeType r := by
  cases r
  · exact hv.principal
  · exact hv.resource

theorem scopeAttr_attrs {C' : TypingCtx} {S : Schema} {e : ReqEnv} (hv : EnvView C' S e)
    {r : ScopeRoot} {p : Path} {ty : CedarType} {attrs : RecordType}
    (hattrs : entityAttrs? S (e.scopeType r) = some attrs) (h : C'.scopeAttrType? r p = some ty) :
    pathType? (fun q => decide (Guard.scope r q ∈ C'.facts)) attrs [] p = some ty := by
  unfold TypingCtx.scopeAttrType? at h
  rw [hv.ets, view_scopeType hv r] at h
  have hattrs' : S.ets.attrs? (e.scopeType r) = some attrs := hattrs
  rw [hattrs'] at h
  exact h

/-! ## Typing in every environment -/

/-- The condition is well-typed with the bindings `Γ` in every request environment of the leaf, in
a typing context that sees the environment exactly as the crate's validator does. -/
def AllTyped (C : LeafCtx) (Γ : Bindings) (ψ : Formula) : Prop :=
  ∀ e ∈ C.envs, ∃ C', ViewExact C' C e ∧ ψ.WellTyped C' Γ

/-- The operand is typed with the bindings `Γ` in every request environment of the leaf. -/
def AllTypedT (C : LeafCtx) (Γ : Bindings) (t : Term) : Prop :=
  ∀ e ∈ C.envs, ∃ C' τ, ViewExact C' C e ∧ Term.Typed C' Γ t τ

section

variable {C : LeafCtx} {Γ : Bindings}

theorem AllTyped.one (henv : C.envs ≠ []) {ψ : Formula} (h : AllTyped C Γ ψ) :
    ∃ e C', e ∈ C.envs ∧ ViewExact C' C e ∧ ψ.WellTyped C' Γ := by
  obtain ⟨e, he⟩ := List.exists_mem_of_ne_nil _ henv
  obtain ⟨C', hv, hw⟩ := h e he
  exact ⟨e, C', he, hv, hw⟩

theorem AllTypedT.one (henv : C.envs ≠ []) {t : Term} (h : AllTypedT C Γ t) :
    ∃ e C' τ, e ∈ C.envs ∧ ViewExact C' C e ∧ Term.Typed C' Γ t τ := by
  obtain ⟨e, he⟩ := List.exists_mem_of_ne_nil _ henv
  obtain ⟨C', τ, hv, ht⟩ := h e he
  exact ⟨e, C', τ, he, hv, ht⟩

theorem AllTyped.and {φ ψ : Formula} (h : AllTyped C Γ (.and φ ψ)) :
    AllTyped C Γ φ ∧ AllTyped C Γ ψ := by
  refine ⟨fun e he => ?_, fun e he => ?_⟩ <;> obtain ⟨C', hv, hw⟩ := h e he
  · cases hw with | and h1 _ => exact ⟨C', hv, h1⟩
  · cases hw with | and _ h2 => exact ⟨C', hv, h2⟩

theorem AllTyped.since {φ ψ : Formula} {w : Window} (h : AllTyped C Γ (.since φ w ψ)) :
    AllTyped C Γ φ ∧ AllTyped C Γ ψ := by
  refine ⟨fun e he => ?_, fun e he => ?_⟩ <;> obtain ⟨C', hv, hw⟩ := h e he
  · cases hw with | since _ h1 _ => exact ⟨C', hv, h1⟩
  · cases hw with | since _ _ h2 => exact ⟨C', hv, h2⟩

theorem AllTyped.not {φ : Formula} (h : AllTyped C Γ (.not φ)) : AllTyped C Γ φ := by
  intro e he
  obtain ⟨C', hv, hw⟩ := h e he
  cases hw with | not h1 => exact ⟨C', hv, h1⟩

theorem AllTyped.formerly {φ : Formula} {w : Window} (h : AllTyped C Γ (.formerly w φ)) :
    AllTyped C Γ φ := by
  intro e he
  obtain ⟨C', hv, hw⟩ := h e he
  cases hw with | formerly _ h1 => exact ⟨C', hv, h1⟩

theorem AllTyped.previous {φ : Formula} {w : Window} (h : AllTyped C Γ (.previous w φ)) :
    AllTyped C Γ φ := by
  intro e he
  obtain ⟨C', hv, hw⟩ := h e he
  cases hw with | previous _ h1 => exact ⟨C', hv, h1⟩

theorem AllTyped.exist {x : Binder} {φ : Formula} (h : AllTyped C Γ (.exist x φ)) :
    AllTyped C ((x.name, annotationSort x.ty) :: Γ) φ := by
  intro e he
  obtain ⟨C', hv, hw⟩ := h e he
  cases hw with
  | exist hb h1 =>
    obtain ⟨-, rfl⟩ := binder_of_sort hv.ets hb
    exact ⟨C', hv, h1⟩

theorem AllTyped.cmp {op : CmpOp} {l r : Term} (h : AllTyped C Γ (.cmp op l r)) :
    AllTypedT C Γ l ∧ AllTypedT C Γ r := by
  refine ⟨fun e he => ?_, fun e he => ?_⟩ <;> obtain ⟨C', hv, hw⟩ := h e he
  · cases hw with
    | eq _ hl _ _ => exact ⟨C', _, hv, hl⟩
    | ord _ hl _ => exact ⟨C', _, hv, hl⟩
  · cases hw with
    | eq _ _ hr _ => exact ⟨C', _, hv, hr⟩
    | ord _ _ hr => exact ⟨C', _, hv, hr⟩

theorem AllTypedT.arith {op : ArithOp} {l r : Term} (h : AllTypedT C Γ (.arith op l r)) :
    AllTypedT C Γ l ∧ AllTypedT C Γ r := by
  refine ⟨fun e he => ?_, fun e he => ?_⟩ <;> obtain ⟨C', τ, hv, ht⟩ := h e he
  · cases ht with | arith hl _ => exact ⟨C', _, hv, hl⟩
  · cases ht with | arith _ hr => exact ⟨C', _, hv, hr⟩

theorem AllTypedT.count {dom : List Binder} {body : Formula}
    (h : AllTypedT C Γ (.agg (.count dom body))) : AllTyped C (binderBindings dom ++ Γ) body := by
  intro e he
  obtain ⟨C', τ, hv, ht⟩ := h e he
  cases ht with
  | agg ha =>
    cases ha with
    | count hd hb =>
      obtain ⟨-, -, rfl⟩ := domain_of_sorts hv.ets hd
      exact ⟨C', hv, hb⟩

theorem AllTypedT.sum {s : VarName} {dom : List Binder} {body : Formula}
    (h : AllTypedT C Γ (.agg (.sum s dom body))) : AllTyped C (binderBindings dom ++ Γ) body := by
  intro e he
  obtain ⟨C', τ, hv, ht⟩ := h e he
  cases ht with
  | agg ha =>
    cases ha with
    | sum hd _ hb =>
      obtain ⟨-, -, rfl⟩ := domain_of_sorts hv.ets hd
      exact ⟨C', hv, hb⟩

/-- A well-typed aggregate's `for` list is well-formed. -/
theorem AllTypedT.countDom (henv : C.envs ≠ []) {dom : List Binder} {body : Formula}
    (h : AllTypedT C Γ (.agg (.count dom body))) :
    (dom.map (·.name)).Nodup ∧ ∀ b ∈ dom, binderTypeDeclared C.schema b.ty = true := by
  obtain ⟨e, C', τ, he, hv, ht⟩ := h.one henv
  cases ht with
  | agg ha =>
    cases ha with
    | count hd _ =>
      obtain ⟨hnd, hdecl, -⟩ := domain_of_sorts hv.ets hd
      exact ⟨hnd, hdecl⟩

theorem AllTypedT.sumDom (henv : C.envs ≠ []) {s : VarName} {dom : List Binder} {body : Formula}
    (h : AllTypedT C Γ (.agg (.sum s dom body))) :
    (dom.map (·.name)).Nodup ∧ ∀ b ∈ dom, binderTypeDeclared C.schema b.ty = true := by
  obtain ⟨e, C', τ, he, hv, ht⟩ := h.one henv
  cases ht with
  | agg ha =>
    cases ha with
    | sum hd _ _ =>
      obtain ⟨hnd, hdecl, -⟩ := domain_of_sorts hv.ets hd
      exact ⟨hnd, hdecl⟩

theorem AllTypedT.atoms : ∀ {t : Term}, AllTypedT C Γ t → ∀ u ∈ termAtoms t, AllTypedT C Γ u
  | .arith op l r, h, u, hu => by
    simp only [termAtoms, List.mem_cons, List.mem_append] at hu
    rcases hu with rfl | hu | hu
    · exact h
    · exact AllTypedT.atoms h.arith.1 u hu
    · exact AllTypedT.atoms h.arith.2 u hu
  | .entity _, h, u, hu | .long _, h, u, hu | .decimal _, h, u, hu | .string _, h, u, hu
  | .bool _, h, u, hu | .context _, h, u, hu | .scope _ _, h, u, hu | .var _, h, u, hu
  | .agg _, h, u, hu | .wildcard, h, u, hu => by
    simp only [termAtoms, List.mem_singleton] at hu
    subst hu
    exact h

theorem AllTyped.predArg {a : EntityUID} {k : String} {args : List (Path × Term)}
    (h : AllTyped C Γ (.pred a k args)) {p : Path} {t : Term} (hpt : (p, t) ∈ args)
    (hnw : t ≠ .wildcard) : AllTypedT C Γ t := by
  intro e he
  obtain ⟨C', hv, hw⟩ := h e he
  cases hw with
  | pred _ hargs _ =>
    cases hargs _ hpt with
    | wildcard _ => exact absurd rfl hnw
    | var _ hx _ => exact ⟨C', _, hv, .var hx⟩
    | term _ _ _ _ ht _ => exact ⟨C', _, hv, ht⟩

end

/-! ## Atoms and arguments -/

theorem mem_argsAtoms' {u : Term} :
    ∀ {args : List (Path × Term)}, u ∈ argsAtoms args → ∃ p t, (p, t) ∈ args ∧ u ∈ termAtoms t
  | [], h => by cases h
  | (p, t) :: args, h => by
    simp only [argsAtoms, List.mem_append] at h
    rcases h with h | h
    · exact ⟨p, t, List.mem_cons_self .., h⟩
    · obtain ⟨p', t', hpt, hu⟩ := mem_argsAtoms' h
      exact ⟨p', t', List.mem_cons_of_mem _ hpt, hu⟩

theorem noRes_atoms : ∀ {t : Term}, noReservedHeadReadsT t = true →
    ∀ u ∈ termAtoms t, noReservedHeadReadsT u = true
  | .arith op l r, h, u, hu => by
    simp only [termAtoms, List.mem_cons, List.mem_append] at hu
    have h' := h
    simp only [noReservedHeadReadsT, Bool.and_eq_true] at h'
    rcases hu with rfl | hu | hu
    · exact h
    · exact noRes_atoms h'.1 u hu
    · exact noRes_atoms h'.2 u hu
  | .entity _, h, u, hu | .long _, h, u, hu | .decimal _, h, u, hu | .string _, h, u, hu
  | .bool _, h, u, hu | .context _, h, u, hu | .scope _ _, h, u, hu | .var _, h, u, hu
  | .agg _, h, u, hu | .wildcard, h, u, hu => by
    simp only [termAtoms, List.mem_singleton] at hu
    subst hu
    exact h

theorem noRes_of_arg {p : Path} {t : Term} : ∀ {args : List (Path × Term)},
    noReservedHeadReadsArgs args = true → (p, t) ∈ args → noReservedHeadReadsT t = true
  | [], _, h => by cases h
  | (p', t') :: args, hn, h => by
    simp only [noReservedHeadReadsArgs, Bool.and_eq_true] at hn
    rcases List.mem_cons.mp h with h | h
    · cases h; exact hn.1
    · exact noRes_of_arg hn.2 h

section

variable {C : LeafCtx} {Γ : Bindings}

theorem nodeTerms_typed {n : Formula} (h : AllTyped C Γ n) :
    ∀ u ∈ nodeTerms n, u = .wildcard ∨ AllTypedT C Γ u := by
  intro u hu
  cases n with
  | cmp op l r =>
    simp only [nodeTerms, List.mem_append] at hu
    rcases hu with hu | hu
    · exact .inr (h.cmp.1.atoms u hu)
    · exact .inr (h.cmp.2.atoms u hu)
  | pred a k args =>
    simp only [nodeTerms] at hu
    obtain ⟨p, t, hpt, hu⟩ := mem_argsAtoms' hu
    by_cases hw : t = .wildcard
    · subst hw
      simp only [termAtoms, List.mem_singleton] at hu
      exact .inl hu
    · exact .inr ((h.predArg hpt hw).atoms u hu)
  | _ => simp [nodeTerms] at hu

theorem nodeTerms_noRes {n : Formula} (h : noReservedHeadReadsF n = true) :
    ∀ u ∈ nodeTerms n, noReservedHeadReadsT u = true := by
  intro u hu
  cases n with
  | cmp op l r =>
    simp only [nodeTerms, List.mem_append] at hu
    simp only [noReservedHeadReadsF, Bool.and_eq_true] at h
    rcases hu with hu | hu
    · exact noRes_atoms h.1 u hu
    · exact noRes_atoms h.2 u hu
  | pred a k args =>
    simp only [nodeTerms] at hu
    obtain ⟨p, t, hpt, hu⟩ := mem_argsAtoms' hu
    simp only [noReservedHeadReadsF] at h
    exact noRes_atoms (noRes_of_arg h hpt) u hu
  | _ => simp [nodeTerms] at hu

end

/-! ## The walk's nodes -/

section

variable {C : LeafCtx}

mutual

/-- Every node the crate's walk visits is well-typed in every environment, with some bindings, and
inherits what the crate is stricter about. -/
theorem nodes_typed : (ψ : Formula) → (Γ : Bindings) → AllTyped C Γ ψ →
    noReservedHeadReadsF ψ = true →
    ∀ n ∈ nodesF ψ, ∃ Γ', AllTyped C Γ' n ∧ noReservedHeadReadsF n = true
  | .and φ ψ, Γ, h, hr, n, hn => by
    simp only [nodesF] at hn
    rcases List.mem_cons.mp hn with rfl | hn
    · exact ⟨Γ, h, hr⟩
    simp only [noReservedHeadReadsF, Bool.and_eq_true] at hr
    rcases List.mem_append.mp hn with hn | hn
    · exact nodes_typed φ Γ h.and.1 hr.1 n hn
    · exact nodes_typed ψ Γ h.and.2 hr.2 n hn
  | .since φ w ψ, Γ, h, hr, n, hn => by
    simp only [nodesF] at hn
    rcases List.mem_cons.mp hn with rfl | hn
    · exact ⟨Γ, h, hr⟩
    simp only [noReservedHeadReadsF, Bool.and_eq_true] at hr
    rcases List.mem_append.mp hn with hn | hn
    · exact nodes_typed φ Γ h.since.1 hr.1 n hn
    · exact nodes_typed ψ Γ h.since.2 hr.2 n hn
  | .not φ, Γ, h, hr, n, hn => by
    simp only [nodesF] at hn
    rcases List.mem_cons.mp hn with rfl | hn
    · exact ⟨Γ, h, hr⟩
    simp only [noReservedHeadReadsF] at hr
    exact nodes_typed φ Γ h.not hr n hn
  | .formerly w φ, Γ, h, hr, n, hn => by
    simp only [nodesF] at hn
    rcases List.mem_cons.mp hn with rfl | hn
    · exact ⟨Γ, h, hr⟩
    simp only [noReservedHeadReadsF] at hr
    exact nodes_typed φ Γ h.formerly hr n hn
  | .previous w φ, Γ, h, hr, n, hn => by
    simp only [nodesF] at hn
    rcases List.mem_cons.mp hn with rfl | hn
    · exact ⟨Γ, h, hr⟩
    simp only [noReservedHeadReadsF] at hr
    exact nodes_typed φ Γ h.previous hr n hn
  | .exist x φ, Γ, h, hr, n, hn => by
    simp only [nodesF] at hn
    rcases List.mem_cons.mp hn with rfl | hn
    · exact ⟨Γ, h, hr⟩
    simp only [noReservedHeadReadsF] at hr
    exact nodes_typed φ _ h.exist hr n hn
  | .pred a k args, Γ, h, hr, n, hn => by
    simp only [nodesF, List.mem_singleton] at hn
    subst hn
    exact ⟨Γ, h, hr⟩
  | .cmp op l r, Γ, h, hr, n, hn => by
    simp only [nodesF] at hn
    rcases List.mem_cons.mp hn with rfl | hn
    · exact ⟨Γ, h, hr⟩
    simp only [noReservedHeadReadsF, Bool.and_eq_true] at hr
    rcases List.mem_append.mp hn with hn | hn
    · exact nodesT_typed l Γ h.cmp.1 hr.1 n hn
    · exact nodesT_typed r Γ h.cmp.2 hr.2 n hn
  | .tp x, Γ, h, hr, n, hn => by
    simp only [nodesF, List.mem_singleton] at hn
    subst hn
    exact ⟨Γ, h, hr⟩

theorem nodesT_typed : (t : Term) → (Γ : Bindings) → AllTypedT C Γ t →
    noReservedHeadReadsT t = true →
    ∀ n ∈ nodesT t, ∃ Γ', AllTyped C Γ' n ∧ noReservedHeadReadsF n = true
  | .agg (.count dom body), Γ, h, hr, n, hn => by
    simp only [nodesT, nodesA] at hn
    simp only [noReservedHeadReadsT] at hr
    exact nodes_typed body _ h.count hr n hn
  | .agg (.sum s dom body), Γ, h, hr, n, hn => by
    simp only [nodesT, nodesA] at hn
    simp only [noReservedHeadReadsT] at hr
    exact nodes_typed body _ h.sum hr n hn
  | .arith op l r, Γ, h, hr, n, hn => by
    simp only [nodesT, List.mem_append] at hn
    simp only [noReservedHeadReadsT, Bool.and_eq_true] at hr
    rcases hn with hn | hn
    · exact nodesT_typed l Γ h.arith.1 hr.1 n hn
    · exact nodesT_typed r Γ h.arith.2 hr.2 n hn
  | .entity _, _, _, _, n, hn | .long _, _, _, _, n, hn | .decimal _, _, _, _, n, hn
  | .string _, _, _, _, n, hn | .bool _, _, _, _, n, hn | .context _, _, _, _, n, hn
  | .scope _ _, _, _, _, n, hn | .var _, _, _, _, n, hn | .wildcard, _, _, _, n, hn => by
    simp [nodesT] at hn

end

end

/-! ## Event names -/

section

variable {C : LeafCtx} {C' : TypingCtx} {e : ReqEnv}

theorem argTyped_field {Γ : Bindings} {sig : Dogwood.Spec.EventSignature} {p : Path} {t : Term}
    (h : Formula.ArgTyped C' Γ sig (p, t)) : (sig.field? p).isSome := by
  cases h with
  | wildcard hfd => rw [hfd]; rfl
  | var hfd _ _ => rw [hfd]; rfl
  | term hfd _ _ _ _ _ => rw [hfd]; rfl

mutual

theorem eventNames_none (hv : ViewExact C' C e) :
    ∀ (ψ : Formula) (Γ : Bindings), ψ.WellTyped C' Γ → eventNamesF C.events ψ = none
  | .and φ ψ, Γ, h => by
    cases h with
    | and h1 h2 => simp [eventNamesF, eventNames_none hv φ Γ h1, eventNames_none hv ψ Γ h2]
  | .since φ w ψ, Γ, h => by
    cases h with
    | since _ h1 h2 => simp [eventNamesF, eventNames_none hv φ Γ h1, eventNames_none hv ψ Γ h2]
  | .not φ, Γ, h => by
    cases h with
    | not h1 => simpa [eventNamesF] using eventNames_none hv φ Γ h1
  | .formerly w φ, Γ, h => by
    cases h with
    | formerly _ h1 => simpa [eventNamesF] using eventNames_none hv φ Γ h1
  | .previous w φ, Γ, h => by
    cases h with
    | previous _ h1 => simpa [eventNamesF] using eventNames_none hv φ Γ h1
  | .exist x φ, Γ, h => by
    cases h with
    | exist _ h1 => simpa [eventNamesF] using eventNames_none hv φ _ h1
  | .pred a k args, Γ, h => by
    cases h with
    | @pred _ _ _ _ sig hsig hargs _ =>
      obtain ⟨ev, hev⟩ := Option.isSome_iff_exists.mp (hv.sigOnly a k (by rw [hsig]; rfl))
      simp only [eventNamesF, predEventProblem, hev, List.findSome?_eq_none_iff]
      rintro ⟨p, t⟩ hpt
      rw [hv.leafIff a k ev hev sig hsig p (argTyped_field (hargs _ hpt))]
  | .cmp op l r, Γ, h => by
    cases h with
    | eq _ hl hr _ =>
      simp [eventNamesF, eventNamesT_none hv l Γ _ hl, eventNamesT_none hv r Γ _ hr]
    | ord _ hl hr =>
      simp [eventNamesF, eventNamesT_none hv l Γ _ hl, eventNamesT_none hv r Γ _ hr]
  | .tp _, _, _ => rfl

theorem eventNamesT_none (hv : ViewExact C' C e) :
    ∀ (t : Term) (Γ : Bindings) (τ : TType), Term.Typed C' Γ t τ → eventNamesT C.events t = none
  | .agg (.count dom body), Γ, τ, h => by
    cases h with
    | agg ha =>
      cases ha with
      | count _ hb => simpa [eventNamesT, eventNamesA] using eventNames_none hv body _ hb
  | .agg (.sum s dom body), Γ, τ, h => by
    cases h with
    | agg ha =>
      cases ha with
      | sum _ _ hb => simpa [eventNamesT, eventNamesA] using eventNames_none hv body _ hb
  | .arith op l r, Γ, τ, h => by
    cases h with
    | arith hl hr =>
      simp [eventNamesT, eventNamesT_none hv l Γ _ hl, eventNamesT_none hv r Γ _ hr]
  | .entity _, _, _, _ | .long _, _, _, _ | .decimal _, _, _, _ | .string _, _, _, _
  | .bool _, _, _, _ | .context _, _, _, _ | .scope _ _, _, _, _ | .var _, _, _, _
  | .wildcard, _, _, _ => rfl

end

end

/-! ## The checks at a node -/

section

variable {C : LeafCtx} {Γ : Bindings}

theorem windowProblem_none {C' : TypingCtx} {w : Window} (hm : C'.maxWindow = C.cap)
    (h : w.withinCap C'.maxWindow = true) : windowProblem C w = none := by
  rw [hm] at h
  simp only [Window.withinCap, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  simp only [windowProblem]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]

theorem windowsAt_nil (henv : C.envs ≠ []) {n : Formula} (h : AllTyped C Γ n) :
    windowsAt C n = [] := by
  obtain ⟨e, C', he, hv, hw⟩ := h.one henv
  cases hw with
  | formerly hw' _ => simp [windowsAt, windowProblem_none hv.maxWindow hw']
  | previous hw' _ => simp [windowsAt, windowProblem_none hv.maxWindow hw']
  | since hw' _ _ => simp [windowsAt, windowProblem_none hv.maxWindow hw']
  | _ => rfl

theorem not_wildcard {C' : TypingCtx} {t : Term} {τ : TType} (h : Term.Typed C' Γ t τ) :
    t ≠ .wildcard := by
  rintro rfl; cases h

theorem wildcardAt_nil (henv : C.envs ≠ []) {n : Formula} (h : AllTyped C Γ n) :
    wildcardAt n = [] := by
  obtain ⟨e, C', he, hv, hw⟩ := h.one henv
  have key : ∀ {op : CmpOp} {l r : Term}, l ≠ .wildcard → r ≠ .wildcard →
      wildcardAt (.cmp op l r) = [] := by
    intro op l r hl hr
    unfold wildcardAt
    split <;> simp_all
  cases hw with
  | eq _ hl hr _ => exact key (not_wildcard hl) (not_wildcard hr)
  | ord _ hl hr => exact key (not_wildcard hl) (not_wildcard hr)
  | _ => rfl

theorem acts_action {S : Schema} (hap : actionsApart S = true) {uid : EntityUID}
    (h : S.acts.contains uid = true) : uid.ty.id = "Action" := by
  simp only [actionsApart, Bool.and_eq_true, List.all_eq_true] at hap
  simp only [Cedar.Validation.ActionSchema.contains, Option.isSome_iff_exists] at h
  obtain ⟨v, hv⟩ := h
  simpa using hap.1 _ (Cedar.Data.Map.find?_mem_toList hv)

theorem ets_not_action {S : Schema} (hap : actionsApart S = true) {ety : EntityType}
    {v : Cedar.Validation.EntitySchemaEntry} (h : S.ets.find? ety = some v) :
    ety.id ≠ "Action" := by
  simp only [actionsApart, Bool.and_eq_true, List.all_eq_true] at hap
  simpa using hap.2 _ (Cedar.Data.Map.find?_mem_toList h)

theorem entityProblem_none {S : Schema} {declared : EntityType → Option (List String)}
    (hap : actionsApart S = true) {uid : EntityUID}
    (h : (S.ets.isValidEntityUID uid || S.acts.contains uid) = true) :
    entityProblem S declared uid = none := by
  simp only [entityProblem]
  by_cases ha : uid.ty.id = "Action"
  · have hc : S.acts.contains uid = true := by
      cases hc : S.acts.contains uid
      · rw [hc, Bool.or_false] at h
        simp only [Cedar.Validation.EntitySchema.isValidEntityUID] at h
        split at h
        · rename_i v hv; exact absurd ha (ets_not_action hap hv)
        · cases h
      · rfl
    simp [ha, hc]
  · have hc : S.acts.contains uid = false := by
      cases hc : S.acts.contains uid
      · rfl
      · exact absurd (acts_action hap hc) ha
    rw [hc, Bool.or_false] at h
    simp only [Cedar.Validation.EntitySchema.isValidEntityUID] at h
    have ha' : (uid.ty.id == "Action") = false := by simpa using ha
    rw [ha']
    simp only [Bool.false_eq_true, if_false]
    split at h
    · rename_i entry hf
      rw [hf]
      cases entry with
      | standard _ => rfl
      | enum eids =>
        simp only [Cedar.Validation.EntitySchemaEntry.isValidEntityEID] at h
        simp [h]
    · cases h

theorem entityAt_nil (henv : C.envs ≠ []) (hap : actionsApart C.schema = true) {u : Term}
    (h : u = .wildcard ∨ AllTypedT C Γ u) : entityAt C.schema C.declaredEnum u = [] := by
  cases u with
  | entity uid =>
    rcases h with h | h
    · cases h
    obtain ⟨e, C', τ, he, hv, ht⟩ := h.one henv
    cases ht with
    | entity hval =>
      rw [hv.ets, hv.acts uid] at hval
      simp [entityAt, entityProblem_none hap hval]
  | _ => rfl

theorem decimalAt_nil (henv : C.envs ≠ []) {u : Term} (h : u = .wildcard ∨ AllTypedT C Γ u) :
    decimalAt u = [] := by
  cases u with
  | decimal s =>
    rcases h with h | h
    · cases h
    obtain ⟨e, C', τ, he, hv, ht⟩ := h.one henv
    cases ht with
    | decimal hp => simp [decimalAt, hp]
  | _ => rfl

theorem summandAt_nil (henv : C.envs ≠ []) (decl : List Binder) {u : Term}
    (h : u = .wildcard ∨ AllTypedT C Γ u) : summandAt decl u = [] := by
  cases u with
  | agg a =>
    cases a with
    | sum s dom body =>
      rcases h with h | h
      · cases h
      obtain ⟨e, C', τ, he, hv, ht⟩ := h.one henv
      cases ht with
      | agg ha =>
        cases ha with
        | sum hd hs _ =>
          obtain ⟨hnd, -, rfl⟩ := domain_of_sorts hv.ets hd
          unfold binderBindings at hs
          obtain ⟨b, hb, hbe⟩ := List.mem_map.mp hs
          simp only [Prod.mk.injEq] at hbe
          obtain ⟨hbn, hbt⟩ := hbe
          simp only [summandAt, find?_of_mem_nodup hnd hb hbn, Option.map_some, Option.some_or]
          simp [summand_of_int hbt]
    | count _ _ => rfl
  | _ => rfl

theorem scopePathProblem_none {S : Schema} {entry : ActionSchemaEntry} {ro : Root}
    {narrow : ScopeConstraint} {a : String} {rest : List String}
    (hall : ∀ ety ∈ admittedTypes S entry ro narrow, ∀ attrs, entityAttrs? S ety = some attrs →
      ∃ ty, resolveOne attrs a rest = .ok ty) :
    scopePathProblem S entry ro narrow (a :: rest) = none := by
  have key : resolveScopePath S entry ro narrow (a :: rest) = .resolved ∨
      resolveScopePath S entry ro narrow (a :: rest) = .unknown ∨
      ∃ ts, resolveScopePath S entry ro narrow (a :: rest) = .ambiguous ts := by
    by_cases he : (admittedTypes S entry ro narrow).isEmpty = true
    · simp [resolveScopePath, he]
    · by_cases hn :
          (admittedTypes S entry ro narrow).any (fun ety => (entityAttrs? S ety).isNone) = true
      · simp [resolveScopePath, he, hn]
      · simp only [resolveScopePath, he, hn, Bool.false_eq_true, if_false]
        generalize hfail : (List.filterMap _ _).mergeSort _ = failed
        have hnil : failed = [] := by
          rw [← hfail, List.filterMap_eq_nil_iff.mpr]
          · simp
          · intro x hx
            obtain ⟨ety, hety, rfl⟩ := List.mem_map.mp hx
            have hsome : entityAttrs? S ety ≠ none := by
              rw [Bool.not_eq_true, List.any_eq_false] at hn
              simpa using hn ety hety
            cases hattrs : entityAttrs? S ety with
            | none => exact absurd hattrs hsome
            | some attrs =>
              obtain ⟨ty, hty⟩ := hall ety hety attrs hattrs
              simp [hty]
        subst hnil
        simp only
        split
        · exact .inr (.inr ⟨_, rfl⟩)
        · exact .inl rfl
  rcases key with h | h | ⟨ts, h⟩
  · simp [scopePathProblem, h]
  · simp [scopePathProblem, h]
  · simp [scopePathProblem, h]

theorem pathsAt_nil {u : Term} (h : u = .wildcard ∨ AllTypedT C Γ u)
    (hr : noReservedHeadReadsT u = true)
    {uid : EntityUID} {entry : ActionSchemaEntry} (hact : (uid, entry) ∈ C.actions) :
    pathsAt C uid entry u = [] := by
  cases u with
  | context p =>
    rcases h with h | h
    · cases h
    cases p with
    | nil => rfl
    | cons hd rest =>
      obtain ⟨e, he, rfl, rfl⟩ := env_of_action' hact
      obtain ⟨C', τ, hv, ht⟩ := h e he
      cases ht with
      | context hty =>
        simp only [noReservedHeadReadsT, Bool.not_eq_true'] at hr
        have := resolveContextPath_of_type (hv.context hd hr) hr hty
        simp [pathsAt, contextPathProblem, this]
  | scope r p =>
    rcases h with h | h
    · cases h
    cases p with
    | nil => rfl
    | cons a rest =>
      simp only [pathsAt, Option.toList_eq_nil_iff]
      refine scopePathProblem_none (fun ety hety attrs hattrs => ?_)
      obtain ⟨e, he, rfl, rfl, hsc⟩ := env_of_action hact r hety
      obtain ⟨C', τ, hv, ht⟩ := h e he
      cases ht with
      | scopeAttr _ hty =>
        rw [← hsc] at hattrs
        exact ⟨_, resolveOne_of_pathType (scopeAttr_attrs hv.toEnvView hattrs hty)⟩
  | _ => rfl

theorem optionalAt_nil {u : Term} (h : u = .wildcard ∨ AllTypedT C Γ u)
    (hr : noReservedHeadReadsT u = true) : optionalAt C u = [] := by
  cases u with
  | context p =>
    rcases h with h | h
    · cases h
    simp only [optionalAt, List.filterMap_eq_nil_iff, Option.map_eq_none_iff]
    rintro ⟨uid, entry⟩ hact
    obtain ⟨e, he, rfl, rfl⟩ := env_of_action' hact
    obtain ⟨C', τ, hv, ht⟩ := h e he
    cases ht with
    | context hty =>
      cases p with
      | nil => rfl
      | cons hd rest =>
        simp only [noReservedHeadReadsT, Bool.not_eq_true'] at hr
        unfold TypingCtx.contextType? at hty
        rw [pathType?_congr (hv.context hd hr)] at hty
        exact unguarded_none (fun q hq => by
          simp only [decide_eq_true_eq] at hq ⊢; exact hv.factsExact _ hq) _ _ _ _ hty
  | scope r p =>
    rcases h with h | h
    · cases h
    simp only [optionalAt]
    split
    · rfl
    · rename_i hcond
      simp only [List.flatMap_eq_nil_iff, List.filterMap_eq_nil_iff]
      rintro ⟨uid, entry⟩ hact ety hety
      split
      · rename_i attrs hattrs
        simp only [Option.map_eq_none_iff]
        obtain ⟨e, he, rfl, rfl, hsc⟩ := env_of_action hact r hety
        obtain ⟨C', τ, hv, ht⟩ := h e he
        cases ht with
        | scopeRoot => simp at hcond
        | scopeAttr _ hty =>
          rw [← hsc] at hattrs
          exact unguarded_none (fun q hq => by
            simp only [decide_eq_true_eq] at hq ⊢; exact hv.factsExact _ hq) _ _ _ _
            (scopeAttr_attrs hv.toEnvView hattrs hty)
      · rfl
  | _ => rfl

end

/-! ## Types, in each environment -/

section

variable {C : LeafCtx} {C' : TypingCtx} {e : ReqEnv}

/-- A term the specification types has that sort in the crate's type environment, with the
specification's bindings first. -/
theorem termSort_of_typed (hv : ViewExact C' C e) (he : e ∈ C.envs) {Γ Δ : Bindings} {t : Term}
    {τ : TType} (h : Term.Typed C' Γ t τ) (hr : noReservedHeadReadsT t = true) :
    termSort C.schema e (Γ ++ Δ) t = some τ := by
  cases h with
  | entity _ => rfl
  | long => rfl
  | decimal _ => rfl
  | string => rfl
  | bool => rfl
  | @context _ p ty hty =>
    cases p with
    | nil => simp [TypingCtx.contextType?, pathType?] at hty
    | cons hd rest =>
      simp only [noReservedHeadReadsT, Bool.not_eq_true'] at hr
      have := resolveContextPath_of_type (hv.context hd hr) hr hty
      simp [termSort, contextPathType?, this]
  | scopeRoot => simp [termSort, view_scopeType hv.toEnvView]
  | @scopeAttr _ r p ty hne hty =>
    obtain ⟨attrs, hattrs⟩ := env_attrs he hv.toEnvView r
    cases p with
    | nil => exact absurd rfl hne
    | cons a rest =>
      have := scopeAttr_attrs hv.toEnvView hattrs hty
      simp [termSort, scopeAttrTypeOf?, hattrs, resolveOne_of_pathType this, Except.toOption]
  | var hx =>
    simp only [termSort]
    rw [lookup_append_of_isSome (by rw [hx]; rfl), hx]
  | agg _ => rfl
  | arith _ _ => rfl

theorem arithAtoms_nil (hv : ViewExact C' C e) (he : e ∈ C.envs) {Γ Δ : Bindings} :
    ∀ (t : Term), Term.Typed C' Γ t (.cedar .int) → noReservedHeadReadsT t = true →
      arithAtoms C.schema e (Γ ++ Δ) t = []
  | .arith op l r, h, hr => by
    cases h with
    | arith hl hr' =>
      simp only [noReservedHeadReadsT, Bool.and_eq_true] at hr
      simp [arithAtoms, arithAtoms_nil hv he l hl hr.1, arithAtoms_nil hv he r hr' hr.2]
  | .wildcard, h, _ => by cases h
  | .entity _, h, hr | .long _, h, hr | .decimal _, h, hr | .string _, h, hr | .bool _, h, hr
  | .context _, h, hr | .scope _ _, h, hr | .var _, h, hr | .agg _, h, hr => by
    simp only [arithAtoms]
    rw [termSort_of_typed hv he h hr]

theorem operandArith_nil (hv : ViewExact C' C e) (he : e ∈ C.envs) {Γ Δ : Bindings} {t : Term}
    {τ : TType} (h : Term.Typed C' Γ t τ) (hr : noReservedHeadReadsT t = true) :
    operandArith C.schema e (Γ ++ Δ) t = [] := by
  cases t with
  | arith op l r =>
    have hint : τ = .cedar .int := by cases h; rfl
    subst hint
    exact arithAtoms_nil hv he _ h hr
  | _ => rfl

theorem comparisonProblem_none (hv : ViewExact C' C e) (he : e ∈ C.envs) {Γ Δ : Bindings}
    {op : CmpOp} {l r : Term} (h : (Formula.cmp op l r).WellTyped C' Γ)
    (hrl : noReservedHeadReadsT l = true) (hrr : noReservedHeadReadsT r = true) :
    comparisonProblem C.schema e (Γ ++ Δ) op l r = none := by
  cases h with
  | eq hno hl hr hc =>
    simp only [comparisonProblem, termSort_of_typed hv he hl hrl, termSort_of_typed hv he hr hrr]
    have hno' : op.isOrder = false := by
      cases hop : op.isOrder
      · rfl
      · exact absurd ((isOrder_iff op).mp hop) hno
    simp only [hno', Bool.false_eq_true, if_false]
    rcases hc with rfl | ⟨hn, e₁, e₂, rfl, rfl⟩
    · simp
    · simp [hn]
  | ord ho hl hr =>
    simp only [comparisonProblem, termSort_of_typed hv he hl hrl, termSort_of_typed hv he hr hrr]
    rw [if_pos ((isOrder_iff op).mpr ho)]
    simp

theorem within_ne_timepoint {f : Dogwood.Spec.FieldTy} {τ : TType} (h : f.Within τ) :
    τ ≠ .timepoint := by
  rintro rfl
  cases f with
  | cedar _ => simp [Dogwood.Spec.FieldTy.Within] at h
  | entities etys =>
    simp only [Dogwood.Spec.FieldTy.Within] at h
    obtain ⟨hne, hall⟩ := h
    obtain ⟨ety, hety⟩ := List.exists_mem_of_ne_nil _ hne
    cases hall ety hety

/-- A typed term is not a request-side path of a type temporal conditions do not support: the
specification's typing requires the type supported. -/
theorem unsupported_none_of_typed (hv : ViewExact C' C e) (he : e ∈ C.envs) {Γ : Bindings}
    {t : Term} {τ : TType} (h : Term.Typed C' Γ t τ) (hr : noReservedHeadReadsT t = true) :
    unsupportedOperand C.schema e t = none := by
  have hts := termSort_of_typed hv he (Δ := []) h hr
  cases h with
  | context _ hs =>
    simp only [termSort, Option.map_eq_some_iff] at hts
    obtain ⟨ty', h', heq⟩ := hts
    cases heq
    simp [unsupportedOperand, h', hs]
  | @scopeAttr _ r p ty hne _ hs =>
    cases p with
    | nil => exact absurd rfl hne
    | cons a p =>
      simp only [termSort, Option.map_eq_some_iff] at hts
      obtain ⟨ty', h', heq⟩ := hts
      cases heq
      simp [unsupportedOperand, h', hs]
  | _ => rfl

theorem predArgs_nil (hv : ViewExact C' C e) (he : e ∈ C.envs) {Γ Δ : Bindings} {a : EntityUID}
    {k : String} {args : List (Path × Term)} {sig : Dogwood.Spec.EventSignature}
    (hsig : C'.events.signature? a k = some sig)
    (hargs : ∀ arg ∈ args, Formula.ArgTyped C' Γ sig arg)
    (hr : noReservedHeadReadsArgs args = true) :
    predArgsProblems C.schema C.events e (Γ ++ Δ) a k args = [] := by
  obtain ⟨ev, hev⟩ := Option.isSome_iff_exists.mp (hv.sigOnly a k (by rw [hsig]; rfl))
  obtain ⟨sig', hsig', hag⟩ := hv.events a k ev hev
  obtain rfl : sig = sig' := Option.some.inj (hsig.symm.trans hsig')
  simp only [predArgsProblems, List.flatMap_eq_nil_iff, hev]
  rintro ⟨p, t⟩ hpt
  have hrt := noRes_of_arg hr hpt
  cases hargs _ hpt with
  | wildcard _ =>
    simp only [argUnsupported]
    cases hsp : isSpliced p
    · simp
    · cases splicedFieldType? C.schema a p <;> simp [termSort]
  | @var _ _ _ fd x τ hfd hx hw =>
    simp only [argUnsupported]
    cases hsp : isSpliced p
    · simp
    · obtain ⟨t', hst, hty⟩ := hag.spliced p fd hsp hfd
      rw [hty] at hw
      simp only [Dogwood.Spec.FieldTy.Within] at hw
      subst hw
      simp [hst, termSort, lookup_append_of_isSome (by rw [hx]; rfl : (Γ.lookup x).isSome), hx]
  | @term _ _ _ fd _ τ hfd _ hnv hnw ht hacc =>
    have hts := termSort_of_typed hv he (Δ := Δ) ht hrt
    have hu : argUnsupported C.schema e t = none := by
      cases t <;> first
        | exact absurd rfl (hnv _) | exact absurd rfl hnw
        | exact unsupported_none_of_typed hv he ht hrt
    simp only [hu]
    cases hsp : isSpliced p
    · have hft : fieldType? C.schema ev p = some (some fd.ty) := by rw [hag.fields, hfd]; rfl
      simp only [Bool.false_eq_true, if_false]
      simp [hft, hts, fieldAccepts, (acceptsB_iff _ _).mpr hacc]
    · obtain ⟨t', hst, hty⟩ := hag.spliced p fd hsp hfd
      rw [hty] at hacc
      simp only [Dogwood.Spec.FieldTy.Accepts] at hacc
      subst hacc
      simp [hst, hts]

mutual

/-- **The type check finds nothing in a well-typed condition**, in each environment, with the
specification's bindings followed by the action's input fields. -/
theorem typesF_nil (hv : ViewExact C' C e) (he : e ∈ C.envs) :
    ∀ (ψ : Formula) (Γ : Bindings), ψ.WellTyped C' Γ → noReservedHeadReadsF ψ = true →
      typesF C.schema C.events e (Γ ++ inputBindings e.entry) ψ = []
  | .and φ ψ, Γ, h, hr => by
    cases h with
    | and h1 h2 =>
      simp only [noReservedHeadReadsF, Bool.and_eq_true] at hr
      simp [typesF, typesF_nil hv he φ Γ h1 hr.1, typesF_nil hv he ψ Γ h2 hr.2]
  | .since φ w ψ, Γ, h, hr => by
    cases h with
    | since _ h1 h2 =>
      simp only [noReservedHeadReadsF, Bool.and_eq_true] at hr
      simp [typesF, typesF_nil hv he φ Γ h1 hr.1, typesF_nil hv he ψ Γ h2 hr.2]
  | .not φ, Γ, h, hr => by
    cases h with
    | not h1 => simpa [typesF] using typesF_nil hv he φ Γ h1 hr
  | .formerly w φ, Γ, h, hr => by
    cases h with
    | formerly _ h1 => simpa [typesF] using typesF_nil hv he φ Γ h1 hr
  | .previous w φ, Γ, h, hr => by
    cases h with
    | previous _ h1 => simpa [typesF] using typesF_nil hv he φ Γ h1 hr
  | .exist x φ, Γ, h, hr => by
    cases h with
    | exist hb h1 =>
      obtain ⟨hd, rfl⟩ := binder_of_sort hv.ets hb
      have hbt : bindersTyped C.schema [x] = true := by simp [bindersTyped, hd]
      simp only [typesF, if_pos hbt]
      exact typesF_nil hv he φ _ h1 hr
  | .pred a k args, Γ, h, hr => by
    cases h with
    | pred hsig hargs _ => simp [typesF, predArgs_nil hv he hsig hargs hr]
  | .tp x, Γ, h, _ => by
    cases h with
    | tp hx => simp [typesF, lookup_append_of_isSome (by rw [hx]; rfl : (Γ.lookup x).isSome), hx]
  | .cmp op l r, Γ, h, hr => by
    simp only [noReservedHeadReadsF, Bool.and_eq_true] at hr
    have hcp := comparisonProblem_none hv he (Δ := inputBindings e.entry) h hr.1 hr.2
    cases h with
    | eq _ hl hr' _ =>
      simp [typesF, operandArith_nil hv he hl hr.1, operandArith_nil hv he hr' hr.2, hcp,
        comparisonProblems, unsupported_none_of_typed hv he hl hr.1,
        unsupported_none_of_typed hv he hr' hr.2,
        typesT_nil hv he l Γ _ hl hr.1, typesT_nil hv he r Γ _ hr' hr.2]
    | ord _ hl hr' =>
      simp [typesF, operandArith_nil hv he hl hr.1, operandArith_nil hv he hr' hr.2, hcp,
        comparisonProblems, unsupported_none_of_typed hv he hl hr.1,
        unsupported_none_of_typed hv he hr' hr.2,
        typesT_nil hv he l Γ _ hl hr.1, typesT_nil hv he r Γ _ hr' hr.2]

theorem typesT_nil (hv : ViewExact C' C e) (he : e ∈ C.envs) :
    ∀ (t : Term) (Γ : Bindings) (τ : TType), Term.Typed C' Γ t τ →
      noReservedHeadReadsT t = true → typesT C.schema C.events e (Γ ++ inputBindings e.entry) t = []
  | .agg (.count dom body), Γ, τ, h, hr => by
    cases h with
    | agg ha =>
      cases ha with
      | count hd hb =>
        obtain ⟨hnd, hdecl, rfl⟩ := domain_of_sorts hv.ets hd
        simp only [typesT, typesA, if_pos (bindersTyped_of hnd hdecl)]
        simp only [noReservedHeadReadsT] at hr
        have := typesF_nil hv he body _ hb hr
        rwa [List.append_assoc] at this
  | .agg (.sum s dom body), Γ, τ, h, hr => by
    cases h with
    | agg ha =>
      cases ha with
      | sum hd _ hb =>
        obtain ⟨hnd, hdecl, rfl⟩ := domain_of_sorts hv.ets hd
        simp only [typesT, typesA, if_pos (bindersTyped_of hnd hdecl)]
        simp only [noReservedHeadReadsT] at hr
        have := typesF_nil hv he body _ hb hr
        rwa [List.append_assoc] at this
  | .arith op l r, Γ, τ, h, hr => by
    cases h with
    | arith hl hr' =>
      simp only [noReservedHeadReadsT, Bool.and_eq_true] at hr
      simp [typesT, typesT_nil hv he l Γ _ hl hr.1, typesT_nil hv he r Γ _ hr' hr.2]
  | .entity _, _, _, _, _ | .long _, _, _, _, _ | .decimal _, _, _, _, _ | .string _, _, _, _, _
  | .bool _, _, _, _, _ | .context _, _, _, _, _ | .scope _ _, _, _, _, _ | .var _, _, _, _, _
  | .wildcard, _, _, _, _ => rfl

end

end

/-! ## The validity rules -/

theorem envView_noFacts {C' : TypingCtx} {S : Schema} {e : ReqEnv} (hv : EnvView C' S e) :
    EnvView { C' with facts := [] } S e :=
  ⟨hv.principal, hv.resource, hv.action, hv.context, hv.ets, hv.acts, hv.declared⟩

theorem sort_scopeType {C' : TypingCtx} (r : ScopeRoot) :
    ({ C' with facts := [] } : TypingCtx).scopeType r = C'.scopeType r := by
  cases r <;> rfl

theorem except_mapM_mem' {α β ε : Type} {f : α → Except ε β} :
    ∀ {xs : List α} {ys : List β}, xs.mapM f = .ok ys → ∀ x ∈ xs, ∃ y ∈ ys, f x = .ok y
  | [], _, _, x, hx => by cases hx
  | x :: xs, ys, h, z, hz => by
    simp only [List.mapM_cons, bind, Except.bind, pure, Except.pure] at h
    cases hx : f x with
    | error _ => rw [hx] at h; cases h
    | ok y' =>
      rw [hx] at h
      cases hxs : xs.mapM f with
      | error _ => rw [hxs] at h; cases h
      | ok ys' =>
        rw [hxs] at h
        cases h
        rcases List.mem_cons.mp hz with rfl | hz
        · exact ⟨y', List.mem_cons_self .., hx⟩
        · obtain ⟨y, hy, hf⟩ := except_mapM_mem' hxs z hz
          exact ⟨y, List.mem_cons_of_mem _ hy, hf⟩

theorem mapM_some_of {α β : Type} {f : α → Option β} {P : β → Prop} :
    ∀ {xs : List α}, (∀ x ∈ xs, ∃ y, f x = some y ∧ P y) →
      ∃ ys, xs.mapM f = some ys ∧ ∀ y ∈ ys, P y
  | [], _ => ⟨[], rfl, fun _ h => by cases h⟩
  | x :: xs, h => by
    obtain ⟨y, hy, hp⟩ := h x (List.mem_cons_self ..)
    obtain ⟨ys, hys, hps⟩ := mapM_some_of (fun z hz => h z (List.mem_cons_of_mem _ hz))
    refine ⟨y :: ys, ?_, fun z hz => ?_⟩
    · simp only [List.mapM_cons, hy, hys]; rfl
    · rcases List.mem_cons.mp hz with rfl | hz
      · exact hp
      · exact hps z hz

theorem toSpec_field {pin : Dogwood.Frontend.Pin} {spin : Dogwood.Spec.Pin}
    (h : pin.toSpec = .ok spin) : spin.field = pin.fieldPath := by
  obtain ⟨field, ctxp, root⟩ := pin
  cases root with
  | context =>
    simp only [Dogwood.Frontend.Pin.toSpec, pure, Except.pure, Except.ok.injEq] at h
    subst h; rfl
  | scope =>
    cases ctxp with
    | nil => simp [Dogwood.Frontend.Pin.toSpec] at h
    | cons r0 tail =>
      by_cases hp1 : r0 = "principal"
      · subst hp1
        simp only [Dogwood.Frontend.Pin.toSpec, pure, Except.pure, Except.ok.injEq] at h
        subst h; rfl
      · by_cases hp2 : r0 = "resource"
        · subst hp2
          simp only [Dogwood.Frontend.Pin.toSpec, pure, Except.pure, Except.ok.injEq] at h
          subst h; rfl
        · simp [Dogwood.Frontend.Pin.toSpec, hp1, hp2] at h

section

variable {C : LeafCtx} {Γ : Bindings}

theorem pin_head (hpu : pinHeadsUnreserved C.events = true) {a : EntityUID} {k : String}
    {ev : DerivedEvent} (hev : eventOf? C.events a k = some ev) {field : List String}
    {head : String} {tl : List String}
    (hpin : (⟨field, head :: tl, .context⟩ : Dogwood.Frontend.Pin) ∈ ev.pins) :
    isHoistedName head = false := by
  simp only [pinHeadsUnreserved, List.all_eq_true] at hpu
  simpa using hpu ev (List.mem_of_find?_eq_some hev) _ hpin

/-- What a pin of a predicate the specification types is, in an environment. -/
theorem pin_env {a : EntityUID} {k : String} {args : List (Path × Term)}
    (h : AllTyped C Γ (.pred a k args)) {ev : DerivedEvent} (hev : eventOf? C.events a k = some ev)
    {pin : Dogwood.Frontend.Pin} (hpin : pin ∈ ev.pins) {fty : Option Dogwood.Spec.FieldTy}
    (hfty : fieldType? C.schema ev pin.fieldPath = some fty) {e : ReqEnv} (he : e ∈ C.envs) :
    ∃ C' spin τ, ViewExact C' C e ∧ pin.toSpec = .ok spin ∧
      spin.ref.sort? { C' with facts := [] } = some τ ∧ fieldAccepts fty τ = true := by
  obtain ⟨C', hv, hw⟩ := h e he
  cases hw with
  | @pred _ _ _ _ sig hsig _ hpins =>
    obtain ⟨sig', hsig', hag⟩ := hv.events a k ev hev
    obtain rfl : sig = sig' := Option.some.inj (hsig.symm.trans hsig')
    obtain ⟨spin, hspin, hto⟩ := except_mapM_mem' hag.pins pin hpin
    obtain ⟨fd, τ, hfd, hτ, hacc⟩ := hpins spin hspin
    rw [toSpec_field hto] at hfd
    have hf : fty = some fd.ty := by
      rw [hag.fields, hfd] at hfty
      simpa using hfty.symm
    subst hf
    exact ⟨C', spin, τ, hv, hto, hτ, by simpa [fieldAccepts] using (acceptsB_iff _ _).mpr hacc⟩

/-- A scope pin's request-side path is declared and required in every environment of an action,
of a type the field can hold. -/
theorem pin_scope_sorts {uid : EntityUID} {entry : ActionSchemaEntry}
    (hact : (uid, entry) ∈ C.actions) (r : ScopeRoot) (tail : Path)
    {fty : Option Dogwood.Spec.FieldTy}
    (hall : ∀ e ∈ C.envs, e.uid = uid → e.entry = entry → ∃ C' τ, ViewExact C' C e ∧
      (Dogwood.Spec.PinRef.scope r tail).sort? { C' with facts := [] } = some τ ∧
        fieldAccepts fty τ = true) :
    ∃ sorts, (if tail.isEmpty then
        some ((admittedTypes C.schema entry (Root.ofSpec r) (C.narrow (Root.ofSpec r))).map
          fun ety => TType.cedar (.entity ety))
      else (admittedTypes C.schema entry (Root.ofSpec r) (C.narrow (Root.ofSpec r))).mapM
        fun ety => (entityAttrs? C.schema ety).bind fun attrs =>
          (requiredPathType? attrs tail).map TType.cedar) = some sorts ∧
      ∀ τ ∈ sorts, fieldAccepts fty τ = true ∧ τ.temporalSupported = true := by
  by_cases hte : tail.isEmpty = true
  · have ht : tail = [] := List.isEmpty_iff.mp hte
    subst ht
    refine ⟨_, rfl, fun τ hτ => ?_⟩
    obtain ⟨ety, hety, rfl⟩ := List.mem_map.mp hτ
    obtain ⟨e, he, h1, h2, hsc⟩ := env_of_action hact r hety
    obtain ⟨C', τ', hv, hs, hacc⟩ := hall e he h1 h2
    simp only [Dogwood.Spec.PinRef.sort?, sort_scopeType, view_scopeType hv.toEnvView, hsc,
      Option.some.injEq] at hs
    subst hs
    exact ⟨hacc, by simp [TType.temporalSupported, Cedar.Validation.CedarType.temporalSupported]⟩
  · rw [if_neg hte]
    have htne : tail ≠ [] := fun h => hte (by simp [h])
    apply mapM_some_of
    intro ety hety
    obtain ⟨e, he, h1, h2, hsc⟩ := env_of_action hact r hety
    obtain ⟨C', τ', hv, hs, hacc⟩ := hall e he h1 h2
    obtain ⟨attrs, hattrs⟩ := env_attrs he hv.toEnvView r
    cases tail with
    | nil => exact absurd rfl htne
    | cons a rest =>
      simp only [Dogwood.Spec.PinRef.sort?,
        Option.map_eq_some_iff, Option.filter_eq_some_iff] at hs
      obtain ⟨ty, ⟨hty, hsup⟩, rfl⟩ := hs
      have hp := scopeAttr_attrs (envView_noFacts hv.toEnvView) hattrs hty
      have hreq := required_of_pathType (by simp) _ _ _ _ hp
      rw [hsc] at hattrs
      exact ⟨.cedar ty, by simp [hattrs, hreq], hacc, by simpa [TType.temporalSupported] using hsup⟩

theorem pinsAt_nil (hpu : pinHeadsUnreserved C.events = true) {a : EntityUID} {k : String}
    {args : List (Path × Term)} (h : AllTyped C Γ (.pred a k args)) : pinsAt C a k = [] := by
  simp only [pinsAt]
  split
  · rfl
  rename_i ev hev
  simp only [List.flatMap_eq_nil_iff]
  intro pin hpin
  split
  · rfl
  rename_i fty hfty
  simp only [List.filterMap_eq_nil_iff]
  rintro ⟨uid, entry⟩ hact
  suffices hs : ∃ sorts, pinRefSorts? C entry pin = some sorts ∧
      ∀ τ ∈ sorts, fieldAccepts fty τ = true ∧ τ.temporalSupported = true by
    obtain ⟨sorts, hsorts, hacc⟩ := hs
    have hf : sorts.find? (!TType.temporalSupported ·) = none := by
      rw [List.find?_eq_none]; intro τ hτ; simp [(hacc τ hτ).2]
    simp only [hsorts, hf, Option.map_eq_none_iff, List.find?_eq_none]
    intro τ hτ
    simp [(hacc τ hτ).1]
  obtain ⟨field, ctxp, root⟩ := pin
  cases root with
  | context =>
    obtain ⟨e, he, h1, rfl⟩ := env_of_action' hact
    obtain ⟨C', spin, τ, hv, hto, hs, hacc⟩ := pin_env h hev hpin hfty he
    simp only [Dogwood.Frontend.Pin.toSpec, pure, Except.pure, Except.ok.injEq] at hto
    subst hto
    simp only [Dogwood.Spec.PinRef.sort?, Option.map_eq_some_iff, Option.filter_eq_some_iff] at hs
    obtain ⟨ty, ⟨hty, hsup⟩, rfl⟩ := hs
    cases ctxp with
    | nil => simp [TypingCtx.contextType?, pathType?] at hty
    | cons head tl =>
      have hh : isHoistedName head = false := pin_head hpu hev hpin
      unfold TypingCtx.contextType? at hty
      rw [pathType?_congr (hv.context head hh)] at hty
      have hreq := required_of_pathType (by simp) _ _ _ _ hty
      exact ⟨[.cedar ty], by simp [pinRefSorts?, hh, hreq],
        by simpa [TType.temporalSupported, hsup] using hacc⟩
  | scope =>
    have hscope : ∀ (r : ScopeRoot) (tail : Path),
        Dogwood.Frontend.Pin.toSpec ⟨field, ctxp, .scope⟩ = .ok ⟨field, .scope r tail⟩ →
        ∀ e ∈ C.envs, e.uid = uid → e.entry = entry → ∃ C' τ, ViewExact C' C e ∧
          (Dogwood.Spec.PinRef.scope r tail).sort? { C' with facts := [] } = some τ ∧
            fieldAccepts fty τ = true := by
      intro r tail hto' e he _ _
      obtain ⟨C', spin, τ, hv, hto, hs, hacc⟩ := pin_env h hev hpin hfty he
      rw [hto'] at hto
      cases hto
      exact ⟨C', τ, hv, hs, hacc⟩
    cases ctxp with
    | nil =>
      obtain ⟨e, he, -, -⟩ := env_of_action' hact
      obtain ⟨C', spin, τ, hv, hto, -⟩ := pin_env h hev hpin hfty he
      simp [Dogwood.Frontend.Pin.toSpec] at hto
    | cons r0 tail =>
      by_cases hp1 : r0 = "principal"
      · subst hp1
        obtain ⟨sorts, hsorts, hacc⟩ := pin_scope_sorts hact .principal tail
          (hscope .principal tail rfl)
        exact ⟨sorts, by simp only [pinRefSorts?]; exact hsorts, hacc⟩
      · by_cases hp2 : r0 = "resource"
        · subst hp2
          obtain ⟨sorts, hsorts, hacc⟩ := pin_scope_sorts hact .resource tail
            (hscope .resource tail rfl)
          exact ⟨sorts, by simp only [pinRefSorts?]; exact hsorts, hacc⟩
        · obtain ⟨e, he, -, -⟩ := env_of_action' hact
          obtain ⟨C', spin, τ, hv, hto, -⟩ := pin_env h hev hpin hfty he
          simp [Dogwood.Frontend.Pin.toSpec, hp1, hp2] at hto

theorem bindingFields_nil (henv : C.envs ≠ []) {sc : List Binder} {a : EntityUID} {k : String}
    {args : List (Path × Term)} (h : AllTyped C Γ (.pred a k args))
    (hd : ∀ b ∈ sc, binderTypeDeclared C.schema b.ty = true)
    (hs : ∀ x, (sc.find? (·.name == x)).map (annotationSort ·.ty) = Γ.lookup x) :
    bindingFieldsAt C sc a k args = [] := by
  obtain ⟨e, C', he, hv, hw⟩ := h.one henv
  cases hw with
  | @pred _ _ _ _ sig hsig hargs _ =>
    simp only [bindingFieldsAt]
    split
    · rfl
    rename_i ev hev
    obtain ⟨sig', hsig', hag⟩ := hv.events a k ev hev
    obtain rfl : sig = sig' := Option.some.inj (hsig.symm.trans hsig')
    simp only [List.filterMap_eq_nil_iff]
    rintro ⟨p, t⟩ hpt
    cases t with
    | var x =>
      simp only
      split
      · rfl
      cases hargs _ hpt with
      | @var _ _ _ fd _ τ hfd hx hwi =>
        have hft : fieldType? C.schema ev p = some (some fd.ty) := by rw [hag.fields, hfd]; rfl
        rw [hft]
        cases hb : sc.find? (·.name == x) with
        | none => rfl
        | some b =>
          have hsx := hs x
          rw [hb, hx] at hsx
          simp only [Option.map_some, Option.some.injEq] at hsx
          subst hsx
          have hnt : b.ty ≠ .timepoint := by
            intro hbt
            rw [hbt] at hwi
            exact within_ne_timepoint hwi rfl
          simp [binderValueSort_of_declared (hd b (List.mem_of_find?_eq_some hb)) hnt, fieldWithin,
            (withinB_iff _ _).mpr hwi]
      | term _ _ hnv _ _ _ => exact absurd rfl (hnv x)
    | _ => rfl

theorem not_mem_take_of_nodup {l : List String} (hnd : l.Nodup) {n : String} {i : Nat}
    (h : (n, i) ∈ l.zipIdx) : (l.take i).contains n = false := by
  have h' := List.mem_zipIdx_iff_getElem?.mp h
  simp only at h'
  obtain ⟨hi, rfl⟩ := List.getElem?_eq_some_iff.mp h'
  cases hc : (l.take i).contains l[i]
  · rfl
  · exfalso
    have hmem : l[i] ∈ l.take i := by simpa using hc
    obtain ⟨j, hj, heq⟩ := List.mem_take_iff_getElem.mp hmem
    rw [List.nodup_iff_pairwise_ne, List.pairwise_iff_getElem] at hnd
    exact hnd j i (by omega) hi (by omega) heq

theorem forListAt_nil (henv : C.envs ≠ []) : ∀ {t : Term}, AllTypedT C Γ t → forListAt t = []
  | .agg (.count dom body), h => by
    obtain ⟨hnd, -⟩ := h.countDom henv
    simp only [forListAt, eraseDups_eq_nil_iff, List.filterMap_eq_nil_iff]
    rintro ⟨n, i⟩ hni
    simp only [not_mem_take_of_nodup hnd hni, Bool.false_eq_true, if_false]
  | .agg (.sum s dom body), h => by
    obtain ⟨hnd, -⟩ := h.sumDom henv
    simp only [forListAt, eraseDups_eq_nil_iff, List.filterMap_eq_nil_iff]
    rintro ⟨n, i⟩ hni
    simp only [not_mem_take_of_nodup hnd hni, Bool.false_eq_true, if_false]
  | .arith op l r, h => by
    simp [forListAt, forListAt_nil henv h.arith.1, forListAt_nil henv h.arith.2]
  | .entity _, _ | .long _, _ | .decimal _, _ | .string _, _ | .bool _, _ | .context _, _
  | .scope _ _, _ | .var _, _ | .wildcard, _ => rfl

theorem binderTypesAt_nil (henv : C.envs ≠ []) :
    ∀ {t : Term}, AllTypedT C Γ t → binderTypesAt C.schema t = []
  | .agg (.count dom body), h => by
    obtain ⟨-, hdecl⟩ := h.countDom henv
    simp only [binderTypesAt, eraseDups_eq_nil_iff, List.filterMap_eq_nil_iff,
      binderTypeProblem]
    intro b hb
    simp [hdecl b hb]
  | .agg (.sum s dom body), h => by
    obtain ⟨-, hdecl⟩ := h.sumDom henv
    simp only [binderTypesAt, eraseDups_eq_nil_iff, List.filterMap_eq_nil_iff,
      binderTypeProblem]
    intro b hb
    simp [hdecl b hb]
  | .arith op l r, h => by
    simp [binderTypesAt, binderTypesAt_nil henv h.arith.1, binderTypesAt_nil henv h.arith.2]
  | .entity _, _ | .long _, _ | .decimal _, _ | .string _, _ | .bool _, _ | .context _, _
  | .scope _ _, _ | .var _, _ | .wildcard, _ => rfl

theorem argTyped_simple {C' : TypingCtx} {sig : Dogwood.Spec.EventSignature} {p : Path} {t : Term}
    (h : Formula.ArgTyped C' Γ sig (p, t)) : t.Simple := by
  cases h with
  | wildcard _ => trivial
  | var _ _ _ => trivial
  | term _ hs _ _ _ _ => exact hs

theorem validityT_simple {sc : List Binder} {t : Term} (h : t.Simple) : validityT C sc t = [] := by
  cases t <;> first | rfl | exact h.elim

theorem validityArgs_nil {sc : List Binder} :
    ∀ {args : List (Path × Term)}, (∀ p t, (p, t) ∈ args → t.Simple) → validityArgs C sc args = []
  | [], _ => rfl
  | (p, t) :: args, h => by
    simp only [validityArgs, validityT_simple (h p t (List.mem_cons_self ..)),
      validityArgs_nil (fun p' t' hm => h p' t' (List.mem_cons_of_mem _ hm)), List.append_nil]

end

theorem scope_cons {sc : List Binder} {Γ : Bindings} {x : Binder}
    (hs : ∀ y, (sc.find? (·.name == y)).map (annotationSort ·.ty) = Γ.lookup y) :
    ∀ y, ((x :: sc).find? (·.name == y)).map (annotationSort ·.ty) =
      Bindings.lookup ((x.name, annotationSort x.ty) :: Γ) y := by
  intro y
  rw [lookup_cons, List.find?_cons]
  by_cases hxy : x.name = y
  · simp [hxy]
  · have : (x.name == y) = false := by simpa using hxy
    rw [this, if_neg hxy]
    exact hs y

theorem scope_dom {sc : List Binder} {Γ : Bindings} {dom : List Binder}
    (hnd : (dom.map (·.name)).Nodup)
    (hs : ∀ y, (sc.find? (·.name == y)).map (annotationSort ·.ty) = Γ.lookup y) :
    ∀ y, ((dom.reverse ++ sc).find? (·.name == y)).map (annotationSort ·.ty) =
      (binderBindings dom ++ Γ).lookup y := by
  intro y
  rw [lookup_binderBindings, List.find?_append, Option.map_or, find?_reverse_of_nodup y dom hnd,
    hs y]

section

variable {C : LeafCtx}

mutual

/-- **The validity rules find nothing in a condition well-typed in every environment**, with the
validity rules' binders `sc` matching the specification's bindings `Γ`. -/
theorem validity_nil (henv : C.envs ≠ []) (hpu : pinHeadsUnreserved C.events = true) :
    ∀ (ψ : Formula) (Γ : Bindings) (sc : List Binder), AllTyped C Γ ψ →
      noReservedHeadReadsF ψ = true → (∀ b ∈ sc, binderTypeDeclared C.schema b.ty = true) →
      (∀ x, (sc.find? (·.name == x)).map (annotationSort ·.ty) = Γ.lookup x) →
      validityF C sc ψ = []
  | .and φ ψ, Γ, sc, h, hr, hd, hs => by
    simp only [noReservedHeadReadsF, Bool.and_eq_true] at hr
    simp [validityF, validityAt, validity_nil henv hpu φ Γ sc h.and.1 hr.1 hd hs,
      validity_nil henv hpu ψ Γ sc h.and.2 hr.2 hd hs]
  | .since φ w ψ, Γ, sc, h, hr, hd, hs => by
    simp only [noReservedHeadReadsF, Bool.and_eq_true] at hr
    simp [validityF, validityAt, validity_nil henv hpu φ Γ sc h.since.1 hr.1 hd hs,
      validity_nil henv hpu ψ Γ sc h.since.2 hr.2 hd hs]
  | .not φ, Γ, sc, h, hr, hd, hs => by
    simp only [noReservedHeadReadsF] at hr
    simp [validityF, validityAt, validity_nil henv hpu φ Γ sc h.not hr hd hs]
  | .formerly w φ, Γ, sc, h, hr, hd, hs => by
    simp only [noReservedHeadReadsF] at hr
    simp [validityF, validityAt, validity_nil henv hpu φ Γ sc h.formerly hr hd hs]
  | .previous w φ, Γ, sc, h, hr, hd, hs => by
    simp only [noReservedHeadReadsF] at hr
    simp [validityF, validityAt, validity_nil henv hpu φ Γ sc h.previous hr hd hs]
  | .exist x φ, Γ, sc, h, hr, hd, hs => by
    simp only [noReservedHeadReadsF] at hr
    obtain ⟨e, C', he, hv, hw⟩ := h.one henv
    have hdx : binderTypeDeclared C.schema x.ty = true := by
      cases hw with
      | exist hb _ => exact (binder_of_sort hv.ets hb).1
    have hbt : bindersTyped C.schema [x] = true := by simp [bindersTyped, hdx]
    simp only [validityF, validityAt, binderTypeProblem, hdx, if_true, Option.toList_none,
      List.nil_append, if_pos hbt]
    exact validity_nil henv hpu φ _ (x :: sc) h.exist hr
      (fun b hb => by
        rcases List.mem_cons.mp hb with rfl | hb
        · exact hdx
        · exact hd b hb) (scope_cons hs)
  | .pred a k args, Γ, sc, h, hr, hd, hs => by
    have hnr := hr
    simp only [validityF, validityAt, eraseDups_eq_nil_iff, List.append_eq_nil_iff,
      List.flatMap_eq_nil_iff]
    obtain ⟨e, C', he, hv, hw⟩ := h.one henv
    refine ⟨⟨⟨fun u hu => optionalAt_nil (nodeTerms_typed h u hu) (nodeTerms_noRes hnr u hu),
      pinsAt_nil hpu h⟩, bindingFields_nil henv h hd hs⟩, ?_⟩
    cases hw with
    | pred _ hargs _ => exact validityArgs_nil (fun p t hpt => argTyped_simple (hargs _ hpt))
  | .cmp op l r, Γ, sc, h, hr, hd, hs => by
    have hnr := hr
    simp only [noReservedHeadReadsF, Bool.and_eq_true] at hr
    simp only [validityF, validityAt, eraseDups_eq_nil_iff, List.append_eq_nil_iff,
      List.flatMap_eq_nil_iff]
    exact ⟨⟨⟨⟨⟨⟨fun u hu => optionalAt_nil (nodeTerms_typed h u hu) (nodeTerms_noRes hnr u hu),
      forListAt_nil henv h.cmp.1⟩, forListAt_nil henv h.cmp.2⟩, binderTypesAt_nil henv h.cmp.1⟩,
      binderTypesAt_nil henv h.cmp.2⟩, validityT_nil henv hpu l Γ sc h.cmp.1 hr.1 hd hs⟩,
      validityT_nil henv hpu r Γ sc h.cmp.2 hr.2 hd hs⟩
  | .tp _, _, _, _, _, _, _ => rfl

theorem validityT_nil (henv : C.envs ≠ []) (hpu : pinHeadsUnreserved C.events = true) :
    ∀ (t : Term) (Γ : Bindings) (sc : List Binder), AllTypedT C Γ t →
      noReservedHeadReadsT t = true → (∀ b ∈ sc, binderTypeDeclared C.schema b.ty = true) →
      (∀ x, (sc.find? (·.name == x)).map (annotationSort ·.ty) = Γ.lookup x) →
      validityT C sc t = []
  | .agg (.count dom body), Γ, sc, h, hr, hd, hs => by
    obtain ⟨hnd, hdecl⟩ := h.countDom henv
    simp only [noReservedHeadReadsT] at hr
    simp only [validityT, validityA, if_pos (bindersTyped_of hnd hdecl)]
    exact validity_nil henv hpu body _ _ h.count hr
      (fun b hb => by
        rcases List.mem_append.mp hb with hb | hb
        · exact hdecl b (List.mem_reverse.mp hb)
        · exact hd b hb) (scope_dom hnd hs)
  | .agg (.sum s dom body), Γ, sc, h, hr, hd, hs => by
    obtain ⟨hnd, hdecl⟩ := h.sumDom henv
    simp only [noReservedHeadReadsT] at hr
    simp only [validityT, validityA, if_pos (bindersTyped_of hnd hdecl)]
    exact validity_nil henv hpu body _ _ h.sum hr
      (fun b hb => by
        rcases List.mem_append.mp hb with hb | hb
        · exact hdecl b (List.mem_reverse.mp hb)
        · exact hd b hb) (scope_dom hnd hs)
  | .arith op l r, Γ, sc, h, hr, hd, hs => by
    simp only [noReservedHeadReadsT, Bool.and_eq_true] at hr
    simp [validityT, validityT_nil henv hpu l Γ sc h.arith.1 hr.1 hd hs,
      validityT_nil henv hpu r Γ sc h.arith.2 hr.2 hd hs]
  | .entity _, _, _, _, _, _, _ | .long _, _, _, _, _, _, _ | .decimal _, _, _, _, _, _, _
  | .string _, _, _, _, _, _, _ | .bool _, _, _, _, _, _, _ | .context _, _, _, _, _, _, _
  | .scope _ _, _, _, _, _, _, _ | .var _, _, _, _, _, _, _ | .wildcard, _, _, _, _, _, _ => rfl

end

end

end TypingComplete

/-! ## The theorem -/

open TypingComplete in
/-- **The validator's temporal checks are complete for typing.** On a temporal leaf of a rule with
a request environment, well-typed in every request environment in a typing context of the
specification that sees the environment exactly as the crate's validator does, and that monitors
time, the crate's validator reports nothing, except where it is stricter than the specification:
a read or a pin of a `context.<path>` whose head lowering
reserves, or an entity literal of a schema whose actions and entity types are not kept apart by
name. -/
theorem leaf_complete {C : LeafCtx} {φ : Formula} (hmon : φ.MonitorsTime) (henv : C.envs ≠ [])
    (hspec : ∀ e ∈ C.envs, ∃ C', ViewExact C' C e ∧ φ.WellTyped C' [])
    (hres : noReservedHeadReadsF φ = true)
    (hapart : actionsApart C.schema = true) (hpins : pinHeadsUnreserved C.events = true)
    (hhor : ∀ H, C.horizonCap = some H → φ.horizon .seconds ≤ H) :
    leafFindings C φ = [] := by
  have hall : AllTyped C [] φ := hspec
  have hnodes := nodes_typed φ [] hall hres
  simp only [leafFindings, List.append_eq_nil_iff, Option.toList_eq_nil_iff,
    List.flatMap_eq_nil_iff, mergeEnvFindings_eq_nil_iff, walkTerms]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · obtain ⟨e, C', he, hv, hw⟩ := hall.one henv
    exact eventNames_none hv φ [] hw
  · rw [walkF_nil]
    intro n hn
    obtain ⟨Γ', hn', -⟩ := hnodes n hn
    exact windowsAt_nil henv hn'
  · simp only [horizonProblem]
    cases hc : C.horizonCap with
    | none => rfl
    | some H =>
      simp only
      rw [if_neg (by have := hhor H hc; omega)]
  · rw [walkF_nil]
    intro n hn
    obtain ⟨Γ', hn', -⟩ := hnodes n hn
    exact wildcardAt_nil henv hn'
  · rw [walkF_nil]
    intro n hn
    obtain ⟨Γ', hn', -⟩ := hnodes n hn
    rw [List.flatMap_eq_nil_iff]
    exact fun u hu => entityAt_nil henv hapart (nodeTerms_typed hn' u hu)
  · rw [walkF_nil]
    intro n hn
    obtain ⟨Γ', hn', -⟩ := hnodes n hn
    rw [List.flatMap_eq_nil_iff]
    exact fun u hu => decimalAt_nil henv (nodeTerms_typed hn' u hu)
  · rintro ⟨uid, entry⟩ hact
    rw [walkF_nil]
    intro n hn
    obtain ⟨Γ', hn', hr'⟩ := hnodes n hn
    rw [List.flatMap_eq_nil_iff]
    exact fun u hu => pathsAt_nil (nodeTerms_typed hn' u hu) (nodeTerms_noRes hr' u hu) hact
  · exact (checkTpDependence_eq_nil_iff φ).mpr hmon
  · intro e he
    obtain ⟨C', hv, hw⟩ := hspec e he
    exact typesF_nil hv he φ [] hw hres
  · rw [walkF_nil]
    intro n hn
    obtain ⟨Γ', hn', -⟩ := hnodes n hn
    rw [List.flatMap_eq_nil_iff]
    exact fun u hu => summandAt_nil henv _ (nodeTerms_typed hn' u hu)
  · exact validity_nil henv hpins φ [] [] hall hres (fun _ hb => by cases hb)
      (fun _ => by simp [Bindings.lookup])

end Dogwood.Thm.Frontend
