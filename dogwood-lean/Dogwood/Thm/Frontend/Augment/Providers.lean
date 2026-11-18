import Dogwood.Thm.Frontend.Augment.Basic
import Dogwood.Frontend.Driver
import Dogwood.Frontend.Conformance

/-!
# Provider resolution gives each provider leaf its declared output type

`resolveProviders` attaches to each provider field the declaration of the provider its
invocation names. Its declared output type, the output type of the provider or of the last method
of its chain (`declaredOutput`), is then:

* the type of the hoisted field as cedarify writes it (`ProviderDecls.cedarTypeOf`, which the
  augmentation parses), `cedarTypeOf_eq_declared`;
* the type the specification gives the leaf (`Provider.Call.outputType?`) under the conformance
  bridge's conversion of the declarations (`providerDeclsToSpec`), `resolveProvider_outputType`.
-/

namespace Dogwood.Frontend.Augment

open ProviderDecls
open Cedar.Validation (CedarType)

/-- The declared type of a call's value: the provider's output type, or the output type of the
last method of its chain, when that method is declared. -/
def declaredOutput (d : ProviderDecl) (methods : List String) : Option ParamType :=
  match methods.getLast? with
  | none => some d.outputType
  | some m => (d.methods.lookup m).map (·.outputType)

theorem resolveProviders_eq (decls : Option Declarations) (names : List (String × String))
    (fields : List ProviderField) :
    resolveProviders decls names fields = .ok (fields.map (resolveProvider decls names)) := rfl

/-- The resolved declaration is the declaration of the provider the invocation names. -/
theorem resolveProvider_declaration (decls : Option Declarations) (names : List (String × String))
    (f : ProviderField) :
    (resolveProvider decls names f).declaration = decls.bind (·.get f.invocation.key) := rfl

/-- The enums the resolved field carries are the declared enums its call references, and their
names those the action schema exports them under. -/
theorem resolveProvider_entityTypes (d : Declarations) (names : List (String × String))
    (f : ProviderField) (decl : ProviderDecl) (h : d.get f.invocation.key = some decl) :
    (resolveProvider (some d) names f).entityTypes =
        (decl.referencedEntityTypes (f.methods.map (·.name))).filterMap
          (fun n => (d.entityTypeDecls.lookup n).map (n, ·)) ∧
      (resolveProvider (some d) names f).entityTypeNames =
        ((resolveProvider (some d) names f).entityTypes).filterMap
          (fun (n, _) => (names.lookup n).map (n, ·)) := by
  simp [resolveProvider, h]

/-- **The hoisted field is typed by the declared output type**: the Cedar type text cedarify
gives a declared provider's field is that of its declared output type. -/
theorem cedarTypeOf_eq_declared {decls : Option Declarations} {names : List (String × String)}
    {key : String} {methods : List String} {d : ProviderDecl} {p : ParamType}
    (hd : decls.bind (·.get key) = some d) (ho : declaredOutput d methods = some p) :
    cedarTypeOf decls names key methods = p.toCedarTypeWith names := by
  unfold cedarTypeOf declaredOutput at *
  simp only [hd] at *
  split
  · rename_i last hlast
    rw [hlast] at ho
    simp only [Option.bind_some] at *
    cases hm : d.methods.lookup last with
    | none => simp [hm] at ho
    | some md => simp [hm] at ho; subst ho; rfl
  · rename_i hlast
    rw [hlast] at ho
    simp only [Option.some.injEq] at ho; subst ho; rfl

/-! ## The specification's signature -/

/-- The name the conformance bridge gives a provider key (`providerDeclToSpec`). -/
def keyName (key : String) : Cedar.Spec.Name :=
  ⟨(key.splitOn "::").getLast?.getD "", (key.splitOn "::").dropLast⟩

theorem providerDeclToSpec_function {S : Cedar.Validation.Schema} {key : String} {d : ProviderDecl}
    {sig : Dogwood.Spec.Provider.Signature} (h : providerDeclToSpec S key d = .ok sig) :
    sig.function = keyName key := by
  unfold providerDeclToSpec at h
  obtain ⟨_, _, h⟩ := bind_eq_ok.mp h
  obtain ⟨_, _, h⟩ := bind_eq_ok.mp h
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h; rfl

/-- When every element converts, keeping those that convert keeps them all. -/
theorem filterMap_toOption_of_mapM {α β ε : Type} {f : α → Except ε β} :
    ∀ {l : List α} {ms : List β}, l.mapM f = .ok ms → l.filterMap (fun a => (f a).toOption) = ms
  | [], ms, h => by
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at h; subst h; rfl
  | a :: rest, ms, h => by
    rw [List.mapM_cons] at h
    cases hfa : f a with
    | error e => simp [hfa, bind, Except.bind] at h
    | ok b =>
      cases hr : List.mapM f rest with
      | error e => simp [hfa, hr, bind, Except.bind] at h
      | ok bs =>
        simp only [hfa, hr, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
        subst h
        have ih := filterMap_toOption_of_mapM hr
        rw [List.filterMap_cons, hfa, ih]
        rfl

/-- The converted declarations are the declarations that convert, in order. -/
theorem providerDeclsToSpec_fst (d : Declarations) (S : Cedar.Validation.Schema) :
    (providerDeclsToSpec (some d) S).1 =
      d.available.filterMap fun (n, decl) => (providerDeclToSpec S n decl).toOption := by
  unfold providerDeclsToSpec
  suffices ∀ (l : List (String × ProviderDecl)) (out : Dogwood.Spec.Provider.Declarations)
      (skipped : List String),
      (l.foldl (fun (acc : Dogwood.Spec.Provider.Declarations × List String) (e : String × ProviderDecl) =>
        match providerDeclToSpec S e.1 e.2 with
        | .ok s => (acc.1 ++ [s], acc.2)
        | .error _ => (acc.1, acc.2 ++ [e.1])) (out, skipped)).1 =
        out ++ l.filterMap fun (n, decl) => (providerDeclToSpec S n decl).toOption by
    have h := this d.available [] []
    rw [List.nil_append] at h
    exact h
  intro l
  induction l with
  | nil => simp
  | cons e rest ih =>
    intro out skipped
    obtain ⟨n, decl⟩ := e
    simp only [List.foldl_cons, List.filterMap_cons]
    cases hc : providerDeclToSpec S n decl with
    | error _ => simp only; rw [ih]; simp [Except.toOption]
    | ok s => simp only; rw [ih]; simp [Except.toOption]

/-- With distinct names, the signature found for a declared key is its converted declaration. -/
theorem find?_converted {d : Declarations} {S : Cedar.Validation.Schema} {key : String}
    {decl : ProviderDecl} {sig : Dogwood.Spec.Provider.Signature}
    (hnd : (d.available.map fun e => keyName e.1).Nodup) (hget : d.get key = some decl)
    (hconv : providerDeclToSpec S key decl = .ok sig) :
    Dogwood.Spec.Provider.Declarations.find? (providerDeclsToSpec (some d) S).1 (keyName key) =
      some sig := by
  rw [providerDeclsToSpec_fst]
  unfold Dogwood.Spec.Provider.Declarations.find?
  obtain ⟨l₁, l₂, hsplit, _⟩ := List.lookup_eq_some_iff.mp hget
  rw [hsplit] at hnd ⊢
  simp only [List.map_append, List.map_cons, List.nodup_append, List.nodup_cons, List.mem_map] at hnd
  obtain ⟨_, _, hdisj⟩ := hnd
  rw [List.filterMap_append, List.find?_append]
  have hnone : ∀ s ∈ l₁.filterMap (fun (e : String × ProviderDecl) =>
      (providerDeclToSpec S e.1 e.2).toOption), ¬ (s.function == keyName key) = true := by
    intro s hs
    obtain ⟨⟨n, dn⟩, hmem, hs⟩ := List.mem_filterMap.mp hs
    cases hc : providerDeclToSpec S n dn with
    | error _ => simp [hc, Except.toOption] at hs
    | ok s' =>
      simp only [hc, Except.toOption, Option.some.injEq] at hs; subst hs
      rw [providerDeclToSpec_function hc]
      have := hdisj (keyName n) ⟨(n, dn), hmem, rfl⟩ (keyName key) (List.mem_cons_self ..)
      simpa using this
  have h1 := List.find?_eq_none.mpr hnone
  simp only [Except.toOption] at h1 ⊢
  rw [h1]
  simp [hconv, providerDeclToSpec_function hconv]

/-- A successful conversion of a declaration whose methods all convert, unfolded: its output and
its methods' are the converted declared types. (A method that does not convert is left out of
the signature.) -/
theorem providerDeclToSpec_ok {S : Cedar.Validation.Schema} {key : String} {d : ProviderDecl}
    {sig : Dogwood.Spec.Provider.Signature} (h : providerDeclToSpec S key d = .ok sig)
    {ms : List Dogwood.Spec.Provider.MethodSig}
    (hms : d.methods.mapM (fun (m, md) => methodDeclToSpec S m md) = .ok ms) :
    paramTypeToCedar S d.outputType = .ok sig.output ∧ sig.methods = ms := by
  unfold providerDeclToSpec at h
  obtain ⟨args, _, h⟩ := bind_eq_ok.mp h
  obtain ⟨out, hout, h⟩ := bind_eq_ok.mp h
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  exact ⟨hout, filterMap_toOption_of_mapM hms⟩

/-- The converted methods: the method found by name is the converted declaration of the first
declared method of that name. -/
theorem find?_converted_method {S : Cedar.Validation.Schema} :
    ∀ {methods : List (String × MethodDecl)} {ms : List Dogwood.Spec.Provider.MethodSig},
      methods.mapM (fun (m, md) => methodDeclToSpec S m md) = .ok ms →
      ∀ name, (ms.find? (·.name == name)).map (·.output) =
        ((methods.lookup name).map fun md => (paramTypeToCedar S md.outputType).toOption).join
  | [], ms, h, name => by
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at h; subst h; rfl
  | (m, md) :: rest, ms, h, name => by
    rw [List.mapM_cons] at h
    obtain ⟨msig, hmsig, h⟩ := bind_eq_ok.mp h
    obtain ⟨ms', hms', h⟩ := bind_eq_ok.mp h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    unfold methodDeclToSpec at hmsig
    obtain ⟨_, _, hmsig⟩ := bind_eq_ok.mp hmsig
    obtain ⟨_, _, hmsig⟩ := bind_eq_ok.mp hmsig
    obtain ⟨o, ho, hmsig⟩ := bind_eq_ok.mp hmsig
    simp only [pure, Except.pure, Except.ok.injEq] at hmsig
    subst hmsig
    rw [lookup_cons_eq]
    by_cases hn : name = m
    · subst hn; simp [List.find?, ho, Except.toOption]
    · have : (m == name) = false := by simp [Ne.symm hn]
      simp only [List.find?, this, if_neg hn]
      exact find?_converted_method hms' name

theorem mapM_preserves_name {g : Provider.MethodCall → Except String Dogwood.Spec.Provider.MethodCall} :
    ∀ {ms : List Provider.MethodCall} {mcs : List Dogwood.Spec.Provider.MethodCall},
      ms.mapM g = .ok mcs → (∀ m r, g m = .ok r → r.name = m.name) →
        mcs.map (·.name) = ms.map (·.name)
  | [], mcs, h, _ => by simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at h; subst h; rfl
  | m :: rest, mcs, h, hg => by
    rw [List.mapM_cons] at h
    obtain ⟨r, hr, h⟩ := bind_eq_ok.mp h
    obtain ⟨rs, hrs, h⟩ := bind_eq_ok.mp h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    simp [hg m r hr, mapM_preserves_name hrs hg]

/-- **The specification types a resolved provider leaf by its declared output type.** Let the
provider the field's invocation names be declared (`decls.get key = some d`), its declaration
convert to the specification's signature (as the conformance bridge converts it), the
declarations' names be distinct, and the invocation's segments be those of its key. Then the
specification's declared type of the field's call is the converted declared output type of the
call (`declaredOutput`): the provider's, or that of the last method of its chain. The methods
must convert too (`hmeth`): the conversion leaves out a method whose type names an entity type
the schema lacks. -/
theorem resolveProvider_outputType {decls : Declarations} {names : List (String × String)}
    {f : ProviderField} {S : Cedar.Validation.Schema} {d : ProviderDecl} {p : ParamType}
    {sig : Dogwood.Spec.Provider.Signature} {c : Dogwood.Spec.Provider.Call}
    {ms : List Dogwood.Spec.Provider.MethodSig}
    (hget : decls.get f.invocation.key = some d)
    (hconv : providerDeclToSpec S f.invocation.key d = .ok sig)
    (hmeth : d.methods.mapM (fun (m, md) => methodDeclToSpec S m md) = .ok ms)
    (hnd : (decls.available.map fun e => keyName e.1).Nodup)
    (hsplit : f.invocation.key.splitOn "::" = f.invocation.function)
    (hcall : (f.toLowered (resolveProvider (some decls) names f)).toCall = .ok c)
    (ho : declaredOutput d (f.methods.map (·.name)) = some p) :
    (resolveProvider (some decls) names f).declaration = some d ∧
      Dogwood.Spec.Provider.Call.outputType? (providerDeclsToSpec (some decls) S).1 c =
        (paramTypeToCedar S p).toOption := by
  refine ⟨by simp [resolveProvider, hget], ?_⟩
  -- the call's function and methods
  unfold LoweredProviderField.toCall at hcall
  simp only [ProviderField.toLowered] at hcall
  obtain ⟨id, hid⟩ : ∃ id, f.invocation.function.getLast? = some id := by
    cases h : f.invocation.function.getLast? with
    | none => simp [h, bind, Except.bind] at hcall
    | some id => exact ⟨id, rfl⟩
  simp only [hid] at hcall
  obtain ⟨fn, hfn0, hcall⟩ := bind_eq_ok.mp hcall
  simp only [pure, Except.pure, Except.ok.injEq] at hfn0
  subst hfn0
  obtain ⟨args, _, hcall⟩ := bind_eq_ok.mp hcall
  obtain ⟨mcs, hmcs, hcall⟩ := bind_eq_ok.mp hcall
  simp only [pure, Except.pure, Except.ok.injEq] at hcall
  subst hcall
  have hfn : (⟨id, f.invocation.function.dropLast⟩ : Cedar.Spec.Name) = keyName f.invocation.key := by
    simp [keyName, hsplit, hid]
  have hnames : mcs.map (·.name) = f.methods.map (·.name) :=
    mapM_preserves_name hmcs fun m r hr => by
      obtain ⟨_, _, hr⟩ := bind_eq_ok.mp hr
      simp only [pure, Except.pure, Except.ok.injEq] at hr
      subst hr; rfl
  unfold Dogwood.Spec.Provider.Call.outputType?
  simp only
  rw [hfn, find?_converted hnd hget hconv]
  simp only
  obtain ⟨hout, hsigm⟩ := providerDeclToSpec_ok hconv hmeth
  unfold declaredOutput at ho
  rw [← hnames] at ho
  cases hlast : mcs.getLast? with
  | none =>
    have : (mcs.map (·.name)).getLast? = none := by simp [hlast]
    rw [this] at ho
    simp only [Option.some.injEq] at ho; subst ho
    simp [hout, Except.toOption]
  | some m =>
    have : (mcs.map (·.name)).getLast? = some m.name := by simp [hlast]
    rw [this] at ho
    dsimp only
    rw [hsigm, find?_converted_method hmeth m.name]
    cases hm : d.methods.lookup m.name with
    | none => simp [hm] at ho
    | some md => simp only [hm, Option.map_some, Option.some.injEq] at ho; subst ho; simp

end Dogwood.Frontend.Augment
