import Dogwood.Frontend.Derive
import Dogwood.Frontend.Signatures
import Cedar.Thm.Data.List.Lemmas

/-!
# The events derivation produces

`Derive.derive` produces, for each namespace of the action schema, each action of it, and each
declaration of the DSL, one event (`derive_event_mem`): of that action, of the declaration's kind,
with the declaration's decision flag. The consequences:

* **every derived event names a declared action** (`derive_event_declared`);
* **a declaration yields an event on every action** (`derive_event_complete`);
* the **decision flag is the declaration's** (`derive_decision`), so it is a flag of the kind,
  the same on every action, when the DSL gives each kind one flag
  (`derive_decision_uniform`). Without that hypothesis it is not
  (`derive_decision_not_uniform`); the crate's parser guarantees it, since it rejects a kind
  declared twice (`check_kinds_distinct`).
-/

namespace Dogwood.Thm.Frontend.Derivation

open Dogwood.Frontend Dogwood.Frontend.Derive Dogwood.Frontend.CedarSchema
open Dogwood.Frontend.EventSchemaDsl

/-! ## The list monad in `Except` -/

theorem mapM_ok_mem {α β ε : Type} {f : α → Except ε β} {xs : List α} {ys : List β}
    (h : xs.mapM f = .ok ys) {y : β} (hy : y ∈ ys) : ∃ x ∈ xs, f x = .ok y := by
  induction xs generalizing ys with
  | nil => simp [pure, Except.pure] at h; subst h; simp at hy
  | cons x xs ih =>
    simp only [List.mapM_cons, bind, Except.bind, pure, Except.pure] at h
    cases hx : f x with
    | error _ => simp [hx] at h
    | ok y' =>
      cases hxs : xs.mapM f with
      | error _ => simp [hx, hxs] at h
      | ok ys' =>
        simp [hx, hxs] at h
        subst h
        rcases List.mem_cons.mp hy with rfl | hy
        · exact ⟨x, by simp, hx⟩
        · obtain ⟨x', hx', hf⟩ := ih hxs hy
          exact ⟨x', by simp [hx'], hf⟩

theorem mapM_ok_complete {α β ε : Type} {f : α → Except ε β} {xs : List α} {ys : List β}
    (h : xs.mapM f = .ok ys) {x : α} (hx : x ∈ xs) : ∃ y ∈ ys, f x = .ok y := by
  induction xs generalizing ys with
  | nil => simp at hx
  | cons x₀ xs ih =>
    simp only [List.mapM_cons, bind, Except.bind, pure, Except.pure] at h
    cases hx₀ : f x₀ with
    | error _ => simp [hx₀] at h
    | ok y' =>
      cases hxs : xs.mapM f with
      | error _ => simp [hx₀, hxs] at h
      | ok ys' =>
        simp [hx₀, hxs] at h
        subst h
        rcases List.mem_cons.mp hx with rfl | hx
        · exact ⟨y', by simp, hx₀⟩
        · obtain ⟨y, hy, hf⟩ := ih hxs hx
          exact ⟨y, by simp [hy], hf⟩

theorem flatMapM_ok_mem {α β ε : Type} {f : α → Except ε (List β)} {xs : List α} {ys : List β}
    (h : xs.flatMapM f = .ok ys) {y : β} (hy : y ∈ ys) :
    ∃ x ∈ xs, ∃ zs, f x = .ok zs ∧ y ∈ zs := by
  induction xs generalizing ys with
  | nil => simp [pure, Except.pure] at h; subst h; simp at hy
  | cons x xs ih =>
    simp only [List.flatMapM_cons, bind, Except.bind, pure, Except.pure] at h
    cases hx : f x with
    | error _ => simp [hx] at h
    | ok zs =>
      cases hxs : xs.flatMapM f with
      | error _ => simp [hx, hxs] at h
      | ok ys' =>
        simp [hx, hxs] at h
        subst h
        rcases List.mem_append.mp hy with hy | hy
        · exact ⟨x, by simp, zs, hx, hy⟩
        · obtain ⟨x', hx', zs', hf, hz⟩ := ih hxs hy
          exact ⟨x', by simp [hx'], zs', hf, hz⟩

theorem flatMapM_ok_complete {α β ε : Type} {f : α → Except ε (List β)} {xs : List α}
    {ys : List β} (h : xs.flatMapM f = .ok ys) {x : α} (hx : x ∈ xs) :
    ∃ zs, f x = .ok zs ∧ ∀ z ∈ zs, z ∈ ys := by
  induction xs generalizing ys with
  | nil => simp at hx
  | cons x₀ xs ih =>
    simp only [List.flatMapM_cons, bind, Except.bind, pure, Except.pure] at h
    cases hx₀ : f x₀ with
    | error _ => simp [hx₀] at h
    | ok zs =>
      cases hxs : xs.flatMapM f with
      | error _ => simp [hx₀, hxs] at h
      | ok ys' =>
        simp [hx₀, hxs] at h
        subst h
        rcases List.mem_cons.mp hx with rfl | hx
        · exact ⟨zs, hx₀, fun z hz => List.mem_append_left _ hz⟩
        · obtain ⟨zs', hf, hz⟩ := ih hxs hx
          exact ⟨zs', hf, fun z h' => List.mem_append_right _ (hz z h')⟩

/-! ## The events -/

/-- What deriving one declaration's fields on an action reads. -/
def ctxOf (f : Fragment) (ns : Option String) (id : String) (a : ActionDef) (decl : EventDecl) :
    Ctx :=
  { fragment := f, actionId := id, kind := decl.kind, action := a, home := ns }

/-- One event is the declaration's, on the action: its namespace, action, kind and decision
flag, and the fields and pins of its field specs. -/
theorem deriveOne_ok {f : Fragment} {p : List String} {ns : Option String} {id : String}
    {a : ActionDef} {decl : EventDecl} {e : DerivedEvent}
    (h : deriveOne f p ns id a decl = .ok e) :
    e.namespace = p ++ ["Action"] ∧ e.action = id ∧ e.kind = decl.kind ∧
      e.decision = decl.decision ∧
      ∃ acc, deriveSpecs (ctxOf f ns id a decl) [] decl.fields ⟨[], [], []⟩ = .ok acc ∧
        e.fields = acc.fields ∧ e.pins = acc.pins := by
  unfold deriveOne at h
  cases hs : deriveSpecs (ctxOf f ns id a decl) [] decl.fields ⟨[], [], []⟩ with
  | error _ => simp [ctxOf] at hs; simp [hs, bind, Except.bind] at h
  | ok acc =>
    simp [ctxOf] at hs
    simp [hs, bind, Except.bind, pure, Except.pure] at h
    subst h
    exact ⟨rfl, rfl, rfl, rfl, acc, rfl, rfl, rfl⟩

/-- `derive`'s result, from its events. -/
theorem derive_ok {dsl : EventSchemaDsl.EventSchema} {f : Fragment} {d : DerivedEventSchema}
    (h : derive dsl f = .ok d) :
    deriveEvents f dsl.decls = .ok d.events ∧ limits dsl = .ok (d.maxWindow, d.maxHorizon) := by
  unfold derive at h
  cases he : deriveEvents f dsl.decls with
  | error _ => simp [he] at h
  | ok es =>
    simp only [he] at h
    cases hl : limits dsl with
    | error _ => simp [hl, throw, throwThe, MonadExceptOf.throw] at h
    | ok wh =>
      obtain ⟨w, hz⟩ := wh
      simp only [hl, pure, Except.pure, Except.ok.injEq] at h
      subst h
      exact ⟨rfl, rfl⟩

/-- **The derived events.** Each is the event of a declaration of the DSL on an action of the
fragment. -/
theorem derive_event_mem {dsl : EventSchemaDsl.EventSchema} {f : Fragment}
    {d : DerivedEventSchema} (h : derive dsl f = .ok d) {e : DerivedEvent} (he : e ∈ d.events) :
    ∃ ns nd, (ns, nd) ∈ f ∧ ∃ id a, (id, a) ∈ nd.actions ∧ ∃ decl ∈ dsl.decls,
      deriveOne f (nsPath ns) ns id a decl = .ok e := by
  have hev := (derive_ok h).1
  unfold deriveEvents at hev
  obtain ⟨⟨ns, nd⟩, hmem, zs, hzs, hez⟩ := flatMapM_ok_mem hev he
  obtain ⟨⟨id, a⟩, hmem', zs', hzs', hez'⟩ := flatMapM_ok_mem hzs hez
  obtain ⟨decl, hdecl, hone⟩ := mapM_ok_mem hzs' hez'
  exact ⟨ns, nd, hmem, id, a, hmem', decl, hdecl, hone⟩

/-- **Every declaration yields an event on every action.** -/
theorem derive_event_complete {dsl : EventSchemaDsl.EventSchema} {f : Fragment}
    {d : DerivedEventSchema} (h : derive dsl f = .ok d) {ns : Option String} {nd : NamespaceDef}
    (hns : (ns, nd) ∈ f) {id : String} {a : ActionDef} (ha : (id, a) ∈ nd.actions)
    {decl : EventDecl} (hdecl : decl ∈ dsl.decls) :
    ∃ e ∈ d.events, deriveOne f (nsPath ns) ns id a decl = .ok e := by
  have hev := (derive_ok h).1
  unfold deriveEvents at hev
  obtain ⟨zs, hzs, hsub⟩ := flatMapM_ok_complete hev hns
  obtain ⟨zs', hzs', hsub'⟩ := flatMapM_ok_complete hzs ha
  obtain ⟨e, he, hone⟩ := mapM_ok_complete hzs' hdecl
  exact ⟨e, hsub _ (hsub' _ he), hone⟩

/-- **Every derived event names a declared action**, and has its declaration's kind and
decision flag. -/
theorem derive_event_declared {dsl : EventSchemaDsl.EventSchema} {f : Fragment}
    {d : DerivedEventSchema} (h : derive dsl f = .ok d) {e : DerivedEvent} (he : e ∈ d.events) :
    ∃ ns nd, (ns, nd) ∈ f ∧ e.namespace = nsPath ns ++ ["Action"] ∧
      (∃ a, (e.action, a) ∈ nd.actions) ∧
      ∃ decl ∈ dsl.decls, e.kind = decl.kind ∧ e.decision = decl.decision := by
  obtain ⟨ns, nd, hns, id, a, ha, decl, hdecl, hone⟩ := derive_event_mem h he
  obtain ⟨hn, hid, hk, hdec, -⟩ := deriveOne_ok hone
  exact ⟨ns, nd, hns, hn, ⟨a, hid ▸ ha⟩, decl, hdecl, hk, hdec⟩

/-- An event's decision flag is that of a declaration of its kind. -/
theorem derive_decision {dsl : EventSchemaDsl.EventSchema} {f : Fragment}
    {d : DerivedEventSchema} (h : derive dsl f = .ok d) {e : DerivedEvent} (he : e ∈ d.events) :
    ∃ decl ∈ dsl.decls, decl.kind = e.kind ∧ decl.decision = e.decision := by
  obtain ⟨_, _, _, _, _, decl, hdecl, hk, hd⟩ := derive_event_declared h he
  exact ⟨decl, hdecl, hk.symm, hd.symm⟩

/-- The DSL gives each kind one decision flag. -/
def FlagPerKind (dsl : EventSchemaDsl.EventSchema) : Prop :=
  ∀ d₁ ∈ dsl.decls, ∀ d₂ ∈ dsl.decls, d₁.kind = d₂.kind → d₁.decision = d₂.decision

/-- **The decision flag is a flag of the kind**, the same on every action, when the DSL gives
each kind one flag. -/
theorem derive_decision_uniform {dsl : EventSchemaDsl.EventSchema} {f : Fragment}
    {d : DerivedEventSchema} (h : derive dsl f = .ok d) (hflag : FlagPerKind dsl)
    {e₁ e₂ : DerivedEvent} (he₁ : e₁ ∈ d.events) (he₂ : e₂ ∈ d.events)
    (hk : e₁.kind = e₂.kind) : e₁.decision = e₂.decision := by
  obtain ⟨d₁, hd₁, hk₁, hdec₁⟩ := derive_decision h he₁
  obtain ⟨d₂, hd₂, hk₂, hdec₂⟩ := derive_decision h he₂
  rw [← hdec₁, ← hdec₂]
  exact hflag d₁ hd₁ d₂ hd₂ (by rw [hk₁, hk₂, hk])

/-- A DSL that declares the kind `k` twice, once as a decision kind. `derive` accepts it; the
crate's parser rejects it (`check_kinds_distinct`). -/
def twoFlagsDsl : EventSchemaDsl.EventSchema where
  maxWindow := none
  decls := [{ span := default, decision := true, binder := "A", kind := "k", fields := [] },
            { span := default, decision := false, binder := "A", kind := "k", fields := [] }]

/-- An action schema with one action, `Action::"a"`, in the root namespace. -/
def oneActionFragment : Fragment :=
  [(none, { commonTypes := [], entityTypes := [],
            actions := [("a", { attributes := none, appliesTo := none, memberOf := none,
                                annotations := [] })],
            annotations := [] })]

/-- **Counterexample**: without `FlagPerKind`, two events of one kind on one action can
disagree on the decision flag (the specification's `isDecisionKind` then treats the kind as a
decision kind). -/
theorem derive_decision_not_uniform :
    ∃ d, derive twoFlagsDsl oneActionFragment = .ok d ∧
      ∃ e₁ ∈ d.events, ∃ e₂ ∈ d.events, e₁.kind = e₂.kind ∧ e₁.decision ≠ e₂.decision := by
  refine ⟨_, rfl, ?_⟩
  exact ⟨_, List.mem_cons_self .., _, List.mem_cons_of_mem _ (List.mem_cons_self ..), rfl,
    by decide⟩

end Dogwood.Thm.Frontend.Derivation
