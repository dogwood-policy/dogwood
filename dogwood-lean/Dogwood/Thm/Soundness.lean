import Dogwood.Thm.Resolution
import Dogwood.Thm.Monitorable
import Dogwood.Thm.Valuation
import Dogwood.Thm.Values
import Dogwood.Thm.Readings
import Dogwood.Thm.Eval
import Dogwood.Thm.Injection
import Dogwood.Spec.Validity

/-!
# Soundness of the temporal part

Validity makes the semantics of a temporal leaf use only values of the types the leaf declares,
and makes every comparison it evaluates compare two values. At a decision event that is an
instance of the typing environment, that supplies the scope entities whose attributes the leaf
reads (`Event.Supplies`, `Formula.scopeReads`), and whose leaf's facts hold, over a trace whose
events conform, and under a total reading:

* **typed witnesses** (`restricts_sorted`, `sat_exist_sorted`, `rows_sorted`): every value a
  satisfying assignment gives a restricted variable has the variable's declared sort, so an
  `exists` holds only of values of its binder's type, and an aggregate counts only rows of its
  domain's types;
* **two-valued comparisons** (`operand_resolves`): every comparison operand, under a valuation
  that gives each variable in scope a value of its sort, denotes a value;
* **soundness** (`Formula.WellTyped.sound`): every comparison the satisfaction of the leaf reaches
  is two-valued, and every witness and row it uses is typed (`Formula.Sound`).

The corollaries follow: `!=` and `!(==)` coincide wherever both operands denote
(`sat_ne_iff_not_eq`), and the binding idiom `exists x. (t == x && φ)` is `φ` with `x` bound to
the value of `t` (`sat_binding_idiom`).
-/

namespace Dogwood.Thm

open Dogwood.Spec Dogwood.Spec.Temporal
open Cedar.Spec (Value EntityUID Attr)
open Cedar.Data (Map)
open Cedar.Validation (CedarType RecordType TypeEnv Schema)
open Cedar.Thm (InstanceOfType InstanceOfEntityType)

/-! ## Environments and values -/

/-- A value's type depends on the environment only through its entity types and actions. -/
theorem instanceOfType_congr_env {env env' : TypeEnv} (hets : env'.ets = env.ets)
    (hacts : env'.acts = env.acts) {w : Value} {ty : CedarType} (h : InstanceOfType env w ty) :
    InstanceOfType env' w ty := by
  induction h with
  | instance_of_bool b bty h₁ => exact .instance_of_bool b bty h₁
  | instance_of_int => exact .instance_of_int
  | instance_of_string => exact .instance_of_string
  | instance_of_entity e ety h₁ =>
    refine .instance_of_entity e ety ⟨h₁.1, ?_⟩
    have := h₁.2
    simp only [Cedar.Validation.EntityUID.WellFormed] at this ⊢
    rw [hets, hacts]
    exact this
  | instance_of_set s ty _ ih => exact .instance_of_set s ty ih
  | instance_of_record r rty h₁ _ h₃ ih => exact .instance_of_record r rty h₁ ih h₃
  | instance_of_ext x xty h₁ => exact .instance_of_ext x xty h₁

theorem ofTVal_inj {w₁ w₂ : TVal} (h : CVal.ofTVal w₁ = CVal.ofTVal w₂) : w₁ = w₂ := by
  cases w₁ with
  | val a =>
    cases w₂ with
    | val b => exact congrArg TVal.val (ofValue_inj.mp h)
    | tp k =>
      simp only [CVal.ofTVal] at h
      rcases ofValue_cases a with ⟨i, rfl⟩ | ⟨ha, _⟩
      · simp [CVal.ofValue] at h
      · rw [ha] at h; cases h
  | tp k =>
    cases w₂ with
    | val b =>
      simp only [CVal.ofTVal] at h
      rcases ofValue_cases b with ⟨i, rfl⟩ | ⟨hb, _⟩
      · simp [CVal.ofValue] at h
      · rw [hb] at h; cases h
    | tp k' => simp only [CVal.ofTVal, CVal.tp.injEq] at h; rw [h]

theorem ofTVal_eq_num {w : TVal} {m : Int} (h : CVal.ofTVal w = .num m) :
    ∃ i : Int64, w = .val (.prim (.int i)) := by
  cases w with
  | val a =>
    obtain ⟨i, rfl, _⟩ := ofValue_eq_num.mp h
    exact ⟨i, rfl⟩
  | tp k => cases h

/-- An atomic term denotes the comparison operand of the value it evaluates to. -/
theorem denotes_atomic {ι : ImplChoices} {rate : TickRate} {σ : Trace} {e : Event} {vis : Nat → Prop}
    {v : Valuation} {j : Nat} {t : Term} (ht : t.Atomic) {c : CVal} :
    Denotes ι rate σ e vis v j t c ↔ ∃ w, t.eval? e v = some w ∧ c = CVal.ofTVal w := by
  cases t <;> simp_all [Denotes, Term.Atomic]

theorem readLong_num {f : Int → Option Int} {n : Int} {c : CVal} (h : readLong f n = some c) :
    ∃ m, c = .num m := by
  unfold readLong at h
  split at h
  · simp only [Option.some.injEq] at h; exact ⟨n, h.symm⟩
  · simp only [Option.map_eq_some_iff] at h
    obtain ⟨m, _, rfl⟩ := h
    exact ⟨m, rfl⟩

/-- An aggregate or a compound denotes an integer. -/
theorem denotes_compound_num {ι : ImplChoices} {rate : TickRate} {σ : Trace} {e : Event} {vis : Nat → Prop}
    {v : Valuation} {j : Nat} {t : Term} (ht : ¬ t.Atomic) (hw : t ≠ .wildcard) {c : CVal}
    (h : Denotes ι rate σ e vis v j t c) : ∃ m, c = .num m := by
  cases t with
  | agg a =>
    obtain ⟨n, _, hc⟩ := h
    exact readLong_num hc
  | arith op l r =>
    obtain ⟨_, _, _, _, hc⟩ := h
    exact readLong_num hc
  | wildcard => exact absurd rfl hw
  | _ => exact absurd trivial ht

/-! ## Typed witnesses -/

theorem field?_mem {sig : EventSignature} {p : Path} {fd : FieldDecl} (h : sig.field? p = some fd) :
    fd ∈ sig.fields ∧ fd.path = p := by
  unfold EventSignature.field? at h
  exact ⟨List.mem_of_find?_eq_some h, by simpa using List.find?_some h⟩

theorem signature?_spec {S : EventSchema} {a : EntityUID} {k : String} {sig : EventSignature}
    (h : S.signature? a k = some sig) : sig.action = a ∧ sig.kind = k := by
  unfold EventSchema.signature? at h
  have := List.find?_some h
  simpa using this

theorem lookup_cons_ne {b : VarName × TType} {Γ : Bindings} {x : VarName} (h : b.1 ≠ x) :
    Bindings.lookup (b :: Γ) x = Γ.lookup x := by
  have : (b.1 == x) = false := by simpa using h
  simp [Bindings.lookup, this]

theorem lookup_cons_eq {b : VarName × TType} {Γ : Bindings} :
    Bindings.lookup (b :: Γ) b.1 = some b.2 := by
  simp [Bindings.lookup]

theorem binder_sort_name {ets : Cedar.Validation.EntitySchema} {y : Binder} {b : VarName × TType}
    (h : Binder.sort? ets y = some b) : b.1 = y.name := by
  unfold Binder.sort? at h
  split at h
  · cases h
  · simp only [Option.map_eq_some_iff] at h
    obtain ⟨_, _, rfl⟩ := h
    rfl

section

variable {ι : ImplChoices} {rate : TickRate} {σ : Trace} {e : Event} {vis : Nat → Prop} {A : Schema} {C : TypingCtx}

/-- A logged field value of a field type holds a value of every sort the field binds. -/
theorem hasValue_hasSort (hA : C.env.ets = A.ets ∧ C.env.acts = A.acts) {ft : FieldTy} {w : Value}
    {τ : TType} (hw : ft.HasValue A w) (hin : ft.Within τ) : (TVal.val w).HasSort C.env τ := by
  cases ft with
  | cedar ty =>
    simp only [FieldTy.Within] at hin
    subst hin
    have := Cedar.Thm.instance_of_type_refl (env := ⟨A.ets, A.acts, default⟩) hw
    exact instanceOfType_congr_env (env := ⟨A.ets, A.acts, default⟩) (by simp [hA.1])
      (by simp [hA.2]) this
  | entities etys =>
    obtain ⟨uid, rfl, hty, hvalid⟩ := hw
    obtain ⟨_, hall⟩ := hin
    rw [hall uid.ty hty]
    refine hasSort_val (.instance_of_entity _ _ ⟨rfl, ?_⟩)
    simp [Cedar.Validation.EntityUID.WellFormed, hA.1, hvalid]

/-- **Restricted variables are typed.** In a well-typed condition that holds, over a trace whose
events conform, at an event that supplies the scope entities the condition reads, every variable
the condition restricts, given the variables of `R` typed, holds a value of its sort. -/
theorem restricts_sorted (hA : C.env.ets = A.ets ∧ C.env.acts = A.acts)
    (htr : ∀ (k : Nat) (q : TimePoint), σ[k]? = some q → q.event.Conforms A C.events)
    (he : e.InstanceOf C.env) (hf : ∀ g ∈ C.facts, g.Holds e) :
    ∀ (φ : Formula) {Γ : Bindings} {R : VarName → Prop} {v : Valuation} {j : Nat},
      Formula.WellTyped C Γ φ → (∀ r ∈ φ.scopeReads, e.Supplies C.env r) →
      Sat ι rate σ e vis v j φ → (∀ y, R y → Valuation.SortedVar C.env Γ v y) →
      ∀ x, φ.Restricts R x → Valuation.SortedVar C.env Γ v x
  | .pred a k args, Γ, R, v, j, hty, _, hsat, _, x, hx => by
    obtain ⟨p, hp⟩ := hx
    cases hty with
    | pred hsig hargs _ =>
      rename_i sig
      intro τ hτ
      obtain ⟨q, hq, hqa, hqk, hmatch⟩ := hsat
      obtain ⟨w, hw, hm⟩ := hmatch _ hp
      simp only [Term.Matches, Term.eval?] at hm
      -- The event's signature is the predicate's.
      have hconf := htr j q hq
      unfold Event.Conforms at hconf
      rw [hqa, hqk, hsig] at hconf
      cases hargs _ hp with
      | var hfd hlook hwithin =>
        rename_i fd τ'
        rw [hlook] at hτ
        cases hτ
        obtain ⟨hmem, hpath⟩ := field?_mem hfd
        have hlog := hconf.fields fd hmem
        unfold FieldDecl.LoggedBy at hlog
        rw [hpath, hw] at hlog
        exact ⟨_, hm, hasValue_hasSort hA hlog hwithin⟩
      | term _ _ hnv _ _ _ => exact absurd rfl (hnv x)
  | .tp y, Γ, R, v, j, hty, _, hsat, _, x, hx => by
    simp only [Formula.Restricts] at hx
    subst hx
    cases hty with
    | tp hlook =>
      intro τ hτ
      rw [hlook] at hτ
      cases hτ
      exact ⟨_, hsat, trivial⟩
  | .cmp op l r, Γ, R, v, j, hty, hsup, hsat, hR, x, hx => by
    cases op <;> simp only [Formula.Restricts] at hx
    obtain ⟨heq, hval⟩ := hx
    obtain ⟨a, b, ha, hb, hab⟩ := hsat
    simp only [CmpOp.Holds] at hab
    subst hab
    cases hty with
    | ord ho _ _ => exact ho.elim
    | eq hno hl hr hc =>
      rename_i τ₁ τ₂
      have hτ : τ₁ = τ₂ := by
        rcases hc with h | ⟨h, _⟩
        · exact h
        · rw [heq] at h; cases h
      subst hτ
      -- The variable side, and the value side.
      have key : ∀ (t : Term), Term.Typed C Γ t τ₁ → (∀ y ∈ t.fv, R y) →
          (∀ root ∈ t.scopeReads, e.Supplies C.env root) →
          ∀ c, Denotes ι rate σ e vis v j t c → ∀ w, c = CVal.ofTVal w →
            w.HasSort C.env τ₁ := by
        intro t ht hfv hst c hc w hw
        by_cases hat : t.Atomic
        · obtain ⟨w', hw', rfl⟩ := (denotes_atomic hat).mp hc
          obtain ⟨w'', hw'', hs⟩ := term_resolves ht hat he hst hf (v := v)
            (fun y hy => hR y (hfv y hy))
          rw [hw'] at hw''
          cases hw''
          rw [ofTVal_inj hw.symm]
          exact hs
        · have hwild : t ≠ .wildcard := fun h => by subst h; cases ht
          obtain ⟨m, rfl⟩ := denotes_compound_num hat hwild hc
          obtain ⟨i, rfl⟩ := ofTVal_eq_num hw.symm
          have : τ₁ = .cedar .int := by
            cases t with
            | agg _ => cases ht; rfl
            | arith _ _ _ => cases ht; rfl
            | wildcard => cases ht
            | _ => exact absurd trivial hat
          subst this
          exact hasSort_val .instance_of_int
      intro τ hτ
      rcases valueSide_of_eq heq with ⟨rfl, hvs⟩ | ⟨rfl, hvs⟩
      · obtain ⟨w, hw, rfl⟩ := denotes_var ha
        cases hl with
        | var hlook =>
          rw [hlook] at hτ
          cases hτ
          rw [hvs] at hval
          exact ⟨w, hw, key r hr hval
            (fun root h => hsup root (by simp [Formula.scopeReads, h])) _ hb w rfl⟩
      · obtain ⟨w, hw, hwc⟩ := denotes_var hb
        cases hr with
        | var hlook =>
          rw [hlook] at hτ
          cases hτ
          rw [hvs] at hval
          exact ⟨w, hw, key l hl hval
            (fun root h => hsup root (by simp [Formula.scopeReads, h])) _ ha w hwc⟩
  | .not _, _, _, _, _, _, _, _, _, _, hx => hx.elim
  | .formerly _ φ, Γ, R, v, j, hty, hsup, hsat, hR, x, hx => by
    cases hty with
    | formerly _ hφ =>
      obtain ⟨k, _, _, _, hs⟩ := hsat
      exact restricts_sorted hA htr he hf φ hφ (fun r h => hsup r (by simp [Formula.scopeReads, h]))
        hs hR x hx
  | .previous _ φ, Γ, R, v, j, hty, hsup, hsat, hR, x, hx => by
    cases hty with
    | previous _ hφ =>
      obtain ⟨k, _, _, _, _, hs⟩ := hsat
      exact restricts_sorted hA htr he hf φ hφ (fun r h => hsup r (by simp [Formula.scopeReads, h]))
        hs hR x hx
  | .since φ _ ψ, Γ, R, v, j, hty, hsup, hsat, hR, x, hx => by
    cases hty with
    | since _ _ hψ =>
      obtain ⟨k, _, _, _, hs, _⟩ := hsat
      exact restricts_sorted hA htr he hf ψ hψ (fun r h => hsup r (by simp [Formula.scopeReads, h]))
        hs hR x hx
  | .exist y φ, Γ, R, v, j, hty, hsup, hsat, hR, x, hx => by
    obtain ⟨hxy, hx⟩ := hx
    cases hty with
    | exist hb hφ =>
      rename_i b
      obtain ⟨w', hs⟩ := hsat
      have hbn : b.1 = y.name := binder_sort_name hb
      have hlookx : Bindings.lookup (b :: Γ) x = Γ.lookup x :=
        lookup_cons_ne (by rw [hbn]; exact Ne.symm hxy)
      have h := restricts_sorted hA htr he hf φ hφ hsup hs (R := fun z => z ≠ y.name ∧ R z)
        (fun z ⟨hzy, hz⟩ τ hτ => by
          have hlz : Bindings.lookup (b :: Γ) z = Γ.lookup z :=
            lookup_cons_ne (by rw [hbn]; exact Ne.symm hzy)
          rw [hlz] at hτ
          obtain ⟨w, hw, hws⟩ := hR z hz τ hτ
          exact ⟨w, by simp [Valuation.bind, hzy, hw], hws⟩) x hx
      intro τ hτ
      rw [← hlookx] at hτ
      obtain ⟨w, hw, hws⟩ := h τ hτ
      exact ⟨w, by simpa [Valuation.bind, hxy] using hw, hws⟩
  | .and φ ψ, Γ, R, v, j, hty, hsup, hsat, hR, x, hx => by
    cases hty with
    | and hφ hψ =>
      exact hx (fun z => Valuation.SortedVar C.env Γ v z) hR
        (fun z hz => restricts_sorted hA htr he hf φ hφ
          (fun r h => hsup r (by simp [Formula.scopeReads, h])) hsat.1 (fun y hy => hy) z hz)
        (fun z hz => restricts_sorted hA htr he hf ψ hψ
          (fun r h => hsup r (by simp [Formula.scopeReads, h])) hsat.2 (fun y hy => hy) z hz)


/-- **An `exists` holds only of a value of its binder's type.** -/
theorem sat_exist_sorted (hA : C.env.ets = A.ets ∧ C.env.acts = A.acts)
    (htr : ∀ (k : Nat) (q : TimePoint), σ[k]? = some q → q.event.Conforms A C.events)
    (he : e.InstanceOf C.env) (hf : ∀ g ∈ C.facts, g.Holds e) {x : Binder} {φ : Formula}
    {Γ : Bindings} {R : VarName → Prop} {v : Valuation} {j : Nat} {b : VarName × TType}
    (hb : Binder.sort? C.env.ets x = some b) (hφ : Formula.WellTyped C (b :: Γ) φ)
    (hsup : ∀ r ∈ φ.scopeReads, e.Supplies C.env r)
    (hs : (Formula.exist x φ).Safe R) (hR : ∀ y, R y → Valuation.SortedVar C.env Γ v y)
    {w : TVal} (hsat : Sat ι rate σ e vis (v.bind x.name w) j φ) : w.HasSort C.env b.2 := by
  have hbn := binder_sort_name hb
  have h := restricts_sorted hA htr he hf φ hφ hsup hsat (R := fun z => z ≠ x.name ∧ R z)
    (fun z ⟨hzy, hz⟩ τ hτ => by
      rw [lookup_cons_ne (by rw [hbn]; exact Ne.symm hzy)] at hτ
      obtain ⟨w', hw', hws⟩ := hR z hz τ hτ
      exact ⟨w', by simp [Valuation.bind, hzy, hw'], hws⟩) x.name hs.1
  obtain ⟨w', hw', hws⟩ := h b.2 (by rw [← hbn]; exact lookup_cons_eq)
  have : w' = w := by simpa [Valuation.bind] using hw'.symm
  rw [← this]
  exact hws

theorem domainSorts_spec {ets : Cedar.Validation.EntitySchema} {dom : List Binder}
    {Δ : Bindings} (h : domainSorts? ets dom = some Δ) :
    (dom.map (·.name)).Nodup ∧ Δ.map (·.1) = dom.map (·.name) := by
  unfold domainSorts? at h
  split at h
  · rename_i hnd
    refine ⟨hnd, ?_⟩
    clear hnd
    induction dom generalizing Δ with
    | nil => simp at h; subst h; rfl
    | cons d dom ih =>
      simp only [List.mapM_cons] at h
      cases hb : Binder.sort? ets d with
      | none => rw [hb] at h; cases h
      | some b =>
        cases hΔ' : List.mapM (Binder.sort? ets) dom with
        | none => rw [hb, hΔ'] at h; cases h
        | some Δ' =>
          rw [hb, hΔ'] at h
          have hΔ : Δ = b :: Δ' := by simpa using h.symm
          subst hΔ
          simp [binder_sort_name hb, ih hΔ']
  · cases h

theorem dedup_of_nodup {α : Type} [BEq α] [LawfulBEq α] : {xs : List α} → xs.Nodup → dedup xs = xs
  | [], _ => rfl
  | x :: xs, h => by
    obtain ⟨hx, hxs⟩ := List.nodup_cons.mp h
    simp only [dedup, dedup_of_nodup hxs, List.cons.injEq, true_and]
    exact List.filter_eq_self.mpr fun y hy => by
      have : y ≠ x := fun hyx => hx (hyx ▸ hy)
      simpa using this

theorem lookup_append_not_mem {Δ Γ : Bindings} {y : VarName} (h : y ∉ Δ.map (·.1)) :
    Bindings.lookup (Δ ++ Γ) y = Γ.lookup y := by
  induction Δ with
  | nil => rfl
  | cons b Δ ih =>
    simp only [List.map_cons, List.mem_cons, not_or] at h
    rw [List.cons_append, lookup_cons_ne (Ne.symm h.1), ih h.2]

/-- **An aggregate counts only rows of its domain's types.** Every row of a well-typed safe
aggregate, with the variables in scope typed, gives each `for` variable a value of its type. -/
theorem rows_sorted (hA : C.env.ets = A.ets ∧ C.env.acts = A.acts)
    (htr : ∀ (k : Nat) (q : TimePoint), σ[k]? = some q → q.event.Conforms A C.events)
    (he : e.InstanceOf C.env) (hf : ∀ g ∈ C.facts, g.Holds e) {dom : List Binder}
    {body : Formula} {Γ Δ : Bindings} {R : VarName → Prop} {v : Valuation} {j : Nat}
    (hΔ : domainSorts? C.env.ets dom = some Δ) (hbody : Formula.WellTyped C (Δ ++ Γ) body)
    (hsup : ∀ r ∈ body.scopeReads, e.Supplies C.env r)
    (hrestr : ∀ b ∈ dom, body.Restricts (fun z => z ∉ dom.map (·.name) ∧ R z) b.name)
    (hv : Valuation.Sorted C.env Γ v) {row : List TVal}
    (hsat : Sat ι rate σ e vis (v.bindAll (domainNames dom) row) j body) :
    Valuation.Sorted C.env (Δ ++ Γ) (v.bindAll (domainNames dom) row) := by
  obtain ⟨hnd, hnames⟩ := domainSorts_spec hΔ
  have hdn : domainNames dom = dom.map (·.name) := dedup_of_nodup hnd
  intro y
  by_cases hy : y ∈ dom.map (·.name)
  · obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hy
    exact restricts_sorted hA htr he hf body hbody hsup hsat
      (R := fun z => z ∉ dom.map (·.name) ∧ R z)
      (fun z ⟨hz, _⟩ τ hτ => by
        rw [lookup_append_not_mem (by rw [hnames]; exact hz)] at hτ
        obtain ⟨w, hw, hws⟩ := hv z τ hτ
        refine ⟨w, ?_, hws⟩
        rw [bindAll_not_mem (by rw [hdn]; exact hz)]
        exact hw) _ (hrestr b hb)
  · intro τ hτ
    rw [lookup_append_not_mem (by rw [hnames]; exact hy)] at hτ
    obtain ⟨w, hw, hws⟩ := hv y τ hτ
    refine ⟨w, ?_, hws⟩
    rw [bindAll_not_mem (by rw [hdn]; exact hy)]
    exact hw

end

/-! ## Two-valued comparisons -/

/-- A comparison operand's value fits its sort: a value of the sort, or an integer of `Long`
sort (an aggregate total or an arithmetic result, read as an integer). -/
def _root_.Dogwood.Spec.Temporal.CVal.Fits (env : TypeEnv) (c : CVal) (τ : TType) : Prop :=
  (∃ w, c = CVal.ofTVal w ∧ w.HasSort env τ) ∨ (τ = .cedar .int ∧ ∃ m, c = .num m)

theorem fits_int_num {env : TypeEnv} {c : CVal} (h : c.Fits env (.cedar .int)) : ∃ m, c = .num m := by
  rcases h with ⟨w, rfl, hw⟩ | ⟨_, h⟩
  · cases w with
    | val a =>
      have : InstanceOfType env a .int := hw
      cases this
      exact ⟨_, rfl⟩
    | tp _ => exact hw.elim
  · exact h

section

variable {ι : ImplChoices} {rate : TickRate} {σ : Trace} {e : Event} {vis : Nat → Prop} {C : TypingCtx}

/-- **Every typed operand denotes a value of its sort**, under a total reading, at an instance of
the environment whose facts hold, with the variables in scope typed. -/
theorem operand_resolves (hι : ι.Total) (he : e.InstanceOf C.env)
    (hf : ∀ g ∈ C.facts, g.Holds e) {v : Valuation} {j : Nat} :
    ∀ {Γ : Bindings} {t : Term} {τ : TType} {R : VarName → Prop}, Term.Typed C Γ t τ →
      (∀ r ∈ t.scopeReads, e.Supplies C.env r) →
      t.Safe R → Valuation.Sorted C.env Γ v → ∃ c, Denotes ι rate σ e vis v j t c ∧ c.Fits C.env τ
  | Γ, t, τ, R, ht, hsup, hs, hv => by
    by_cases hat : t.Atomic
    · obtain ⟨w, hw, hws⟩ := term_resolves ht hat he hsup hf (v := v) (fun y _ => hv y)
      exact ⟨_, (denotes_atomic hat).mpr ⟨w, hw, rfl⟩, .inl ⟨w, rfl, hws⟩⟩
    · cases ht with
      | agg _ =>
        rename_i a _
        obtain ⟨n, hn⟩ := total_exists (J := j) (ι := ι) (σ := σ) (e := e) (vis := vis) hs v
          (Nat.le_refl j)
        have hsome := hι.aggregate n
        have : ∃ c, ι.aggregateValue n = some c := by
          unfold ImplChoices.aggregateValue readLong
          split
          · exact ⟨_, rfl⟩
          · cases h : ι.outOfRange n with
            | none => rw [h] at hsome; cases hsome
            | some m => exact ⟨.num m, by simp⟩
        obtain ⟨c, hc⟩ := this
        exact ⟨c, ⟨n, hn, hc⟩, .inr ⟨rfl, readLong_num hc⟩⟩
      | arith hl hr =>
        rename_i op l r
        obtain ⟨cl, hcl, hfl⟩ := operand_resolves (v := v) (j := j) hι he hf hl
          (fun r h => hsup r (by simp [Term.scopeReads, h])) hs.1 hv
        obtain ⟨cr, hcr, hfr⟩ := operand_resolves (v := v) (j := j) hι he hf hr
          (fun r h => hsup r (by simp [Term.scopeReads, h])) hs.2 hv
        obtain ⟨m, rfl⟩ := fits_int_num hfl
        obtain ⟨n', rfl⟩ := fits_int_num hfr
        have hsome := hι.arith (op.apply m n')
        have : ∃ c, ι.arithValue (op.apply m n') = some c := by
          unfold ImplChoices.arithValue readLong
          split
          · exact ⟨_, rfl⟩
          · cases h : ι.arithOutOfRange (op.apply m n') with
            | none => rw [h] at hsome; cases hsome
            | some k => exact ⟨.num k, by simp⟩
        obtain ⟨c, hc⟩ := this
        exact ⟨c, ⟨m, n', hcl, hcr, hc⟩, .inr ⟨rfl, readLong_num hc⟩⟩
      | _ => exact absurd trivial hat

end

/-! ## Soundness -/

end Dogwood.Thm

namespace Dogwood.Spec.Temporal

open Dogwood.Spec Dogwood.Thm
open Cedar.Validation (Schema)

section

variable (ι : ImplChoices) (rate : TickRate) (σ : Trace) (e : Event) (vis : Nat → Prop) (C : TypingCtx)

mutual

/-- **The satisfaction of `φ` is sound** at timepoint `j` under `v`: every comparison it reaches
has two operands that denote values, and every witness and aggregate row it uses gives its
variables values of their declared sorts. -/
def Formula.Sound (Γ : Bindings) (v : Valuation) (j : Nat) :
    Formula → Prop
  | .and φ ψ => Formula.Sound Γ v j φ ∧ Formula.Sound Γ v j ψ
  | .not φ => Formula.Sound Γ v j φ
  | .formerly _ φ => ∀ k ≤ j, Formula.Sound Γ v k φ
  | .previous _ φ => ∀ k ≤ j, Formula.Sound Γ v k φ
  | .since φ _ ψ => ∀ k ≤ j, Formula.Sound Γ v k φ ∧ Formula.Sound Γ v k ψ
  | .pred _ _ _ => True
  | .cmp _ l r => (∃ a, Denotes ι rate σ e vis v j l a) ∧ (∃ b, Denotes ι rate σ e vis v j r b) ∧
      Term.Sound Γ v j l ∧ Term.Sound Γ v j r
  | .exist x φ => ∀ b, Binder.sort? C.env.ets x = some b → ∀ w,
      Sat ι rate σ e vis (v.bind x.name w) j φ →
        w.HasSort C.env b.2 ∧ Formula.Sound (b :: Γ) (v.bind x.name w) j φ
  | .tp _ => True

/-- The satisfaction of the operand's aggregates is sound. -/
def Term.Sound (Γ : Bindings) (v : Valuation) (j : Nat) :
    Term → Prop
  | .agg a => Aggregate.Sound Γ v j a
  | .arith _ l r => Term.Sound Γ v j l ∧ Term.Sound Γ v j r
  | _ => True

/-- Every row of the aggregate gives its domain values of their sorts, and the satisfaction of
its body is sound at the row. -/
def Aggregate.Sound (Γ : Bindings) (v : Valuation) (j : Nat) :
    Aggregate → Prop
  | .count dom body => ∀ Δ, domainSorts? C.env.ets dom = some Δ → ∀ row,
      Sat ι rate σ e vis (v.bindAll (domainNames dom) row) j body →
        Valuation.Sorted C.env (Δ ++ Γ) (v.bindAll (domainNames dom) row) ∧
          Formula.Sound (Δ ++ Γ) (v.bindAll (domainNames dom) row) j body
  | .sum _ dom body => ∀ Δ, domainSorts? C.env.ets dom = some Δ → ∀ row,
      Sat ι rate σ e vis (v.bindAll (domainNames dom) row) j body →
        Valuation.Sorted C.env (Δ ++ Γ) (v.bindAll (domainNames dom) row) ∧
          Formula.Sound (Δ ++ Γ) (v.bindAll (domainNames dom) row) j body

end

end

section

variable {ι : ImplChoices} {rate : TickRate} {σ : Trace} {e : Event} {vis : Nat → Prop} {A : Schema} {C : TypingCtx}

mutual

/-- **Soundness of the temporal part.** A well-typed safe condition, at an instance of the
environment that supplies the scope entities the condition reads and whose facts hold, over a
trace whose events conform, under a total reading, with the variables in scope typed, is sound at
every timepoint. -/
theorem Formula.WellTyped.sound
    (hι : ι.Total) (hA : C.env.ets = A.ets ∧ C.env.acts = A.acts)
    (htr : ∀ (k : Nat) (q : TimePoint), σ[k]? = some q → q.event.Conforms A C.events)
    (he : e.InstanceOf C.env) (hf : ∀ g ∈ C.facts, g.Holds e) :
    ∀ {Γ : Bindings} {φ : Formula}, Formula.WellTyped C Γ φ →
      (∀ r ∈ φ.scopeReads, e.Supplies C.env r) → ∀ {R : VarName → Prop}
      {v : Valuation} {j : Nat}, φ.Safe R → Valuation.Sorted C.env Γ v →
        Formula.Sound ι rate σ e vis C Γ v j φ
  | _, _, .and h₁ h₂, hsup, _, _, _, hs, hv =>
    ⟨Formula.WellTyped.sound hι hA htr he hf h₁
      (fun r h => hsup r (by simp [Formula.scopeReads, h])) hs.1 hv,
     Formula.WellTyped.sound hι hA htr he hf h₂
      (fun r h => hsup r (by simp [Formula.scopeReads, h])) hs.2 hv⟩
  | _, _, .not h, hsup, _, _, _, hs, hv => Formula.WellTyped.sound hι hA htr he hf h hsup hs.2 hv
  | _, _, .formerly _ h, hsup, _, _, _, hs, hv => fun _ _ =>
    Formula.WellTyped.sound hι hA htr he hf h hsup hs hv
  | _, _, .previous _ h, hsup, _, _, _, hs, hv => fun _ _ =>
    Formula.WellTyped.sound hι hA htr he hf h hsup hs hv
  | _, _, .since _ h₁ h₂, hsup, _, _, _, hs, hv => fun _ _ =>
    ⟨Formula.WellTyped.sound hι hA htr he hf h₁
      (fun r h => hsup r (by simp [Formula.scopeReads, h])) hs.2.2 hv,
     Formula.WellTyped.sound hι hA htr he hf h₂
      (fun r h => hsup r (by simp [Formula.scopeReads, h])) hs.1 hv⟩
  | _, _, .pred _ _ _, _, _, _, _, _, _ => trivial
  | _, _, .eq _ hl hr _, hsup, _, v, j, hs, hv => by
    obtain ⟨a, ha, _⟩ := operand_resolves (σ := σ) (vis := vis) (v := v) (j := j) hι he hf hl
      (fun r h => hsup r (by simp [Formula.scopeReads, h])) hs.2.1 hv
    obtain ⟨b, hb, _⟩ := operand_resolves (σ := σ) (vis := vis) (v := v) (j := j) hι he hf hr
      (fun r h => hsup r (by simp [Formula.scopeReads, h])) hs.2.2 hv
    exact ⟨⟨a, ha⟩, ⟨b, hb⟩,
      Term.Typed.sound hι hA htr he hf hl (fun r h => hsup r (by simp [Formula.scopeReads, h]))
        hs.2.1 hv,
      Term.Typed.sound hι hA htr he hf hr (fun r h => hsup r (by simp [Formula.scopeReads, h]))
        hs.2.2 hv⟩
  | _, _, .ord _ hl hr, hsup, _, v, j, hs, hv => by
    obtain ⟨a, ha, _⟩ := operand_resolves (σ := σ) (vis := vis) (v := v) (j := j) hι he hf hl
      (fun r h => hsup r (by simp [Formula.scopeReads, h])) hs.2.1 hv
    obtain ⟨b, hb, _⟩ := operand_resolves (σ := σ) (vis := vis) (v := v) (j := j) hι he hf hr
      (fun r h => hsup r (by simp [Formula.scopeReads, h])) hs.2.2 hv
    exact ⟨⟨a, ha⟩, ⟨b, hb⟩,
      Term.Typed.sound hι hA htr he hf hl (fun r h => hsup r (by simp [Formula.scopeReads, h]))
        hs.2.1 hv,
      Term.Typed.sound hι hA htr he hf hr (fun r h => hsup r (by simp [Formula.scopeReads, h]))
        hs.2.2 hv⟩
  | Γ, .exist x φ, .exist hb hφ, hsup, R, v, j, hs, hv => by
    intro b' hb' w hsat
    rw [hb] at hb'
    cases hb'
    rename_i b
    have hw := sat_exist_sorted hA htr he hf hb hφ hsup hs (fun y _ => hv y) hsat
    refine ⟨hw, Formula.WellTyped.sound hι hA htr he hf hφ hsup hs.2 ?_⟩
    have hbn := binder_sort_name hb
    intro y τ hτ
    by_cases hy : y = x.name
    · subst hy
      rw [← hbn, lookup_cons_eq] at hτ
      cases hτ
      exact ⟨w, by simp [Valuation.bind], hw⟩
    · rw [lookup_cons_ne (by rw [hbn]; exact Ne.symm hy)] at hτ
      obtain ⟨w', hw', hws⟩ := hv y τ hτ
      exact ⟨w', by simp [Valuation.bind, hy, hw'], hws⟩
  | _, _, .tp _, _, _, _, _, _, _ => trivial

theorem Term.Typed.sound
    (hι : ι.Total) (hA : C.env.ets = A.ets ∧ C.env.acts = A.acts)
    (htr : ∀ (k : Nat) (q : TimePoint), σ[k]? = some q → q.event.Conforms A C.events)
    (he : e.InstanceOf C.env) (hf : ∀ g ∈ C.facts, g.Holds e) :
    ∀ {Γ : Bindings} {t : Term} {τ : TType}, Term.Typed C Γ t τ →
      (∀ r ∈ t.scopeReads, e.Supplies C.env r) → ∀ {R : VarName → Prop}
      {v : Valuation} {j : Nat}, t.Safe R → Valuation.Sorted C.env Γ v →
        Term.Sound ι rate σ e vis C Γ v j t
  | _, _, _, .agg h, hsup, _, _, _, hs, hv => Aggregate.Typed.sound hι hA htr he hf h hsup hs hv
  | _, _, _, .arith h₁ h₂, hsup, _, _, _, hs, hv =>
    ⟨Term.Typed.sound hι hA htr he hf h₁ (fun r h => hsup r (by simp [Term.scopeReads, h])) hs.1 hv,
     Term.Typed.sound hι hA htr he hf h₂ (fun r h => hsup r (by simp [Term.scopeReads, h])) hs.2 hv⟩
  | _, _, _, .entity _, _, _, _, _, _, _ | _, _, _, .long, _, _, _, _, _, _
  | _, _, _, .decimal _, _, _, _, _, _, _ | _, _, _, .string, _, _, _, _, _, _
  | _, _, _, .bool, _, _, _, _, _, _ | _, _, _, .context _ _, _, _, _, _, _, _
  | _, _, _, .scopeRoot, _, _, _, _, _, _
  | _, _, _, .scopeAttr _ _ _, _, _, _, _, _, _ | _, _, _, .var _, _, _, _, _, _, _ => trivial

theorem Aggregate.Typed.sound
    (hι : ι.Total) (hA : C.env.ets = A.ets ∧ C.env.acts = A.acts)
    (htr : ∀ (k : Nat) (q : TimePoint), σ[k]? = some q → q.event.Conforms A C.events)
    (he : e.InstanceOf C.env) (hf : ∀ g ∈ C.facts, g.Holds e) :
    ∀ {Γ : Bindings} {a : Aggregate}, Aggregate.Typed C Γ a →
      (∀ r ∈ a.scopeReads, e.Supplies C.env r) → ∀ {R : VarName → Prop}
      {v : Valuation} {j : Nat}, a.Safe R → Valuation.Sorted C.env Γ v →
        Aggregate.Sound ι rate σ e vis C Γ v j a
  | _, _, .count hd hbody, hsup, _, _, _, hs, hv => by
    intro Δ' hΔ' row hsat
    rw [hd] at hΔ'
    cases hΔ'
    have hsorted := rows_sorted hA htr he hf hd hbody
      (fun r h => hsup r (by simp [Aggregate.scopeReads, h])) hs.1 hv hsat
    exact ⟨hsorted, Formula.WellTyped.sound hι hA htr he hf hbody
      (fun r h => hsup r (by simp [Aggregate.scopeReads, h])) hs.2 hsorted⟩
  | _, _, .sum hd _ hbody, hsup, _, _, _, hs, hv => by
    intro Δ' hΔ' row hsat
    rw [hd] at hΔ'
    cases hΔ'
    have hsorted := rows_sorted hA htr he hf hd hbody
      (fun r h => hsup r (by simp [Aggregate.scopeReads, h])) hs.1 hv hsat
    exact ⟨hsorted, Formula.WellTyped.sound hι hA htr he hf hbody
      (fun r h => hsup r (by simp [Aggregate.scopeReads, h])) hs.2 hsorted⟩

end

end

end Dogwood.Spec.Temporal

namespace Dogwood.Thm

open Dogwood.Spec Dogwood.Spec.Temporal
open Cedar.Spec (Value EntityUID Attr)
open Cedar.Validation (CedarType RecordType TypeEnv Schema)
open Cedar.Thm (InstanceOfType InstanceOfEntityType)

/-! ## Corollaries -/

section

variable {ι : ImplChoices} {rate : TickRate} {σ : Trace} {e : Event} {vis : Nat → Prop}

/-- **`!=` and `!(==)` coincide** wherever both operands denote a value. -/
theorem sat_ne_iff_not_eq {v : Valuation} {j : Nat} {l r : Term}
    (hl : ∃ a, Denotes ι rate σ e vis v j l a) (hr : ∃ b, Denotes ι rate σ e vis v j r b) :
    Sat ι rate σ e vis v j (.cmp .ne l r) ↔ Sat ι rate σ e vis v j (.not (.cmp .eq l r)) := by
  obtain ⟨a, ha⟩ := hl
  obtain ⟨b, hb⟩ := hr
  simp only [Sat, CmpOp.Holds]
  constructor
  · rintro ⟨a', b', ha', hb', hne⟩ ⟨a'', b'', ha'', hb'', heq⟩
    rw [denotes_unique l ha' ha'', denotes_unique r hb' hb''] at hne
    exact hne heq
  · intro h
    exact ⟨a, b, ha, hb, fun heq => h ⟨a, b, ha, hb, heq⟩⟩

/-- **The binding idiom is substitution.** When `t` denotes the operand of the value `w`, and
does not mention `x`, `exists x. (t == x && φ)` holds exactly when `φ` holds with `x` bound to
`w`. -/
theorem sat_binding_idiom {v : Valuation} {j : Nat} {x : Binder} {t : Term} {φ : Formula}
    (hx : x.name ∉ t.fv) {c : CVal} (hc : Denotes ι rate σ e vis v j t c) {w : TVal}
    (hw : c = CVal.ofTVal w) :
    Sat ι rate σ e vis v j (.exist x (.and (.cmp .eq t (.var x.name)) φ)) ↔
      Sat ι rate σ e vis (v.bind x.name w) j φ := by
  have hct : ∀ w' a, Denotes ι rate σ e vis (v.bind x.name w') j t a ↔ Denotes ι rate σ e vis v j t a :=
    fun w' a => denotes_congr_val t _ _ j (fun y hy => by
      have : y ≠ x.name := fun h => hx (h ▸ hy)
      simp [Valuation.bind, this]) a
  simp only [Sat, CmpOp.Holds]
  constructor
  · rintro ⟨w', ⟨a, b, ha, hb, rfl⟩, hφ⟩
    obtain ⟨w'', hw'', hb'⟩ := denotes_var hb
    have hw''' : w' = w'' := by simpa [Valuation.bind] using hw''
    subst hw'''
    have := denotes_unique t ((hct _ _).mp ha) hc
    rw [this, hw] at hb'
    rw [← ofTVal_inj hb'] at hφ
    exact hφ
  · intro hφ
    refine ⟨w, ⟨c, c, (hct w c).mpr hc, ?_, rfl⟩, hφ⟩
    simp [Denotes, Term.eval?, Valuation.bind, hw]

/-- Under the clamping reading, every operand denotes the operand of a value: an aggregate's or an
arithmetic result's integer is a `Long`. So the binding idiom binds every operand that denotes. -/
theorem clamp_denotes_value {v : Valuation} {j : Nat} {t : Term} {c : CVal}
    (h : Denotes ImplChoices.clamp rate σ e vis v j t c) : ∃ w, c = CVal.ofTVal w := by
  by_cases hat : t.Atomic
  · obtain ⟨w, _, rfl⟩ := (denotes_atomic hat).mp h
    exact ⟨w, rfl⟩
  · have hnum : ∀ n, ImplChoices.clamp.arithValue n = some c ∨ ImplChoices.clamp.aggregateValue n = some c →
        ∃ w, c = CVal.ofTVal w := by
      intro n hn
      rcases hn with hn | hn
      · rw [clamp_arithValue, Option.some.injEq] at hn
        subst hn
        refine ⟨.val (.prim (.int (Int64.ofInt (clampLong n)))), ?_⟩
        simp only [CVal.ofTVal, CVal.ofValue]
        rw [toInt_ofInt_clamp]
      · rw [clamp_aggregateValue, Option.some.injEq] at hn
        subst hn
        refine ⟨.val (.prim (.int (Int64.ofInt (clampLong n)))), ?_⟩
        simp only [CVal.ofTVal, CVal.ofValue]
        rw [toInt_ofInt_clamp]
    cases t with
    | agg a =>
      obtain ⟨n, _, hc⟩ := h
      exact hnum n (.inr hc)
    | arith op l r =>
      obtain ⟨_, _, _, _, hc⟩ := h
      exact hnum _ (.inl hc)
    | wildcard => simp [Denotes, Term.eval?] at h
    | _ => exact absurd trivial hat

end

/-! ## The leaves of a valid policy set -/

theorem envsOf_schema {P : PolicySet} {p : Policy} {env : TypeEnv} (h : env ∈ P.envsOf p) :
    env.ets = P.actionSchema.ets ∧ env.acts = P.actionSchema.acts := by
  unfold PolicySet.envsOf at h
  have h := (List.mem_filter.mp h).1
  unfold Schema.environments at h
  simp only [List.mem_map] at h
  obtain ⟨_, _, rfl⟩ := h
  exact ⟨rfl, rfl⟩

/-- A decision event whose request Cedar's validator accepts is an instance, in its request
part, of an environment of the action schema. -/
theorem request_instance {A : Schema} {e : Event} {pr rs : EntityUID}
    (h : succeeds (Cedar.Validation.validateRequest A (e.request pr rs)) = true) :
    ∃ env ∈ A.environments, Cedar.Thm.InstanceOfRequestType (e.request pr rs) env := by
  unfold Cedar.Validation.validateRequest at h
  split at h
  · rename_i hany
    obtain ⟨env, henv, hm⟩ := List.any_eq_true.mp hany
    exact ⟨env, henv, Cedar.Thm.instance_of_request_type_refl hm⟩
  · cases h

/-- `Event.InstanceOf`, from Cedar's request type. -/
theorem instanceOf_of_request {env : TypeEnv} {e : Event} {pr rs : EntityUID}
    (hpr : e.principal = some pr) (hrs : e.resource = some rs)
    (h : Cedar.Thm.InstanceOfRequestType (e.request pr rs) env) :
    e.InstanceOf env :=
  ⟨⟨pr, hpr, h.1⟩, ⟨rs, hrs, h.2.2.1⟩, h.2.2.2⟩

/-- **Soundness of the temporal leaves of a valid policy set.** At a decision, over a trace whose
events conform, under a total reading: every temporal leaf of every rule, in every environment
its rule admits of which the decision event is an instance, when the event supplies the scope
entities the leaf reads, at a position whose facts hold at the event, is sound after pin
injection (`Formula.Sound`): every comparison its satisfaction reaches is two-valued, and every
witness and row it uses is typed. -/
theorem leaves_sound {P : PolicySet} (hv : P.Valid) {ι : ImplChoices} (hι : ι.Total)
    {σ : Trace} (htr : ∀ (k : Nat) (q : TimePoint), σ[k]? = some q →
      q.event.Conforms P.actionSchema P.schema)
    (n : Nat) {pt : TimePoint} {p : Policy} (hp : p ∈ P.policies) {φ : Formula} {F : List Guard}
    (hφ : (.inl φ, F) ∈ p.toExpr.leafFacts []) {env : TypeEnv} (henv : env ∈ P.envsOf p)
    (he : pt.event.InstanceOf env)
    (hsup : ∀ r ∈ (φ.injectPins P.schema).scopeReads, pt.event.Supplies env r)
    (hf : ∀ g ∈ F, g.Holds pt.event) (vis : Nat → Prop) :
    (φ.injectPins P.schema).Sound ι P.tickRate σ pt.event vis (P.typingCtx env F) []
      Valuation.empty n := by
  have hleaf := hv.temporal p hp φ F hφ
  have hty : Formula.WellTyped (P.typingCtx env F) [] (φ.injectPins P.schema) :=
    Formula.wellTyped_injectPins (C := P.typingCtx env F) (hleaf.wellTyped env henv)
  have hsafe : (φ.injectPins P.schema).IsSafe := (Formula.isSafe_injectPins P.schema φ).mpr hleaf.safe
  exact Formula.WellTyped.sound hι (envsOf_schema henv) htr he hf hty hsup hsafe
    (fun _ τ h => by simp [Bindings.lookup] at h)

end Dogwood.Thm
