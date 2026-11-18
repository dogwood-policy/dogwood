import Dogwood.Thm.Frontend.Cedarify.Rules

/-!
# The crate's names for the hoisted leaves

Rule `i` has the key `ruleKey d i` (`policy_<i>`, or `<d>_<i>` under a distincter `d`;
`ruleKey_eq`), and the Cedar id `ruleId d ids i` (`cedarify_tags`). Its leaves are numbered
`0, 1, …` in evaluation order, temporal and provider leaves together: a temporal leaf is the
context attribute `<key>__temporal_<n>`, a provider leaf the attribute `<key>_p_<n>` of
`context.providers`. No two leaves of a set have the same rule and number, whatever their kinds
(`cedarify_tags`), and the names are distinct (`cedarify_names_nodup`): the temporal names, with
`providers` when there is a provider leaf, are the context attributes lowering adds, and they are
distinct, as the specification's `PolicySet.Valid.namesNodup` requires of its own names.

Lowering does not check that the action schema leaves those names free (the specification's
`namesFresh`): `cedarify_names_fresh` gives a sufficient condition, and
`Dogwood.Thm.Frontend.Cedarify.Examples` shows a set cedarify lowers whose name is declared.
-/

namespace Dogwood.Thm.Frontend.Cedarify

open Dogwood.Spec
open Dogwood.Frontend
open Dogwood.Frontend.Cedarify

/-! ## Decimal numerals -/

/-- The value of a list of decimal digits. -/
def ofDigits (cs : List Char) : Nat := cs.foldl (fun acc c => acc * 10 + (c.toNat - '0'.toNat)) 0

theorem ofDigits_append_singleton (cs : List Char) (c : Char) :
    ofDigits (cs ++ [c]) = ofDigits cs * 10 + (c.toNat - '0'.toNat) := by
  simp [ofDigits, List.foldl_append]

theorem digitChar_value : (d : Nat) → d < 10 → (Nat.digitChar d).toNat - '0'.toNat = d
  | 0, _ => by decide | 1, _ => by decide | 2, _ => by decide | 3, _ => by decide
  | 4, _ => by decide | 5, _ => by decide | 6, _ => by decide | 7, _ => by decide
  | 8, _ => by decide | 9, _ => by decide
  | _ + 10, h => by omega

theorem ofDigits_toDigits (n : Nat) : ofDigits (Nat.toDigits 10 n) = n := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    rw [Nat.toDigits_eq_if (by decide)]
    split
    · have := digitChar_value n ‹_›
      simpa [ofDigits] using this
    · rw [ofDigits_append_singleton, ih (n / 10) (by omega),
        digitChar_value _ (Nat.mod_lt _ (by decide))]
      omega

theorem toDigits_inj {a b : Nat} (h : Nat.toDigits 10 a = Nat.toDigits 10 b) : a = b := by
  rw [← ofDigits_toDigits a, ← ofDigits_toDigits b, h]

theorem isDigit_of_mem_toDigits {n : Nat} {c : Char} (h : c ∈ Nat.toDigits 10 n) :
    c.isDigit = true :=
  Nat.isDigit_of_mem_toDigits (by decide) (by decide) h

theorem toList_toString (n : Nat) : (toString n).toList = Nat.toDigits 10 n := by
  rw [Nat.toString_eq_ofList_toDigits, String.toList_ofList]

/-- A run of digits followed by a non-digit is cut where the digits end. -/
theorem digits_append_cancel :
    (a a' : List Char) → (b b' : List Char) → (∀ c ∈ a, c.isDigit = true) →
    (∀ c ∈ a', c.isDigit = true) → (∀ c ∈ b.head?, c.isDigit = false) →
    (∀ c ∈ b'.head?, c.isDigit = false) → a ++ b = a' ++ b' → a = a' ∧ b = b'
  | [], [], _, _, _, _, _, _, h => ⟨rfl, by simpa using h⟩
  | [], c :: _, b, _, _, ha', hb, _, h => by
    cases b with
    | nil => simp at h
    | cons x _ =>
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
      have := hb x (by simp)
      rw [h.1, ha' c (by simp)] at this
      cases this
  | c :: _, [], _, b', ha, _, _, hb', h => by
    cases b' with
    | nil => simp at h
    | cons x _ =>
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
      have := hb' x (by simp)
      rw [← h.1, ha c (by simp)] at this
      cases this
  | c :: as, c' :: as', b, b', ha, ha', hb, hb', h => by
    simp only [List.cons_append, List.cons.injEq] at h
    obtain ⟨rfl, h⟩ := h
    have := digits_append_cancel as as' b b' (fun x hx => ha x (by simp [hx]))
      (fun x hx => ha' x (by simp [hx])) hb hb' h
    exact ⟨by rw [this.1], this.2⟩

/-- A name `p ++ <i> ++ s ++ <n>`, with `s` starting with a non-digit, determines `i` and `n`. -/
theorem numbered_inj {p s : String} {c : Char} {rest : List Char} (hs : s.toList = c :: rest)
    (hc : c.isDigit = false) {i j n m : Nat}
    (h : p ++ toString i ++ s ++ toString n = p ++ toString j ++ s ++ toString m) :
    i = j ∧ n = m := by
  have h := congrArg String.toList h
  simp only [String.toList_append, toList_toString, List.append_assoc, hs] at h
  have h := List.append_cancel_left h
  have := digits_append_cancel _ _ _ _ (fun _ hx => isDigit_of_mem_toDigits hx)
    (fun _ hx => isDigit_of_mem_toDigits hx) (by simpa using hc) (by simpa using hc) h
  refine ⟨toDigits_inj this.1, toDigits_inj ?_⟩
  simpa using this.2

/-- A name `p ++ <i>` determines `i`. -/
theorem suffix_inj {p : String} {i j : Nat} (h : p ++ toString i = p ++ toString j) : i = j := by
  have h := congrArg String.toList h
  simp only [String.toList_append, toList_toString] at h
  exact toDigits_inj (List.append_cancel_left h)

/-! ## The names -/

/-- The text a rule key starts with: `policy_`, or the distincter and `_`. -/
def keyPrefix : Option String → String
  | some d => d ++ "_"
  | none => "policy_"

theorem ruleKey_eq (d : Option String) (i : Nat) : ruleKey d i = keyPrefix d ++ toString i := by
  cases d <;> rfl

theorem temporalName_inj {d : Option String} {i j n m : Nat}
    (h : temporalName (ruleKey d i) n = temporalName (ruleKey d j) m) : i = j ∧ n = m := by
  simp only [temporalName, ruleKey_eq] at h
  exact numbered_inj (s := "__temporal_") (c := '_') (rest := "_temporal_".toList) (by decide)
    (by decide) h

theorem providerName_inj {d : Option String} {i j n m : Nat}
    (h : providerName (ruleKey d i) n = providerName (ruleKey d j) m) : i = j ∧ n = m := by
  simp only [providerName, ruleKey_eq] at h
  exact numbered_inj (s := "_p_") (c := '_') (rest := "p_".toList) (by decide) (by decide) h

theorem leafAttr_inj {i j : Nat} (h : leafAttr i = leafAttr j) : i = j := suffix_inj h

theorem temporalName_ne_providers (d : Option String) (i n : Nat) :
    temporalName (ruleKey d i) n ≠ "providers" := by
  intro h
  have := congrArg String.length h
  simp only [temporalName, ruleKey_eq, String.length_append] at this
  have h₁ : 0 < (toString i).length := Nat.length_repr_pos
  have h₂ : 0 < (toString n).length := Nat.length_repr_pos
  have h₃ : "__temporal_".length = 11 := by decide
  have h₄ : "providers".length = 9 := by decide
  omega

/-! ## Each leaf's rule and number -/

/-- The fields of `s` are named by `(rule, number)` tags, no two alike, each satisfying `P`. -/
def TagsOK (d : Option String) (s : St) (P : Nat × Nat → Prop) : Prop :=
  ∃ ct pt : List (Nat × Nat),
    s.contextFields.map (·.fieldName) = ct.map (fun t => temporalName (ruleKey d t.1) t.2) ∧
    s.providerFields.map (·.fieldName) = pt.map (fun t => providerName (ruleKey d t.1) t.2) ∧
    (ct ++ pt).Nodup ∧ ∀ t ∈ ct ++ pt, P t

theorem TagsOK.mono {d : Option String} {s : St} {P P' : Nat × Nat → Prop}
    (h : TagsOK d s P) (hP : ∀ t, P t → P' t) : TagsOK d s P' := by
  obtain ⟨ct, pt, hc, hp, hn, hb⟩ := h
  exact ⟨ct, pt, hc, hp, hn, fun t ht => hP t (hb t ht)⟩

/-- The tags of rule `i` so far: earlier rules, or rule `i` below the next number. -/
def Before (i o : Nat) (t : Nat × Nat) : Prop := t.1 < i ∨ (t.1 = i ∧ t.2 < o)

theorem not_mem_of_before {i o : Nat} {L : List (Nat × Nat)} (h : ∀ t ∈ L, Before i o t) :
    (i, o) ∉ L := fun hm => by
  rcases h _ hm with h | h <;> simp at h

theorem TagsOK.hoistTemporal {d : Option String} {i : Nat} {env : Env} {t : Surface.Temporal.Block}
    {s : St} (hk : s.key = ruleKey d i) (h : TagsOK d s (Before i s.ordinal)) :
    TagsOK d (hoistTemporal env t s).2 (Before i (hoistTemporal env t s).2.ordinal) := by
  obtain ⟨errs, he, -⟩ := hoistTemporal_snd env t s
  rw [he]
  dsimp only
  obtain ⟨ct, pt, hc, hp, hn, hb⟩ := h
  have hx := not_mem_of_before hb
  refine ⟨ct ++ [(i, s.ordinal)], pt, ?_, hp, ?_, ?_⟩
  · simp [hc, hk]
  · simp only [List.mem_append, not_or] at hx
    simp only [List.nodup_append, List.mem_append, List.mem_singleton] at hn ⊢
    refine ⟨⟨hn.1, by simp, fun a ha b hb' => ?_⟩, hn.2.1, ?_⟩
    · rintro rfl; exact hx.1 (hb' ▸ ha)
    · rintro a (ha | rfl) b hb'
      · exact hn.2.2 a ha b hb'
      · rintro rfl; exact hx.2 hb'
  · intro u hu
    simp only [List.mem_append, List.mem_singleton] at hu
    rcases hu with (hu | rfl) | hu
    · rcases hb u (by simp [hu]) with h | h
      · exact .inl h
      · exact .inr ⟨h.1, by omega⟩
    · exact .inr ⟨rfl, by simp⟩
    · rcases hb u (by simp [hu]) with h | h
      · exact .inl h
      · exact .inr ⟨h.1, by omega⟩

theorem TagsOK.hoistProvider {d : Option String} {i : Nat} {env : Env}
    {inv : Frontend.Provider.Invocation} {ms : List Frontend.Provider.MethodCall} {s : St}
    (hk : s.key = ruleKey d i) (h : TagsOK d s (Before i s.ordinal)) :
    TagsOK d (hoistProvider env inv ms s).2 (Before i (hoistProvider env inv ms s).2.ordinal) := by
  obtain ⟨errs, he, -⟩ := hoistProvider_snd env inv ms s
  rw [he]
  dsimp only
  obtain ⟨ct, pt, hc, hp, hn, hb⟩ := h
  have hx := not_mem_of_before hb
  refine ⟨ct, pt ++ [(i, s.ordinal)], hc, ?_, ?_, ?_⟩
  · simp [hp, hk]
  · rw [← List.append_assoc]
    simp only [List.nodup_append, List.mem_singleton] at hn ⊢
    exact ⟨hn, by simp, fun a ha b hb' => by subst hb'; rintro rfl; exact hx (by simpa using ha)⟩
  · intro u hu
    simp only [List.mem_append, List.mem_singleton] at hu
    rcases hu with hu | hu | rfl
    · rcases hb u (by simp [hu]) with h | h
      · exact .inl h
      · exact .inr ⟨h.1, by omega⟩
    · rcases hb u (by simp [hu]) with h | h
      · exact .inl h
      · exact .inr ⟨h.1, by omega⟩
    · exact .inr ⟨rfl, by simp⟩

theorem TagsOK.hoists {d : Option String} {i : Nat} {env : Env} {s s' : St} (h : Hoists env s s')
    (hk : s.key = ruleKey d i) (ht : TagsOK d s (Before i s.ordinal)) :
    TagsOK d s' (Before i s'.ordinal) := by
  induction h with
  | refl => exact ht
  | temporal t _ ih =>
    obtain ⟨errs, he, -⟩ := hoistTemporal_snd env t _
    exact ih (by rw [he]; exact hk) (ht.hoistTemporal hk)
  | provider inv ms _ ih =>
    obtain ⟨errs, he, -⟩ := hoistProvider_snd env inv ms _
    exact ih (by rw [he]; exact hk) (ht.hoistProvider hk)

theorem lowerPolicy_tags {decls : Option ProviderDecls.Declarations}
    {enumNames : List (String × String)} {d : Option String} {i : Nat} {id : String}
    {p : Surface.Policy} {s : St} {ro : RuleOut} {s' : St}
    (h : lowerPolicy decls enumNames (ruleKey d i) id p s = .ok (ro, s'))
    (ht : TagsOK d s (fun t => t.1 < i)) : TagsOK d s' (fun t => t.1 < i + 1) := by
  have hh := (lowerPolicy_lowers h).1
  have h₀ : TagsOK d { s with key := ruleKey d i, ordinal := 0 } (Before i 0) :=
    ht.mono fun t ht => .inl ht
  exact (h₀.hoists hh rfl).mono fun t ht => by
    rcases ht with ht | ht
    · omega
    · omega

/-- What lowering the rules records, rule by rule. -/
theorem lowerPoliciesFrom_tags {decls : Option ProviderDecls.Declarations}
    {enumNames : List (String × String)} {d : Option String} {ids : Option (List String)} :
    (i : Nat) → (ps : List Surface.Policy) → (acc res : Rules) →
    lowerPoliciesFrom decls enumNames d ids i ps acc = .ok res →
    TagsOK d acc.st (fun t => t.1 < i) →
    TagsOK d res.st (fun t => t.1 < i + ps.length) ∧
    res.ruleKeys = acc.ruleKeys ++ (List.range' i ps.length).map (ruleKey d) ∧
    res.ruleIds = acc.ruleIds ++ (List.range' i ps.length).map (ruleId d ids)
  | i, [], acc, res, h, ht => by
    simp only [lowerPoliciesFrom, Except.ok.injEq] at h
    subst h
    exact ⟨by simpa using ht, by simp, by simp⟩
  | i, p :: ps, acc, res, h, ht => by
    simp only [lowerPoliciesFrom] at h
    cases hp : lowerPolicy decls enumNames (ruleKey d i) (ruleId d ids i) p acc.st with
    | error _ => simp [hp, bind, Except.bind] at h
    | ok q =>
      obtain ⟨ro, s₁⟩ := q
      simp only [hp, bind, Except.bind] at h
      split at h
      · simp at h
      · have := lowerPoliciesFrom_tags (i + 1) ps _ res h (lowerPolicy_tags hp ht)
        refine ⟨this.1.mono fun t ht => by simp at ht ⊢; omega, ?_, ?_⟩
        · rw [this.2.1]; simp [List.range'_succ]
        · rw [this.2.2]; simp [List.range'_succ]

/-! ## Cedarify's names -/

theorem assemble_contextNames (frag : CedarSchema.Fragment) (referenced : List String)
    (enumNames : List (String × String)) (rules : Rules) :
    (assemble frag referenced enumNames rules).cedarified.contextFields.map (·.fieldName) =
      rules.st.contextFields.map (·.fieldName) := by
  simp [assemble, Function.comp_def]

theorem assemble_providerNames (frag : CedarSchema.Fragment) (referenced : List String)
    (enumNames : List (String × String)) (rules : Rules) :
    (assemble frag referenced enumNames rules).cedarified.providerFields.map (·.fieldName) =
      rules.st.providerFields.map (·.fieldName) := by
  simp [assemble, Function.comp_def]

/-- **Each leaf's rule and number.** Cedarify names the fields it hoists by tags `(i, n)`: the
`n`-th leaf of rule `i` is `context.<ruleKey d i>__temporal_<n>` if it is temporal and
`context.providers.<ruleKey d i>_p_<n>` if it is a provider chain; no two fields have the same
tag, whatever their kinds; and every rule is one of the set's. The rule keys are
`ruleKey d 0, ruleKey d 1, …`, and the Cedar ids `ruleId d ids 0, …`. -/
theorem cedarify_tags {ps : Surface.PolicySet} {frag : CedarSchema.Fragment}
    {decls : Option ProviderDecls.Declarations} {d : Option String} {ids : Option (List String)}
    {w : WithSpec} (h : cedarifyFull ps frag decls d ids = .ok w) :
    (∃ ct pt : List (Nat × Nat),
      w.cedarified.contextFields.map (·.fieldName) =
        ct.map (fun t => temporalName (ruleKey d t.1) t.2) ∧
      w.cedarified.providerFields.map (·.fieldName) =
        pt.map (fun t => providerName (ruleKey d t.1) t.2) ∧
      (ct ++ pt).Nodup ∧ ∀ t ∈ ct ++ pt, t.1 < ps.policies.length) ∧
    w.cedarified.ruleKeys = (List.range ps.policies.length).map (ruleKey d) ∧
    w.cedarified.ruleIds = (List.range ps.policies.length).map (ruleId d ids) := by
  obtain ⟨enumNames, referenced, rules, hr, rfl⟩ := cedarifyFull_rules h
  have := lowerPoliciesFrom_tags 0 ps.policies _ rules hr ⟨[], [], rfl, rfl, by simp, by simp⟩
  obtain ⟨ct, pt, hc, hp, hn, hb⟩ := this.1
  refine ⟨⟨ct, pt, by rw [assemble_contextNames, hc], by rw [assemble_providerNames, hp], hn,
    fun t ht => by simpa using hb t ht⟩, ?_, ?_⟩
  · simp [assemble, this.2.1, List.range_eq_range']
  · simp [assemble, this.2.2, List.range_eq_range']

theorem nodup_map_of_inj {α β : Type} {f : α → β} (hf : ∀ a b, f a = f b → a = b) {l : List α}
    (h : l.Nodup) : (l.map f).Nodup := by
  rw [List.Nodup, List.pairwise_map]
  exact h.imp fun hne heq => hne (hf _ _ heq)

/-- **The names are distinct.** The temporal fields' names are distinct, and so are the provider
fields'; and the context attributes lowering adds (the temporal fields' names, and `providers`
when there is a provider field) are distinct. -/
theorem cedarify_names_nodup {ps : Surface.PolicySet} {frag : CedarSchema.Fragment}
    {decls : Option ProviderDecls.Declarations} {d : Option String} {ids : Option (List String)}
    {w : WithSpec} (h : cedarifyFull ps frag decls d ids = .ok w) :
    (w.cedarified.contextFields.map (·.fieldName)).Nodup ∧
    (w.cedarified.providerFields.map (·.fieldName)).Nodup ∧
    (w.cedarified.contextFields.map (·.fieldName) ++
      (if w.cedarified.providerFields.isEmpty then [] else ["providers"])).Nodup := by
  obtain ⟨⟨ct, pt, hc, hp, hn, -⟩, -⟩ := cedarify_tags h
  have hn' := List.nodup_append.mp hn
  have h₁ : (w.cedarified.contextFields.map (·.fieldName)).Nodup := by
    rw [hc]
    exact nodup_map_of_inj (fun a b hab => Prod.ext (temporalName_inj hab).1 (temporalName_inj hab).2)
      hn'.1
  refine ⟨h₁, ?_, ?_⟩
  · rw [hp]
    exact nodup_map_of_inj (fun a b hab => Prod.ext (providerName_inj hab).1 (providerName_inj hab).2)
      hn'.2.1
  · split
    · simpa using h₁
    · refine List.nodup_append.mpr ⟨h₁, by simp, fun a ha b hb => ?_⟩
      simp only [List.mem_singleton] at hb
      subst hb
      rw [hc] at ha
      obtain ⟨t, -, rfl⟩ := List.mem_map.mp ha
      exact temporalName_ne_providers d t.1 t.2

/-! ## Fresh names -/

/-- The context attributes cedarify's lowering adds: each temporal field's name, and `providers`
when there is a provider field (the hoisted names `Lowered.hoistedNames` drops again). -/
def addedNames (c : Cedarified) : List String :=
  c.contextFields.map (·.fieldName) ++ (if c.providerFields.isEmpty then [] else ["providers"])

theorem temporalName_eq_prefix (d : Option String) (i n : Nat) :
    ∃ x, temporalName (ruleKey d i) n = keyPrefix d ++ x :=
  ⟨toString i ++ "__temporal_" ++ toString n, by
    simp [temporalName, ruleKey_eq, String.append_assoc]⟩

/-- **When the names are fresh.** The names cedarify adds are fresh in an action schema (the
specification's `namesFresh`, for the crate's names) when no action's context declares an
attribute beginning with the rules' key prefix (`policy_`, or the distincter and `_`), nor
`providers` if there is a provider field. They are not fresh exactly when some action's context
declares one of them: `<ruleKey d i>__temporal_<n>` for a hoisted temporal leaf `(i, n)`
(`cedarify_tags`), or `providers`. Lowering checks neither. -/
theorem cedarify_names_fresh {ps : Surface.PolicySet} {frag : CedarSchema.Fragment}
    {decls : Option ProviderDecls.Declarations} {d : Option String} {ids : Option (List String)}
    {w : WithSpec} (h : cedarifyFull ps frag decls d ids = .ok w) (A : Cedar.Validation.Schema)
    (hk : ∀ act ∈ A.acts.toList, ∀ x, act.2.context.find? (keyPrefix d ++ x) = none)
    (hp : w.cedarified.providerFields ≠ [] →
      ∀ act ∈ A.acts.toList, act.2.context.find? "providers" = none) :
    ∀ act ∈ A.acts.toList, ∀ a ∈ addedNames w.cedarified, act.2.context.find? a = none := by
  obtain ⟨⟨ct, pt, hc, -, -, -⟩, -⟩ := cedarify_tags h
  intro act hact a ha
  simp only [addedNames, List.mem_append] at ha
  rcases ha with ha | ha
  · rw [hc] at ha
    obtain ⟨t, -, rfl⟩ := List.mem_map.mp ha
    obtain ⟨x, hx⟩ := temporalName_eq_prefix d t.1 t.2
    rw [hx]
    exact hk act hact x
  · split at ha
    · simp at ha
    · next hne =>
      simp only [List.mem_singleton] at ha
      subst ha
      exact hp (by simpa using hne) act hact

end Dogwood.Thm.Frontend.Cedarify
