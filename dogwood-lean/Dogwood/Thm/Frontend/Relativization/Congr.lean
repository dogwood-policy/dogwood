import Dogwood.Thm.Frontend.LeafPasses.Unorder
import Dogwood.Thm.Frontend.Relativization.Names
import Dogwood.Thm.Valuation

/-!
# The extended relation depends on a valuation only through a condition's names

`xsat_congr_names`: two valuations that agree on every variable a condition names
(`LeafPasses.condNames`, bound or used) make it hold at the same timepoints, under every reading;
the same holds of what an operand denotes and of an aggregate's total. So a leaf that uses no
name of the relativization rewrite's fresh form means the same under a valuation that binds the
rewrite's names (`xsat_congr_fresh`).
-/

namespace Dogwood.Thm.Frontend

open Dogwood.Frontend Dogwood.Frontend.LeafPasses Surface.Temporal
open Dogwood.Spec (Event Trace TickRate)
open Dogwood.Spec.Temporal (Valuation ImplChoices CVal TVal ArgsMatch)

/-- Two valuations agree on every name that does not start with `pre`: they differ at most on
the relativization rewrite's fresh names, drawn with the prefix `pre`. -/
def AgreeOff (pre : String) (v v' : Valuation) : Prop :=
  ∀ x, hasPrefix pre x = false → v' x = v x

theorem AgreeOff.refl (pre : String) (v : Valuation) : AgreeOff pre v v := fun _ _ => rfl

theorem AgreeOff.bind {pre : String} {v v' : Valuation} (h : AgreeOff pre v v') {x : String}
    (hx : hasPrefix pre x = true) (w : TVal) : AgreeOff pre v (v'.bind x w) := by
  intro y hy
  simp only [Valuation.bind, if_neg (ne_of_startsWith hy hx)]
  exact h y hy

theorem AgreeOff.bindAll {pre : String} {v v' : Valuation} (h : AgreeOff pre v v')
    {xs : List String} (hxs : ∀ x ∈ xs, hasPrefix pre x = true) (ws : List TVal) :
    AgreeOff pre v (v'.bindAll xs ws) := by
  induction xs generalizing v' ws with
  | nil => cases ws <;> exact h
  | cons x xs ih =>
    cases ws with
    | nil => exact h
    | cons w ws =>
      simp only [Valuation.bindAll]
      exact ih (h.bind (hxs x (List.mem_cons_self ..)) w)
        (fun y hy => hxs y (List.mem_cons_of_mem _ hy)) ws

theorem eval_congr_spec {e : Event} {v v' : Valuation} (t' : Dogwood.Spec.Temporal.Term)
    (h : ∀ x, t' = .var x → v x = v' x) : t'.eval? e v = t'.eval? e v' := by
  cases t' <;> simp_all [Dogwood.Spec.Temporal.Term.eval?]

/-- A term's value depends only on the names it uses. -/
theorem eval_toSpec_congr {e : Event} {t : Surface.Temporal.Term} {t' : Dogwood.Spec.Temporal.Term}
    (h : t.toSpec = .ok t') {v v' : Valuation} (hv : ∀ y ∈ termNames t, v y = v' y) :
    t'.eval? e v = t'.eval? e v' := by
  apply eval_congr_spec
  rintro x rfl
  obtain rfl := toSpec_eq_var h
  exact hv x (by simp [termNames])

theorem argsMatch_names_congr {e : Event} {v v' : Valuation} {ev : Event} :
    (args : List NamedArg) → {args' : List (Dogwood.Spec.Path × Dogwood.Spec.Temporal.Term)} →
    NamedArg.toSpecList args = .ok args' → (∀ y ∈ argNames args, v y = v' y) →
    (ArgsMatch e v ev args' ↔ ArgsMatch e v' ev args')
  | [], args', h, _ => by
    simp only [NamedArg.toSpecList, pure_eq_ok] at h; subst h
    simp [ArgsMatch]
  | ⟨n, t⟩ :: rest, args', h, hv => by
    simp only [NamedArg.toSpecList, bind_eq_ok, pure_eq_ok] at h
    obtain ⟨t', ht, rest', hrest, rfl⟩ := h
    simp only [argNames, List.mem_append] at hv
    have ih := argsMatch_names_congr (e := e) (ev := ev) rest hrest fun y hy => hv y (.inr hy)
    have he := eval_toSpec_congr (e := e) ht fun y hy => hv y (.inl hy)
    simp only [ArgsMatch, List.mem_cons, forall_eq_or_imp] at ih ⊢
    refine and_congr ?_ ih
    refine exists_congr fun w => and_congr_right fun _ => ?_
    cases t' <;> simp only [Dogwood.Spec.Temporal.Term.Matches] <;> rw [he]

section
variable {ι : ImplChoices} {rate : TickRate} {σ : Trace} {e : Event} {vis : Nat → Prop}
  {ord : Bool} {dom : Domain}

theorem toName_eq_ok {s : BinderSlot} {x : String} (h : s.toName = .ok x) : s = .name x := by
  cases s <;> simp_all [BinderSlot.toName, pure, Except.pure, throw, throwThe, MonadExceptOf.throw]

theorem xdenotes_default {t : Surface.Temporal.Term} (ht : TermAtom t) (v : Valuation) (j : Nat)
    (c : CVal) :
    XDenotes ι rate σ e vis ord dom v j t c ↔
      ∃ t', t.toSpec = .ok t' ∧ ∃ w, t'.eval? e v = some w ∧ c = CVal.ofTVal w := by
  cases t <;> first | exact absurd ht id | exact Iff.rfl

theorem xdenotes_atom_congr (t : Surface.Temporal.Term) (ht : TermAtom t) (v v' : Valuation) (j : Nat)
    (h : ∀ y ∈ termNames t, v y = v' y) (c : CVal) :
    XDenotes ι rate σ e vis ord dom v j t c ↔ XDenotes ι rate σ e vis ord dom v' j t c := by
  rw [xdenotes_default ht, xdenotes_default ht]
  exact exists_congr fun t' => and_congr_right fun ht' => by rw [eval_toSpec_congr ht' h]

mutual

/-- **The extended relation depends only on a condition's names.** -/
theorem xsat_congr_names : (c : Condition) → (v v' : Valuation) → (j : Nat) →
    (∀ y ∈ condNames c, v y = v' y) →
    (XSat ι rate σ e vis ord dom v j c ↔ XSat ι rate σ e vis ord dom v' j c)
  | ⟨_, .and l r⟩, v, v', j, h => by
    simp only [condNames, kindNames, List.mem_append] at h
    simp only [XSat, xsat_congr_names l v v' j (fun y hy => h y (.inl hy)),
      xsat_congr_names r v v' j (fun y hy => h y (.inr hy))]
  | ⟨_, .or l r⟩, v, v', j, h => by
    simp only [condNames, kindNames, List.mem_append] at h
    simp only [XSat, xsat_congr_names l v v' j (fun y hy => h y (.inl hy)),
      xsat_congr_names r v v' j (fun y hy => h y (.inr hy))]
  | ⟨_, .not c⟩, v, v', j, h => by
    simp only [condNames, kindNames] at h
    simp only [XSat, xsat_congr_names c v v' j h]
  | ⟨_, .formerly w c⟩, v, v', j, h => by
    simp only [condNames, kindNames] at h
    simp only [XSat]
    exact exists_congr fun win => and_congr_right' (exists_congr fun k => and_congr_right' (and_congr_right'
      (and_congr_right' (xsat_congr_names c v v' k h))))
  | ⟨_, .previous w c⟩, v, v', j, h => by
    simp only [condNames, kindNames] at h
    simp only [XSat]
    exact exists_congr fun win => and_congr_right' (exists_congr fun k => and_congr_right' (and_congr_right'
      (and_congr_right' (and_congr_right' (xsat_congr_names c v v' k h)))))
  | ⟨_, .since l w r⟩, v, v', j, h => by
    simp only [condNames, kindNames, List.mem_append] at h
    simp only [XSat]
    exact exists_congr fun win => and_congr_right' (exists_congr fun k => and_congr_right' (and_congr_right'
      (and_congr_right' (and_congr (xsat_congr_names r v v' k (fun y hy => h y (.inr hy)))
        (forall_congr' fun k' => imp_congr_right fun _ => imp_congr_right fun _ => imp_congr_right fun _ =>
          xsat_congr_names l v v' k' (fun y hy => h y (.inl hy)))))))
  | ⟨_, .exists ⟨s, ty⟩ c⟩, v, v', j, h => by
    simp only [condNames, kindNames, List.mem_cons] at h
    simp only [XSat]
    refine exists_congr fun x => and_congr_right fun hx => exists_congr fun w => and_congr_right' ?_
    obtain rfl := toName_eq_ok hx
    refine xsat_congr_names c _ _ j fun y hy => ?_
    by_cases hyx : y = x
    · subst hyx; simp [Valuation.bind]
    · simp only [Valuation.bind, if_neg hyx]
      exact h y (.inr hy)
  | ⟨_, .predicate ⟨_, ns, a, kd, args⟩⟩, v, v', j, h => by
    simp only [condNames, kindNames] at h
    simp only [XSat]
    refine exists_congr fun uid => exists_congr fun args' => and_congr_right' (and_congr_right fun ha =>
      exists_congr fun p => and_congr_right' (and_congr_right' (and_congr_right' ?_)))
    exact argsMatch_names_congr args ha h
  | ⟨_, .comparison op l r⟩, v, v', j, h => by
    simp only [condNames, kindNames, List.mem_append] at h
    simp only [XSat]
    exact exists_congr fun a => exists_congr fun b => and_congr
      (xdenotes_congr_names l v v' j (fun y hy => h y (.inl hy)) a)
      (and_congr_left' (xdenotes_congr_names r v v' j (fun y hy => h y (.inr hy)) b))
  | ⟨_, .tp s⟩, v, v', j, h => by
    simp only [condNames, kindNames, List.mem_singleton] at h
    simp only [XSat]
    refine exists_congr fun x => and_congr_right fun hx => ?_
    obtain rfl := toName_eq_ok hx
    rw [h x rfl]
  | ⟨_, .call _⟩, _, _, _, _ => Iff.rfl
  | ⟨_, .sigilRef _ _⟩, _, _, _, _ => Iff.rfl
  | ⟨_, .refine _ _ _⟩, _, _, _, _ => Iff.rfl

theorem xdenotes_congr_names : (t : Surface.Temporal.Term) → (v v' : Valuation) → (j : Nat) →
    (∀ y ∈ termNames t, v y = v' y) → (c : CVal) →
    (XDenotes ι rate σ e vis ord dom v j t c ↔ XDenotes ι rate σ e vis ord dom v' j t c)
  | .agg ⟨_, k⟩, v, v', j, h, c => by
    simp only [termNames] at h
    simp only [XDenotes]
    exact exists_congr fun n => and_congr_left' (xtotal_congr_names k v v' j h n)
  | .arith op l r, v, v', j, h, c => by
    simp only [termNames, List.mem_append] at h
    simp only [XDenotes]
    exact exists_congr fun m => exists_congr fun n => and_congr
      (xdenotes_congr_names l v v' j (fun y hy => h y (.inl hy)) _)
      (and_congr_left' (xdenotes_congr_names r v v' j (fun y hy => h y (.inr hy)) _))
  | .entity a b, v, v', j, h, c | .integer a, v, v', j, h, c | .decimal a, v, v', j, h, c
  | .string a, v, v', j, h, c | .bool a, v, v', j, h, c | .contextField a, v, v', j, h, c
  | .scopeField a, v, v', j, h, c | .var a, v, v', j, h, c | .array a, v, v', j, h, c
  | .paramRef a, v, v', j, h, c | .binderRef a, v, v', j, h, c | .wildcard, v, v', j, h, c =>
    xdenotes_atom_congr _ (by exact trivial) v v' j h c

theorem xtotal_congr_names : (k : AggExprKind) → (v v' : Valuation) → (j : Nat) →
    (∀ y ∈ aggNames k, v y = v' y) → (n : Int) →
    (XTotal ι rate σ e vis ord dom v j k n ↔ XTotal ι rate σ e vis ord dom v' j k n)
  | .count vs b, v, v', j, h, n => by
    simp only [aggNames, List.mem_append] at h
    simp only [XTotal]
    refine exists_congr fun bs => and_congr_right' (exists_congr fun rows => and_congr_right'
      (and_congr_left' (forall_congr' fun row => iff_congr Iff.rfl ?_)))
    refine ⟨fun ⟨hl, hr, hs⟩ => ⟨hl, hr, ?_⟩, fun ⟨hl, hr, hs⟩ => ⟨hl, hr, ?_⟩⟩
    · exact (xsat_congr_names b _ _ j (fun y hy => Dogwood.Thm.bindAll_congr hl y (.inr (h y (.inr hy))))).mp hs
    · exact (xsat_congr_names b _ _ j (fun y hy => Dogwood.Thm.bindAll_congr hl y (.inr (h y (.inr hy))))).mpr hs
  | .sum s vs b, v, v', j, h, n => by
    simp only [aggNames, List.mem_cons, List.mem_append] at h
    simp only [XTotal]
    refine exists_congr fun x => exists_congr fun bs => and_congr_right' (and_congr_right'
      (exists_congr fun rows => and_congr_right'
      (and_congr_left' (forall_congr' fun row => iff_congr Iff.rfl ?_))))
    refine ⟨fun ⟨hl, hr, hs⟩ => ⟨hl, hr, ?_⟩, fun ⟨hl, hr, hs⟩ => ⟨hl, hr, ?_⟩⟩
    · exact (xsat_congr_names b _ _ j
        (fun y hy => Dogwood.Thm.bindAll_congr hl y (.inr (h y (by simp [hy]))))).mp hs
    · exact (xsat_congr_names b _ _ j
        (fun y hy => Dogwood.Thm.bindAll_congr hl y (.inr (h y (by simp [hy]))))).mpr hs
  | .call _, _, _, _, _, _ => Iff.rfl

end

/-- **A leaf without fresh names ignores the rewrite's bindings.** -/
theorem xsat_congr_fresh {pre : String} {c : Condition} (hc : NoFreshNames pre c)
    {v v' : Valuation} (h : AgreeOff pre v v') (j : Nat) :
    XSat ι rate σ e vis ord dom v' j c ↔ XSat ι rate σ e vis ord dom v j c :=
  xsat_congr_names c v' v j fun y hy => h y (hc y hy)

end

end Dogwood.Thm.Frontend
