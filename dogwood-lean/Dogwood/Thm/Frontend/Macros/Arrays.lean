import Dogwood.Thm.Frontend.Macros.Expand
import Dogwood.Thm.Frontend.Macros.Safety

/-!
# Array constants, and what an accepted block is

* `rejectArrays_ok`: a set passes `rejectArrays` iff none of its temporal blocks holds an array
  constant (`condHasArray`), in a predicate argument or a comparison operand, also inside
  an aggregate's body and an arithmetic operand.
* `cond_projects`: a temporal condition with no macro syntax, no array constant, no
  internal disjunction and every scope field rooted at `principal` or `resource` (what the parser
  produces) projects to a formula of the specification.
* `accepted_safe`: so every temporal block of a set that expansion and the array check accept
  projects to a formula of the specification, and that formula is safe (`Formula.IsSafe`).
* `rejectArrays_arith`: an array constant in the body of an aggregate that is an arithmetic
  operand is rejected, though expansion accepts the set (arithmetic is experimental in the
  crate).
-/

namespace Dogwood.Thm.Frontend.Macros

open Dogwood.Frontend Dogwood.Frontend.Macros
open Dogwood.Frontend.Surface (Expr ExprKind PolicySet MacroDef Policy Cond)
open Dogwood.Frontend.Surface.Temporal

/-! ## The array check -/

theorem rejectArrays_ok {ps : PolicySet} :
    rejectArrays ps = .ok () ↔
      ∀ p ∈ ps.policies, ∀ x ∈ policyBlocks p, condHasArray x.2.condition = false := by
  unfold rejectArrays
  cases hf : (ps.policies.flatMap policyBlocks).find?
      (fun (_, b) => condHasArray b.condition) with
  | none =>
    simp only [pure_eq_ok, true_iff]
    intro p hp x hx
    have := List.find?_eq_none.mp hf x (List.mem_flatMap.mpr ⟨p, hp, hx⟩)
    simpa using this
  | some y =>
    obtain ⟨sp, b⟩ := y
    simp only [throw_ne_ok, false_iff]
    intro hall
    have hm := List.mem_of_find?_eq_some hf
    have hy := List.find?_some hf
    obtain ⟨p, hp, hx⟩ := List.mem_flatMap.mp hm
    have := hall p hp _ hx
    simp_all

/-! ## Projecting a clean condition -/

theorem splitOnAux_ne_nil (s sep : String) (b i j : String.Pos.Raw) (r : List String) :
    String.splitOnAux s sep b i j r ≠ [] := by
  fun_induction String.splitOnAux s sep b i j r <;> simp_all

theorem splitOn_ne_nil (s sep : String) : s.splitOn sep ≠ [] := by
  unfold String.splitOn
  split
  · simp
  · exact splitOnAux_ne_nil _ _ _ _ _ _

theorem entityUid_ok (ty id : String) : ∃ u, entityUid ty id = .ok u := by
  unfold entityUid
  have := splitOn_ne_nil ty "::"
  simp only
  cases h : (ty.splitOn "::").getLast? with
  | none => simp [List.getLast?_eq_none_iff] at h; exact absurd h this
  | some last => exact ⟨_, rfl⟩

mutual

/-- No internal disjunction, and every scope field rooted at `principal` or `resource`: what the
parser produces (the relativization rewrite, after this stage, is what builds disjunctions). -/
def condRooted : Condition → Bool
  | ⟨_, .or _ _⟩ => false
  | ⟨_, .and l r⟩ => condRooted l && condRooted r
  | ⟨_, .since l _ r⟩ => condRooted l && condRooted r
  | ⟨_, .not c⟩ => condRooted c
  | ⟨_, .formerly _ c⟩ => condRooted c
  | ⟨_, .previous _ c⟩ => condRooted c
  | ⟨_, .exists _ c⟩ => condRooted c
  | ⟨_, .predicate ⟨_, _, _, _, args⟩⟩ => argsRooted args
  | ⟨_, .comparison _ l r⟩ => termRooted l && termRooted r
  | ⟨_, .refine b fs _⟩ => condRooted b && argsRooted fs
  | ⟨_, .tp _⟩ => true
  | ⟨_, .call _⟩ => true
  | ⟨_, .sigilRef _ _⟩ => true

def argsRooted : List NamedArg → Bool
  | [] => true
  | ⟨_, t⟩ :: rest => termRooted t && argsRooted rest

def termRooted : Term → Bool
  | .scopeField ("principal" :: _) => true
  | .scopeField ("resource" :: _) => true
  | .scopeField _ => false
  | .agg ⟨_, .sum _ _ b⟩ => condRooted b
  | .agg ⟨_, .count _ b⟩ => condRooted b
  | .arith _ l r => termRooted l && termRooted r
  | _ => true

end

/-- An aggregation holds an array constant in its body. -/
def aggHasArray : AggExprKind → Bool
  | .sum _ _ b => condHasArray b
  | .count _ b => condHasArray b
  | .call _ => false

def aggRooted : AggExprKind → Bool
  | .sum _ _ b => condRooted b
  | .count _ b => condRooted b
  | .call _ => true

theorem slot_name {sp : Span} {s : BinderSlot} (h : noResidueSlot sp s = .ok ()) :
    ∃ n, s = .name n := by
  cases s <;> simp_all [noResidueSlot, residue, err_ne_ok]

theorem binders_project {sp : Span} : {vs : List TypedBinder} →
    (vs.forM fun v => noResidueSlot sp v.slot) = .ok () →
    ∃ dom, vs.mapM TypedBinder.toSpec = .ok dom
  | [], _ => ⟨[], rfl⟩
  | ⟨s, ty⟩ :: rest, h => by
    rw [forM_eq_ok] at h
    obtain ⟨n, rfl⟩ := slot_name (h ⟨s, ty⟩ List.mem_cons_self)
    obtain ⟨dom, hd⟩ := binders_project (vs := rest)
      (forM_eq_ok.mpr fun v hv => h v (List.mem_cons_of_mem _ hv))
    exact ⟨⟨n, ty⟩ :: dom, by simp only [List.mapM_cons, hd]; rfl⟩

mutual

theorem cond_projects : (c : Condition) → noResidue c = .ok () → condHasArray c = false →
    condRooted c = true → ∃ φ, c.toFormula = .ok φ
  | ⟨_, .and l r⟩, hr, ha, hro => by
    simp only [noResidue, seq_eq_ok] at hr
    simp only [condHasArray, Bool.or_eq_false_iff] at ha
    simp only [condRooted, Bool.and_eq_true] at hro
    obtain ⟨a, hl⟩ := cond_projects l hr.1 ha.1 hro.1
    obtain ⟨b, hr'⟩ := cond_projects r hr.2 ha.2 hro.2
    exact ⟨.and a b, by simp only [Condition.toFormula, ConditionKind.toFormula, hl, hr']; rfl⟩
  | ⟨_, .or _ _⟩, _, _, hro => by simp [condRooted] at hro
  | ⟨_, .not c⟩, hr, ha, hro => by
    simp only [noResidue] at hr
    simp only [condHasArray] at ha
    simp only [condRooted] at hro
    obtain ⟨a, hc⟩ := cond_projects c hr ha hro
    exact ⟨.not a, by simp only [Condition.toFormula, ConditionKind.toFormula, hc]; rfl⟩
  | ⟨_, .formerly w c⟩, hr, ha, hro => by
    simp only [noResidue, seq_eq_ok] at hr
    simp only [condHasArray] at ha
    simp only [condRooted] at hro
    obtain ⟨a, hc⟩ := cond_projects c hr.2 ha hro
    cases w with
    | paramRef _ => simp [noResidueWithin, residue, err_ne_ok] at hr
    | concrete i =>
      exact ⟨.formerly ⟨i.amount.toInt, i.unit⟩ a,
        by simp only [Condition.toFormula, ConditionKind.toFormula, hc]; rfl⟩
  | ⟨_, .previous w c⟩, hr, ha, hro => by
    simp only [noResidue, seq_eq_ok] at hr
    simp only [condHasArray] at ha
    simp only [condRooted] at hro
    obtain ⟨a, hc⟩ := cond_projects c hr.2 ha hro
    cases w with
    | paramRef _ => simp [noResidueWithin, residue, err_ne_ok] at hr
    | concrete i =>
      exact ⟨.previous ⟨i.amount.toInt, i.unit⟩ a,
        by simp only [Condition.toFormula, ConditionKind.toFormula, hc]; rfl⟩
  | ⟨_, .since l w r⟩, hr, ha, hro => by
    simp only [noResidue, seq_eq_ok] at hr
    simp only [condHasArray, Bool.or_eq_false_iff] at ha
    simp only [condRooted, Bool.and_eq_true] at hro
    obtain ⟨a, hl⟩ := cond_projects l hr.2.1 ha.1 hro.1
    obtain ⟨b, hr'⟩ := cond_projects r hr.2.2 ha.2 hro.2
    cases w with
    | paramRef _ => simp [noResidueWithin, residue, err_ne_ok] at hr
    | concrete i =>
      exact ⟨.since a ⟨i.amount.toInt, i.unit⟩ b,
        by simp only [Condition.toFormula, ConditionKind.toFormula, hl, hr']; rfl⟩
  | ⟨_, .predicate ⟨_, ns, act, k, args⟩⟩, hr, ha, hro => by
    simp only [noResidue] at hr
    simp only [condHasArray] at ha
    simp only [condRooted] at hro
    obtain ⟨args', hargs⟩ := args_project args hr ha hro
    obtain ⟨u, hu⟩ := entityUid_ok ("::".intercalate ns) act
    exact ⟨.pred u k args', by
      simp only [Condition.toFormula, ConditionKind.toFormula, hu, hargs]; rfl⟩
  | ⟨_, .comparison op l r⟩, hr, ha, hro => by
    simp only [noResidue, seq_eq_ok] at hr
    simp only [condHasArray, Bool.or_eq_false_iff] at ha
    simp only [condRooted, Bool.and_eq_true] at hro
    obtain ⟨l', hl⟩ := term_projects l hr.1 ha.1 hro.1
    obtain ⟨r', hr'⟩ := term_projects r hr.2 ha.2 hro.2
    exact ⟨.cmp op l' r', by simp only [Condition.toFormula, ConditionKind.toFormula, hl, hr']; rfl⟩
  | ⟨_, .exists ⟨s, ty⟩ c⟩, hr, ha, hro => by
    simp only [noResidue, seq_eq_ok] at hr
    simp only [condHasArray] at ha
    simp only [condRooted] at hro
    obtain ⟨n, rfl⟩ := slot_name hr.1
    obtain ⟨a, hc⟩ := cond_projects c hr.2 ha hro
    exact ⟨.exist ⟨n, ty⟩ a, by
      simp only [Condition.toFormula, ConditionKind.toFormula, TypedBinder.toSpec,
        BinderSlot.toName, hc]; rfl⟩
  | ⟨_, .tp s⟩, hr, _, _ => by
    simp only [noResidue] at hr
    obtain ⟨n, rfl⟩ := slot_name hr
    exact ⟨.tp n, rfl⟩
  | ⟨_, .call _⟩, hr, _, _ => by simp [noResidue, residue, err_ne_ok] at hr
  | ⟨_, .sigilRef s _⟩, hr, _, _ => by cases s <;> simp [noResidue, residue, err_ne_ok] at hr
  | ⟨_, .refine _ _ _⟩, hr, _, _ => by simp [noResidue, residue, err_ne_ok] at hr

theorem args_project : (args : List NamedArg) → {sp : Span} → noResidueArgs sp args = .ok () →
    argsHaveArray args = false → argsRooted args = true →
    ∃ args', NamedArg.toSpecList args = .ok args'
  | [], _, _, _, _ => ⟨[], rfl⟩
  | ⟨n, t⟩ :: rest, _, hr, ha, hro => by
    simp only [noResidueArgs, seq_eq_ok] at hr
    simp only [argsHaveArray, Bool.or_eq_false_iff] at ha
    simp only [argsRooted, Bool.and_eq_true] at hro
    obtain ⟨t', ht⟩ := term_projects t hr.1 ha.1 hro.1
    obtain ⟨rest', hrest⟩ := args_project rest hr.2 ha.2 hro.2
    exact ⟨(fieldPathSplit n, t') :: rest', by simp only [NamedArg.toSpecList, ht, hrest]; rfl⟩

theorem term_projects : (t : Term) → {sp : Span} → noResidueTerm sp t = .ok () →
    termHasArray t = false → termRooted t = true → ∃ t', t.toSpec = .ok t'
  | .entity ty id, _, _, _, _ => by
    obtain ⟨u, hu⟩ := entityUid_ok ty id
    exact ⟨.entity u, by simp only [Term.toSpec, hu]; rfl⟩
  | .integer _, _, _, _, _ => ⟨_, rfl⟩
  | .decimal _, _, _, _, _ => ⟨_, rfl⟩
  | .string _, _, _, _, _ => ⟨_, rfl⟩
  | .bool _, _, _, _, _ => ⟨_, rfl⟩
  | .contextField _, _, _, _, _ => ⟨_, rfl⟩
  | .var _, _, _, _, _ => ⟨_, rfl⟩
  | .wildcard, _, _, _, _ => ⟨_, rfl⟩
  | .scopeField [], _, _, _, hro => by simp [termRooted] at hro
  | .scopeField (hd :: tl), _, _, _, hro => by
    by_cases h1 : hd = "principal"
    · subst h1; exact ⟨_, rfl⟩
    · by_cases h2 : hd = "resource"
      · subst h2; exact ⟨_, rfl⟩
      · simp [termRooted, h1, h2] at hro
  | .array _, _, _, ha, _ => by simp [termHasArray] at ha
  | .agg ⟨_, k⟩, _, hr, ha, hro => by
    simp only [noResidueTerm] at hr
    obtain ⟨a, hk⟩ := agg_projects k hr (by cases k <;> simp_all [termHasArray, aggHasArray])
      (by cases k <;> simp_all [termRooted, aggRooted])
    exact ⟨.agg a, by simp only [Term.toSpec, hk]; rfl⟩
  | .arith op l r, _, hr, ha, hro => by
    simp only [noResidueTerm, seq_eq_ok] at hr
    simp only [termHasArray, Bool.or_eq_false_iff] at ha
    simp only [termRooted, Bool.and_eq_true] at hro
    obtain ⟨l', hl⟩ := term_projects l hr.1 ha.1 hro.1
    obtain ⟨r', hr'⟩ := term_projects r hr.2 ha.2 hro.2
    exact ⟨.arith op l' r', by simp only [Term.toSpec, hl, hr']; rfl⟩
  | .paramRef _, _, hr, _, _ => by simp [noResidueTerm, residue, err_ne_ok] at hr
  | .binderRef _, _, hr, _, _ => by simp [noResidueTerm, residue, err_ne_ok] at hr

theorem agg_projects : (k : AggExprKind) → {asp : Span} → noResidueAgg asp k = .ok () →
    aggHasArray k = false → aggRooted k = true → ∃ a, AggExprKind.toSpec k = .ok a
  | .sum bv vs b, _, hr, ha, hro => by
    simp only [noResidueAgg, seq_eq_ok] at hr
    obtain ⟨n, rfl⟩ := slot_name hr.1
    obtain ⟨dom, hd⟩ := binders_project hr.2.1
    obtain ⟨body, hb⟩ := cond_projects b hr.2.2 ha hro
    exact ⟨.sum n dom body, by
      simp only [AggExprKind.toSpec, BinderSlot.toName, hd, hb]; rfl⟩
  | .count vs b, _, hr, ha, hro => by
    simp only [noResidueAgg, seq_eq_ok] at hr
    obtain ⟨dom, hd⟩ := binders_project hr.1
    obtain ⟨body, hb⟩ := cond_projects b hr.2 ha hro
    exact ⟨.count dom body, by simp only [AggExprKind.toSpec, hd, hb]; rfl⟩
  | .call _, _, hr, _, _ => by simp [noResidueAgg, residue, err_ne_ok] at hr

end

/-! ## Every accepted block projects to a safe formula -/

/-- What a temporal block of a macro-free expression satisfies. -/
def BlockOk (ck : Bool) (x : Span × Block) : Prop :=
  noResidue x.2.condition = .ok () ∧ (ck = true → checkLeaf x.2.condition = .ok ())

mutual

theorem macroFree_blocks : (e : Expr) → {ck : Bool} → MacroFreeE ck e → ∀ x ∈ exprBlocks e, BlockOk ck x
  | ⟨.extension t, sp⟩, _, h, x, hx => by
    simp only [exprBlocks, List.mem_singleton] at hx
    subst hx
    exact h
  | ⟨.call _ args, _⟩, _, ⟨_, h⟩, x, hx => by
    simp only [exprBlocks] at hx
    exact macroFreeL_blocks args h x hx
  | ⟨.paramRef _, _⟩, _, h, _, _ => h.elim
  | ⟨.lit _, _⟩, _, _, x, hx => by simp [exprBlocks] at hx
  | ⟨.var _, _⟩, _, _, x, hx => by simp [exprBlocks] at hx
  | ⟨.slot _, _⟩, _, _, x, hx => by simp [exprBlocks] at hx
  | ⟨.unaryApp _ e, _⟩, _, h, x, hx => by
    simp only [exprBlocks] at hx
    exact macroFree_blocks e h x hx
  | ⟨.binaryApp _ l r, _⟩, _, ⟨h₁, h₂⟩, x, hx => by
    simp only [exprBlocks, List.mem_append] at hx
    rcases hx with hx | hx
    · exact macroFree_blocks l h₁ x hx
    · exact macroFree_blocks r h₂ x hx
  | ⟨.getAttr e _, _⟩, _, h, x, hx => by
    simp only [exprBlocks] at hx
    exact macroFree_blocks e h x hx
  | ⟨.hasAttr e _, _⟩, _, h, x, hx => by
    simp only [exprBlocks] at hx
    exact macroFree_blocks e h x hx
  | ⟨.like e _, _⟩, _, h, x, hx => by
    simp only [exprBlocks] at hx
    exact macroFree_blocks e h x hx
  | ⟨.is e _ none, _⟩, _, h, x, hx => by
    simp only [exprBlocks] at hx
    exact macroFree_blocks e h x hx
  | ⟨.is e _ (some y), _⟩, _, ⟨h₁, h₂⟩, x, hx => by
    simp only [exprBlocks, List.mem_append] at hx
    rcases hx with hx | hx
    · exact macroFree_blocks e h₁ x hx
    · exact macroFree_blocks y h₂ x hx
  | ⟨.ite c t e, _⟩, _, ⟨h₁, h₂, h₃⟩, x, hx => by
    simp only [exprBlocks, List.mem_append] at hx
    rcases hx with (hx | hx) | hx
    · exact macroFree_blocks c h₁ x hx
    · exact macroFree_blocks t h₂ x hx
    · exact macroFree_blocks e h₃ x hx
  | ⟨.set xs, _⟩, _, h, x, hx => by
    simp only [exprBlocks] at hx
    exact macroFreeL_blocks xs h x hx
  | ⟨.record es, _⟩, _, h, x, hx => by
    simp only [exprBlocks] at hx
    exact macroFreeR_blocks es h x hx
  | ⟨.methodCall r _ args, _⟩, _, ⟨h₁, h₂⟩, x, hx => by
    simp only [exprBlocks, List.mem_append] at hx
    rcases hx with hx | hx
    · exact macroFree_blocks r h₁ x hx
    · exact macroFreeL_blocks args h₂ x hx

theorem macroFreeL_blocks : (xs : List Expr) → {ck : Bool} → MacroFreeL ck xs →
    ∀ x ∈ exprsBlocks xs, BlockOk ck x
  | [], _, _, x, hx => by simp [exprsBlocks] at hx
  | e :: rest, _, ⟨h₁, h₂⟩, x, hx => by
    simp only [exprsBlocks, List.mem_append] at hx
    rcases hx with hx | hx
    · exact macroFree_blocks e h₁ x hx
    · exact macroFreeL_blocks rest h₂ x hx

theorem macroFreeR_blocks : (xs : List (String × Expr)) → {ck : Bool} → MacroFreeR ck xs →
    ∀ x ∈ entriesBlocks xs, BlockOk ck x
  | [], _, _, x, hx => by simp [entriesBlocks] at hx
  | (_, e) :: rest, _, ⟨h₁, h₂⟩, x, hx => by
    simp only [entriesBlocks, List.mem_append] at hx
    rcases hx with hx | hx
    · exact macroFree_blocks e h₁ x hx
    · exact macroFreeR_blocks rest h₂ x hx

end

/-- **What an accepted block is.** Every temporal block of a set that `expand` and
`rejectArrays` accept, if it has no internal disjunction and its scope fields are rooted at
`principal` or `resource` (as the parser guarantees), projects to a formula of the
specification, and that formula is safe. -/
theorem accepted_safe {ps ps' : PolicySet} (he : expand ps = .ok ps')
    (ha : rejectArrays ps' = .ok ()) {p : Policy} (hp : p ∈ ps'.policies) {x : Span × Block}
    (hx : x ∈ policyBlocks p) (hro : condRooted x.2.condition = true) :
    ∃ φ, x.2.condition.toFormula = .ok φ ∧ φ.IsSafe := by
  obtain ⟨-, hexp⟩ := expand_expanded he
  obtain ⟨c, hc, hxc⟩ := List.mem_flatMap.mp hx
  obtain ⟨hr, hl⟩ := macroFree_blocks c.body (hexp p hp c hc) x hxc
  obtain ⟨φ, hφ⟩ := cond_projects x.2.condition hr (rejectArrays_ok.mp ha p hp x hx) hro
  exact ⟨φ, hφ, checkLeaf_isSafe (hl rfl) hφ⟩

/-! ## An array constant under arithmetic -/

section ArithmeticArray

open Dogwood.Frontend.Surface (Scope)

def sp0 : Span := ⟨0, 0⟩
def cnd (k : ConditionKind) : Condition := ⟨sp0, k⟩

def arrayPred : Condition :=
  cnd (.predicate ⟨sp0, ["Repo", "Action"], "Open", "request", [⟨"input.repo", .array [.integer 1]⟩]⟩)

def arrayBody : Condition :=
  cnd (.formerly (.concrete ⟨1, .hours⟩) (cnd (.and arrayPred (cnd (.tp (.name "t"))))))

def arrayCount : Term := .agg ⟨sp0, .count [⟨.name "t", .timepoint⟩] arrayBody⟩

/-- `(count for (t: Timepoint). where (formerly within 1h
(Repo::Action::"Open"::request{ input.repo: [1] } && tp(t)))) - 0 <= 2`. -/
def arrayLeaf : Condition :=
  cnd (.comparison .le (.arith .sub arrayCount (.integer 0)) (.integer 2))

def arrayPolicy : Policy :=
  ⟨sp0, [], .permit, default, [⟨sp0, .when, ⟨.extension ⟨arrayLeaf, sp0⟩, sp0⟩⟩]⟩

def arraySet : PolicySet := ⟨[arrayPolicy], []⟩

/-- **An array constant under arithmetic is rejected**: expansion accepts the set, its block
holds an array constant inside the body of an aggregate that is an operand of `-`, and
`rejectArrays` rejects it, as the crate's `reject_temporal_arrays` does: its walk looks into
arithmetic operands. -/
theorem rejectArrays_arith :
    (expand arraySet).isOk = true ∧ condHasArray arrayLeaf = true ∧
      (rejectArrays arraySet).isOk = false := by
  decide +kernel

end ArithmeticArray

end Dogwood.Thm.Frontend.Macros
