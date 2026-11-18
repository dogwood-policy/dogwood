import Dogwood.Eval.Safety
import Dogwood.Eval.Typing
import Dogwood.Thm.SafetyDecide
import Dogwood.Thm.TypingDecide

/-!
# Acceptance: unit tests for the reference checker

The unit tests of the reference checker (`extension/temporal/check.rs`), restated against the
specification's safety (`Formula.IsSafe`) and typing (`Formula.WellTyped`), in a small test
schema (`ctx`). `accepted φ` is both, decided (`Dogwood.Thm.isSafeB_iff`,
`Dogwood.Thm.Formula.check_eq_nil_iff`). Each example is checked by the kernel.

These complement the conformance runs (`Dogwood.Conformance`), which can only compare
conditions the crate accepts: the crate exposes no syntax tree for a condition it rejects.

Safety is order-independent, so the tests about the conjunct order hold the opposite
verdict for the conditions the reference rejects only because a conjunct comes before its
restrictor: those conditions are safe (see `## Conjunct order` below). Typing rejects what the
reference's binding check rejects for a reserved binder name, a misplaced aggregate, or a free
variable.
-/

namespace Dogwood.Examples.Acceptance

open Dogwood.Spec Dogwood.Spec.Temporal Dogwood.Eval
open Cedar.Spec (EntityUID EntityType)
open Cedar.Validation (CedarType)
open Cedar.Data (Map Set)

def drupeAction (a : String) : EntityUID := ⟨⟨"Action", ["Drupe"]⟩, a⟩

/-- `Drupe::Action::"a"::request{ … }` -/
def req (a : String) (args : List (Path × Term) := []) : Formula :=
  .pred (drupeAction a) "request" args

def v (x : String) : Term := .var x

def h1 : Window := ⟨1, .hours⟩

def ty (t : String) : BinderType := if t = "Timepoint" then .timepoint else .named [t]

/-- `exists (x : T). φ` -/
def ex (x t : String) (φ : Formula) : Formula := .exist ⟨x, ty t⟩ φ

/-- `count for (x₁ : T₁), …. where φ` -/
def count (dom : List (String × String)) (φ : Formula) : Term :=
  .agg (.count (dom.map fun (x, t) => ⟨x, ty t⟩) φ)

/-- `sum s for (x₁ : T₁), …. where φ` -/
def sum (s : String) (dom : List (String × String)) (φ : Formula) : Term :=
  .agg (.sum s (dom.map fun (x, t) => ⟨x, ty t⟩) φ)

/-- The fields every test event logs. -/
def testFields : List FieldDecl :=
  [⟨["input", "user"], .cedar .string, false⟩, ⟨["input", "amount"], .cedar .int, false⟩,
   ⟨["input", "recipient"], .cedar .string, false⟩, ⟨["input", "doc"], .cedar .string, false⟩]

/-- The actions of the tests, each with a `request` and a `response` kind. -/
def testActions : List String :=
  ["Login", "Logout", "Transfer", "Read", "Ping", "Open", "Close", "Pay", "A", "B"]

def testEvents : EventSchema :=
  testActions.flatMap fun a =>
    [⟨drupeAction a, "request", true, [], testFields⟩, ⟨drupeAction a, "response", false, [], testFields⟩]

/-- The typing context of the tests: a `Login` request of an `OAuthUser`, whose context's
`input` record has a `user` and an `amount`. -/
def oauthUser : EntityType := ⟨"OAuthUser", ["Drupe"]⟩

def testRequest : Cedar.Validation.RequestType where
  principal := oauthUser
  action := drupeAction "Login"
  resource := oauthUser
  context := Map.make [("input", .required (.record (Map.make
    [("user", .required .string), ("amount", .required .int)])))]

def testEnv : Cedar.Validation.TypeEnv where
  ets := Map.make [(oauthUser, .standard ⟨Set.empty, Map.empty, none⟩)]
  acts := Map.empty
  reqty := testRequest

def ctx : TypingCtx where
  env := testEnv
  events := testEvents
  maxWindow := defaultMaxWindow
  facts := []

/-- The condition is safe and well-typed: the counterpart of the reference checker's
`check_leaf`, which also rejects a conjunct that comes before its restrictor. -/
def accepted (φ : Formula) : Bool := isSafeB φ && (φ.check ctx []).isEmpty

theorem accepted_iff (φ : Formula) : accepted φ = true ↔ φ.IsSafe ∧ φ.WellTyped ctx [] := by
  simp [accepted, Dogwood.Thm.isSafeB_iff, List.isEmpty_iff, Dogwood.Thm.Formula.check_eq_nil_iff]

-- exists_restricted_by_predicate_field_is_safe
example : accepted (ex "x" "String" (req "Login" [(["input", "user"], v "x")])) = true := by decide +kernel

-- exists_restricted_by_tp_is_safe
example : accepted (ex "t" "Timepoint" (.tp "t")) = true := by decide +kernel

-- exists_restricted_by_agg_equality_is_safe
example : accepted (ex "n" "Long" (.and
    (.cmp .eq (count [("t", "Timepoint")] (.and (req "Login") (.tp "t"))) (v "n"))
    (.cmp .gt (v "n") (.long 0)))) = true := by decide +kernel

-- agg_for_var_absent_from_body_is_rejected
example : accepted (ex "n" "Long" (.and
    (.cmp .eq (count [("x", "String"), ("t", "Timepoint")] (.and (req "Login") (.tp "t"))) (v "n"))
    (.cmp .ge (v "n") (.long 1)))) = false := by decide +kernel

-- agg_for_var_used_positively_is_safe
example : accepted (ex "n" "Long" (.and
    (.cmp .eq (count [("x", "String"), ("t", "Timepoint")]
      (.and (req "Login" [(["input", "user"], v "x")]) (.tp "t"))) (v "n"))
    (.cmp .ge (v "n") (.long 1)))) = true := by decide +kernel

-- agg_sum_summand_for_var_is_safe
example : accepted (ex "s" "Long" (.and
    (.cmp .eq (sum "a" [("a", "Long"), ("t", "Timepoint")]
      (.and (req "Transfer" [(["input", "amount"], v "a")]) (.tp "t"))) (v "s"))
    (.cmp .ge (v "s") (.long 1)))) = true := by decide +kernel

-- exists_restricted_by_literal_equality_is_safe
example : accepted (ex "x" "Long" (.cmp .eq (v "x") (.long 5))) = true := by decide +kernel

-- exists_with_no_restrictor_is_rejected
example : accepted (ex "x" "Long" (.and (.cmp .lt (.long 0) (v "x")) (.cmp .lt (v "x") (.long 2)))) =
    false := by decide +kernel

-- exists_restricted_only_under_negation_is_rejected
example : accepted (ex "x" "String" (.not (req "Login" [(["input", "user"], v "x")]))) = false := by
  decide +kernel

-- negation_outside_a_closed_exists_is_safe
example : accepted (.not (ex "x" "String" (req "Login" [(["input", "user"], v "x")]))) = true := by
  decide +kernel

-- exists_restricted_under_formerly_is_safe
example : accepted (ex "x" "String" (.formerly h1 (req "Login" [(["input", "user"], v "x")]))) =
    true := by decide +kernel

-- exists_restricted_by_predicate_under_nested_exists_is_safe
example : accepted (ex "v" "String" (ex "g" "String"
    (req "Transfer" [(["input", "user"], v "v"), (["input", "recipient"], v "g")]))) = true := by
  decide +kernel

-- exists_with_only_inner_binder_restricted_is_rejected
example : accepted (ex "v" "String" (ex "g" "String" (req "Transfer" [(["input", "recipient"], v "g")]))) =
    false := by decide +kernel

-- nested_exists_restrictor_under_formerly_is_safe
example : accepted (ex "v" "String" (ex "g" "String" (.formerly h1
    (req "Transfer" [(["input", "user"], v "v"), (["input", "recipient"], v "g")])))) = true := by
  decide +kernel

-- nested_exists_restrictor_under_since_right_is_safe
example : accepted (ex "v" "String" (ex "g" "String" (.since (req "Ping") h1
    (req "Transfer" [(["input", "user"], v "v"), (["input", "recipient"], v "g")])))) = true := by
  decide +kernel

-- nested_exists_restrictor_only_in_since_left_is_rejected
example : accepted (ex "v" "String" (ex "g" "String" (.since
    (req "Transfer" [(["input", "user"], v "v")]) h1
    (req "Ping" [(["input", "recipient"], v "g")])))) = false := by decide +kernel

-- triple_nested_exists_outer_restricted_innermost_is_safe
example : accepted (ex "v" "String" (ex "g" "String" (ex "h" "String"
    (req "Transfer" [(["input", "user"], v "v"), (["input", "recipient"], v "g"),
      (["input", "doc"], v "h")])))) = true := by decide +kernel

-- nested_exists_binder_shadowing_is_rejected
example : accepted (ex "v" "String" (ex "v" "String" (req "Transfer" [(["input", "user"], v "v")]))) =
    false := by decide +kernel

-- shadowing_outer_binder_restricted_by_sibling_conjunct_is_safe
example : accepted (ex "v" "String" (.and (req "Login" [(["input", "user"], v "v")])
    (ex "v" "String" (req "Transfer" [(["input", "user"], v "v")])))) = true := by decide +kernel

-- shadowing_outer_restricted_but_inner_unrestricted_is_rejected
example : accepted (ex "v" "String" (.and (req "Login" [(["input", "user"], v "v")])
    (ex "v" "String" (req "Ping")))) = false := by decide +kernel

-- nested_exists_restrictor_via_conjunct_inside_inner_is_safe
example : accepted (ex "v" "String" (ex "g" "String" (.and (req "Login" [(["input", "user"], v "v")])
    (req "Transfer" [(["input", "recipient"], v "g")])))) = true := by decide +kernel

-- nested_exists_restrictor_only_under_negation_is_rejected
example : accepted (ex "v" "String" (ex "g" "String" (.and
    (req "Transfer" [(["input", "recipient"], v "g")])
    (.not (req "Login" [(["input", "user"], v "v")]))))) = false := by decide +kernel

-- aggregate_as_comparison_operand_is_accepted
example : accepted (.cmp .lt (.long 0) (count [("t", "Timepoint")] (.and (req "Login") (.tp "t")))) =
    true := by decide +kernel

-- aggregate_in_predicate_arg_is_rejected
example : accepted (req "Login" [(["input", "amount"], count [("t", "Timepoint")] (.tp "t"))]) =
    false := by decide +kernel

-- ordering_filter_after_restrictor_is_accepted
example : accepted (ex "a" "Long" (.and (.formerly h1 (req "Transfer" [(["input", "amount"], v "a")]))
    (.cmp .gt (v "a") (.long 100)))) = true := by decide +kernel

-- ordering_filter_before_restrictor_is_rejected
-- The reference rejects this condition for its conjunct order only; it is safe.
example : accepted (ex "a" "Long" (.and (.cmp .gt (v "a") (.long 100))
    (.formerly h1 (req "Transfer" [(["input", "amount"], v "a")])))) = true := by decide +kernel

-- ordering_filter_between_restrictors_is_accepted
example : accepted (ex "a" "Long" (.and (.and
    (.formerly h1 (req "Transfer" [(["input", "amount"], v "a")]))
    (.cmp .gt (v "a") (.long 100))) (.formerly h1 (req "Login")))) = true := by decide +kernel

-- guarded_negation_after_restrictor_is_accepted
example : accepted (ex "u" "String" (.and (.formerly h1 (req "Login" [(["input", "user"], v "u")]))
    (.not (.formerly h1 (req "Logout" [(["input", "user"], v "u")]))))) = true := by decide +kernel

-- negation_before_restrictor_is_rejected
-- The reference rejects this condition for its conjunct order only; it is safe.
example : accepted (ex "u" "String" (.and (.not (.formerly h1 (req "Logout" [(["input", "user"], v "u")])))
    (.formerly h1 (req "Login" [(["input", "user"], v "u")])))) = true := by decide +kernel

-- migration_shape_agg_eq_then_filter_is_accepted
example : accepted (ex "n" "Long" (.and
    (.cmp .eq (count [("t", "Timepoint")] (.formerly h1 (.and (req "Login") (.tp "t")))) (v "n"))
    (.cmp .gt (v "n") (.long 0)))) = true := by decide +kernel

-- rejects_{principal,resource,context,action}_as_exists_binder
example : ["principal", "resource", "context", "action"].all (fun x =>
    !accepted (ex x "String" (.formerly h1 (req "Login" [(["input", "user"], v x)])))) = true := by
  decide +kernel

-- rejects_{principal,resource}_as_tp_binder
example : ["principal", "resource"].all (fun x =>
    !accepted (ex "t" "Timepoint" (.and (.tp "t") (.tp x)))) = true := by decide +kernel

-- rejects_{context,principal}_as_for_binder
example : ["context", "principal"].all (fun x =>
    !accepted (ex "n" "Long" (.and
      (.cmp .eq (count [(x, "Timepoint")] (.formerly h1 (.and (req "Login") (.tp x)))) (v "n"))
      (.cmp .gt (v "n") (.long 0))))) = true := by decide +kernel

-- non_reserved_binders_stay_accepted
example : accepted (ex "user" "String" (.formerly h1 (req "Login" [(["input", "user"], v "user")]))) =
    true := by decide +kernel

-- agg_for_var_only_under_negation_is_rejected
example : accepted (ex "nn" "Long" (.and
    (.cmp .eq (count [("x", "String")] (.not (.formerly h1 (req "Login" [(["input", "user"], v "x")]))))
      (v "nn"))
    (.cmp .ge (v "nn") (.long 1)))) = false := by decide +kernel

-- sum_summand_only_under_negation_is_rejected
example : accepted (ex "nn" "Long" (.and
    (.cmp .eq (sum "a" [("a", "Long")] (.not (.formerly h1 (req "Transfer" [(["input", "amount"], v "a")]))))
      (v "nn"))
    (.cmp .eq (v "nn") (.long 0)))) = false := by decide +kernel

-- agg_for_var_only_in_since_left_is_rejected
example : accepted (ex "nn" "Long" (.and
    (.cmp .eq (count [("w", "String")] (.since (req "Read" [(["input", "user"], v "w")]) h1 (req "Login")))
      (v "nn"))
    (.cmp .ge (v "nn") (.long 1)))) = false := by decide +kernel

-- agg_for_var_in_since_right_is_accepted
example : accepted (ex "nn" "Long" (.and
    (.cmp .eq (count [("w", "String")] (.since (req "Ping") h1 (req "Login" [(["input", "user"], v "w")])))
      (v "nn"))
    (.cmp .ge (v "nn") (.long 1)))) = true := by decide +kernel

-- agg_for_var_guarded_negation_stays_accepted
example : accepted (ex "n" "Long" (.and
    (.cmp .eq (count [("q", "String")] (.and
        (.formerly h1 (req "Transfer" [(["input", "user"], v "q")]))
        (.not (ex "r" "Timepoint" (.formerly h1 (.and (req "Logout" [(["input", "user"], v "q")])
          (.tp "r")))))))
      (v "n"))
    (.cmp .ge (v "n") (.long 2)))) = true := by decide +kernel

-- agg_correlated_with_enclosing_binder_stays_accepted
example : accepted (ex "u" "String" (.and (.formerly h1 (req "Login" [(["input", "user"], v "u")]))
    (.cmp .ge (count [("t", "Timepoint")]
      (.formerly h1 (.and (req "Transfer" [(["input", "user"], v "u")]) (.tp "t")))) (.long 2)))) =
    true := by decide +kernel

-- exists_restricted_only_by_double_negation_is_rejected
example : accepted (ex "x" "String" (.not (.not (.formerly h1 (req "Login" [(["input", "user"], v "x")]))))) =
    false := by decide +kernel

-- exists_restrictor_beside_double_negation_stays_accepted
example : accepted (ex "x" "String" (.and (.formerly h1 (req "Login" [(["input", "user"], v "x")]))
    (.not (.not (.formerly h1 (req "Login" [(["input", "user"], v "x")])))))) = true := by decide +kernel

-- leaf_free_var_in_filter_is_rejected
example : accepted (Formula.and (.formerly h1 (req "Transfer" [(["input", "amount"], v "a")]))
    (.cmp .gt (v "a") (.long 100))) = false := by decide +kernel

-- leaf_free_var_guarded_negation_is_rejected
example : accepted (Formula.and (.formerly h1 (req "Login" [(["input", "user"], v "u")]))
    (.not (.formerly h1 (req "Logout" [(["input", "user"], v "u")])))) = false := by
  decide +kernel

-- leaf_single_use_free_var_is_rejected
example : accepted (Formula.formerly h1 (req "Login" [(["input", "user"], v "u")])) = false := by
  decide +kernel

-- leaf_free_tp_binder_is_rejected
example : accepted (Formula.formerly h1 (.and (req "Login") (.tp "t"))) = false := by decide +kernel

-- closed_leaves_stay_accepted
example : accepted (Formula.and
    (.formerly h1 (req "Login" [(["input", "user"], .context ["input", "user"])]))
    (.not (req "Logout" [(["input", "user"], .context ["input", "user"])]))) = true := by
  decide +kernel
example : accepted (ex "a" "Long" (.and (.formerly h1 (req "Transfer" [(["input", "amount"], v "a")]))
    (.cmp .gt (v "a") (.long 100)))) = true := by decide +kernel
example : accepted (ex "n" "Long" (.and
    (.cmp .eq (count [("t", "Timepoint")] (.formerly h1 (.and (req "Login") (.tp "t")))) (v "n"))
    (.cmp .gt (v "n") (.long 0)))) = true := by decide +kernel

/-! ## Conjunct order

The reference checker walks each `&&` chain left to right. Safety is a closure, so a conjunct
may read a variable that a later conjunct restricts. Every test below that the reference
rejects only for the order of its conjuncts is safe, and the tests say so. -/

def user (x : String) : List (Path × Term) := [(["input", "user"], v x)]
def amount (x : String) : List (Path × Term) := [(["input", "amount"], v x)]

/-- `count for (t : Timepoint). where (formerly within 1h (Drupe::Action::"a"::request{ input.user: u } && tp(t)))` -/
def countBy (a u : String) (args : String → List (Path × Term) := user) : Term :=
  count [("t", "Timepoint")] (.formerly h1 (.and (req a (args u)) (.tp "t")))

-- agg_eq_correlated_var_restricted_after_is_rejected
-- The reference rejects this condition for its conjunct order only; it is safe.
example : accepted (ex "u" "String" (ex "n" "Long" (.and
    (.and (.cmp .eq (countBy "Login" "u") (v "n")) (.cmp .ge (v "n") (.long 2)))
    (.formerly h1 (req "Login" (user "u")))))) = true := by decide +kernel

-- agg_eq_correlated_var_restricted_before_stays_accepted
example : accepted (ex "u" "String" (ex "n" "Long" (.and
    (.and (.formerly h1 (req "Login" (user "u"))) (.cmp .eq (countBy "Login" "u") (v "n")))
    (.cmp .ge (v "n") (.long 2))))) = true := by decide +kernel

-- agg_eq_correlated_var_restricted_in_enclosing_chain_stays_accepted
example : accepted (ex "u" "String" (.and (.formerly h1 (req "Login" (user "u")))
    (ex "n" "Long" (.and (.cmp .eq (countBy "Login" "u") (v "n")) (.cmp .ge (v "n") (.long 2)))))) =
    true := by decide +kernel

-- agg_eq_correlated_var_restricted_only_after_nested_exists_is_rejected
-- The reference rejects this condition for its conjunct order only; it is safe.
example : accepted (ex "u" "String" (.and
    (ex "n" "Long" (.and (.cmp .eq (countBy "Login" "u") (v "n")) (.cmp .ge (v "n") (.long 2))))
    (.formerly h1 (req "Login" (user "u"))))) = true := by decide +kernel

-- agg_eq_shadowing_binder_cuts_inherited_restriction
-- The reference rejects this condition for its conjunct order only; it is safe.
example : accepted (ex "u" "String" (.and (.formerly h1 (req "Login" (user "u")))
    (ex "u" "String" (ex "n" "Long" (.and
      (.and (.cmp .eq (countBy "Transfer" "u") (v "n")) (.cmp .ge (v "n") (.long 1)))
      (.formerly h1 (req "Transfer" (user "u")))))))) = true := by decide +kernel

-- not_equal_is_a_pure_filter_in_the_demands_walk
-- The reference rejects this condition for its conjunct order only; it is safe.
example : accepted (ex "a" "Long" (.and (.cmp .ne (v "a") (.long 5))
    (.formerly h1 (req "Transfer" (amount "a"))))) = true := by decide +kernel
example : accepted (ex "a" "Long" (.and (.formerly h1 (req "Transfer" (amount "a")))
    (.cmp .ne (v "a") (.long 5)))) = true := by decide +kernel

-- parenthesized_subchain_inherits_preceding_restrictors
example : accepted (ex "a" "Long" (.and (.formerly h1 (req "Transfer" (amount "a")))
    (.and (.cmp .gt (v "a") (.long 100)) (.formerly h1 (req "Login"))))) = true := by decide +kernel
-- The reference rejects this condition for its conjunct order only; it is safe.
example : accepted (ex "a" "Long" (.and
    (.and (.cmp .gt (v "a") (.long 100)) (.formerly h1 (req "Transfer" (amount "a"))))
    (.formerly h1 (req "Login")))) = true := by decide +kernel

-- self_referential_agg_equality_is_rejected
example : accepted (ex "u" "Long" (.cmp .eq (countBy "Transfer" "u" amount) (v "u"))) = false := by
  decide +kernel
example : accepted (ex "u" "Long" (.and (.formerly h1 (req "Transfer" (amount "u")))
    (.cmp .eq (countBy "Transfer" "u" amount) (v "u")))) = true := by decide +kernel

-- shadowing_for_binder_does_not_inherit_the_seed
-- The reference rejects this condition for its conjunct order only; it is safe.
example : accepted (ex "u" "Long" (.and (.formerly h1 (req "Transfer" (amount "u")))
    (.cmp .ge (count [("u", "Long"), ("t", "Timepoint")] (.and (.cmp .gt (v "u") (.long 100))
      (.formerly h1 (.and (req "Transfer" (amount "u")) (.tp "t"))))) (.long 1)))) = true := by
  decide +kernel
-- The reference rejects this condition for its conjunct order only; it is safe.
example : accepted (ex "u" "Long" (.and (.formerly h1 (req "Transfer" (amount "u")))
    (.cmp .ge (count [("w", "Long"), ("t", "Timepoint")] (.and (.cmp .gt (v "w") (.long 100))
      (.formerly h1 (.and (req "Transfer" (amount "w")) (.tp "t"))))) (.long 1)))) = true := by
  decide +kernel
example : accepted (ex "u" "Long" (.and (.formerly h1 (req "Transfer" (amount "u")))
    (.cmp .ge (count [("t", "Timepoint")] (.and (.cmp .gt (v "u") (.long 100))
      (.formerly h1 (.and (req "Login") (.tp "t"))))) (.long 1)))) = true := by decide +kernel

-- since_left_demand_propagates_through_formerly
-- The reference rejects this condition for its conjunct order only; it is safe.
example : accepted (ex "u" "String" (.and
    (.formerly h1 (.since (req "Read" (user "u")) h1 (req "Login")))
    (.formerly h1 (req "Transfer" (user "u"))))) = true := by decide +kernel

-- since_left_var_restricted_after_is_rejected
-- The reference rejects this condition for its conjunct order only; it is safe.
example : accepted (ex "u" "String" (.and (.since (req "Read" (user "u")) h1 (req "Login"))
    (.formerly h1 (req "Transfer" (user "u"))))) = true := by decide +kernel

-- since_left_var_restricted_before_stays_accepted
example : accepted (ex "u" "String" (.and (.formerly h1 (req "Transfer" (user "u")))
    (.since (req "Read" (user "u")) h1 (req "Login")))) = true := by decide +kernel

-- since_left_var_restricted_by_anchor_stays_accepted
example : accepted (ex "u" "String" (.since (req "Read" (user "u")) h1 (req "Login" (user "u")))) =
    true := by decide +kernel

-- wildcard_equality_is_not_a_restrictor
example : accepted (ex "x" "String" (.cmp .eq (v "x") .wildcard)) = false := by decide +kernel
example : accepted (ex "a" "Long" (.and (.cmp .eq (v "a") .wildcard) (.cmp .gt (v "a") (.long 100)))) =
    false := by decide +kernel

/-! ## Compound (arithmetic) operands -/

/-- `Drupe::Action::"a"::response{ … }` -/
def resp (a : String) (args : List (Path × Term) := []) : Formula :=
  .pred ⟨⟨"Action", ["Drupe"]⟩, a⟩ "response" args

-- aggregate_difference_operand_is_accepted
example : accepted (.cmp .le
    (.arith .sub (count [("t", "Timepoint")] (.and (req "Open") (.tp "t")))
      (count [("t", "Timepoint")] (.and (resp "Close") (.tp "t"))))
    (.long 10)) = true := by decide +kernel

-- compound_equality_binds_the_bare_variable_side
example : accepted (ex "n1" "Long" (.and (req "A" [(["input", "amount"], v "n1")])
    (ex "n2" "Long" (.and (req "B" [(["input", "amount"], v "n2")])
      (ex "m" "Long" (.and (.cmp .eq (.arith .add (v "n1") (v "n2")) (v "m"))
        (.cmp .gt (v "m") (.long 5)))))))) = true := by decide +kernel

-- no_algebraic_solving_through_a_compound
example : accepted (ex "m" "Long" (.cmp .eq (.arith .add (v "m") (.long 1)) (.long 5))) = false := by
  decide +kernel

-- compound_filter_demands_its_variables
-- The reference rejects this condition for its conjunct order only; it is safe.
example : accepted (ex "a" "Long" (.and (.cmp .gt (.arith .add (v "a") (.long 1)) (.long 2))
    (req "A" [(["input", "amount"], v "a")]))) = true := by decide +kernel
example : accepted (ex "a" "Long" (.and (req "A" [(["input", "amount"], v "a")])
    (.cmp .gt (.arith .add (v "a") (.long 1)) (.long 2)))) = true := by decide +kernel

-- wildcard_compound_is_not_a_restrictor
example : accepted (ex "m" "Long" (.cmp .eq (v "m") (.arith .mul .wildcard (.long 2)))) = false := by
  decide +kernel

-- aggregate_leaves_of_a_compound_get_for_domain_checks
example : accepted (.cmp .le
    (.arith .add (count [("x", "String")] (.not (.formerly h1 (req "A" [(["input", "user"], v "x")]))))
      (.long 1))
    (.long 5)) = false := by decide +kernel

-- arithmetic_in_predicate_arg_is_rejected_as_placement_error
example : accepted (req "Pay" [(["input", "amount"], .arith .add (.long 1) (.long 2))]) = false := by
  decide +kernel

/-- Why the restriction closure is least: two equalities that each bind one variable from the
other are well-typed, but the pairs that satisfy them form an infinite set. Safety rejects the
aggregate, because neither equality's variable is restricted unless the other's already is. -/
def circular : Formula :=
  .cmp .ge (count [("x", "Long"), ("y", "Long")]
      (.and (.cmp .eq (v "x") (.arith .add (v "y") (.long 1)))
        (.cmp .eq (v "y") (.arith .sub (v "x") (.long 1)))))
    (.long 0)

example : (circular.check ctx []).isEmpty = true := by decide +kernel
example : isSafeB circular = false := by decide +kernel

end Dogwood.Examples.Acceptance
