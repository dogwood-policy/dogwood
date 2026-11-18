#!/usr/bin/env python3
"""Write the validity and runtime probes of conformance/probes.

Usage: python3 conformance/probegen.py conformance/probes

Each probe is a bundle directory: a policy whose first comment says what it probes, the shared
action schema, and a trace. The timestamp probes are written by hand and left alone.
"""
import os, sys, textwrap
root = sys.argv[1]
SCHEMA = '''namespace Drupe {
  type LoginInput = { user: String };
  type ReadInput = { user: String, note?: String, level?: Long };
  entity Gateway;
  entity OAuthUser = { id: String, level: Long } tags String;
  action "Login" appliesTo {
    principal: [OAuthUser],
    resource: [Gateway],
    context: { input: LoginInput }
  };
  action "Read" appliesTo {
    principal: [OAuthUser],
    resource: [Gateway],
    context: { input: ReadInput }
  };
}
'''
def ev(ts, kind, action, user, extra_ctx='', extra_log='', entities='', principal='alice', caller=None):
    caller = caller or principal
    ctx = f'user: "{user}"' + extra_ctx
    ent = f' entities({entities})' if entities else ''
    return (f'@{ts} scope(principal: Drupe::OAuthUser::"{principal}", resource: Drupe::Gateway::"gw1"){ent} '
            f'request_context(input: {{ {ctx} }}) Drupe::Action::"{action}"::{kind}(input: {{ {ctx} }}, '
            f'callerPrincipal: Drupe::OAuthUser::"{caller}", callerResource: Drupe::Gateway::"gw1", requestId: "r{ts}"{extra_log})')
ALICE = 'Drupe::OAuthUser::"alice": { id: "alice", level: 5 }'
LOGIN_OK = [ev(0, 'request', 'Login', 'alice', entities=ALICE), ev(5, 'response', 'Login', 'alice', entities=ALICE)]
probes = {}
def probe(name, readme, policy, trace, schema=SCHEMA, extra=None):
    probes[name] = (readme, policy, trace, schema, extra or {})

READ_AFTER_LOGIN = '''@id("read_after_login")
permit (principal, action == Drupe::Action::"Read", resource)
when temporal {
    formerly within 1h Drupe::Action::"Login"::response{ input.user: context.input.user }
};
'''

# --- validation rules ---
probe('validation_optional_unguarded',
      'A temporal leaf reads the optional `context.input.note` without a `has` test guarding it. The specification rejects it (optional attributes).',
      '''permit (principal, action == Drupe::Action::"Read", resource)
when temporal {
    formerly within 1h Drupe::Action::"Login"::response{ input.user: context.input.note }
};
''', LOGIN_OK + [ev(10, 'request', 'Read', 'alice', ', note: "alice"', entities=ALICE)])
probe('validation_optional_guarded',
      'The same leaf, guarded by `context.input has note` in an earlier condition of the rule. The specification accepts it.',
      '''permit (principal, action == Drupe::Action::"Read", resource)
when { context.input has note }
when temporal {
    formerly within 1h Drupe::Action::"Login"::response{ input.user: context.input.note }
};
''', LOGIN_OK + [ev(10, 'request', 'Read', 'alice', ', note: "alice"', entities=ALICE), ev(20, 'request', 'Read', 'alice', entities=ALICE)])
probe('validation_duplicate_for_names',
      'A `count` lists the same `for` variable twice. The specification rejects it (binders).',
      '''permit (principal, action == Drupe::Action::"Read", resource)
when temporal {
    (count for (t: Timepoint), (t: Timepoint). where (
        formerly within 1h (Drupe::Action::"Login"::response{ input.user: context.input.user } && tp(t))
    )) >= 1
};
''', LOGIN_OK + [ev(10, 'request', 'Read', 'alice', entities=ALICE)])
probe('validation_timepoint_ordered',
      'Two timepoint variables are ordered. Timepoints are equality-only, so the specification rejects it (timepoints).',
      '''permit (principal, action == Drupe::Action::"Read", resource)
when temporal {
    exists (s: Timepoint). exists (t: Timepoint). (
        formerly within 1h (Drupe::Action::"Login"::request{ input.user: context.input.user } && tp(s))
        && formerly within 1h (Drupe::Action::"Login"::response{ input.user: context.input.user } && tp(t))
        && s < t
    )
};
''', LOGIN_OK + [ev(10, 'request', 'Read', 'alice', entities=ALICE)])
probe('validation_string_ordered',
      'A `String` is ordered. Ordering applies only to `Long`, so the specification rejects it (comparison operands).',
      '''permit (principal, action == Drupe::Action::"Read", resource)
when temporal {
    exists (u: String). (
        formerly within 1h Drupe::Action::"Login"::response{ input.user: u }
        && u < context.input.user
    )
};
''', LOGIN_OK + [ev(10, 'request', 'Read', 'alice', entities=ALICE)])
probe('validation_principal_id_attribute',
      '`principal.id` reads the `id` attribute `OAuthUser` declares, a `String`, as in Cedar. Accepted.',
      '''permit (principal, action == Drupe::Action::"Read", resource)
when temporal {
    formerly within 1h Drupe::Action::"Login"::response{ input.user: principal.id }
};
''', LOGIN_OK + [ev(10, 'request', 'Read', 'alice', entities=ALICE)])

# --- fields of an extension type ---
EXT_SCHEMA = '''namespace Drupe {
  type LoginInput = { user: String, at: datetime };
  type ReadInput = { user: String, since: datetime };
  entity Gateway;
  entity OAuthUser;
  action "Login" appliesTo {
    principal: [OAuthUser],
    resource: [Gateway],
    context: { input: LoginInput }
  };
  action "Read" appliesTo {
    principal: [OAuthUser],
    resource: [Gateway],
    context: { input: ReadInput }
  };
}
'''
T1, T2 = '2026-01-01T00:00:00Z', '2026-01-02T00:00:00Z'
EXT_TRACE = [ev(0, 'request', 'Login', 'alice', f', at: datetime("{T1}")'),
             ev(5, 'response', 'Login', 'alice', f', at: datetime("{T1}")'),
             ev(10, 'request', 'Read', 'alice', f', since: datetime("{T1}")'),
             ev(20, 'request', 'Read', 'alice', f', since: datetime("{T2}")')]
probe('validation_datetime_binder',
      'A `datetime` variable binds the `datetime` field `input.at`, and is compared with the `datetime` attribute `context.input.since`. Temporal conditions do not support `datetime`, so both reject the binder (binders).',
      '''permit (principal, action == Drupe::Action::"Read", resource)
when temporal {
    exists (t: datetime). (
        formerly within 1h Drupe::Action::"Login"::response{ input.user: context.input.user, input.at: t }
        && t == context.input.since
    )
};
''', EXT_TRACE, schema=EXT_SCHEMA)
probe('validation_datetime_string_binder',
      'A `String` variable binds the `datetime` field `input.at`. Not every value of the field is a `String`, so the specification rejects it (predicate arguments), and so does the crate. A validator that typed the field as a `String` would accept the leaf, which never matches.',
      '''permit (principal, action == Drupe::Action::"Read", resource)
when temporal {
    exists (t: String). formerly within 1h Drupe::Action::"Login"::response{ input.user: context.input.user, input.at: t }
};
''', EXT_TRACE, schema=EXT_SCHEMA)
probe('validation_datetime_argument',
      'The `datetime` attribute `context.input.since` is the argument of the `datetime` field `input.at`. Temporal conditions do not support `datetime`, so both reject it (extension types).',
      '''permit (principal, action == Drupe::Action::"Read", resource)
when temporal {
    formerly within 1h Drupe::Action::"Login"::response{ input.user: context.input.user, input.at: context.input.since }
};
''', EXT_TRACE, schema=EXT_SCHEMA)
probe('validation_datetime_wildcard',
      'A wildcard matches the `datetime` field `input.at`. The leaf reads no `datetime` value, so both accept it, and allow every `Read` after the login.',
      '''permit (principal, action == Drupe::Action::"Read", resource)
when temporal {
    formerly within 1h Drupe::Action::"Login"::response{ input.user: context.input.user, input.at: * }
};
''', EXT_TRACE, schema=EXT_SCHEMA)
# `later` is an optional `datetime`, read with no `has` test.
EXT_OPT_SCHEMA = EXT_SCHEMA.replace('type ReadInput = { user: String, since: datetime };',
                                    'type ReadInput = { user: String, since: datetime, later?: datetime };')
assert EXT_OPT_SCHEMA != EXT_SCHEMA
probe('validation_datetime_optional_unguarded',
      'The optional `datetime` attribute `context.input.later` is compared with no `has` test. Both reject it. The specification reports the optional attribute (optional attributes); the crate reports that and the unsupported type (extension types), a difference the baseline expects.',
      '''permit (principal, action == Drupe::Action::"Read", resource)
when temporal {
    formerly within 1h (Drupe::Action::"Login"::response{ input.user: context.input.user } && context.input.later == context.input.later)
};
''', None, schema=EXT_OPT_SCHEMA)
probe('validation_datetime_string_literal',
      'A `String` literal is the argument of the `datetime` field `input.at`. The field cannot hold a `String`, so the specification rejects it (predicate arguments), and so does the crate. A validator that typed the field as a `String` would accept the leaf, which never matches.',
      '''permit (principal, action == Drupe::Action::"Read", resource)
when temporal {
    formerly within 1h Drupe::Action::"Login"::response{ input.user: context.input.user, input.at: "2026-01-01T00:00:00Z" }
};
''', EXT_TRACE, schema=EXT_SCHEMA)

# --- runtime conformance ---
probe('runtime_nonconforming_context',
      'The `Read` request context lacks the required `input.user`. The specification fails the decision closed (nonconforming request context); the crate fails it closed too, with the reason in its diagnostics.',
      READ_AFTER_LOGIN,
      LOGIN_OK + [ev(10, 'request', 'Read', 'alice', entities=ALICE).replace('request_context(input: { user: "alice" })', 'request_context(input: { note: "x" })')])
probe('runtime_nonconforming_entities',
      'The entity data gives `level` a `String`, where the schema declares a `Long`. The specification fails the decision closed (nonconforming entity store); the crate fails it closed too, with the reason in its diagnostics.',
      READ_AFTER_LOGIN,
      LOGIN_OK + [ev(10, 'request', 'Read', 'alice', entities='Drupe::OAuthUser::"alice": { id: "alice", level: "five" }')])
probe('runtime_caller_mismatch',
      'The `Read` request logs `callerPrincipal` as bob while its principal is alice. The mirror rule makes the event nonconforming: the specification fails the decision closed (nonconforming decision event); the crate fails it closed too, with the reason in its diagnostics.',
      READ_AFTER_LOGIN,
      LOGIN_OK + [ev(10, 'request', 'Read', 'alice', entities=ALICE, caller='bob')])
probe('runtime_nonconforming_history',
      "A `Login` response logs `input.user` as a `Long`. Ingestion rejects it (`Rejection.nonconforming`); the crate rejects it too, so neither allows the later `Read` that only it could allow.",
      '''@id("read_after_login_any")
permit (principal, action == Drupe::Action::"Read", resource)
when temporal {
    formerly within 1h Drupe::Action::"Login"::response{ input.user: * }
};
''',
      [ev(0, 'response', 'Login', 'alice', entities=ALICE).replace('Drupe::Action::"Login"::response(input: { user: "alice" }', 'Drupe::Action::"Login"::response(input: { user: 7 }'),
       ev(10, 'request', 'Read', 'alice', entities=ALICE)])
probe('runtime_principal_id_supplied',
      "The entity data gives alice an `id` attribute of \"mallory\". Both read `principal.id` as the supplied attribute, as Cedar does, and deny: the login was by alice.",
      '''permit (principal, action == Drupe::Action::"Read", resource)
when temporal {
    formerly within 1h Drupe::Action::"Login"::response{ input.user: principal.id }
};
''', LOGIN_OK + [ev(10, 'request', 'Read', 'alice', entities='Drupe::OAuthUser::"alice": { id: "mallory", level: 5 }')])

probe('runtime_missing_scope_entity',
      "A temporal leaf reads `principal.level` under a negation, and the first `Read` supplies no entity data for alice. The specification fails that decision closed (missing scope entity); the crate adds a bare entity, so the comparison is false, its negation true, and it allows. With alice's data supplied, both decide alike.",
      '''@id("read_after_login_level")
permit (principal, action == Drupe::Action::"Read", resource)
when temporal {
    formerly within 1h (
        Drupe::Action::"Login"::response{ input.user: context.input.user } && !(principal.level < 3)
    )
};
''',
      [ev(0, 'request', 'Login', 'alice'), ev(5, 'response', 'Login', 'alice'),
       ev(10, 'request', 'Read', 'alice'),
       ev(20, 'request', 'Read', 'alice', entities='Drupe::OAuthUser::"alice": { id: "alice", level: 1 }'),
       ev(30, 'request', 'Read', 'alice', entities=ALICE)])

def scopeless(line):
    """The event of `line` with no scope: no principal, no resource, no entity data."""
    head, rest = line.split(' ', 1)
    assert rest.startswith('scope(')
    rest = rest[rest.index(') ') + 2:]
    if rest.startswith('entities('):
        rest = rest[rest.index(') ') + 2:]
    return head + ' ' + rest

probe('runtime_scopeless_history',
      "A `Login` response that carries no scope logs alice as its caller. Under the strict mirror rule, a caller field is logged only by an event that carries the caller, so ingestion rejects it (`Rejection.nonconforming`), and alice's `Read` has no login to rely on: the specification denies it. The crate does the same under its default rule, `MirrorRule::Strict`: it rejects the response and denies the `Read`. Under the opt-out `MirrorRule::Current`, which accepts any logged caller when the request side does not resolve, it would ingest the response and allow the `Read`.",
      READ_AFTER_LOGIN,
      [ev(0, 'request', 'Login', 'alice', entities=ALICE), scopeless(ev(5, 'response', 'Login', 'alice')),
       ev(10, 'request', 'Read', 'alice', entities=ALICE)])
probe('runtime_forged_rate_limit',
      "Three scope-less `Read` requests log alice as their caller, ahead of alice's own `Read`. Under the strict mirror rule ingestion rejects them, so alice's first request is under her limit, and the specification allows it. Under its default rule, `MirrorRule::Strict`, the crate fails each forged request closed and does not record it, so it allows her request too. Under the opt-out `MirrorRule::Current`, which accepts any logged caller when the request side does not resolve, it would record them in alice\'s history and deny her request.",
      '''@id("read")
permit (principal, action == Drupe::Action::"Read", resource);
@id("read_rate_limit")
forbid (principal, action == Drupe::Action::"Read", resource)
when temporal {
    (count for (t: Timepoint). where formerly within 1h (Drupe::Action::"Read"::request{} && tp(t))) > 2
};
''',
      [scopeless(ev(1, 'request', 'Read', 'alice')), scopeless(ev(2, 'request', 'Read', 'alice')),
       scopeless(ev(3, 'request', 'Read', 'alice')), ev(10, 'request', 'Read', 'alice', entities=ALICE)])

# --- field names that hold a `.` ---
DOTTED_SCHEMA = '''namespace Drupe {
  type UserRef = { id: String };
  type In = { "user.id": String, user: UserRef };
  entity Gateway;
  entity OAuthUser;
  action "Login" appliesTo {
    principal: [OAuthUser],
    resource: [Gateway],
    context: { input: In }
  };
  action "Logout" appliesTo {
    principal: [OAuthUser],
    resource: [Gateway],
    context: { input: In }
  };
  action "Read" appliesTo {
    principal: [OAuthUser],
    resource: [Gateway],
    context: { input: In }
  };
}
'''
def dotted(ts, kind, action, nested, quoted):
    """An event by alice whose `input` has the nested `user.id` `nested` and the attribute
    `"user.id"` `quoted`, logged and in the request context."""
    inp = f'input: {{ "user.id": "{quoted}", user: {{ id: "{nested}" }} }}'
    return (f'@{ts} scope(principal: Drupe::OAuthUser::"alice", resource: Drupe::Gateway::"gw1") '
            f'request_context({inp}) Drupe::Action::"{action}"::{kind}({inp}, '
            f'callerPrincipal: Drupe::OAuthUser::"alice", callerResource: Drupe::Gateway::"gw1", requestId: "r{ts}")')
probe('runtime_dotted_attribute_permit',
      "The `input` record has an attribute named \"user.id\" and a record `user` with an `id`. A path steps one level per `.`, so `context.input.user.id` and the field `input.user.id` are the `id` inside `user`, never the attribute \"user.id\". The first `Read` shares the `Login`'s nested id and not its \"user.id\": allowed. The second has bob's nested id and alice's in its \"user.id\": denied. A request environment that gave the two paths one key would read the attribute, and decide both the other way.",
      '''permit (principal, action == Drupe::Action::"Read", resource)
when temporal {
    formerly within 1h Drupe::Action::"Login"::response{ input.user.id: context.input.user.id }
};
''',
      [dotted(0, 'request', 'Login', 'alice', 'q0'), dotted(5, 'response', 'Login', 'alice', 'q0'),
       dotted(10, 'request', 'Read', 'alice', 'q10'), dotted(20, 'request', 'Read', 'bob', 'alice')],
      schema=DOTTED_SCHEMA)
probe('runtime_dotted_attribute_forbid',
      "The same records under a `forbid`. The first `Read` shares the `Logout`'s nested id and not its \"user.id\": the forbid blocks it. The second has bob's nested id and alice's in its \"user.id\": allowed. A request environment that gave the two paths one key would allow the first and deny the second.",
      '''permit (principal, action == Drupe::Action::"Read", resource);
forbid (principal, action == Drupe::Action::"Read", resource)
when temporal {
    formerly within 1h Drupe::Action::"Logout"::response{ input.user.id: context.input.user.id }
};
''',
      [dotted(0, 'request', 'Logout', 'alice', 'q0'), dotted(5, 'response', 'Logout', 'alice', 'q0'),
       dotted(10, 'request', 'Read', 'alice', 'q10'), dotted(20, 'request', 'Read', 'bob', 'alice')],
      schema=DOTTED_SCHEMA)

# --- validity rules of `PolicySet.Valid`, one probe each ---
GAP_SCHEMA = """namespace Drupe {
  type LoginInput = { user: String };
  type Profile = { name: String };
  type ReadInput = {
    user: String,
    note?: String,
    count: Long,
    owner: OAuthUser,
    profile: Profile,
    card: { number: Long },
    when: datetime
  };
  entity Gateway;
  entity Bot;
  entity Group;
  entity OAuthUser in [Group] = { id: Long, level: Long, dept?: String };
  action "Login" appliesTo {
    principal: [OAuthUser],
    resource: [Gateway],
    context: { input: LoginInput }
  };
  action "Read" appliesTo {
    principal: [OAuthUser],
    resource: [Gateway],
    context: { input: ReadInput }
  };
  action "Ping" appliesTo {
    principal: [OAuthUser, Bot],
    resource: [Gateway],
    context: { input: ReadInput }
  };
}
namespace Other {
  entity OAuthUser;
}
"""
GAP_PROVIDERS = """{
  "availableProviders": {
    "Risk::Score": {
      "argumentTypes": [ { "paramType": "string" } ],
      "outputType": { "paramType": "long" }
    },
    "Risk::Chain": {
      "argumentTypes": [],
      "outputType": { "paramType": "set", "items": { "paramType": "string" } },
      "availableMethods": {
        "first": {
          "inputType": { "paramType": "set", "items": { "paramType": "long" } },
          "outputType": { "paramType": "long" }
        }
      }
    }
  }
}
"""
def login_and(condition):
    return ('formerly within 1h (Drupe::Action::"Login"::request{ input.user: context.input.user } && '
            + condition + ')')
def read_rule(leaf, scope='principal, action == Drupe::Action::"Read", resource', cedar=''):
    return f'permit ({scope})\n{cedar}when temporal {{\n    {leaf}\n}};\n'
def gap(name, readme, policy, extra=None):
    probe(name, readme, policy, None, schema=GAP_SCHEMA, extra=extra)

# `rank` is a `Long` on an `OAuthUser` and a `String` on a `Bot`; `Ping` admits both.
RANK_SCHEMA = """namespace Drupe {
  type LoginInput = { user: String };
  entity Gateway;
  entity OAuthUser = { rank: Long };
  entity Bot = { rank: String };
  action "Login" appliesTo {
    principal: [OAuthUser, Bot],
    resource: [Gateway],
    context: { input: LoginInput }
  };
  action "Ping" appliesTo {
    principal: [OAuthUser, Bot],
    resource: [Gateway],
    context: { input: LoginInput }
  };
}
"""
def ping_rule(condition):
    return read_rule(
        'formerly within 1h (Drupe::Action::"Login"::request{ input.user: context.input.user } && '
        + condition + ')', scope='principal, action == Drupe::Action::"Ping", resource')
probe('validation_attribute_typed_per_environment',
      '`principal.rank` is a `Long` on an `OAuthUser` and a `String` on a `Bot`, and compared with itself. It is well typed in each request environment, as Cedar types it, so both accept it. The crate used to reject it as ambiguous.',
      ping_rule('principal.rank == principal.rank'), None, schema=RANK_SCHEMA)
probe('validation_attribute_typed_per_environment_wrong_in_one',
      '`principal.rank` is compared with a `Long`, which is wrong for a `Bot`. Both reject it (comparison operands).',
      ping_rule('principal.rank == 5'), None, schema=RANK_SCHEMA)

gap('validation_wildcard_operand',
    'A wildcard is a comparison operand: the comparison is always false. The specification rejects it (placement).',
    read_rule(login_and('context.input.user == *')))
gap('validation_undeclared_action_literal',
    'An action literal names no declared action. The specification rejects it (paths).',
    read_rule(login_and('Drupe::Action::"Lgoin" == Drupe::Action::"Login"')))
gap('validation_unparsable_decimal',
    'A `decimal` literal with five digits after its point does not parse. The specification rejects it (paths).',
    read_rule(login_and('decimal("1.23456") == decimal("1.0")')))
gap('validation_unqualified_binder_type',
    'A binder is declared `OAuthUser`, which names no declared entity type: the entity type is `Drupe::OAuthUser`. The specification rejects it (binders).',
    read_rule('exists (u: OAuthUser). formerly within 1h Drupe::Action::"Login"::request{ callerPrincipal: u }'))
gap('validation_entity_type_namespace',
    'An argument of type `Other::OAuthUser` is given to a field of type `Drupe::OAuthUser`: the two share their last segment only. The specification rejects it (predicate arguments).',
    read_rule('formerly within 1h Drupe::Action::"Read"::request{ input.owner: Other::OAuthUser::"alice" }'))
gap('validation_scope_root_per_environment',
    'On `Ping`, whose principals are `OAuthUser`s and `Bot`s, `principal` is given to a field that holds an `OAuthUser`. In the request environment of a `Bot`, the specification rejects it (predicate arguments).',
    read_rule('formerly within 1h Drupe::Action::"Ping"::request{ input.owner: principal }',
              scope='principal, action == Drupe::Action::"Ping", resource'))
gap('validation_binding_equality_entity_types',
    'An equality binds a `Drupe::OAuthUser` variable to `resource`, a `Drupe::Gateway`. The specification rejects it (comparison operands).',
    read_rule('exists (x: Drupe::OAuthUser). (\n        formerly within 1h Drupe::Action::"Login"::request{ input.user: context.input.user } && x == resource\n    )'))
gap('validation_extension_type_operand',
    'A `datetime` attribute is compared with a `String`. Temporal conditions do not support `datetime`, so the specification rejects it (extension types).',
    read_rule(login_and('context.input.when == "2026-01-01"')))
gap('validation_record_operands',
    'Two records of different shapes are compared. The specification rejects it (comparison operands).',
    read_rule(login_and('context.input.profile == context.input.card')))
gap('validation_named_field_argument',
    'The event schema types `requestId` as a `String`, and a predicate gives it a `Long`. The specification rejects it (predicate arguments).',
    read_rule('formerly within 1h Drupe::Action::"Login"::request{ requestId: 5 }'))
gap('validation_principal_id_declared_attribute',
    '`principal.id` is the `id` attribute `OAuthUser` declares, a `Long`, and is compared with a `Long`. Both accept it.',
    read_rule(login_and('principal.id == 5')))
gap('validation_principal_in_group',
    'Under `principal in Drupe::Group::"staff"` on `Ping`, a leaf reads `principal.level`, which a `Bot` lacks. A `Bot` cannot be in a `Group`, so the rule decides no `Bot`, and both accept it.',
    read_rule(login_and('principal.level > 3'),
              scope='principal in Drupe::Group::"staff", action == Drupe::Action::"Ping", resource'))
gap('validation_impossible_policy',
    'The rule\'s scope admits a `Bot` principal for `Read`, which has none: the policy is impossible. The specification rejects it (cedar), as cedar-lean\'s validator does.',
    read_rule('formerly within 1h Drupe::Action::"Login"::request{ input.user: context.input.user }',
              scope='principal is Drupe::Bot, action == Drupe::Action::"Read", resource'))
gap('validation_context_read_whole',
    'The Cedar part of a rule with a temporal leaf reads the request context whole, which lowering extends with the leaves\' values. The specification rejects it (context reads).',
    read_rule('formerly within 1h Drupe::Action::"Login"::request{ input.user: context.input.user }',
              cedar='when { context == context }\n'))
gap('validation_temporal_reads_hoisted',
    'A temporal leaf reads `context.policy_0__temporal_0`, an attribute lowering adds, not one of the request. The specification rejects it (paths).',
    read_rule(login_and('context.policy_0__temporal_0 == true')))
gap('validation_provider_optional_argument',
    'A provider argument reads the optional `context.input.note` without a `has` test. The provider contract tolerates an absent argument, and both accept it.',
    'permit (principal, action == Drupe::Action::"Read", resource)\nwhen { Risk::Score(context.input.note) > 3 };\n',
    extra={'providers.json': GAP_PROVIDERS})
gap('validation_provider_argument_type',
    'A provider declared to take a `String` is given `principal`, an entity. The specification rejects it (providers).',
    'permit (principal, action == Drupe::Action::"Read", resource)\nwhen { Risk::Score(principal) > 3 };\n',
    extra={'providers.json': GAP_PROVIDERS})
gap('validation_provider_method_input',
    'A provider method declared to take a `Set<Long>` follows a stage that produces a `Set<String>`. The specification rejects it (providers).',
    'permit (principal, action == Drupe::Action::"Read", resource)\nwhen { Risk::Chain().first() > 3 };\n',
    extra={'providers.json': GAP_PROVIDERS})
gap('validation_compound_aggregate_event',
    'An aggregate inside a compound operand names an undeclared event (`experimental-arithmetic`). The specification rejects it (event names).',
    read_rule('(count for (t: Timepoint). where (formerly within 1h (Drupe::Action::"Nope"::request{} && tp(t)))) + 1 > 3'))
gap('validation_compound_aggregate_constant',
    'An aggregate inside a compound operand has a body that does not vary with the timepoint (`experimental-arithmetic`). The specification rejects it (time dependence).',
    read_rule('(count for (a: Long). where (a == context.input.count)) + 1 > 3'))

# --- lowering edge cases found by the Lean port of the frontend ---
LOGIN_LEAF = 'formerly within 1h Drupe::Action::"Login"::request{ input.user: context.input.user }'
ROOT_TYPE_SCHEMA = SCHEMA.replace('namespace Drupe {\n  type LoginInput = { user: String };\n',
                                  'type LoginInput = { user: String };\nnamespace Drupe {\n')
probe('runtime_root_common_type',
      'The action schema declares `LoginInput` in the root namespace, and `Drupe`\'s actions refer to it bare. Cedar resolves the name there, and so do the derived events, which have the field `input.user`. Both allow alice\'s `Read` after her login and deny bob\'s.',
      read_rule(LOGIN_LEAF),
      LOGIN_OK + [ev(10, 'request', 'Read', 'alice', entities=ALICE),
                  ev(20, 'request', 'Read', 'bob', principal='bob')],
      schema=ROOT_TYPE_SCHEMA)
probe('validation_enum_parent',
      'An entity type has an enumerated entity type as its parent, which Cedar allows and the specification\'s validity does not (`Schema.standardAncestors`). Both reject it (schema).',
      read_rule(LOGIN_LEAF), None,
      schema=SCHEMA.replace('  entity Gateway;\n', '  entity Gateway;\n  entity Application enum ["TinyTodo"];\n')
                   .replace('entity OAuthUser = ', 'entity OAuthUser in [Application] = '))
probe('runtime_pin_named_binder',
      'An authored binder is named `__pin_ti0`, a name of the form the relativization rewrite gives its own binders, and is used inside a `previous`. The rewrite draws names no variable of the leaf starts with, so it does not capture the binder. Both allow alice\'s `Read` after her login.',
      read_rule('exists (__pin_ti0: Timepoint). (\n        formerly within 1h (Drupe::Action::"Login"::request{ input.user: context.input.user } && tp(__pin_ti0))\n        && previous within 1h (formerly within 1h (Drupe::Action::"Login"::request{ input.user: context.input.user } && tp(__pin_ti0))))'),
      [ev(1000, 'request', 'Login', 'alice', entities=ALICE), ev(1010, 'request', 'Read', 'alice', entities=ALICE)])
# --- pins under another name (89d3e3c0): a pin to the principal, the resource, or a context path
# is symmetric whatever its field is called, and its field must hold the event's own value ---
def pin_schema(pin):
    return ('decision event <A>::request {\n    ...inputs(A),\n    callerPrincipal: principalType(A),\n'
            '    callerResource: resourceType(A),\n    requestId: String,\n    ' + pin + ',\n}\n\n'
            'event <A>::response {\n    ...inputs(A),\n    callerPrincipal: principalType(A),\n'
            '    callerResource: resourceType(A),\n    requestId: String,\n    ' + pin + ',\n}\n')
READ_AFTER_ANY_LOGIN = '''permit (principal, action == Drupe::Action::"Read", resource)
when temporal {
    formerly within 1h Drupe::Action::"Login"::response{}
};
'''
probe('runtime_renamed_principal_pin_forged',
      'Under `pin actor = principal` on every kind, mallory\'s Login response logs `actor: alice`. The pin is symmetric whatever its field is called, so both reject the response at ingestion, and alice\'s `Read` is denied; after her own login it is allowed. Before 89d3e3c0, the crate ingested the forged response, and allowed the first `Read`.',
      READ_AFTER_ANY_LOGIN,
      [ev(0, 'response', 'Login', 'alice', principal='mallory', extra_log=', actor: Drupe::OAuthUser::"alice"'),
       ev(10, 'request', 'Read', 'alice', entities=ALICE, extra_log=', actor: Drupe::OAuthUser::"alice"'),
       ev(20, 'response', 'Login', 'alice', entities=ALICE, extra_log=', actor: Drupe::OAuthUser::"alice"'),
       ev(30, 'request', 'Read', 'alice', entities=ALICE, extra_log=', actor: Drupe::OAuthUser::"alice"')],
      extra={'event.dwschema': pin_schema('pin actor: principalType(A) = principal')})
probe('runtime_renamed_context_pin_forged',
      'Under `pin sid = context.input.user` on every kind, a Login response whose `input.user` is mallory logs `sid: "alice"`. The pin is symmetric, so both reject it, and alice\'s `Read` is denied; after a login in her own `sid` it is allowed.',
      READ_AFTER_ANY_LOGIN,
      [ev(0, 'response', 'Login', 'mallory', principal='alice', extra_log=', sid: "alice"'),
       ev(10, 'request', 'Read', 'alice', entities=ALICE, extra_log=', sid: "alice"'),
       ev(20, 'response', 'Login', 'alice', entities=ALICE, extra_log=', sid: "alice"'),
       ev(30, 'request', 'Read', 'alice', entities=ALICE, extra_log=', sid: "alice"')],
      extra={'event.dwschema': pin_schema('pin sid: String = context.input.user')})
probe('runtime_attribute_pin_unchecked',
      'Under `pin uid = principal.id`, a pin to an attribute, which is not symmetric, a Login response logs `uid: "someone"`. Both ingest it: the field need only be logged. It does not match alice\'s `Read`, whose `principal.id` is "alice", so the `Read` is denied; after a login that logs `uid: "alice"` it is allowed.',
      READ_AFTER_ANY_LOGIN,
      [ev(0, 'response', 'Login', 'alice', entities=ALICE, extra_log=', uid: "someone"'),
       ev(10, 'request', 'Read', 'alice', entities=ALICE, extra_log=', uid: "alice"'),
       ev(20, 'response', 'Login', 'alice', entities=ALICE, extra_log=', uid: "alice"'),
       ev(30, 'request', 'Read', 'alice', entities=ALICE, extra_log=', uid: "alice"')],
      extra={'event.dwschema': pin_schema('pin uid: String = principal.id')})
probe('lowering_array_under_arithmetic',
      'An array constant in the body of an aggregate that is an operand of `*` (`experimental-arithmetic`). Lowering rejects it, as it rejects every array constant.',
      read_rule('(count for (t: Timepoint). where (formerly within 1h (Drupe::Action::"Login"::request{ input.user: ["a", "b"] } && tp(t)))) * 2 >= 1'),
      None)
probe('lowering_macro_error_span',
      'A Cedar macro is called in a temporal block. Expansion rejects it, and the error points at the call in the policy.',
      'def cedar c(?p) { ?p == principal };\n' + read_rule('c(principal)'), None)
probe('lowering_cyclic_common_type',
      'An action\'s context is a common type with an attribute of a common type that contains itself. Inlining the context would recurse without end; lowering rejects the cycle.',
      read_rule(LOGIN_LEAF), None,
      schema=SCHEMA.replace('  type ReadInput', '  type A = { x: A };\n  type ReadCtx = { input: ReadInput, meta: A };\n  type ReadInput')
                   .replace('context: { input: ReadInput }', 'context: ReadCtx'))
probe('validation_context_read_empty_record',
      'The Cedar part of a rule with a temporal leaf compares the request context with `{}`, which lowering extends with the leaves\' values. Both reject it (context reads).',
      read_rule(LOGIN_LEAF, cedar='when { context == {} }\n'), None)
probe('lowering_declared_hoisted_name',
      'The action schema declares `policy_0__temporal_0: Bool` in the context of `Read`, the name lowering gives the rule\'s temporal leaf. Lowering rejects it, whatever the attribute\'s type, as `PolicySet.Valid` (names fresh) does.',
      read_rule(LOGIN_LEAF), None,
      schema=SCHEMA.replace('context: { input: ReadInput }', 'context: { input: ReadInput, policy_0__temporal_0: Bool }'))
probe('lowering_binding_value_operand',
      'A macro\'s body binds `$x` to `$y + 1` before the count that binds `$y`. Expansion rejects it; the error names the value operand, not an aggregate operand, which it is not.',
      'def temporal bind() { exists ($x: Long). exists ($y: Long). ($x == $y + 1\n    && (count for ($t: Timepoint). where (formerly within 1h (Drupe::Action::"Login"::request{} && tp($t)))) == $y) };\n'
      + read_rule('bind()'), None)
DECIMAL_PROVIDERS = """{
  "availableProviders": {
    "Risk::Score": {
      "argumentTypes": [],
      "outputType": { "paramType": "record", "fields": { "score": { "paramType": "decimal" } }, "required": ["score"] },
      "implementation": { "kind": "rhai", "script": "fn evaluate() { #{ score: parse_decimal(\\"0.75\\") } }" }
    }
  }
}
"""
probe('lowering_declared_providers_record',
      'The action schema declares a `providers` record in the context of `Read`, the attribute lowering gives the rule\'s provider leaves. Lowering rejects it.',
      'permit (principal, action == Drupe::Action::"Read", resource)\nwhen { Risk::Score().score.greaterThan(decimal("0.5")) };\n', None,
      schema=SCHEMA.replace('context: { input: ReadInput }', 'context: { input: ReadInput, providers: { legacy: String } }'),
      extra={'providers.json': DECIMAL_PROVIDERS})
probe('runtime_provider_decimal_type_name',
      'The namespace declares a common type named `decimal`, and a provider\'s output has a field of type `decimal`, the extension type. The shared provider type writes it `__cedar::decimal`, which the namespace\'s type does not capture. Both allow the `Read`.',
      'permit (principal, action == Drupe::Action::"Read", resource)\nwhen { Risk::Score().score.greaterThan(decimal("0.5")) };\n',
      [ev(10, 'request', 'Read', 'alice', entities=ALICE)],
      schema=SCHEMA.replace('  entity Gateway;\n', '  type decimal = { foo: Long };\n  entity Gateway;\n'),
      extra={'providers.json': DECIMAL_PROVIDERS})
QUOTED_PROVIDERS = """{
  "availableProviders": {
    "Http::Head": {
      "argumentTypes": [],
      "outputType": { "paramType": "record", "fields": { "content-type": { "paramType": "string" } }, "required": ["content-type"] },
      "implementation": { "kind": "rhai", "script": "fn evaluate() { #{ \\"content-type\\": \\"text/plain\\" } }" }
    }
  }
}
"""
probe('runtime_provider_quoted_field',
      'A provider\'s output record has a field named `content-type`, which is not a Cedar identifier. The shared provider type writes it as a string, as Cedar\'s schema printer does, so lowering succeeds. Both allow the `Read`.',
      'permit (principal, action == Drupe::Action::"Read", resource)\nwhen { Http::Head()["content-type"] == "text/plain" };\n',
      [ev(10, 'request', 'Read', 'alice', entities=ALICE)],
      extra={'providers.json': QUOTED_PROVIDERS})

# --- found by generated differential runs (conformance/gen-run.sh) ---
probe('lowering_folded_boolean_literals',
      'A rule conjoins two Boolean literals before its temporal leaf, and has two clauses of `true`. Cedar\'s expression builder folds `&&` of two Boolean literals into one, so the crate lowers `true && true && temporal { … }` to `true && context.<leaf>`, and the clauses to `true`; the Lean port of the frontend folds them the same way. Both allow alice\'s `Read` after her login.',
      '@id("read_after_login_folded")\npermit (principal, action == Drupe::Action::"Read", resource)\n'
      'when { true && true && temporal { formerly within 1h Drupe::Action::"Login"::response{ input.user: context.input.user } } }\n'
      'when { true }\nwhen { true };\n',
      LOGIN_OK + [ev(10, 'request', 'Read', 'alice', entities=ALICE)])
gap('validation_aggregate_operand_two_findings',
    'On `Ping`, whose principal may be a `Bot`, an aggregate counts `Login` requests, whose `callerPrincipal` is an `OAuthUser`: the pin `callerPrincipal = principal` correlates the field with a `Bot`, a predicate-argument finding and a pin finding inside one comparison operand. The specification\'s typing check reports every problem of an operand, so both report both.',
    read_rule('(count for (t: Timepoint). where formerly within 1h (Drupe::Action::"Login"::request{} && tp(t))) >= 1',
              scope='principal, action == Drupe::Action::"Ping", resource'))
probe('validation_undeclared_field_term',
      'A predicate argument names a field the event does not declare, and its term reads a context attribute `Read` does not declare. The crate reports both (event names, paths); so does the specification, whose typing check also checks the term of an argument for an undeclared field.',
      'permit (principal, action == Drupe::Action::"Read", resource)\n'
      'when temporal {\n    formerly within 1h Drupe::Action::"Login"::response{ nosuch: context.input.nosuch }\n};\n',
      None)
probe('runtime_erring_rule_missing_scope_entity',
      'A rule reads `principal.level` in its Cedar part and in its temporal leaf, and alice\'s `Read` supplies no entity data; another rule allows every request. The specification fails the decision closed (missing scope entity). The crate adds a bare entity: the first rule errs, with an error in the diagnostics, and the second allows. The crate decided, though its diagnostics hold an error, so the conformance harness reports the runtime gap, not a disagreement of verdicts; on the data supplied both allow.',
      '@id("allow_all")\npermit (principal, action, resource);\n'
      '@id("read_level")\npermit (principal, action == Drupe::Action::"Read", resource)\nwhen { principal.level < 3 }\n'
      'when temporal {\n    formerly within 1h (Drupe::Action::"Login"::response{ input.user: context.input.user } && principal.level > 1)\n};\n',
      LOGIN_OK + [ev(10, 'request', 'Read', 'alice')])
UNUSED_METHOD_PROVIDERS = """{
  "entityTypes": { "Risk::Level": { "enum": ["LOW", "HIGH"] } },
  "availableProviders": {
    "Risk::Scan": {
      "argumentTypes": [ { "paramType": "string" } ],
      "outputType": { "paramType": "bool" },
      "availableMethods": {
        "level": { "argumentTypes": [], "outputType": { "paramType": "entity", "entityType": "Risk::Level" } }
      },
      "implementation": { "kind": "rhai", "script": "fn evaluate(a0) { if type_of(a0) == \\"()\\" { return false; } a0 == \\"alice\\" }\\nfn level(input) { \\"LOW\\" }" }
    }
  }
}
"""
probe('validation_provider_unused_method_enum',
      'A provider declares a method whose output is a provider enum, and the rule calls the provider without the method, so lowering does not add the enum to the schema. The bridge leaves out the method alone: leaving out the whole declaration would make the specification find the invocation undeclared. Both accept the set, and allow alice\'s `Read`.',
      '@id("read_scanned")\npermit (principal, action == Drupe::Action::"Read", resource)\nwhen { Risk::Scan(context.input.user) };\n',
      [ev(10, 'request', 'Read', 'alice', entities=ALICE)],
      extra={'providers.json': UNUSED_METHOD_PROVIDERS})
probe('validation_context_read_own_leaf_name',
      'The Cedar part of rule 0 reads `context.policy_0__temporal_0`, the name lowering gives the rule\'s own temporal leaf. The crate records the read while it lowers the authored rule and rejects it (context reads); the Lean port of its validator takes the reads from the authored rules too, since in the lowered rule the author\'s read is indistinguishable from lowering\'s reference to the leaf. The bridge translates the lowered rule, so the specification sees the leaf twice and accepts: the conformance baseline lists the difference.',
      'permit (principal, action == Drupe::Action::"Read", resource)\n'
      'when { context.policy_0__temporal_0 && temporal { formerly within 1h Drupe::Action::"Login"::response{ input.user: context.input.user } } };\n',
      None)
probe('runtime_stamped_ingestion_change',
      'A `Login` response that logs `input.user` as a `Long` is rejected at ingestion; alice\'s later `Read` is recorded before her own `Login` response. The specification stamps the `Read` one tick after the response, and allows it; the crate takes the times as given, and denies. The harness reports the decision once, as stamping, not also as a decision ingestion changes.',
      READ_AFTER_LOGIN,
      [ev(0, 'response', 'Login', 'alice', entities=ALICE).replace('Drupe::Action::"Login"::response(input: { user: "alice" }', 'Drupe::Action::"Login"::response(input: { user: 7 }'),
       ev(5, 'response', 'Login', 'alice', entities=ALICE),
       ev(3, 'request', 'Read', 'alice', entities=ALICE)])
probe('lowering_unparsable_schema_and_array',
      'The action schema writes an attribute name with a JSON-style escape, `"\\u00c4"`, which Cedar\'s schema syntax does not have, and the policy puts an array in a temporal predicate argument. The public pipeline fails first at the derivation of the event signatures, which parses the action schema; the export\'s stages that need the schema do not run, and the array check, which does not, fails. The frontend harness\'s `export` check counts the schema\'s rejection where the pipeline meets it.',
      'permit (principal, action == Drupe::Action::"Read", resource)\n'
      'when temporal {\n    formerly within 1h Drupe::Action::"Login"::response{ input.user: ["a", "b"] }\n};\n',
      None, schema=SCHEMA.replace('type ReadInput = { user: String, note?: String, level?: Long };',
                                  'type ReadInput = { user: String, note?: String, level?: Long, "\\u00c4": String };'))
probe('lowering_unparsable_event_schema_and_provider_error',
      'The event schema does not parse, and the provider declarations declare an enum outside their providers\' namespaces. The public pipeline parses the event schema before it checks the declarations, and fails there; the frontend harness\'s `export` check counts the event schema\'s rejection first.',
      'permit (principal, action == Drupe::Action::"Read", resource)\nwhen { Risk::Scan(context.input.user) };\n',
      None,
      extra={'event.dwschema': 'decision event <A>::request {\n    ...inputs(A),\n    ,\n}\n',
             'providers.json': UNUSED_METHOD_PROVIDERS.replace('"Risk::Level"', '"Elsewhere::Level"')})
probe('lowering_cyclic_action_hierarchy',
      'The actions `Login` and `Read` are each in the other. Cedar rejects the schema when it compiles the augmented one; the message is Cedar\'s, which the frontend harness compares by category, in its `pipeline` check too.',
      READ_AFTER_LOGIN, None,
      schema=SCHEMA.replace('action "Login" appliesTo', 'action "Login" in ["Read"] appliesTo')
                   .replace('action "Read" appliesTo', 'action "Read" in ["Login"] appliesTo'))

# --- Cedar 4.14 ---
probe('validation_external_declarations',
      'The action schema declares an entity type and an action `external` (Cedar 4.14, RFC 116). Cedar\'s validator validates no policy against an incomplete schema, so both reject the rule (Cedar).',
      read_rule(LOGIN_LEAF), None,
      schema=SCHEMA.replace('  entity Gateway;\n', '  entity Gateway;\n  external entity Remote in [Gateway];\n')
                   .replace('  action "Login" appliesTo', '  external action "Outside";\n  action "Login" appliesTo'))
probe('lowering_external_enum_ancestor',
      'An entity type declared `external` (Cedar 4.14) has an enumerated entity type as its parent, which no definition of it could list. Cedar rejects the schema, and so does the frontend.',
      read_rule(LOGIN_LEAF), None,
      schema=SCHEMA.replace('  entity Gateway;\n', '  entity Gateway;\n  entity Application enum ["TinyTodo"];\n'
                                                   '  external entity Remote in [Application];\n'))
HAS_SCHEMA = SCHEMA.replace('type ReadInput = { user: String, note?: String, level?: Long };',
                            'type ReadInput = { user: String, meta?: { tag?: String, "if"?: String } };')
probe('runtime_extended_has',
      'The Cedar part tests `context.input has meta.tag`, a path of identifiers, which Cedar 4.14 keeps as one extended `has`, and reads the attribute it guards. Both allow alice\'s `Read` that carries the tag after her login, and deny her `Read` without it.',
      read_rule(LOGIN_LEAF, cedar='when { context.input has meta.tag && context.input.meta.tag == "ok" }\n'),
      LOGIN_OK + [ev(10, 'request', 'Read', 'alice', extra_ctx=', meta: { tag: "ok" }', entities=ALICE),
                  ev(20, 'request', 'Read', 'alice', extra_ctx=', meta: {}', entities=ALICE)],
      schema=HAS_SCHEMA)
probe('runtime_extended_has_reserved',
      'The Cedar part tests `context.input has meta.if`, a path with a reserved word, which lowering writes as the conjunction `context.input has meta && context.input.meta has if`, as Cedar 4.11 wrote every path. Both allow alice\'s `Read` that carries the attribute after her login, and deny her `Read` without it.',
      read_rule(LOGIN_LEAF, cedar='when { context.input has meta.if }\n'),
      LOGIN_OK + [ev(10, 'request', 'Read', 'alice', extra_ctx=', meta: { "if": "x" }', entities=ALICE),
                  ev(20, 'request', 'Read', 'alice', extra_ctx=', meta: {}', entities=ALICE)],
      schema=HAS_SCHEMA)

for name, (readme, policy, trace, schema, extra) in probes.items():
    d = os.path.join(root, name)
    os.makedirs(d, exist_ok=True)
    comment = ''.join('// ' + line + '\n' for line in textwrap.wrap(readme, 96))
    open(os.path.join(d, 'policy.dw'), 'w').write(comment + policy)
    open(os.path.join(d, 'schema.cedarschema'), 'w').write(schema)
    if trace is not None:
        open(os.path.join(d, 'trace.log'), 'w').write('\n'.join(trace) + '\n')
    for f, c in extra.items():
        open(os.path.join(d, f), 'w').write(c)
print(len(probes), 'probes')
