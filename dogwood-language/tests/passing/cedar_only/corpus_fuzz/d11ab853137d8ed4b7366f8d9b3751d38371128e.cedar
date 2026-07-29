forbid(
  principal in jc::a::"\u{18}222222222222\u{18}\u{18}\u{18}\u{18}2\u{18}\u{18}\u{18}\u{18}\u{18}\u{18}\u{18}\u{18}",
  action in [jc::Action::"action",jc::Action::"action"],
  resource in jc::a::"\u{18}222222222222\u{18}\u{18}\u{18}\u{18}2\u{18}\u{18}\u{18}\u{18}\u{18}\u{18}\u{18}\u{18}"
) when {
  (true && ((if ("" like "") then (if true then [[[[jc::a::"\u{18}222222222222\u{18}\u{18}\u{18}\u{18}2\u{18}\u{18}\u{18}\u{18}\u{18}\u{18}\u{18}\u{18}", jc::a::"\u{18}222222222222\u{18}\u{18}\u{18}\u{18}2\u{18}\u{18}\u{18}\u{18}\u{18}\u{18}\u{18}\u{18}", jc::a::"\u{18}222222222222\u{18}\u{18}\u{18}\u{18}2\u{18}\u{18}\u{18}\u{18}\u{18}\u{18}\u{18}\u{18}"], [jc::a::"\u{18}222222222222\u{18}\u{18}\u{18}\u{18}2\u{18}\u{18}\u{18}\u{18}\u{18}\u{18}\u{18}\u{18}", principal, resource], [resource, resource]], [[], [resource]], [[resource, resource], [jc::a::"\u{18}222222222222\u{18}\u{18}\u{18}\u{18}2\u{18}\u{18}\u{18}\u{18}\u{18}\u{18}\u{18}\u{18}", resource]]], [[[resource, resource], [jc::a::"\u{18}222222222222\u{18}\u{18}\u{18}\u{18}2\u{18}\u{18}\u{18}\u{18}\u{18}\u{18}\u{18}\u{18}"]], [[principal, principal, principal], [], []]], []] else []) else []).containsAny([]))) && false
};
