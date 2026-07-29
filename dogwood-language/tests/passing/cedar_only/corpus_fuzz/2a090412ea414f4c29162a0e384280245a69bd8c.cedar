@V("")
forbid(
  principal == A::A::j::a::"yR",
  action in [A::A::j::Action::"action"],
  resource
) when {
  ((true && (principal is A::A::j::a)) && (((if false then {"": resource} else {"": action})[""]) is A::A::j::a)) && true
};
