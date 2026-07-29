@d("")
forbid(
  principal == a::"\0\0",
  action in [Action::"^",Action::"^",Action::"^"],
  resource
) when {
  true && ((if (action in [principal, a::"\0\0"]) then (-53947541819277134) else (-53947541819277134)) == (-53947541819277134))
};
