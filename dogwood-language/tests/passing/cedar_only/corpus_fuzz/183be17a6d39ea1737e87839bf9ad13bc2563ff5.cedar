forbid(
  principal in a::"\0",
  action in [Action::"action",Action::"action"],
  resource in a::"\0"
) when {
  (true && (!((if (principal is a) then ((datetime("0000-01-01T14:45:00Z")).durationSince(datetime("0000-01-01"))) else (duration("0ms"))) <= (duration("0ms"))))) && false
};
