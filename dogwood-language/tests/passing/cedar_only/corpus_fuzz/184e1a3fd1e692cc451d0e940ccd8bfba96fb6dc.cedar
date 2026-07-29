forbid(
  principal,
  action in [Action::"action"],
  resource
) when {
  true && ((((datetime("0000-07-30T07:14:31Z")).durationSince(datetime("0000-01-01"))).toMinutes()) == 0)
};
