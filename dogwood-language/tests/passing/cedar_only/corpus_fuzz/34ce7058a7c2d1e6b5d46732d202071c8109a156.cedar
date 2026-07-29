@W0dd00000000("")
permit(
  principal,
  action in [Action::"action",Action::"action"],
  resource == a::""
) when {
  true && ((if (action is a) then action else action) is a)
};
