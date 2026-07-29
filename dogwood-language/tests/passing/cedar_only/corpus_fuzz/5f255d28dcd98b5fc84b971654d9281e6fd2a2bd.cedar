@Y000000000000("")
permit(
  principal,
  action in [Action::"action"],
  resource
) when {
  (true && ("" like "\0*\0*:\0**\0")) && false
};
