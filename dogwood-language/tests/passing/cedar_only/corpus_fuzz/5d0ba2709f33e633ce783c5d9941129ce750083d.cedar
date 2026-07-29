forbid(
  principal in a::"",
  action in [Action::"action"],
  resource is a in a::""
) when {
  ((true && (("\0\u{f}" like "") || ("" like ""))) && ("" like "")) && ("" like "")
};
