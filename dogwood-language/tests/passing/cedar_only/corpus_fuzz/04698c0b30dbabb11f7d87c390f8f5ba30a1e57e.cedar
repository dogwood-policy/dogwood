@r2pf000000000000("")
forbid(
  principal is a in a::"",
  action in [Action::"action"],
  resource in a::""
) when {
  ((true && ("\0" like "\0*")) && ((if true then "\0" else "\0") like "\0*")) && true
};
