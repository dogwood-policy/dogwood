@rDcppe0000000000("")
forbid(
  principal in a::"",
  action == Action::"action",
  resource == a::""
) when {
  (true && (a::"" is a)) && (a::"" is a)
};
