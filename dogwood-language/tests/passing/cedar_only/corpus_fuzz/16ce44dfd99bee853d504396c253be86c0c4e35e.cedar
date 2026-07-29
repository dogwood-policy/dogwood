@A000000000000000("")
forbid(
  principal in a::"",
  action == Action::"action",
  resource in a::""
) when {
  (true && (("" == "") || ((if true then [action] else [action]).isEmpty()))) && ((if ([action].isEmpty()) then [action] else [action]).isEmpty())
};
