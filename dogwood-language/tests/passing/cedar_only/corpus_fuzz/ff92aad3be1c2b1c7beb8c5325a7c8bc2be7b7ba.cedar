forbid(
  principal in a::"",
  action == Action::"action",
  resource in a::""
) when {
  (true && (["{{E{,\0\0{{{\0", "{{E{,\0\0{{{\0", "{{E{,\0\0{{{\0"].containsAny([{}, {}]))) && false
};
