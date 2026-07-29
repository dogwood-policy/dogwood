forbid(
  principal in a::"",
  action == Action::"action",
  resource in a::""
) when {
  (true && (["{{\0", "{{\0", "{{\0"].containsAny([[{"{{\0": {"{{\0": a::"O"}}, {"{{\0": {"{{\0": resource}}, {"{{\0": {"{{\0": resource}}], [{"{{\0": {"{{\0": principal}}, {"{{\0": context}], [{"{{\0": context}, context]]))) && false
};
