forbid(
  principal in a::"",
  action == Action::"action",
  resource in a::""
) when {
  (true && (["{{E{,\0\0{{{\0", "{{E{,\0\0{{{\0", "{{E{,\0\0{{{\0"].containsAny([[{"{{E{,\0\0{{{\0": {"{{E{,\0\0{{{\0": a::"O"}}, {"{{E{,\0\0{{{\0": {"{{E{,\0\0{{{\0": resource}}, {"{{E{,\0\0{{{\0": {"{{E{,\0\0{{{\0": resource}}], [{"{{E{,\0\0{{{\0": {"{{E{,\0\0{{{\0": principal}}, context], [{"{{E{,\0\0{{{\0": {"{{E{,\0\0{{{\0": principal}}, context, context]]))) && false
};
