permit(
  principal,
  action,
  resource in a::"\0\0\0"
) when {
  (true && ((if ([[resource, a::"\0\0\0"], [resource, action]].containsAny([[false, false], [false, false]])) then [] else (if false then [{"": ""}, {"": ""}] else [{"": ""}, {"": ""}])).containsAny([[duration("0ms"), duration("0ms")], []]))) && false
};
