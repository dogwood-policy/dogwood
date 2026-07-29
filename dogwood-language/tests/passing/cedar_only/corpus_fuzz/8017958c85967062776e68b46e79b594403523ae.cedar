permit(
  principal,
  action,
  resource in a::"\0\0"
) when {
  (true && ((if ([[resource, resource], [a::"\0\0", principal]].containsAny([[resource, resource], [resource, resource]])) then (if false then [context] else []) else [{"": ""}, {"": ""}]).containsAny(if ([[resource, resource], [resource, resource]].containsAny([[resource, resource], [principal, principal]])) then [] else []))) && false
};
