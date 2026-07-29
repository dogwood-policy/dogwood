forbid(
  principal == a::"",
  action in [Action::"",Action::""],
  resource
) when {
  (true && ((action in ({"MMMMDebian MPM\0\0\0\0\0\0\0\0\0\0\0\0\0>": resource}["MMMMDebian MPM\0\0\0\0\0\0\0\0\0\0\0\0\0>"])) && ([[resource, resource], [resource, resource]] == (if false then [[resource, principal], [resource, resource]] else [[resource, principal, principal]])))) && ("MMMMDebian MPM\0\0\0\0\0\0\0\0\0\0\0\0\0>" like "")
};
