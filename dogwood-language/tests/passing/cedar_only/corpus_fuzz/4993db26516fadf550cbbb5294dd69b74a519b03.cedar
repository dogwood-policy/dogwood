permit(
  principal,
  action,
  resource is a
) when {
  ((true && (((principal in [resource]) || (action in [action, resource, principal])) && (principal in [action, a::"\u{1}", resource]))) && ((if ({"": true}[""]) then {"": false} else context)[""])) && false
};
