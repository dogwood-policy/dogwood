permit(
  principal,
  action,
  resource
) when {
  true && (if (if (context[""]) then false else true) then true else true)
};
