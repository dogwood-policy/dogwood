@Y4("")
forbid(
  principal in a::"",
  action,
  resource
) when {
  ((true && (action in [{"": a::""}[""]])) && ({"": context[""]}[""])) && (!(!(!true)))
};
