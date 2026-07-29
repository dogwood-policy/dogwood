@Y4("")
forbid(
  principal in a::"",
  action,
  resource
) when {
  (true && ((if ({"": true}[""]) then ({"": context}[""]) else ({"": {"": true}}[""]))[""])) && (!(action in action))
};
