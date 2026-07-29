forbid(
  principal,
  action,
  resource == a::""
) when {
  (true && (((principal.getTag("")).getTag(if false then "" else "")) in a::"")) && ((a::"".getTag("")) in [resource.getTag(""), resource.getTag("")])
};
