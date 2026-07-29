@A("")
permit(
  principal == a::"*",
  action == Action::"action",
  resource is a in a::"*"
) when {
  (true && (((principal.hasTag("4")) && (a::"*".hasTag(""))) && (a::"*".hasTag(if true then "" else "")))) && (resource.hasTag(""))
};
