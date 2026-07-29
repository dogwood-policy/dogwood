@T__4424("")
permit(
  principal,
  action == Action::"action",
  resource
) when {
  true && (resource in [a::"0", principal])
};
