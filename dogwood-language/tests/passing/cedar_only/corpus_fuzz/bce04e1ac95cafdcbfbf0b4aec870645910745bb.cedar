@A("")
forbid(
  principal,
  action in [Action::"action"],
  resource is a in a::"R"
) when {
  true && (a::"R".r)
};
