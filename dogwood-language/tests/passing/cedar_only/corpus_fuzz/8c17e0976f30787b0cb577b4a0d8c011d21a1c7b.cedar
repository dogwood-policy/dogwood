@A("")
forbid(
  principal,
  action,
  resource == a::"R"
) when {
  true && (resource.q)
};
