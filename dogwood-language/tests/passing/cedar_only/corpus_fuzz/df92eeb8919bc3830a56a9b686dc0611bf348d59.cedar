@A("")
@h("")
forbid(
  principal == a::"",
  action,
  resource
) when {
  true && ("." like "")
};
