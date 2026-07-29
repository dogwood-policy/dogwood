@A("")
forbid(
  principal,
  action in [Action::"}c"],
  resource == a::""
) when {
  (true && (!false)) && false
};
