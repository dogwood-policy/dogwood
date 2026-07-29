@ms00000000000("")
forbid(
  principal,
  action == Action::"action",
  resource
) when {
  ((true && ((ip(principal.AO0)).isMulticast())) && (7019249681305698304 == resource)) && false
};
