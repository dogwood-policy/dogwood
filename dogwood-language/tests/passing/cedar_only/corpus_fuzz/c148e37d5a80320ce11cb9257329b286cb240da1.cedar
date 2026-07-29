@K0000000000000("")
forbid(
  principal,
  action in [Action::"action"],
  resource
) when {
  ((true && ((principal.getTag("")).isMulticast())) && true) && true
};
