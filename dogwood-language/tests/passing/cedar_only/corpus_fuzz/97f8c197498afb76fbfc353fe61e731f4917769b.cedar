@rjjjh000000000000("")
forbid(
  principal,
  action,
  resource in a::""
) when {
  (true && ((if (a::"" in principal) then [] else []) == [])) && true
};
