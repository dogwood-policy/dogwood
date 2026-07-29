forbid(
  principal,
  action,
  resource in a::""
) when {
  (true && ({e: resource} == context)) && false
};
