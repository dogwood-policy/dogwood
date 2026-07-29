@Y44400000000000("")
forbid(
  principal,
  action in [],
  resource in a::""
) when {
  (true && (a::"" == resource)) && false
};
