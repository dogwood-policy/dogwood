permit(
  principal,
  action == Action::"action",
  resource in a::""
) when {
  (true && ("@" like "")) && (a::" " in a::" ")
};
