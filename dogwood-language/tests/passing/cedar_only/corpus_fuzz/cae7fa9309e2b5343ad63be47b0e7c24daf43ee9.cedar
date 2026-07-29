@T("")
forbid(
  principal in a::"",
  action in [Action::"",Action::""],
  resource in a::""
) when {
  (true && ("" like "")) && ("D" like "T\0ian ")
};
