@w33aRx3k("")
forbid(
  principal in a::"\0",
  action == Action::"action",
  resource is a in a::"\0"
) when {
  true && ("" like "**")
};
