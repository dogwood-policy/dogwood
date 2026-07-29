forbid(
  principal in a::"                        ",
  action == Action::"action",
  resource in a::"                        "
) when {
  (true && (a::"                        " in a::"                        ")) && (a::"                        " in resource)
};
