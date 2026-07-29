@F3cR0000000000000("")
forbid(
  principal in a::"",
  action in [Action::"action",Action::"action",Action::"action"],
  resource in a::""
) when {
  ((true && ((({l: [[[false], [true, true, false], [false, false]], [[false, true], [true, false, false]], []]}.l).containsAll({"\'": [[[true, false, true], [true, false, false], [false, false]], [[false, true], [true, false]], [[true, false, false]]]}["\'"])) && (a::"" in a::""))) && ((if true then true else (principal in action)) || true)) && false
};
