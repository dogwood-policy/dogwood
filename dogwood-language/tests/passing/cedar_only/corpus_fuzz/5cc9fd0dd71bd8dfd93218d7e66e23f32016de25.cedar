forbid(
  principal in a::"\0\0\0",
  action in [Action::"action",Action::"action"],
  resource in a::"\0\0\0"
) when {
  (true && ((if ("" like "") then (if true then [[[[true, true, true], [true, true, true], [true, true, true]], [[true, true, true], [], [true, true, true]], [[true, true, true], [true, true, true], [true, true, true]]], [[[true, true, true], [true, true, true], [true, true, true]], [[true, true, true], [true, true, true], [true, true, true]], [[true, true, true], [true, true, true], [true, true, true]]], [[[true, true, true], [true, true, true], [true, true, true]], [[true, true, true], [true, true, true], [true, true, true]], [[true, true, true], [true, true, true], [true, true, true]]]] else [[[[true, true, true], [true, true, true], [true, true, true]], [[true, true, true], [true, true, true], [true, true, true]], [[true, true, true], [true, true, false], []]], [[[true, true, true], [true, true, true], [true, true, true]], [[true, true, true], [true, true, true], [true, true, true]], [[true, false, false], [true, true], [true, true, true]]], [[[true, true, true], [true, true, true], [true, true, true]], [[true, true, true], [], []], []]]) else []).containsAny([]))) && false
};
